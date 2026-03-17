//! The middle "end" of our compiler is the part that transforms our well-formed
//! source-language abstract syntax tree (AST) into the intermediate representation

use crate::ast::{self, *};
use crate::ssa::{self, *};
use crate::{frontend::Resolver, identifiers::*};
use std::collections::{HashMap, HashSet};

pub struct Lowerer {
    pub vars: IdGen<VarName>,
    pub funs: IdGen<FunName>,
    pub blocks: IdGen<BlockName>,
    /// The live variables at the start of each function.
    fun_scopes: HashMap<FunName, Vec<VarName>>,
    /// The functions that should be lambda lifted.
    should_lift: HashSet<FunName>,
    /// The name of the basic block generated for each function.
    fun_as_block: HashMap<FunName, BlockName>,
    /// Lifted functions. Removed after the lowering pass.
    lifted_funs: Vec<(FunBlock, BasicBlock)>,
}

/// A helper struct for variable renaming.
#[derive(Clone)]
struct Substitution {
    /// The map of old variables to new variables.
    rename_map: HashMap<VarName, VarName>,
}
impl Substitution {
    fn new() -> Self {
        Substitution { rename_map: HashMap::new() }
    }
    fn insert(&mut self, old: VarName, new: VarName) {
        self.rename_map.insert(old, new);
    }
    fn run(&self, mut var: VarName) -> VarName {
        while let Some(new) = self.rename_map.get(&var) {
            var = new.to_owned();
        }
        var
    }
}

/// Indicates whether the expression being compiled is in a tail position.
#[derive(Clone, Debug)]
enum Continuation {
    Return,
    Block(VarName, BlockBody),
}

impl Continuation {
    fn invoke(self, imm: Immediate) -> BlockBody {
        match self {
            Continuation::Return => BlockBody::Terminator(Terminator::Return(imm)),
            Continuation::Block(dest, b) => {
                BlockBody::Operation { dest, op: Operation::Immediate(imm), next: Box::new(b) }
            }
        }
    }
}

impl From<Resolver> for Lowerer {
    fn from(resolver: Resolver) -> Self {
        let Resolver { vars, funs, .. } = resolver;
        Lowerer {
            vars,
            funs,
            blocks: IdGen::new(),
            fun_scopes: HashMap::new(),
            should_lift: HashSet::new(),
            fun_as_block: HashMap::new(),
            lifted_funs: Vec::new(),
        }
    }
}

/// Traverse the AST and collect the live variables at the start of each function.
/// Also collect the functions that are non-tail called and the functions that are called
/// by a lifted function, either tail or non-tail.
struct Lifter {
    /// Functions that are non-tail called.
    non_tail_called_funs: HashSet<FunName>,
    /// The call graph of the program.
    /// Records all functions that are called, either tail or non-tail.
    /// Used to lift all functions called by a lifted function.
    fun_calls: HashMap<FunName, HashSet<FunName>>,
}

impl Lifter {
    /// What should be lambda lifted?
    /// 1. Any function that is called with a non-tail call.
    /// 2. Any function that is called by a lifted function.
    pub fn should_lift(&self) -> HashSet<FunName> {
        let mut should_lift = HashSet::new();
        // find all functions that should be lifted
        let mut worklist = self.non_tail_called_funs.iter().cloned().collect::<Vec<_>>();
        while let Some(fun) = worklist.pop() {
            // 1. include the function in worklist to the result set
            if should_lift.insert(fun.clone()) {
                // 2. if it's the first time met, add all functions that it calls to the worklist
                worklist.extend(self.fun_calls.get(&fun).cloned().unwrap_or_default());
            }
        }
        should_lift
    }
}

impl Lifter {
    fn new() -> Self {
        Self { non_tail_called_funs: HashSet::new(), fun_calls: HashMap::new() }
    }

    fn lift_prog(&mut self, prog: &BoundProg) {
        let Prog { externs: _, name, param: _, body, loc: _ } = prog;
        self.lift_expr(body, &name, true);
    }

    fn lift_expr(&mut self, e: &BoundExpr, site: &FunName, tail_position: bool) {
        match e {
            Expr::Num(_, _) | Expr::Bool(_, _) | Expr::Var(_, _) => {}
            Expr::Prim { prim: _, args, loc: _ } => {
                for arg in args {
                    self.lift_expr(arg, site, false);
                }
            }
            Expr::Let { bindings, body, loc: _ } => {
                for Binding { var: _, expr } in bindings {
                    self.lift_expr(expr, site, false);
                }
                self.lift_expr(body, site, tail_position);
            }
            Expr::If { cond, thn, els, loc: _ } => {
                self.lift_expr(cond, site, false);
                self.lift_expr(thn, site, tail_position);
                self.lift_expr(els, site, tail_position);
            }
            Expr::FunDefs { decls, body, loc: _ } => {
                for FunDecl { name, body, .. } in decls {
                    self.lift_expr(body, name, true);
                }
                self.lift_expr(body, site, tail_position);
            }
            Expr::Call { fun, args, loc: _ } => {
                if !tail_position {
                    self.non_tail_called_funs.insert(fun.clone());
                }
                self.fun_calls.entry(site.clone()).or_default().insert(fun.clone());
                for arg in args {
                    self.lift_expr(arg, site, false);
                }
            }
        }
    }
}

impl Lowerer {
    pub fn lower_prog(&mut self, prog: BoundProg) -> Program {
        // first, collect all functions that should be lifted
        let mut lifter = Lifter::new();
        lifter.lift_prog(&prog);
        self.should_lift = lifter.should_lift();

        // then, lower the program
        let Prog { externs, name, param, body, loc: _ } = prog;
        // register function scope for the main function
        self.fun_scopes.insert(name.clone(), Vec::new());
        // create a block name for the main function
        let block = self.blocks.fresh(name.hint());
        self.fun_as_block.insert(name.clone(), block.clone());
        // lower the externs
        let externs =
            Vec::from_iter(externs.into_iter().map(|ExtDecl { name, params, loc: _ }| Extern {
                name,
                params: params.into_iter().map(|(p, _)| p).collect(),
            }));
        // lower the parameter
        let (param, _) = param;
        // lower the body
        let body = self.lower_expr_kont(
            body,
            &vec![param.clone()],
            &Substitution::new(),
            Continuation::Return,
        );
        // collect the lifted functions and blocks
        let (mut funs, mut blocks): (Vec<FunBlock>, Vec<BasicBlock>) =
            std::mem::take(&mut self.lifted_funs).into_iter().unzip();
        // create the entry block and function
        blocks.push(BasicBlock { label: block.clone(), params: vec![param.clone()], body });
        let fun_param = self.vars.fresh(param.hint());
        funs.push(FunBlock {
            name,
            params: vec![fun_param.clone()],
            body: Branch { target: block, args: vec![Immediate::Var(fun_param)] },
        });
        Program { externs, funs, blocks }
    }

    fn kont_to_block(&mut self, k: Continuation) -> (VarName, BlockBody) {
        match k {
            Continuation::Block(x, b) => (x, b),
            Continuation::Return => {
                let x = self.vars.fresh("result");
                (x.clone(), BlockBody::Terminator(Terminator::Return(Immediate::Var(x))))
            }
        }
    }

    /// Compiles an expression to a basic block that uses the continuation k on
    /// the value e produces.
    fn lower_expr_kont(
        &mut self, e: BoundExpr, live: &[VarName], subst: &Substitution, k: Continuation,
    ) -> BlockBody {
        match e {
            Expr::Num(n, _) => {
                todo!("implement this")
            }
            Expr::Bool(b, _) => {
                todo!("implement this")
            }
            Expr::Var(v, _) => k.invoke(Immediate::Var(subst.run(v))),
            Expr::Prim { prim, args, loc: _ } => {
                todo!("implement these primitive operators")
            }
            Expr::Let { bindings, body, loc: _ } => {
                // collect the live variables up to this point
                let mut live = live
                    .to_owned()
                    .into_iter()
                    .chain(bindings.iter().map(|Binding { var: (var, _), .. }| var.clone()))
                    .collect::<Vec<_>>();

                // backwards, here we go
                let block = self.lower_expr_kont(*body, &live, subst, k);

                // reversed, as usual
                bindings.into_iter().rev().fold(block, |block, Binding { var: (var, _), expr }| {
                    live.pop();
                    let expr = self.lower_expr_kont(
                        expr,
                        &live,
                        subst,
                        Continuation::Block(var.clone(), block),
                    );
                    expr
                })
            }
            Expr::If { cond, thn, els, loc: _ } => {
                todo!("implement if expression")
            }
            Expr::FunDefs { decls, body, loc: _ } => {
                // create a block name for each function
                for FunDecl { name: fun, .. } in decls.iter() {
                    let block = self.blocks.fresh(fun.hint());
                    self.fun_as_block.insert(fun.clone(), block);
                    // collect the live variables up to this point
                    self.fun_scopes.insert(fun.clone(), live.to_owned());
                }
                // lower the body
                let next = Box::new(self.lower_expr_kont(*body, live, subst, k));
                // compile the functions
                BlockBody::SubBlocks {
                    blocks: decls
                        .into_iter()
                        .filter_map(|FunDecl { name: fun, params, body, loc: _ }| {
                            let live = live
                                .to_owned()
                                .into_iter()
                                .chain(params.iter().map(|(p, _)| p.clone()))
                                .collect::<Vec<_>>();
                            let block =
                                self.fun_as_block.get(&fun).cloned().expect("fun not found");
                            if self.should_lift.contains(&fun) {
                                // Here we need to produce a fundecl in lifted_funs,
                                // but we need to add extra arguments.
                                let mut subst = subst.clone();
                                // get ambient live variables rename the ambient variables
                                // to be unique; the ambient variables are prefixed with "@"
                                let ambient = self
                                    .fun_scopes
                                    .get(&fun)
                                    .cloned()
                                    .expect("fun not found")
                                    .into_iter()
                                    .map(|v| {
                                        // with a hint from the previous name
                                        let new = self.vars.fresh(format!("@{}", v.hint()));
                                        subst.insert(v, new.clone());
                                        new
                                    });
                                // get function parameters prepared
                                let fun_params = params.into_iter().map(|(p, _)| p);
                                // parameters are ambient live variables and the function parameters combined
                                let params = ambient.chain(fun_params).collect::<Vec<_>>();
                                let body =
                                    self.lower_expr_kont(body, &live, &subst, Continuation::Return);
                                let funblock_params = params
                                    .iter()
                                    .map(|p| self.vars.fresh(p.hint()))
                                    .collect::<Vec<_>>();
                                let funblock = FunBlock {
                                    name: fun.clone(),
                                    params: funblock_params.clone(),
                                    body: Branch {
                                        target: block.clone(),
                                        args: funblock_params
                                            .clone()
                                            .into_iter()
                                            .map(|p| Immediate::Var(p))
                                            .collect(),
                                    },
                                };
                                let block = BasicBlock { label: block, params, body };
                                self.lifted_funs.push((funblock, block));
                                None
                            } else {
                                // tail recursive functions are built as sub-blocks
                                Some(BasicBlock {
                                    label: block.clone(),
                                    params: params.into_iter().map(|(p, _)| p).collect(),
                                    body: self.lower_expr_kont(
                                        body,
                                        &live,
                                        subst,
                                        Continuation::Return,
                                    ),
                                })
                            }
                        })
                        .collect(),
                    next,
                }
            }
            Expr::Call { fun, args, loc: _ } => {
                // prepare the arguments
                let (args_var, args_imm): (Vec<_>, _) = args
                    .iter()
                    .enumerate()
                    .map(|(i, _arg)| {
                        // the arguments are named after the function name and the argument index
                        let var = self.vars.fresh(format!("{}_{}", fun.hint(), i));
                        (var.clone(), Immediate::Var(var))
                    })
                    .unzip();
                let lower_call = |lowerer: &mut Lowerer, block: BlockBody| {
                    // backwards, so we need to reverse the arguments
                    args.into_iter().zip(args_var).rev().fold(block, |block, (arg, var)| {
                        lowerer.lower_expr_kont(arg, &live, subst, Continuation::Block(var, block))
                    })
                };
                if fun.is_unmangled() {
                    // extern function. Always produce a call here
                    let (dest, next) = self.kont_to_block(k);
                    lower_call(
                        self,
                        BlockBody::Operation {
                            dest,
                            op: Operation::Call { fun, args: args_imm },
                            next: Box::new(next),
                        },
                    )
                } else {
                    let block = self.fun_as_block.get(&fun).cloned().expect("fun not found");
                    if self.should_lift.contains(&fun) {
                        let ambient = self
                            .fun_scopes
                            .get(&fun)
                            .cloned()
                            .expect("fun not found")
                            .into_iter()
                            .map(|v| subst.run(v));
                        // the arguments are the ambient live variables and the arguments combined
                        let args_imm =
                            ambient.map(|v| Immediate::Var(v)).chain(args_imm).collect::<Vec<_>>();

                        match k {
                            Continuation::Return => lower_call(
                                self,
                                BlockBody::Terminator(Terminator::Branch(Branch {
                                    target: block,
                                    args: args_imm,
                                })),
                            ),
                            Continuation::Block(dest, next) => lower_call(
                                self,
                                BlockBody::Operation {
                                    dest,
                                    op: Operation::Call { fun, args: args_imm },
                                    next: Box::new(next),
                                },
                            ),
                        }
                    } else {
                        // tail calls are compiled to a branch
                        assert!(matches!(k, Continuation::Return));
                        lower_call(
                            self,
                            BlockBody::Terminator(Terminator::Branch(Branch {
                                target: block,
                                args: args_imm,
                            })),
                        )
                    }
                }
            }
        }
    }
}
