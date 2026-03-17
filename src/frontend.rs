//! The frontend of our compiler processes source code into an
//! abstract syntax tree (AST). During this process, the frontend
//! ensures that variables are in scope and renames them to use unique
//! identifiers.

use crate::ast::*;
use crate::identifiers::*;
use crate::span::SrcLoc;
use std::collections::HashSet;

pub struct Resolver {
    pub vars: IdGen<VarName>,
    pub funs: IdGen<FunName>,
}

/// CompileErr is an error type that is used to report errors during
/// compilation.
///
/// In the following constructors, the String argument is the original
/// name of the variable or function and the SrcLoc argument is where
/// in the source program the error occurred.
#[derive(Debug, Clone)]
pub enum CompileErr {
    UnboundVariable(String, SrcLoc),
    DuplicateVariable(String, SrcLoc),
    UnboundFunction(String, SrcLoc),
    DuplicateFunction(String, SrcLoc),
    DuplicateParameter(String, SrcLoc),
    ArityMismatch { name: String, expected: usize, found: usize, loc: SrcLoc },
    IntegerOverflow(i64, SrcLoc),
}

use env::Env;
mod env {
    use super::*;

    #[derive(Clone)]
    pub struct Env {
        vars: im::HashMap<String, VarName>,
        funs: im::HashMap<String, (FunName, usize)>,
    }

    impl Env {
        pub fn new() -> Self {
            Env { vars: im::HashMap::new(), funs: im::HashMap::new() }
        }
        pub fn insert_var(&mut self, var: String, name: VarName) {
            self.vars.insert(var.clone(), name.clone());
        }
        pub fn insert_fun(&mut self, fun: String, name: FunName, arity: usize) {
            self.funs.insert(fun, (name, arity));
        }
        pub fn get_var(&self, var: &str) -> Option<&VarName> {
            self.vars.get(var)
        }
        pub fn get_fun(&self, fun: &str) -> Option<(&FunName, usize)> {
            self.funs.get(fun).map(|(f, arity)| (f, *arity))
        }
    }
}

impl Resolver {
    pub fn new() -> Self {
        Resolver { vars: IdGen::new(), funs: IdGen::new() }
    }

    pub fn resolve_prog(&mut self, prog: SurfProg) -> Result<BoundProg, CompileErr> {
        let SurfProg { externs, name, param, body, loc } = prog;
        let mut extern_fun_names = HashSet::new();

        // register the main function
        extern_fun_names.insert(name.clone());
        let fun = FunName::unmangled("entry");
        let mut env = Env::new();
        env.insert_fun(name, fun.clone(), 1);

        // handle external functions
        let externs = externs
            .into_iter()
            .map(|ExtDecl { name, params, loc }| {
                if !extern_fun_names.insert(name.clone()) {
                    Err(CompileErr::DuplicateFunction(name.clone(), loc.clone()))?;
                }
                let name = self.resolve_proc(name, params.as_slice(), &mut env, true)?;
                let mut env = env.clone();
                let params = self.resolve_params(params, &mut env)?;
                Ok(BoundExtDecl { name, params, loc })
            })
            .collect::<Result<Vec<_>, _>>()?;

        // handle the parameter
        let param = (
            {
                let var = self.vars.fresh(param.0.clone());
                env.insert_var(param.0, var.clone());
                var
            },
            param.1,
        );

        // resolve the body
        let body = self.resolve_expr(body, env)?;

        Ok(BoundProg { externs, name: fun, param, body, loc })
    }
    fn resolve_vec_expr(
        &mut self, exprs: Vec<SurfExpr>, env: Env,
    ) -> Result<Vec<BoundExpr>, CompileErr> {
        exprs.into_iter().map(|expr| self.resolve_expr(expr, env.clone())).collect()
    }
    fn resolve_proc(
        &mut self, name: String, params: &[(String, SrcLoc)], env: &mut Env, external: bool,
    ) -> Result<FunName, CompileErr> {
        let fun =
            if external { FunName::unmangled(name.clone()) } else { self.funs.fresh(name.clone()) };
        // collect the function name
        env.insert_fun(name, fun.clone(), params.len());
        // check for duplicate params
        let mut dup = HashSet::new();
        for (param, loc) in params.iter() {
            if !dup.insert(param.clone()) {
                Err(CompileErr::DuplicateParameter(param.clone(), loc.clone()))?;
            }
        }
        Ok(fun)
    }
    fn resolve_params(
        &mut self, params: Vec<(String, SrcLoc)>, env: &mut Env,
    ) -> Result<Vec<(VarName, SrcLoc)>, CompileErr> {
        Ok(Vec::from_iter(params.into_iter().map(|(param, loc)| {
            let var = self.vars.fresh(param.clone());
            env.insert_var(param.clone(), var.clone());
            (var, loc)
        })))
    }
    fn resolve_expr(&mut self, e: SurfExpr, env: Env) -> Result<BoundExpr, CompileErr> {
        let bound_expr = match e {
            Expr::Num(i, loc) => {
                if i > (i64::MAX >> 1) || i < (i64::MIN >> 1) {
                    Err(CompileErr::IntegerOverflow(i, loc))?;
                }
                Expr::Num(i, loc)
            }
            Expr::Bool(b, loc) => Expr::Bool(b, loc),
            Expr::Var(name, loc) => match env.get_var(&name) {
                Some(var) => Expr::Var(var.clone(), loc),
                _ => Err(CompileErr::UnboundVariable(name, loc))?,
            },
            Expr::Prim { prim, args, loc } => {
                let args = self.resolve_vec_expr(args, env)?;
                Expr::Prim { prim, args, loc }
            }
            Expr::Let { bindings, body, loc } => {
                let mut env = env.clone();
                let mut dup = HashSet::new();
                let bindings = bindings
                    .into_iter()
                    .map(|Binding { var, expr }| {
                        let name = var.0.clone();
                        if dup.contains(&name) {
                            Err(CompileErr::DuplicateVariable(name.clone(), loc))?;
                        }
                        dup.insert(name.clone());
                        let var = (self.vars.fresh(name.clone()), var.1.clone());
                        let expr = self.resolve_expr(expr, env.clone())?;
                        env.insert_var(name, var.0.clone());
                        Ok(Binding { var, expr })
                    })
                    .collect::<Result<_, _>>()?;
                let body = self.resolve_expr(*body, env)?;
                Expr::Let { bindings, body: Box::new(body), loc }
            }
            Expr::If { cond, thn, els, loc } => {
                let cond = self.resolve_expr(*cond, env.clone())?;
                let thn = self.resolve_expr(*thn, env.clone())?;
                let els = self.resolve_expr(*els, env.clone())?;
                Expr::If { cond: Box::new(cond), thn: Box::new(thn), els: Box::new(els), loc }
            }
            Expr::FunDefs { decls, body, loc } => {
                let mut env = env.clone();
                // to avoid duplicate function names within the same recursive definition
                let mut local_fun_names = HashSet::new();
                // first, collect all the function names
                for FunDecl { name, params, loc, .. } in decls.iter() {
                    if !local_fun_names.insert(name.clone()) {
                        Err(CompileErr::DuplicateFunction(name.clone(), loc.clone()))?;
                    }
                    self.resolve_proc(name.clone(), params.as_slice(), &mut env, false)?;
                }
                // then resolve the function bodies
                let decls = decls
                    .into_iter()
                    .map(|FunDecl { name, params, body, loc }| {
                        let name = match env.get_fun(&name) {
                            Some((fun, _)) => fun.clone(),
                            None => unreachable!(),
                        };
                        let mut env = env.clone();
                        let params = self.resolve_params(params, &mut env)?;
                        let body = self.resolve_expr(body, env)?;
                        Ok(FunDecl { name, params, body, loc })
                    })
                    .collect::<Result<_, _>>()?;
                let body = self.resolve_expr(*body, env)?;
                Expr::FunDefs { decls, body: Box::new(body), loc }
            }
            Expr::Call { fun: name, args, loc } => {
                let (fun, arity) = match env.get_fun(&name) {
                    Some(fa) => fa,
                    _ => Err(CompileErr::UnboundFunction(name.clone(), loc.clone()))?,
                };
                if args.len() != arity {
                    Err(CompileErr::ArityMismatch {
                        name: name.clone(),
                        expected: arity,
                        found: args.len(),
                        loc: loc.clone(),
                    })?;
                }
                let fun = fun.clone();
                let args = self.resolve_vec_expr(args, env)?;
                Expr::Call { fun, args, loc }
            }
        };
        Ok(bound_expr)
    }
}
