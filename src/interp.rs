//! Interpreter for the snake language and its SSA form.

use crate::identifiers::*;
use crate::types::*;
use std::{
    fmt::{self, Display},
    hash::Hash,
    rc::Rc,
};

#[derive(Clone, Copy, Debug)]
pub enum Value {
    Int(i64),
    Bool(bool),
    FatPtr(ArenaPtr),
    Raw(Raw),
}

trait AssertInto: Sized {
    fn assert_into<Var, Fun>(value: Value) -> Result<Self, InterpErr<Var, Fun>>;
}
impl AssertInto for i64 {
    fn assert_into<Var, Fun>(value: Value) -> Result<Self, InterpErr<Var, Fun>> {
        match value {
            Value::Int(n) => Ok(n),
            _ => Err(InterpErr::AssertTypeFailed(Type::Int)),
        }
    }
}
impl AssertInto for bool {
    fn assert_into<Var, Fun>(value: Value) -> Result<Self, InterpErr<Var, Fun>> {
        match value {
            Value::Bool(b) => Ok(b),
            _ => Err(InterpErr::AssertTypeFailed(Type::Bool)),
        }
    }
}
impl AssertInto for ArenaPtr {
    fn assert_into<Var, Fun>(value: Value) -> Result<Self, InterpErr<Var, Fun>> {
        match value {
            Value::FatPtr(ptr) => Ok(ptr),
            _ => Err(InterpErr::AssertTypeFailed(Type::Array)),
        }
    }
}
impl AssertInto for Raw {
    fn assert_into<Var, Fun>(value: Value) -> Result<Self, InterpErr<Var, Fun>> {
        match value {
            Value::Raw(n) => Ok(n),
            _ => Err(InterpErr::AssertRawFailed),
        }
    }
}
impl Default for Value {
    fn default() -> Self {
        Self::Int(0)
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Int(n) => write!(f, "{}", n),
            Value::Bool(b) => write!(f, "{}", b),
            Value::FatPtr(ptr) => write!(f, "<arena@{}>", ptr.idx),
            Value::Raw(r) => write!(f, "<raw:{}>", r),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Raw(pub i64);
impl Raw {
    pub fn size(n: usize) -> Self {
        Self(n as i64)
    }
    pub fn downcast<Var, Fun>(self) -> Result<Value, InterpErr<Var, Fun>> {
        if self.0 & Type::Int.mask() == 0 {
            Ok(Value::Int(self.0 >> 1))
        } else if self.0 & Type::Array.mask() == Type::Array.tag() {
            Ok(Value::FatPtr(ArenaPtr { idx: ((self.0 ^ 0b11) >> 2) as usize }))
        } else if self.0 & Type::Bool.mask() == Type::Bool.tag() {
            Ok(Value::Bool(self.0 & 0b100 != 0))
        } else {
            Err(InterpErr::AssertRawFailed)
        }
    }
}
impl From<Raw> for i64 {
    fn from(raw: Raw) -> Self {
        raw.0
    }
}
impl From<Raw> for ArenaPtr {
    fn from(raw: Raw) -> Self {
        Self { idx: raw.0 as usize }
    }
}
impl From<Value> for Raw {
    fn from(value: Value) -> Self {
        match value {
            Value::Int(n) => Self(n << 1),
            Value::Bool(b) => Self(if b { 0b101 } else { 0b001 }),
            Value::FatPtr(ptr) => Self((ptr.idx as i64) << 2 | Type::Array.tag()),
            Value::Raw(r) => r,
        }
    }
}
impl Display for Raw {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "0x{:x}", self.0)
    }
}

#[derive(Clone, Copy, Debug)]
pub struct ArenaPtr {
    idx: usize,
}

pub struct Arena<T> {
    inner: Vec<T>,
}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    pub fn get(&self, ptr: ArenaPtr, idx: usize) -> &T {
        &self.inner[ptr.idx + idx]
    }

    pub fn set(&mut self, ptr: ArenaPtr, idx: usize, val: T) {
        self.inner[ptr.idx + idx] = val;
    }
}

impl Arena<Value> {
    pub fn alloc(&mut self, size: usize) -> ArenaPtr {
        let ptr = ArenaPtr { idx: self.inner.len() };
        self.inner.push(Value::Raw(Raw::size(size)));
        for _ in 0..size {
            self.inner.push(Default::default());
        }
        ptr
    }
    pub fn equal<Var, Fun>(&self, a: &Value, b: &Value) -> Result<bool, InterpErr<Var, Fun>> {
        match (a, b) {
            (Value::Int(a), Value::Int(b)) => Ok(a == b),
            (Value::Bool(a), Value::Bool(b)) => Ok(a == b),
            (Value::FatPtr(a), Value::FatPtr(b)) => {
                let a_size = Raw::assert_into(self.inner[a.idx])?;
                let b_size = Raw::assert_into(self.inner[b.idx])?;
                let a = self.inner[a.idx..=(a.idx + a_size.0 as usize)].into_iter();
                let b = self.inner[b.idx..=(b.idx + b_size.0 as usize)].into_iter();
                a.zip(b).try_fold(true, |acc, (a, b)| Ok(acc && self.equal(a, b)?))
            }
            (Value::Raw(a), Value::Raw(b)) => Ok(a == b),
            _ => Ok(false),
        }
    }
}

#[derive(Clone, Debug)]
pub enum InterpErr<Var, Fun> {
    Unimplemented,
    InvalidArg(String),
    UnboundVar(Var),
    UnboundFun(Fun),
    UnExpectedFun(Fun),
    CallToConst(Value),
    CallWrongArity { name: Fun, expected: usize, got: usize },
    UnboundBlock(BlockName),
    BrWrongArity { name: BlockName, expected: usize, got: usize },
    AssertTypeFailed(Type),
    AssertRawFailed,
    AssertLength,
    AssertInBoundsFailed { bound: i64, of: i64 },
    InvalidEncoding(Raw),
}

impl<Var: Display, Fun: Display> Display for InterpErr<Var, Fun> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InterpErr::Unimplemented => write!(f, "unimplemented"),
            InterpErr::InvalidArg(arg) => write!(f, "invalid argument: {}", arg),
            InterpErr::UnboundVar(var) => write!(f, "unbound variable: {}", var),
            InterpErr::UnboundFun(fun) => write!(f, "unbound function: {}", fun),
            InterpErr::UnExpectedFun(fun) => write!(f, "unexpected function: {}", fun),
            InterpErr::CallToConst(n) => write!(f, "call to constant: {}", n),
            InterpErr::CallWrongArity { name, expected, got } => {
                write!(
                    f,
                    "calling function {} with wrong arity: expected {}, got {}",
                    name, expected, got
                )
            }
            InterpErr::UnboundBlock(block) => write!(f, "unbound block: {}", block),
            InterpErr::BrWrongArity { name, expected, got } => {
                write!(
                    f,
                    "branching to block {} with wrong arity: expected {}, got {}",
                    name, expected, got
                )
            }
            InterpErr::AssertTypeFailed(ty) => write!(f, "{} assertion failed", ty),
            InterpErr::AssertRawFailed => write!(f, "raw encoding assertion failed"),
            InterpErr::AssertLength => write!(f, "negative length"),
            InterpErr::AssertInBoundsFailed { bound, of } => {
                write!(f, "{} is out of bounds of [0, {})", of, bound)
            }
            InterpErr::InvalidEncoding(raw) => write!(f, "invalid encoding: 0x{:x}", raw.0),
        }
    }
}

fn parse_snake_basic_val<Var, Fun>(s: String) -> Result<Value, InterpErr<Var, Fun>> {
    let s = s.trim();
    if s == "true" {
        Ok(Value::Bool(true))
    } else if s == "false" {
        Ok(Value::Bool(false))
    } else if let Ok(x) = s.parse::<i64>() {
        Ok(Value::Int(x))
    } else {
        Err(InterpErr::InvalidArg(s.to_string()))
    }
}

/* ---------------------------------- Snake --------------------------------- */

pub mod ast {
    use super::*;
    use crate::ast::*;
    use im::HashMap;

    pub struct Machine<Var, Fun> {
        redex: Redex<Var, Fun>,
        stack: Stack<Var, Fun>,
        heap: Arena<Value>,
    }

    #[derive(Clone)]
    enum Redex<Var, Fun> {
        Decending { expr: Rc<Expr<Var, Fun>>, env: Env<Var, Fun> },
        Ascending(DynValue<Var, Fun>),
    }

    #[derive(Clone)]
    struct RcFunDef<Var, Fun> {
        params: Vec<Var>,
        body: Rc<Expr<Var, Fun>>,
    }

    #[derive(Clone)]
    struct Closure<Var, Fun> {
        env: Env<Var, Fun>,
        decls: HashMap<Fun, RcFunDef<Var, Fun>>,
        name: Fun,
    }

    #[derive(Clone)]
    enum DynValue<Var, Fun> {
        Value(Value),
        Closure(Closure<Var, Fun>),
    }

    #[derive(Clone, Hash, PartialEq, Eq)]
    enum VarOrFun<Var, Fun> {
        Var(Var),
        Fun(Fun),
    }

    type Env<Var, Fun> = HashMap<VarOrFun<Var, Fun>, DynValue<Var, Fun>>;

    #[derive(Clone)]
    enum Operator<Fun> {
        Prim(Prim),
        Call(Fun),
    }

    #[derive(Clone)]
    enum Stack<Var, Fun> {
        Return,
        Operation {
            operator: Operator<Fun>,
            env: Env<Var, Fun>,
            /// evaluated arguments
            evaluated: Vec<DynValue<Var, Fun>>,
            /// reversed remaining arguments
            remaining: Vec<Rc<Expr<Var, Fun>>>,
            stack: Box<Stack<Var, Fun>>,
        },
        Let {
            env: Env<Var, Fun>,
            var: Var,
            remaining: Vec<(Var, Rc<Expr<Var, Fun>>)>,
            body: Rc<Expr<Var, Fun>>,
            stack: Box<Stack<Var, Fun>>,
        },
        If {
            env: Env<Var, Fun>,
            thn: Rc<Expr<Var, Fun>>,
            els: Rc<Expr<Var, Fun>>,
            stack: Box<Stack<Var, Fun>>,
        },
    }

    impl<Var, Fun> Machine<Var, Fun>
    where
        Var: Hash + Eq + Clone,
        Fun: Hash + Eq + Clone,
    {
        pub fn run<S>(
            Prog { externs, name, param: (param, _), body, loc: _ }: &Prog<Var, Fun>,
            args: impl IntoIterator<Item = S>,
        ) -> Result<Value, InterpErr<Var, Fun>>
        where
            S: Into<String>,
        {
            // Note: extern functions are not supported
            assert!(externs.is_empty(), "extern functions are not supported");

            let args: Vec<Value> = args
                .into_iter()
                .map(Into::into)
                .map(parse_snake_basic_val)
                .collect::<Result<_, _>>()?;
            let mut env = HashMap::new();
            let mut heap = Arena::new();
            let ptr = heap.alloc(args.len());
            args.into_iter().enumerate().for_each(|(i, arg)| {
                heap.set(ptr, i + 1, arg);
            });
            let arr = Value::FatPtr(ptr);
            let decls = HashMap::from_iter([(
                name.clone(),
                RcFunDef { params: vec![param.clone()], body: Rc::new(body.clone()) },
            )]);
            env.insert(
                VarOrFun::Fun(name.clone()),
                DynValue::Closure(Closure { env: HashMap::new(), decls, name: name.clone() }),
            );
            env.insert(VarOrFun::Var(param.clone()), DynValue::Value(arr));
            let redex = Redex::Decending { expr: Rc::new(body.clone()), env };
            let machine = Machine { redex, stack: Stack::Return, heap };
            match machine.run_expr()? {
                DynValue::Value(v) => Ok(v),
                DynValue::Closure(Closure { name, .. }) => Err(InterpErr::UnExpectedFun(name)),
            }
        }
        fn run_expr(mut self) -> Result<DynValue<Var, Fun>, InterpErr<Var, Fun>> {
            loop {
                self = match self {
                    Machine { redex: Redex::Decending { expr, env }, stack, heap } => {
                        Self::dive_expr(expr, env, stack, heap)?
                    }
                    Machine { redex: Redex::Ascending(dv), stack: Stack::Return, heap: _ } => {
                        // the termination of the interpreter
                        break Ok(dv);
                    }
                    Machine { redex: Redex::Ascending(dv), stack, heap } => {
                        Self::run_kont(dv, stack, heap)?
                    }
                };
            }
        }
        fn dive_expr(
            expr: Rc<Expr<Var, Fun>>, env: Env<Var, Fun>, stack: Stack<Var, Fun>,
            heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            let ret_machine = |dv: DynValue<Var, Fun>, stack, heap| Machine {
                redex: Redex::Ascending(dv),
                stack,
                heap,
            };
            let dive_machine = |expr, env, stack, heap| Machine {
                redex: Redex::Decending { expr, env },
                stack,
                heap,
            };
            match expr.as_ref() {
                Expr::Num(n, _) => Ok(ret_machine(DynValue::Value(Value::Int(*n)), stack, heap)),
                Expr::Bool(b, _) => Ok(ret_machine(DynValue::Value(Value::Bool(*b)), stack, heap)),
                Expr::Var(v, _) => {
                    let val = env
                        .get(&VarOrFun::Var(v.clone()))
                        .ok_or_else(|| InterpErr::UnboundVar(v.clone()))?;
                    Ok(ret_machine(val.clone(), stack, heap))
                }
                Expr::Prim { prim, args, loc: _ } => Self::dive_operator(
                    Operator::Prim(prim.clone()),
                    args,
                    env.clone(),
                    stack,
                    heap,
                ),
                Expr::Let { bindings, body, loc: _ } => {
                    let mut remaining: Vec<_> = bindings
                        .iter()
                        .cloned()
                        .rev()
                        .map(|Binding { var: (var, _), expr }| (var, Rc::new(expr.clone())))
                        .collect();
                    let body = Rc::new(body.as_ref().clone());
                    if let Some((var, expr)) = remaining.pop() {
                        let stack = Box::new(stack);
                        Ok(dive_machine(
                            expr,
                            env.clone(),
                            Stack::Let { env, var, remaining, body, stack },
                            heap,
                        ))
                    } else {
                        Ok(dive_machine(body, env.clone(), stack, heap))
                    }
                }
                Expr::If { cond, thn, els, loc: _ } => {
                    let thn = Rc::new(thn.as_ref().clone());
                    let els = Rc::new(els.as_ref().clone());
                    let stack = Box::new(stack);
                    Ok(dive_machine(
                        Rc::new(cond.as_ref().clone()),
                        env.clone(),
                        Stack::If { env, thn, els, stack },
                        heap,
                    ))
                }
                Expr::FunDefs { decls, body, loc: _ } => {
                    let curr = env;
                    let mut next = curr.clone();
                    let decls = HashMap::from_iter(decls.iter().cloned().map(
                        |FunDecl { name, params, body, loc: _ }| {
                            (
                                name.clone(),
                                RcFunDef {
                                    params: params.into_iter().map(|(var, _)| var).collect(),
                                    body: Rc::new(body),
                                },
                            )
                        },
                    ));
                    for name in decls.keys() {
                        next.insert(
                            VarOrFun::Fun(name.clone()),
                            DynValue::Closure(Closure {
                                env: curr.clone(),
                                decls: decls.clone(),
                                name: name.clone(),
                            }),
                        );
                    }
                    Ok(dive_machine(Rc::new(body.as_ref().clone()), next, stack, heap))
                }
                Expr::Call { fun, args, loc: _ } => {
                    Self::dive_operator(Operator::Call(fun.clone()), args, env.clone(), stack, heap)
                }
            }
        }
        fn dive_operator(
            operator: Operator<Fun>, args: &[Expr<Var, Fun>], env: Env<Var, Fun>,
            stack: Stack<Var, Fun>, heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            let dive_machine = |expr, env, stack, heap| Machine {
                redex: Redex::Decending { expr, env },
                stack,
                heap,
            };
            let mut remaining: Vec<_> =
                args.iter().cloned().rev().map(|expr| Rc::new(expr.clone())).collect();
            if let Some(expr) = remaining.pop() {
                let stack = Box::new(stack);
                Ok(dive_machine(
                    expr,
                    env.clone(),
                    Stack::Operation { operator, env, evaluated: Vec::new(), remaining, stack },
                    heap,
                ))
            } else {
                match operator {
                    Operator::Prim(Prim::MakeArray) => Self::run_array(Vec::new(), stack, heap),
                    Operator::Call(fun) => Self::run_call(fun, Vec::new(), env, stack, heap),
                    _ => unreachable!(
                        "no arguments to evaluate in primitive operator, error in our interpreter?!"
                    ),
                }
            }
        }
        fn run_kont(
            dv: DynValue<Var, Fun>, stack: Stack<Var, Fun>, heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            match stack {
                Stack::Return => {
                    unreachable!("return kont should not be run, error in our interpreter?!")
                }
                Stack::Operation { operator, env, mut evaluated, mut remaining, stack } => {
                    evaluated.push(dv);
                    if let Some(expr) = remaining.pop() {
                        Ok(Machine {
                            redex: Redex::Decending { expr, env: env.clone() },
                            stack: Stack::Operation { operator, env, evaluated, remaining, stack },
                            heap,
                        })
                    } else {
                        match operator {
                            Operator::Prim(prim) => match prim {
                                Prim::Add1 => {
                                    Self::run_prim1_int(|n| n + 1, evaluated, *stack, heap)
                                }
                                Prim::Sub1 => {
                                    Self::run_prim1_int(|n| n - 1, evaluated, *stack, heap)
                                }
                                Prim::Not => Self::run_prim1_bool(|b| !b, evaluated, *stack, heap),
                                Prim::Add => {
                                    Self::run_prim2_int_int(|n, m| n + m, evaluated, *stack, heap)
                                }
                                Prim::Sub => {
                                    Self::run_prim2_int_int(|n, m| n - m, evaluated, *stack, heap)
                                }
                                Prim::Mul => {
                                    Self::run_prim2_int_int(|n, m| n * m, evaluated, *stack, heap)
                                }
                                Prim::And => Self::run_prim2_bool_bool(
                                    |n, m| n && m,
                                    evaluated,
                                    *stack,
                                    heap,
                                ),
                                Prim::Or => Self::run_prim2_bool_bool(
                                    |n, m| n || m,
                                    evaluated,
                                    *stack,
                                    heap,
                                ),
                                Prim::Lt => {
                                    Self::run_prim2_int_bool(|n, m| n < m, evaluated, *stack, heap)
                                }
                                Prim::Le => {
                                    Self::run_prim2_int_bool(|n, m| n <= m, evaluated, *stack, heap)
                                }
                                Prim::Gt => {
                                    Self::run_prim2_int_bool(|n, m| n > m, evaluated, *stack, heap)
                                }
                                Prim::Ge => {
                                    Self::run_prim2_int_bool(|n, m| n >= m, evaluated, *stack, heap)
                                }
                                Prim::Eq => Self::run_prim2_heap(
                                    |heap, a, b| Ok(Value::Bool(heap.equal(&a, &b)?)),
                                    evaluated,
                                    *stack,
                                    heap,
                                ),
                                Prim::Neq => Self::run_prim2_heap(
                                    |heap, a, b| Ok(Value::Bool(!heap.equal(&a, &b)?)),
                                    evaluated,
                                    *stack,
                                    heap,
                                ),
                                Prim::IsType(ty) => Self::run_prim1(
                                    |v| {
                                        let b = match (v, ty) {
                                            (Value::Int(_), Type::Int) => true,
                                            (Value::Bool(_), Type::Bool) => true,
                                            (Value::FatPtr(_), Type::Array) => true,
                                            _ => false,
                                        };
                                        Ok(Value::Bool(b))
                                    },
                                    evaluated,
                                    *stack,
                                    heap,
                                ),
                                Prim::NewArray => Self::run_prim1_heap_mut(
                                    |heap, a| {
                                        let size = i64::assert_into(a)?;
                                        let ptr = heap.alloc(size as usize);
                                        Ok(Value::FatPtr(ptr))
                                    },
                                    evaluated,
                                    *stack,
                                    heap,
                                ),
                                Prim::MakeArray => Self::run_array(evaluated, *stack, heap),
                                Prim::ArrayGet => Self::run_prim2_heap(
                                    |heap, ptr, idx| {
                                        let ptr = ArenaPtr::assert_into(ptr)?;
                                        let idx = i64::assert_into(idx)?;
                                        // check index is in bounds
                                        let Value::Raw(len) = heap.get(ptr, 0) else {
                                            Err(InterpErr::AssertRawFailed)?
                                        };
                                        let Raw(len) = *len;
                                        if idx < 0 || idx >= len {
                                            Err(InterpErr::AssertInBoundsFailed {
                                                bound: len,
                                                of: idx,
                                            })?
                                        }
                                        Ok(*heap.get(ptr, idx as usize + 1))
                                    },
                                    evaluated,
                                    *stack,
                                    heap,
                                ),
                                Prim::ArraySet => Self::run_prim3_heap_mut(
                                    |heap, ptr, idx, val| {
                                        let ptr = ArenaPtr::assert_into(ptr)?;
                                        let idx = i64::assert_into(idx)?;
                                        // check index is in bounds
                                        let Value::Raw(len) = heap.get(ptr, 0) else {
                                            Err(InterpErr::AssertRawFailed)?
                                        };
                                        let Raw(len) = *len;
                                        if idx < 0 || idx >= len {
                                            Err(InterpErr::AssertInBoundsFailed {
                                                bound: len,
                                                of: idx,
                                            })?
                                        }
                                        heap.set(ptr, idx as usize + 1, val);
                                        Ok(val)
                                    },
                                    evaluated,
                                    *stack,
                                    heap,
                                ),
                                Prim::Length => Self::run_prim1_heap(
                                    |heap, a| {
                                        let ptr = ArenaPtr::assert_into(a)?;
                                        let size = Raw::assert_into(*heap.get(ptr, 0))?;
                                        Ok(Value::Int(size.0))
                                    },
                                    evaluated,
                                    *stack,
                                    heap,
                                ),
                            },
                            Operator::Call(fun) => {
                                Self::run_call(fun, evaluated, env, *stack, heap)
                            }
                        }
                    }
                }
                Stack::Let { mut env, var, mut remaining, body, stack } => {
                    env.insert(VarOrFun::Var(var.clone()), dv);
                    if let Some((var, expr)) = remaining.pop() {
                        Ok(Machine {
                            redex: Redex::Decending { expr: expr.clone(), env: env.clone() },
                            stack: Stack::Let { env, var, remaining, body, stack },
                            heap,
                        })
                    } else {
                        let stack = *stack;
                        Ok(Machine {
                            redex: Redex::Decending { expr: body.clone(), env },
                            stack,
                            heap,
                        })
                    }
                }
                Stack::If { env, thn, els, stack } => {
                    let n = match dv {
                        DynValue::Value(n) => n,
                        DynValue::Closure(Closure { name, .. }) => {
                            Err(InterpErr::UnExpectedFun(name))?
                        }
                    };
                    let stack = *stack;
                    let Value::Bool(b) = n else { Err(InterpErr::AssertTypeFailed(Type::Bool))? };
                    if b {
                        let expr = thn.clone();
                        Ok(Machine { redex: Redex::Decending { expr, env }, stack, heap })
                    } else {
                        let expr = els.clone();
                        Ok(Machine { redex: Redex::Decending { expr, env }, stack, heap })
                    }
                }
            }
        }
        fn run_prim1_int(
            prim_f: impl Fn(i64) -> i64, args: Vec<DynValue<Var, Fun>>, stack: Stack<Var, Fun>,
            heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            let f = |v| {
                let n = i64::assert_into(v)?;
                Ok(Value::Int(prim_f(n)))
            };
            Self::run_prim1(f, args, stack, heap)
        }
        fn run_prim1_bool(
            prim_f: impl Fn(bool) -> bool, args: Vec<DynValue<Var, Fun>>, stack: Stack<Var, Fun>,
            heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            let f = |v| {
                let b = bool::assert_into(v)?;
                Ok(Value::Bool(prim_f(b)))
            };
            Self::run_prim1(f, args, stack, heap)
        }
        fn run_prim1(
            prim_f: impl Fn(Value) -> Result<Value, InterpErr<Var, Fun>>,
            args: Vec<DynValue<Var, Fun>>, stack: Stack<Var, Fun>, heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            Self::run_prim1_heap_mut(|_, v| prim_f(v), args, stack, heap)
        }
        fn run_prim1_heap(
            prim_f: impl Fn(&Arena<Value>, Value) -> Result<Value, InterpErr<Var, Fun>>,
            args: Vec<DynValue<Var, Fun>>, stack: Stack<Var, Fun>, heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            if args.len() != 1 {
                unreachable!("wrong arity to unary primitive operator, error in our interpreter?!");
            }
            let v = match args.into_iter().next().unwrap() {
                DynValue::Value(v) => v,
                DynValue::Closure(Closure { name, .. }) => Err(InterpErr::UnExpectedFun(name))?,
            };
            let o = prim_f(&heap, v)?;
            Ok(Machine { redex: Redex::Ascending(DynValue::Value(o)), stack, heap })
        }
        fn run_prim1_heap_mut(
            prim_f: impl Fn(&mut Arena<Value>, Value) -> Result<Value, InterpErr<Var, Fun>>,
            args: Vec<DynValue<Var, Fun>>, stack: Stack<Var, Fun>, mut heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            if args.len() != 1 {
                unreachable!("wrong arity to unary primitive operator, error in our interpreter?!");
            }
            let v = match args.into_iter().next().unwrap() {
                DynValue::Value(v) => v,
                DynValue::Closure(Closure { name, .. }) => Err(InterpErr::UnExpectedFun(name))?,
            };
            let o = prim_f(&mut heap, v)?;
            Ok(Machine { redex: Redex::Ascending(DynValue::Value(o)), stack, heap })
        }
        fn run_prim2_int_int(
            prim_f: impl Fn(i64, i64) -> i64, args: Vec<DynValue<Var, Fun>>,
            stack: Stack<Var, Fun>, heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            let f = |v1, v2| {
                let n1 = i64::assert_into(v1)?;
                let n2 = i64::assert_into(v2)?;
                Ok(Value::Int(prim_f(n1, n2)))
            };
            Self::run_prim2(f, args, stack, heap)
        }
        fn run_prim2_bool_bool(
            prim_f: impl Fn(bool, bool) -> bool, args: Vec<DynValue<Var, Fun>>,
            stack: Stack<Var, Fun>, heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            let f = |v1, v2| {
                let b1 = bool::assert_into(v1)?;
                let b2 = bool::assert_into(v2)?;
                Ok(Value::Bool(prim_f(b1, b2)))
            };
            Self::run_prim2(f, args, stack, heap)
        }
        fn run_prim2_int_bool(
            prim_f: impl Fn(i64, i64) -> bool, args: Vec<DynValue<Var, Fun>>,
            stack: Stack<Var, Fun>, heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            let f = |v1, v2| {
                let n1 = i64::assert_into(v1)?;
                let n2 = i64::assert_into(v2)?;
                Ok(Value::Bool(prim_f(n1, n2)))
            };
            Self::run_prim2(f, args, stack, heap)
        }
        fn run_prim2(
            prim_f: impl Fn(Value, Value) -> Result<Value, InterpErr<Var, Fun>>,
            args: Vec<DynValue<Var, Fun>>, stack: Stack<Var, Fun>, heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            Self::run_prim2_heap(|_, a, b| prim_f(a, b), args, stack, heap)
        }
        fn run_prim2_heap(
            prim_f: impl Fn(&Arena<Value>, Value, Value) -> Result<Value, InterpErr<Var, Fun>>,
            args: Vec<DynValue<Var, Fun>>, stack: Stack<Var, Fun>, heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            if args.len() != 2 {
                unreachable!(
                    "wrong arity to binary primitive operator, error in our interpreter?!"
                );
            }
            let mut args = args
                .into_iter()
                .map(|dv| match dv {
                    DynValue::Value(n) => Ok(n),
                    DynValue::Closure(Closure { name, .. }) => Err(InterpErr::UnExpectedFun(name)),
                })
                .collect::<Result<Vec<_>, InterpErr<Var, Fun>>>()?
                .into_iter();
            let (Some(a), Some(b)) = (args.next(), args.next()) else { unreachable!() };
            let o = prim_f(&heap, a, b)?;
            Ok(Machine { redex: Redex::Ascending(DynValue::Value(o)), stack, heap })
        }
        fn run_prim3_heap_mut(
            prim_f: impl Fn(
                &mut Arena<Value>,
                Value,
                Value,
                Value,
            ) -> Result<Value, InterpErr<Var, Fun>>,
            args: Vec<DynValue<Var, Fun>>, stack: Stack<Var, Fun>, mut heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            if args.len() != 3 {
                unreachable!(
                    "wrong arity to binary primitive operator, error in our interpreter?!"
                );
            }
            let mut args = args
                .into_iter()
                .map(|dv| match dv {
                    DynValue::Value(n) => Ok(n),
                    DynValue::Closure(Closure { name, .. }) => Err(InterpErr::UnExpectedFun(name)),
                })
                .collect::<Result<Vec<_>, InterpErr<Var, Fun>>>()?
                .into_iter();
            let (Some(a), Some(b), Some(c)) = (args.next(), args.next(), args.next()) else {
                unreachable!()
            };
            let o = prim_f(&mut heap, a, b, c)?;
            Ok(Machine { redex: Redex::Ascending(DynValue::Value(o)), stack, heap })
        }
        fn run_array(
            args: Vec<DynValue<Var, Fun>>, stack: Stack<Var, Fun>, mut heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            let args = args
                .into_iter()
                .map(|dv| match dv {
                    DynValue::Value(n) => Ok(n),
                    DynValue::Closure(Closure { name, .. }) => Err(InterpErr::UnExpectedFun(name)),
                })
                .collect::<Result<Vec<_>, InterpErr<Var, Fun>>>()?;
            let len = args.len();
            let ptr = heap.alloc(len);
            for (i, arg) in args.into_iter().enumerate() {
                heap.set(ptr, i + 1, arg);
            }
            Ok(Machine {
                redex: Redex::Ascending(DynValue::Value(Value::FatPtr(ptr))),
                stack,
                heap,
            })
        }
        fn run_call(
            fun: Fun, args: Vec<DynValue<Var, Fun>>, env: Env<Var, Fun>, stack: Stack<Var, Fun>,
            heap: Arena<Value>,
        ) -> Result<Self, InterpErr<Var, Fun>> {
            {
                let dv = env
                    .get(&VarOrFun::Fun(fun.clone()))
                    .ok_or_else(|| InterpErr::UnboundFun(fun.clone()))?;
                let Closure { env: clo_env, decls, name } = match dv {
                    DynValue::Closure(closure) => closure,
                    DynValue::Value(v) => Err(InterpErr::CallToConst(v.clone()))?,
                };
                let mut env = clo_env.clone();
                for (name, _) in decls {
                    env.insert(
                        VarOrFun::Fun(name.clone()),
                        DynValue::Closure(Closure {
                            env: clo_env.clone(),
                            decls: decls.clone(),
                            name: name.clone(),
                        }),
                    );
                }
                let Some(RcFunDef { params, body }) = decls.get(&name) else {
                    unreachable!("no corresponding function in closure, error in our interpreter?!")
                };
                if args.len() != params.len() {
                    Err(InterpErr::CallWrongArity {
                        name: name.clone(),
                        expected: params.len(),
                        got: args.len(),
                    })?
                }
                for (param, arg) in params.iter().zip(args) {
                    env.insert(VarOrFun::Var(param.clone()), arg.clone());
                }
                Ok(Machine {
                    redex: Redex::Decending { expr: body.clone(), env: env.clone() },
                    stack,
                    heap,
                })
            }
        }
    }
}

/* ----------------------------------- SSA ---------------------------------- */

pub mod ssa {
    use super::*;
    use crate::ssa::*;
    use std::collections::HashMap;

    struct StackEnv(Frame, Vec<Frame>);
    impl StackEnv {
        fn new() -> Self {
            Self(Frame::new([]), Vec::new())
        }
        fn enter(&mut self) {
            let frame = std::mem::replace(&mut self.0, Frame::new([]));
            self.1.push(frame);
        }
        fn exit(&mut self) {
            self.0 = self.1.pop().unwrap();
        }
        fn current(&mut self) -> &mut Frame {
            &mut self.0
        }
    }
    struct Frame(HashMap<VarName, (usize, Raw)>);
    impl Frame {
        fn new(param_assign: impl IntoIterator<Item = (VarName, Raw)>) -> Self {
            Self(HashMap::from_iter(
                param_assign.into_iter().enumerate().map(|(pos, (var, val))| (var, (pos, val))),
            ))
        }
        fn len(&self) -> usize {
            self.0.len()
        }
        fn insert(&mut self, var: VarName, val: Raw) {
            let pos = self.0.len();
            self.0.insert(var, (pos, val));
        }
        fn get(&self, var: &VarName) -> Option<(usize, &Raw)> {
            self.0.get(var).map(|(pos, val)| (*pos, val))
        }
        fn chop(&mut self, anchor: usize) {
            self.0.retain(|_, (p, _)| *p < anchor);
        }
    }

    #[derive(Clone)]
    struct AnchorBlock {
        /// the position on the stack indicating the start of the block
        anchor: usize,
        params: Vec<VarName>,
        body: BlockBody,
    }

    pub struct Interp {
        stack: StackEnv,
        kont: Vec<(VarName, BlockBody)>,
        funs: im::HashMap<FunName, FunBlock>,
        blocks: im::HashMap<BlockName, AnchorBlock>,
        heap: Arena<Value>,
    }

    /// Trampoline for the interpreter.
    enum State {
        Return(Raw),
        Operation(Operation, VarName, BlockBody),
        OpReturn(Raw),
        Call(FunName, Vec<Raw>),
        Branch(Branch),
        BlockBody(BlockBody),
        Terminator(Terminator),
    }

    impl Interp {
        pub fn new() -> Self {
            Self {
                stack: StackEnv::new(),
                kont: Vec::new(),
                funs: im::HashMap::new(),
                blocks: im::HashMap::new(),
                heap: Arena::new(),
            }
        }
        fn alloc(&mut self, var: VarName, val: Raw) {
            let frame = self.stack.current();
            frame.insert(var, val);
        }

        pub fn run<S>(
            &mut self, Program { externs, funs, blocks }: &Program,
            args: impl IntoIterator<Item = S>,
        ) -> Result<Value, InterpErr<VarName, FunName>>
        where
            S: Into<String>,
        {
            // Note: extern functions are not supported
            let mut exts = externs
                .iter()
                .map(|Extern { name, params: _ }| (name.clone(), ()))
                .collect::<HashMap<_, _>>();
            exts.remove(&FunName::unmangled("snake_equals"));
            exts.remove(&FunName::unmangled("snake_not_equals"));
            exts.remove(&FunName::unmangled("snake_error"));
            exts.remove(&FunName::unmangled("snake_new_array"));
            assert!(exts.is_empty(), "extern functions are not supported");

            let args: Vec<Value> = args
                .into_iter()
                .map(Into::into)
                .map(parse_snake_basic_val)
                .collect::<Result<_, _>>()?;
            self.funs.extend(funs.iter().cloned().map(|f| (f.name.clone(), f.clone())));
            self.blocks.extend(blocks.iter().cloned().map(|BasicBlock { label, params, body }| {
                (label.clone(), AnchorBlock { anchor: 0, params, body })
            }));
            let arr = self.heap.alloc(args.len());
            for (i, arg) in args.into_iter().enumerate() {
                self.heap.set(arr, i + 1, arg);
            }
            let mut state =
                self.run_call(&FunName::unmangled("entry"), vec![Raw::from(Value::FatPtr(arr))])?;

            loop {
                match state {
                    State::Return(val) => match self.kont.pop() {
                        Some((dest, next)) => {
                            self.stack.exit();
                            self.alloc(dest.clone(), val);
                            state = State::BlockBody(next.clone())
                        }
                        None => return val.downcast(),
                    },
                    State::OpReturn(val) => match self.kont.pop() {
                        Some((dest, next)) => {
                            self.alloc(dest.clone(), val);
                            state = State::BlockBody(next.clone())
                        }
                        None => {
                            unreachable!("no return kont for operation, error in our interpreter?!")
                        }
                    },
                    State::Operation(op, dest, next) => {
                        self.kont.push((dest.clone(), next.clone()));
                        state = self.run_operation(&op)?
                    }
                    State::Call(fun, args) => {
                        self.stack.enter();
                        state = self.run_call(&fun, args)?
                    }
                    State::Branch(branch) => state = self.run_branch(&branch)?,
                    State::BlockBody(body) => state = self.run_block_body(&body)?,
                    State::Terminator(terminator) => state = self.run_terminator(&terminator)?,
                }
            }
        }

        /// Run a function call. A frame is already entered before calling this.
        fn run_call(
            &mut self, fun: &FunName, args: Vec<Raw>,
        ) -> Result<State, InterpErr<VarName, FunName>> {
            match fun {
                FunName::Unmangled(f) if f == "snake_equals" => {
                    let a = &args[0];
                    let b = &args[1];
                    Ok(State::Return(Raw::from(Value::Bool(
                        self.heap.equal(&a.downcast()?, &b.downcast()?)?,
                    ))))
                }
                FunName::Unmangled(f) if f == "snake_not_equals" => {
                    let a = &args[0];
                    let b = &args[1];
                    Ok(State::Return(Raw::from(Value::Bool(
                        !self.heap.equal(&a.downcast()?, &b.downcast()?)?,
                    ))))
                }
                _ => {
                    let FunBlock { name: _, params, body: branch } = self.funs[fun].clone();
                    for (param, arg) in params.iter().zip(args) {
                        self.alloc(param.clone(), arg.clone());
                    }
                    Ok(State::Branch(branch.clone()))
                }
            }
        }

        fn run_branch(
            &mut self, Branch { target, args }: &Branch,
        ) -> Result<State, InterpErr<VarName, FunName>> {
            let args =
                args.iter().map(|imm| self.run_immediate(imm)).collect::<Result<Vec<_>, _>>()?;
            let AnchorBlock { anchor, params, body } = self.blocks[target].clone();
            self.stack.current().chop(anchor);
            for (param, arg) in params.iter().zip(args) {
                self.alloc(param.clone(), arg.clone());
            }
            Ok(State::BlockBody(body.clone()))
        }
        fn run_block_body(
            &mut self, block: &BlockBody,
        ) -> Result<State, InterpErr<VarName, FunName>> {
            match block {
                BlockBody::Terminator(terminator) => Ok(State::Terminator(terminator.clone())),
                BlockBody::Operation { dest, op, next } => {
                    Ok(State::Operation(op.clone(), dest.clone(), next.as_ref().clone()))
                }
                BlockBody::SubBlocks { blocks, next } => {
                    let anchor = self.stack.current().len();
                    self.blocks.extend(blocks.iter().cloned().map(
                        |BasicBlock { label, params, body }| {
                            (label.clone(), AnchorBlock { anchor, params, body })
                        },
                    ));
                    Ok(State::BlockBody(next.as_ref().clone()))
                }
                BlockBody::AssertType { ty, arg: of, next } => {
                    let Raw(n) = self.run_immediate(of)?;
                    if n & ty.mask() != ty.tag() {
                        Err(InterpErr::AssertTypeFailed(ty.clone()))?
                    }
                    Ok(State::BlockBody(next.as_ref().clone()))
                }
                BlockBody::AssertLength { len, next } => {
                    let Raw(n) = self.run_immediate(len)?;
                    if n < 0 {
                        Err(InterpErr::AssertLength)?
                    }
                    Ok(State::BlockBody(next.as_ref().clone()))
                }
                BlockBody::AssertInBounds { bound, arg: of, next } => {
                    let Raw(bound) = self.run_immediate(bound)?;
                    let Raw(of) = self.run_immediate(of)?;
                    if of < 0 || bound <= of {
                        Err(InterpErr::AssertInBoundsFailed { bound, of })?
                    }
                    Ok(State::BlockBody(next.as_ref().clone()))
                }
                BlockBody::Store { addr, offset: off, val, next } => {
                    let ptr = ArenaPtr::from(Raw(self.run_immediate(addr)?.0 >> 2));
                    let idx = i64::from(self.run_immediate(off)?);
                    let val = Raw::downcast(self.run_immediate(val)?)?;
                    self.heap.set(ptr, idx as usize, val);
                    Ok(State::BlockBody(next.as_ref().clone()))
                }
            }
        }

        fn run_terminator(
            &mut self, terminator: &Terminator,
        ) -> Result<State, InterpErr<VarName, FunName>> {
            match terminator {
                Terminator::Return(imm) => Ok(State::Return(self.run_immediate(imm)?)),
                Terminator::Branch(br) => Ok(State::Branch(br.clone())),
                Terminator::ConditionalBranch { cond, thn, els } => {
                    let Raw(n) = self.run_immediate(cond)?;
                    if n != 0 {
                        Ok(State::Branch(Branch { target: thn.clone(), args: Vec::new() }))
                    } else {
                        Ok(State::Branch(Branch { target: els.clone(), args: Vec::new() }))
                    }
                }
            }
        }

        fn run_operation(&mut self, op: &Operation) -> Result<State, InterpErr<VarName, FunName>> {
            match op {
                Operation::Immediate(imm) => Ok(State::OpReturn(self.run_immediate(imm)?)),
                Operation::Prim1(prim, imm) => {
                    let Raw(n) = self.run_immediate(imm)?;
                    let o = match prim {
                        Prim1::BitNot => Raw(!n),
                        Prim1::BitSal(m) => Raw(n << m),
                        Prim1::BitSar(m) => Raw(n >> m),
                        Prim1::BitShl(m) => Raw(n << m),
                        Prim1::BitShr(m) => Raw(n >> m),
                    };
                    Ok(State::OpReturn(o))
                }
                Operation::Prim2(prim, imm1, imm2) => {
                    let Raw(n) = self.run_immediate(imm1)?;
                    let Raw(m) = self.run_immediate(imm2)?;
                    let o = match prim {
                        Prim2::Add => n + m,
                        Prim2::Sub => n - m,
                        Prim2::Mul => n * m,
                        Prim2::BitAnd => n & m,
                        Prim2::BitOr => n | m,
                        Prim2::BitXor => n ^ m,
                        Prim2::Lt => (if n < m { 1 } else { 0 }).clone(),
                        Prim2::Le => (if n <= m { 1 } else { 0 }).clone(),
                        Prim2::Gt => (if n > m { 1 } else { 0 }).clone(),
                        Prim2::Ge => (if n >= m { 1 } else { 0 }).clone(),
                        Prim2::Eq => (if n == m { 1 } else { 0 }).clone(),
                        Prim2::Neq => (if n != m { 1 } else { 0 }).clone(),
                    };
                    Ok(State::OpReturn(Raw(o)))
                }
                Operation::Call { fun, args } => {
                    let args = args
                        .iter()
                        .map(|imm| self.run_immediate(imm))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(State::Call(fun.clone(), args))
                }
                Operation::AllocateArray { len } => {
                    let Raw(len) = self.run_immediate(len)?;
                    let arr = self.heap.alloc(len as usize);
                    Ok(State::OpReturn(Raw((arr.idx as i64) << 2)))
                }
                Operation::Load { addr, offset: off } => {
                    let ptr = ArenaPtr::from(Raw(self.run_immediate(addr)?.0 >> 2));
                    let off = i64::from(self.run_immediate(off)?);
                    let val = self.heap.get(ptr, off as usize);
                    Ok(State::OpReturn(Raw::from(*val)))
                }
            }
        }

        fn run_immediate(&mut self, imm: &Immediate) -> Result<Raw, InterpErr<VarName, FunName>> {
            match imm {
                Immediate::Var(v) => {
                    let (_, val) =
                        self.stack.current().get(v).ok_or(InterpErr::UnboundVar(v.clone()))?;
                    Ok(val.clone())
                }
                Immediate::Const(n) => Ok(Raw(*n)),
            }
        }
    }
}
