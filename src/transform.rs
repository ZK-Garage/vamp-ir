use std::collections::{HashMap, HashSet};
use crate::typecheck::{infer_module_types, expand_module_variables, unitize_module_functions, print_types, Type};
use crate::ast::{Module, Definition, TExpr, Pattern, VariableId, LetBinding, Variable, InfixOp, Expr, Intrinsic, Function, Match};

/* A structure for generating unique variable IDs. */
pub struct VarGen(VariableId);

impl VarGen {
    pub fn new() -> Self {
        VarGen(0)
    }
    pub fn generate_id(&mut self) -> VariableId {
        let curr_id = self.0;
        self.0 += 1;
        curr_id
    }
}

/* Replaces variable IDs in the given expression according to the given
 * substitution map. */
fn refresh_expr_variables(
    expr: &mut TExpr,
    map: &HashMap<VariableId, VariableId>,
    prover_defs: &mut HashSet<VariableId>,
    gen: &mut VarGen,
) {
    match &mut expr.v {
        Expr::Sequence(exprs) | Expr::Intrinsic(Intrinsic { args: exprs, .. }) => {
            for expr in exprs {
                refresh_expr_variables(expr, map, prover_defs, gen);
            }
        },
        Expr::Infix(_, expr1, expr2) | Expr::Application(expr1, expr2) |
        Expr::Product(expr1, expr2) | Expr::Cons(expr1, expr2) => {
            refresh_expr_variables(expr1, map, prover_defs, gen);
            refresh_expr_variables(expr2, map, prover_defs, gen);
        },
        Expr::Match(matche) => {
            refresh_expr_variables(&mut matche.0, map, prover_defs, gen);
            for (pat, expr2) in matche.1.iter_mut().zip(matche.2.iter_mut()) {
                let mut map = map.clone();
                refresh_pattern_variables(pat, &mut map, prover_defs, gen);
                refresh_expr_variables(expr2, &map, prover_defs, gen);
            }
        },
        Expr::Negate(expr) => {
            refresh_expr_variables(expr, map, prover_defs, gen);
        },
        Expr::Constant(_) | Expr::Unit | Expr::Nil => {},
        Expr::Variable(var) => {
            if let Some(id) = map.get(&var.id) {
                var.id = *id;
            }
        },
        Expr::Function(fun) => {
            let mut map = map.clone();
            for param in &mut fun.0 {
                refresh_pattern_variables(param, &mut map, prover_defs, gen);
            }
            refresh_expr_variables(&mut fun.1, &map, prover_defs, gen);
        },
        Expr::LetBinding(binding, expr) => {
            refresh_expr_variables(&mut binding.1, map, prover_defs, gen);
            let mut map = map.clone();
            refresh_pattern_variables(&mut binding.0, &mut map, prover_defs, gen);
            refresh_expr_variables(expr, &map, prover_defs, gen);
        },
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Tribool { False, Indeterminate, True }

/* Match the given expression against the given pattern. */
fn match_pattern_expr(
    pat: &Pattern,
    expr: &TExpr,
    map: &mut HashMap<VariableId, TExpr>,
    prover_defs: &mut HashSet<VariableId>,
    gen: &mut VarGen,
) -> Tribool {
    match (pat, &expr.v) {
        (pat, Expr::Variable(var)) if map.contains_key(&var.id) =>
            match_pattern_expr(pat, &map[&var.id].clone(), map, prover_defs, gen),
        (Pattern::As(pat, var), _) => {
            let res = match_pattern_expr(pat, expr, map, prover_defs, gen);
            map.insert(var.id, expr.clone().into());
            res
        },
        (Pattern::Variable(var), expr) => {
            map.insert(var.id, expr.clone().into());
            Tribool::True
        },
        (Pattern::Product(pat1, pat2), Expr::Product(expr1, expr2)) |
        (Pattern::Cons(pat1, pat2), Expr::Cons(expr1, expr2))=> {
            let inner_res1 = match_pattern_expr(pat1, expr1, map, prover_defs, gen);
            let inner_res2 = match_pattern_expr(pat2, expr2, map, prover_defs, gen);
            std::cmp::min(inner_res1, inner_res2)
        },
        (Pattern::Product(_, _), Expr::Variable(var)) => {
            let new_var1 = Variable::new(gen.generate_id());
            let new_var2 = Variable::new(gen.generate_id());
            if prover_defs.contains(&var.id) {
                prover_defs.insert(new_var1.id);
                prover_defs.insert(new_var2.id);
            }
            let inner_expr1 = Box::new(Expr::Variable(new_var1).into());
            let inner_expr2 = Box::new(Expr::Variable(new_var2).into());
            map.insert(var.id, Expr::Product(inner_expr1, inner_expr2).into());
            match_pattern_expr(pat, expr, map, prover_defs, gen)
        },
        (Pattern::Cons(_, _), Expr::Variable(var)) => {
            let new_var1 = Variable::new(gen.generate_id());
            let new_var2 = Variable::new(gen.generate_id());
            if prover_defs.contains(&var.id) {
                prover_defs.insert(new_var1.id);
                prover_defs.insert(new_var2.id);
            }
            let inner_expr1 = Box::new(Expr::Variable(new_var1).into());
            let inner_expr2 = Box::new(Expr::Variable(new_var2).into());
            map.insert(var.id, Expr::Cons(inner_expr1, inner_expr2).into());
            match_pattern_expr(pat, expr, map, prover_defs, gen)
        },
        (Pattern::Unit, Expr::Unit) | (Pattern::Nil, Expr::Nil) =>
            Tribool::True,
        (Pattern::Constant(a), Expr::Constant(b)) if a == b =>
            Tribool::True,
        (Pattern::Constant(a), Expr::Constant(b)) if a != b =>
            Tribool::False,
        (Pattern::Constant(_), Expr::Variable(_) | Expr::Infix(_, _, _)) =>
            Tribool::Indeterminate,
        _ => panic!("unable to match {} against {}", expr, pat),
    }
}

/* Refresh all the variables occuring in the given pattern. */
fn refresh_pattern_variables(
    pat: &mut Pattern,
    map: &mut HashMap<VariableId, VariableId>,
    prover_defs: &mut HashSet<VariableId>,
    gen: &mut VarGen,
) {
    match pat {
        Pattern::As(pat, var) => {
            refresh_pattern_variables(pat, map, prover_defs, gen);
            map.insert(var.id, gen.generate_id());
            if prover_defs.contains(&var.id) {
                prover_defs.insert(map[&var.id]);
            }
            var.id = map[&var.id];
        },
        Pattern::Product(pat1, pat2) | Pattern::Cons(pat1, pat2) => {
            refresh_pattern_variables(pat1, map, prover_defs, gen);
            refresh_pattern_variables(pat2, map, prover_defs, gen);
        },
        Pattern::Variable(var) => {
            map.insert(var.id, gen.generate_id());
            if prover_defs.contains(&var.id) {
                prover_defs.insert(map[&var.id]);
            }
            var.id = map[&var.id];
        },
        Pattern::Constant(_) | Pattern::Unit | Pattern::Nil => {},
    }
}

/* Gives each variable occuring in the pattern a unique ID. Assumes that no
 * variable is used more than once in the pattern. */
fn number_pattern_variables(
    pat: &mut Pattern,
    map: &mut HashMap<String, VariableId>,
    gen: &mut VarGen,
) {
    match pat {
        Pattern::As(pat, var) => {
            number_pattern_variables(pat, map, gen);
            if let Some(name) = &var.name {
                var.id = gen.generate_id();
                map.insert(name.clone(), var.id);
            }
        },
        Pattern::Product(pat1, pat2) | Pattern::Cons(pat1, pat2) => {
            number_pattern_variables(pat1, map, gen);
            number_pattern_variables(pat2, map, gen);
        },
        Pattern::Variable(var) => {
            if let Some(name) = &var.name {
                var.id = gen.generate_id();
                map.insert(name.clone(), var.id);
            }
        },
        Pattern::Constant(_) | Pattern::Unit | Pattern::Nil => {},
    }
}

/* Numbers each variable occuring in the expression according to the binding in
 * local. If there is no such binding, then the global variable map is searched.
 * If not found, then a new global variable binding is made. Binding expressions
 * introduce new local bindings. */
fn number_expr_variables(
    expr: &mut TExpr,
    locals: &HashMap<String, VariableId>,
    globals: &mut HashMap<String, VariableId>,
    gen: &mut VarGen,
) {
    match &mut expr.v {
        Expr::Sequence(exprs) |
        Expr::Intrinsic(Intrinsic { args: exprs, ..}) => {
            for expr in exprs {
                number_expr_variables(expr, locals, globals, gen);
            }
        },
        Expr::Infix(_, expr1, expr2) | Expr::Application(expr1, expr2) |
        Expr::Product(expr1, expr2) | Expr::Cons(expr1, expr2) => {
            number_expr_variables(expr1, locals, globals, gen);
            number_expr_variables(expr2, locals, globals, gen);
        },
        Expr::Negate(expr) => {
            number_expr_variables(expr, locals, globals, gen);
        },
        Expr::Constant(_) | Expr::Unit | Expr::Nil => {},
        Expr::Variable(var) => {
            if let Some(name) = &var.name {
                if let Some(id) = locals.get(name) {
                    var.id = *id;
                } else if let Some(id) = globals.get(name) {
                    var.id = *id;
                } else {
                    var.id = gen.generate_id();
                    globals.insert(name.clone(), var.id);
                }
            }
        },
        Expr::Function(fun) => {
            let mut locals = locals.clone();
            for param in &mut fun.0 {
                number_pattern_variables(param, &mut locals, gen);
            }
            number_expr_variables(&mut fun.1, &mut locals, globals, gen);
        },
        Expr::LetBinding(binding, expr) => {
            let mut locals = locals.clone();
            number_expr_variables(&mut binding.1, &mut locals, globals, gen);
            number_pattern_variables(&mut binding.0, &mut locals, gen);
            number_expr_variables(expr, &mut locals, globals, gen);
        },
        Expr::Match(matche) => {
            number_expr_variables(&mut matche.0, locals, globals, gen);
            for (pat, expr2) in matche.1.iter_mut().zip(matche.2.iter_mut()) {
                let mut locals = locals.clone();
                number_pattern_variables(pat, &mut locals, gen);
                number_expr_variables(expr2, &mut locals, globals, gen);
            }
        },
    }
}

/* Numbers the variables occuring in the definition. Essentially numbers the
 * inner expression, and then numbers the definition pattern variables in global
 * scope. */
fn number_def_variables(
    def: &mut Definition,
    locals: &mut HashMap<String, VariableId>,
    globals: &mut HashMap<String, VariableId>,
    gen: &mut VarGen,
) {
    number_expr_variables(&mut *def.0.1, locals, globals, gen);
    number_pattern_variables(&mut def.0.0, locals, gen);
}

/* Numbers the variables occuring in the module definitions and then those
 * occuring in the module expressions. */
pub fn number_module_variables(
    module: &mut Module,
    globals: &mut HashMap<String, VariableId>,
    gen: &mut VarGen,
) {
    let mut locals = HashMap::new();
    for def in &mut module.defs {
        number_def_variables(def, &mut locals, globals, gen);
    }
    for expr in &mut module.exprs {
        number_expr_variables(expr, &locals, globals, gen);
    }
}

/* Replace each function application occuring in the expression with a let
 * binding containing an inlined body. Returns a normal form of the expression.
 */
fn apply_functions(
    expr: &mut TExpr,
    bindings: &HashMap<VariableId, TExpr>,
    prover_defs: &mut HashSet<VariableId>,
    gen: &mut VarGen,
) -> TExpr {
    match &mut expr.v {
        Expr::Application(expr1, expr2) => {
            match &mut expr1.v {
                Expr::Application(_, _) | Expr::Match(_) => {
                    apply_functions(expr1, bindings, prover_defs, gen);
                    apply_functions(expr, bindings, prover_defs, gen)
                },
                Expr::Intrinsic(intr) => {
                    let expr2_norm = apply_functions(expr2, bindings, prover_defs, gen);
                    *expr = intr.clone().apply(expr2_norm, bindings, prover_defs, gen);
                    apply_functions(expr, bindings, prover_defs, gen)
                },
                Expr::Variable(var) => match bindings.get(&var.id) {
                    Some(val) if !prover_defs.contains(&var.id) => {
                        *expr = Expr::Application(
                            Box::new(val.clone()),
                            expr2.clone()
                        ).into();
                        apply_functions(expr, bindings, prover_defs, gen)
                    },
                    _ => panic!("encountered unbound variable {}", var)
                },
                Expr::Function(_) => {
                    let substitutions = HashMap::new();
                    refresh_expr_variables(expr1, &substitutions, prover_defs, gen);
                    if let Expr::Function(fun) = &mut expr1.v {
                        if fun.0.is_empty() {
                            unreachable!("functions should have at least one parameter");
                        }
                        let arg1 = fun.0.remove(0);
                        let new_body = if fun.0.is_empty() { &*fun.1 } else { expr1 };
                        let new_bind = LetBinding(arg1, expr2.clone());
                        *expr = Expr::LetBinding(new_bind, Box::new(new_body.clone())).into();
                        apply_functions(expr, bindings, prover_defs, gen)
                    } else {
                        unreachable!("refreshing variables changed expression type")
                    }
                },
                Expr::Sequence(seq) => {
                    if let Some(val) = seq.last_mut() {
                        *val = Expr::Application(Box::new(val.clone()), expr2.clone()).into();
                        *expr = *expr1.clone();
                        apply_functions(expr, bindings, prover_defs, gen)
                    } else {
                        unreachable!("encountered an empty sequence")
                    }
                },
                Expr::LetBinding(_, body) => {
                    *body = Box::new(Expr::Application(body.clone(), expr2.clone()).into());
                    *expr = *expr1.clone();
                    apply_functions(expr, bindings, prover_defs, gen)
                },
                Expr::Infix(_, _, _) => {
                    panic!("cannot apply argument {} to infix {}", expr2, expr1)
                },
                Expr::Negate(_) => {
                    panic!("cannot apply argument {} to negation {}", expr2, expr1)
                },
                Expr::Product(_, _) => {
                    panic!("cannot apply argument {} to tuple {}", expr2, expr1)
                },
                Expr::Cons(_, _) => {
                    panic!("cannot apply argument {} to list {}", expr2, expr1)
                },
                Expr::Constant(_) => {
                    panic!("cannot apply argument {} to constant {}", expr2, expr1)
                },
                Expr::Unit => {
                    panic!("cannot apply argument {} to unit {}", expr2, expr1)
                },
                Expr::Nil => {
                    panic!("cannot apply argument {} to nil {}", expr2, expr1)
                },
            }
        },
        Expr::LetBinding(binding, body) => {
            let val = apply_functions(&mut *binding.1, bindings, prover_defs, gen);
            let mut new_bindings = bindings.clone();
            match_pattern_expr(&binding.0, &val, &mut new_bindings, prover_defs, gen);
            let mut normal = apply_functions(body, &new_bindings, prover_defs, gen);
            new_bindings.retain(|k, _v| !bindings.contains_key(k) && !prover_defs.contains(k));
            copy_propagate_expr(&mut normal, &new_bindings);
            normal
        },
        Expr::Match(matche) => {
            let val = apply_functions(&mut matche.0, bindings, prover_defs, gen);
            for (pat, expr2) in matche.1.iter_mut().zip(matche.2.iter_mut()) {
                let mut new_bindings = bindings.clone();
                let res = match_pattern_expr(&pat, &val, &mut new_bindings, prover_defs, gen);
                match res {
                    Tribool::True => {
                        *expr = TExpr {
                            v: Expr::LetBinding(
                                LetBinding(pat.clone(), matche.0.clone()),
                                Box::new(expr2.clone())
                            ),
                            t: expr.t.clone()
                        };
                        return apply_functions(expr, bindings, prover_defs, gen);
                    },
                    Tribool::Indeterminate =>
                        panic!("cannot statically match {} against {}", val, pat),
                    Tribool::False => continue,
                }
            }
            let expr = TExpr { v: Expr::Match(Match(matche.0.clone(), matche.1.clone(), matche.2.clone())), t: None };
            panic!("cannot match {} to any pattern in {}", matche.0, expr);
        },
        Expr::Sequence(seq) => {
            let mut val = None;
            for expr in seq {
                val = Some(apply_functions(expr, &bindings, prover_defs, gen));
            }
            val.expect("encountered empty sequence")
        },
        Expr::Product(expr1, expr2) => {
            Expr::Product(
                Box::new(apply_functions(expr1, &bindings, prover_defs, gen)),
                Box::new(apply_functions(expr2, &bindings, prover_defs, gen)),
            ).into()
        },
        Expr::Cons(expr1, expr2) => {
            Expr::Cons(
                Box::new(apply_functions(expr1, &bindings, prover_defs, gen)),
                Box::new(apply_functions(expr2, &bindings, prover_defs, gen)),
            ).into()
        },
        Expr::Infix(op, expr1, expr2) => {
            let expr1 = apply_functions(expr1, &bindings, prover_defs, gen);
            let expr2 = apply_functions(expr2, &bindings, prover_defs, gen);
            Expr::Infix(op.clone(), Box::new(expr1), Box::new(expr2)).into()
        },
        Expr::Negate(expr1) => {
            Expr::Negate(Box::new(apply_functions(expr1, &bindings, prover_defs, gen))).into()
        },
        t @ (Expr::Constant(_) | Expr::Unit | Expr::Nil) => t.clone().into(),
        Expr::Variable(var) => match bindings.get(&var.id) {
            Some(val) if !prover_defs.contains(&var.id) => val.clone(),
            _ => expr.clone(),
        },
        Expr::Function(fun) => Expr::Function(fun.clone()).into(),
        Expr::Intrinsic(intr) => {
            for arg in &mut intr.args {
                *arg = apply_functions(arg, &bindings, prover_defs, gen);
            }
            Expr::Intrinsic(intr.clone()).into()
        },
    }
}

/* Replace each function application occuring in the definition with a let
 * binding containing an inlined body. */
fn apply_def_functions(
    def: &mut Definition,
    bindings: &mut HashMap<VariableId, TExpr>,
    prover_defs: &mut HashSet<VariableId>,
    gen: &mut VarGen,
) {
    let val = apply_functions(&mut def.0.1, bindings, prover_defs, gen);
    match_pattern_expr(&def.0.0, &val, bindings, prover_defs, gen);
}

/* Replace each function application occuring in the module with a let
 * binding containing an inlined body. */
pub fn apply_module_functions(
    module: &mut Module,
    bindings: &mut HashMap<VariableId, TExpr>,
    prover_defs: &mut HashSet<VariableId>,
    gen: &mut VarGen,
) {
    for def in &mut module.defs {
        apply_def_functions(def, bindings, prover_defs, gen);
    }
    for expr in &mut module.exprs {
        apply_functions(expr, bindings, prover_defs, gen);
    }
}

/* Collect all the variables occuring in the given pattern. */
pub fn collect_pattern_variables(
    pat: &Pattern,
    map: &mut HashMap<VariableId, Variable>,
) {
    match pat {
        Pattern::Variable(var) => {
            map.insert(var.id, var.clone());
        },
        Pattern::As(pat, var) => {
            map.insert(var.id, var.clone());
            collect_pattern_variables(pat, map);
        },
        Pattern::Product(pat1, pat2) | Pattern::Cons(pat1, pat2) => {
            collect_pattern_variables(pat1, map);
            collect_pattern_variables(pat2, map);
        },
        Pattern::Constant(_) | Pattern::Unit | Pattern::Nil => {}
    }
}

/* Collect all the variables occuring in the given expression. */
fn collect_expr_variables(
    expr: &TExpr,
    map: &mut HashMap<VariableId, Variable>,
) {
    match &expr.v {
        Expr::Variable(var) => {
            map.insert(var.id, var.clone());
        },
        Expr::Sequence(exprs) |
        Expr::Intrinsic(Intrinsic { args: exprs, .. }) => {
            for expr in exprs {
                collect_expr_variables(expr, map);
            }
        },
        Expr::Infix(_, expr1, expr2) | Expr::Application(expr1, expr2) |
        Expr::Product(expr1, expr2) | Expr::Cons(expr1, expr2) => {
            collect_expr_variables(expr1, map);
            collect_expr_variables(expr2, map);
        },
        Expr::Negate(expr1) => {
            collect_expr_variables(expr1, map);
        },
        Expr::Function(fun) => {
            for param in &fun.0 {
                collect_pattern_variables(param, map);
            }
            collect_expr_variables(&*fun.1, map);
        },
        Expr::LetBinding(binding, body) => {
            collect_expr_variables(&*binding.1, map);
            collect_pattern_variables(&binding.0, map);
            collect_expr_variables(body, map);
        },
        Expr::Match(matche) => {
            collect_expr_variables(&matche.0, map);
            for (pat, expr2) in matche.1.iter().zip(matche.2.iter()) {
                collect_pattern_variables(pat, map);
                collect_expr_variables(expr2, map);
            }
        },
        Expr::Constant(_) | Expr::Unit | Expr::Nil => {},
    }
}

/* Collect all the variables occuring in the given definition. */
fn collect_def_variables(
    def: &Definition,
    map: &mut HashMap<VariableId, Variable>,
) {
    collect_expr_variables(&*def.0.1, map);
    collect_pattern_variables(&def.0.0, map);
}

/* Collect all the variables occuring in the given module. */
pub fn collect_module_variables(
    module: &Module,
    map: &mut HashMap<VariableId, Variable>,
) {
    for def in &module.defs {
        collect_def_variables(def, map);
    }
    for expr in &module.exprs {
        collect_expr_variables(expr, map);
    }
}

/* Produce the given binary operation making sure to do any straightforward
 * simplifications. */
fn infix_op(op: InfixOp, e1: TExpr, e2: TExpr) -> TExpr {
    match (op, &e1.v, &e2.v) {
        (InfixOp::Multiply, Expr::Constant(1), _) => e2,
        (InfixOp::Multiply, _, Expr::Constant(1)) => e1,
        (InfixOp::Multiply, Expr::Constant(0), _) => e1,
        (InfixOp::Multiply, _, Expr::Constant(0)) => e2,
        (InfixOp::Divide, _, Expr::Constant(1)) => e1,
        (InfixOp::IntDivide, _, Expr::Constant(1)) => e1,
        (InfixOp::Modulo, _, Expr::Constant(1)) =>
            TExpr { v: Expr::Constant(0), t: Some(Type::Int) },
        (InfixOp::Add, Expr::Constant(0), _) => e2,
        (InfixOp::Add, _, Expr::Constant(0)) => e1,
        (InfixOp::Subtract, _, Expr::Constant(0)) => e1,
        (InfixOp::Equal, _, _) =>
            TExpr {
                v: Expr::Infix(op, Box::new(e1), Box::new(e2)),
                t: Some(Type::Unit),
            },
        (InfixOp::Multiply | InfixOp::Divide | InfixOp::Add |
         InfixOp::Subtract | InfixOp::Exponentiate | InfixOp::IntDivide |
         InfixOp::Modulo, _, _) =>
            TExpr {
                v: Expr::Infix(op, Box::new(e1), Box::new(e2)),
                t: Some(Type::Int),
            },
    }
}

/* Flatten the given binding down into the set of constraints it defines. */
fn flatten_binding(
    pat: &Pattern,
    expr: &TExpr,
    flattened: &mut Module,
) {
    match (pat, &expr.v) {
        (pat @ Pattern::Variable(_),
         Expr::Variable(_) | Expr::Constant(_) |
         Expr::Infix(_, _, _) | Expr::Negate(_)) => {
            flattened.defs.push(Definition(LetBinding(
                pat.clone(),
                Box::new(expr.clone()),
            )));
        },
        (Pattern::Constant(pat),
         Expr::Variable(_) | Expr::Constant(_) |
                 Expr::Infix(_, _, _) | Expr::Negate(_)) => {
            flattened.exprs.push(Expr::Infix(
                InfixOp::Equal,
                Box::new(Expr::Constant(*pat).into()),
                Box::new(expr.clone()),
            ).into());
        },
        (Pattern::As(pat, _name), _) => {
            flatten_binding(pat, expr, flattened);
        },
        (Pattern::Unit, Expr::Unit) => {},
        (Pattern::Product(pat1, pat2), Expr::Product(expr1, expr2)) => {
            flatten_binding(pat1, expr1, flattened);
            flatten_binding(pat2, expr2, flattened);
        }
        _ => unreachable!("encountered unexpected binding: {} = {}", pat, expr),
    }
}

/* Flatten the given equality down into the set of constraints it defines. */
fn flatten_equals(
    expr1: &TExpr,
    expr2: &TExpr,
    flattened: &mut Module,
) {
    match (&expr1.v, &expr2.v) {
        (Expr::Unit, Expr::Unit) => {},
        (Expr::Product(expr11, expr12), Expr::Product(expr21, expr22)) => {
            flatten_equals(expr11, expr21, flattened);
            flatten_equals(expr12, expr22, flattened);
        },
        (Expr::Variable(_) | Expr::Negate(_) |
         Expr::Infix(_, _, _) | Expr::Constant(_),
         Expr::Variable(_) | Expr::Negate(_) |
         Expr::Infix(_, _, _) | Expr::Constant(_)) => {
            flattened.exprs.push(Expr::Infix(
                InfixOp::Equal,
                Box::new(expr1.clone()),
                Box::new(expr2.clone())
            ).into());
        },
        _ => unreachable!("encountered unexpected equality: {} = {}", expr1, expr2),
    }
}

/* Flatten the given expression down into the set of constraints it defines. */
fn flatten_expression(
    expr: &TExpr,
    flattened: &mut Module,
) -> TExpr {
    match &expr.v {
        Expr::Sequence(seq) => {
            let mut val = None;
            for expr in seq {
                val = Some(flatten_expression(expr, flattened));
            }
            val.expect("encountered empty sequence").clone()
        },
        Expr::Infix(InfixOp::Equal, expr1, expr2) => {
            let expr1 = flatten_expression(expr1, flattened);
            let expr2 = flatten_expression(expr2, flattened);
            flatten_equals(&expr1, &expr2, flattened);
            Expr::Unit.into()
        },
        Expr::Infix(op, expr1, expr2) => {
            let expr1 = flatten_expression(expr1, flattened);
            let expr2 = flatten_expression(expr2, flattened);
            Expr::Infix(*op, Box::new(expr1), Box::new(expr2)).into()
        },
        Expr::Product(expr1, expr2) => {
            Expr::Product(
                Box::new(flatten_expression(expr1, flattened)),
                Box::new(flatten_expression(expr2, flattened)),
            ).into()
        },
        Expr::Cons(expr1, expr2) => {
            Expr::Cons(
                Box::new(flatten_expression(expr1, flattened)),
                Box::new(flatten_expression(expr2, flattened)),
            ).into()
        },
        Expr::Negate(expr1) =>
            Expr::Negate(Box::new(flatten_expression(expr1, flattened))).into(),
        Expr::Constant(_) | Expr::Variable(_) | Expr::Unit | Expr::Nil => expr.clone(),
        Expr::LetBinding(binding, body) => {
            let val = flatten_expression(&*binding.1, flattened);
            flatten_binding(&binding.0, &val, flattened);
            flatten_expression(body, flattened)
        }
        Expr::Function(_) | Expr::Application(_, _) | Expr::Intrinsic(_) |
        Expr::Match(_) =>
            unreachable!("functions and matches must already by inlined and eliminated"),
    }
}

/* Flatten the given definition down into the set of constraints it defines. */
fn flatten_definition(
    def: &Definition,
    flattened: &mut Module,
) {
    let val = flatten_expression(&*def.0.1, flattened);
    flatten_binding(&def.0.0, &val, flattened);
}

/* Flatten the given module down into the set of constraints it defines. */
pub fn flatten_module(
    module: &Module,
    flattened: &mut Module,
) {
    for def in &module.defs {
        flatten_definition(def, flattened);
    }
    for expr in &module.exprs {
        flatten_expression(expr, flattened);
    }
}

/* Convert each lsit in the given pattern into a tuple. More precisely, each use
 * of the pair constructor is replaced with cons, the list constructor, and each
 * use of unit is replaced with nil, the empty list. */
fn pattern_lists_to_tuples(pat: &mut Pattern) {
    match pat {
        Pattern::Nil => { *pat = Pattern::Unit },
        Pattern::As(pat, _var) => {
            pattern_lists_to_tuples(pat);
        },
        Pattern::Cons(pat1, pat2) => {
            *pat = Pattern::Product(pat1.clone(), pat2.clone());
            pattern_lists_to_tuples(pat);
        },
        Pattern::Product(pat1, pat2) => {
            pattern_lists_to_tuples(pat1);
            pattern_lists_to_tuples(pat2);
        },
        Pattern::Constant(_) | Pattern::Unit | Pattern::Variable(_) => {}
    }
}

/* Convert each lsit in the given expression into a tuple. More precisely, each
 * use of the pair constructor is replaced with cons, the list constructor, and
 * each use of unit is replaced with nil, the empty list. */
fn expr_lists_to_tuples(expr: &mut TExpr) {
    match &mut expr.v {
        Expr::Nil => { *expr = Expr::Unit.into() },
        Expr::Sequence(exprs) |
        Expr::Intrinsic(Intrinsic { args: exprs, .. }) => {
            for expr in exprs {
                expr_lists_to_tuples(expr);
            }
        },
        Expr::Cons(expr1, expr2) => {
            *expr = Expr::Product(expr1.clone(), expr2.clone()).into();
            expr_lists_to_tuples(expr);
        },
        Expr::Infix(_, expr1, expr2) | Expr::Application(expr1, expr2) |
        Expr::Product(expr1, expr2) => {
            expr_lists_to_tuples(expr1);
            expr_lists_to_tuples(expr2);
        },
        Expr::Negate(expr1) => {
            expr_lists_to_tuples(expr1);
        },
        Expr::Function(fun) => {
            for param in &mut fun.0 {
                pattern_lists_to_tuples(param);
            }
            expr_lists_to_tuples(&mut *fun.1);
        },
        Expr::LetBinding(binding, body) => {
            expr_lists_to_tuples(&mut *binding.1);
            pattern_lists_to_tuples(&mut binding.0);
            expr_lists_to_tuples(body);
        },
        Expr::Match(matche) => {
            expr_lists_to_tuples(&mut matche.0);
            for (pat, expr2) in matche.1.iter_mut().zip(matche.2.iter_mut()) {
                pattern_lists_to_tuples(pat);
                expr_lists_to_tuples(expr2);
            }
        },
        Expr::Constant(_) | Expr::Unit | Expr::Variable(_) => {},
    }
}

/* Convert each lsit in the given definition into a tuple. More precisely, each
 * use of the pair constructor is replaced with cons, the list constructor, and
 * each use of unit is replaced with nil, the empty list. */
fn definition_lists_to_tuples(def: &mut Definition) {
    pattern_lists_to_tuples(&mut def.0.0);
    expr_lists_to_tuples(&mut def.0.1);
}

/* Convert each lsit in the given module into a tuple. More precisely, each use
 * of the pair constructor is replaced with cons, the list constructor, and each
 * use of unit is replaced with nil, the empty list. After inlining, this
 * transformation allows the tuple structure inferencer to determine the exact
 * structure of lists. */
fn module_lists_to_tuples(module: &mut Module) {
    for def in &mut module.defs {
        definition_lists_to_tuples(def);
    }
    for expr in &mut module.exprs {
        expr_lists_to_tuples(expr);
    }
}

/* Make an equality expression to constrain the values that satify the circuit.
 * Simultaneously also make a variable definition to enable provers to generate
 * the necessary auxiliary variables. */
fn push_constraint_def(module: &mut Module, out: Pattern, expr: TExpr) {
    module.exprs.push(Expr::Infix(
        InfixOp::Equal,
        Box::new(out.to_expr()),
        Box::new(expr.clone())
    ).into());
    module.defs.push(Definition(LetBinding(out, Box::new(expr))));
}

/* Flatten the given expression down to a single term and place the definitions
 * of its parts into the given module. The parts always take the following form:
 * term1 = -term2 or term1 = term2 OP term3 */
fn flatten_expr_to_3ac(
    out: Option<Pattern>,
    expr: &TExpr,
    flattened: &mut Module,
    gen: &mut VarGen,
) -> Pattern {
    match (out, &expr.v) {
        (None, Expr::Constant(val)) => Pattern::Constant(*val),
        (None, Expr::Variable(var)) => Pattern::Variable(var.clone()),
        (Some(pat),
         Expr::Constant(_) | Expr::Variable(_)) => {
            push_constraint_def(flattened, pat.clone(), expr.clone());
            pat
        },
        (out, Expr::Negate(n)) => {
            let out1_term = flatten_expr_to_3ac(None, n, flattened, gen);
            let rhs = Expr::Negate(Box::new(out1_term.to_expr()));
            let out_var = Variable::new(gen.generate_id());
            let out = out.unwrap_or(Pattern::Variable(out_var.clone()));
            push_constraint_def(flattened, out.clone(), rhs.into());
            out
        },
        (out, Expr::Infix(InfixOp::Exponentiate, e1, e2)) => {
            match e2.v {
                Expr::Constant(0) =>
                    flatten_expr_to_3ac(out, &Expr::Constant(1).into(), flattened, gen),
                Expr::Constant(1) =>
                    flatten_expr_to_3ac(out, e1, flattened, gen),
                Expr::Constant(v2) if v2 > 0 => {
                    // Compute the base once and for all
                    let out1_term = flatten_expr_to_3ac(None, e1, flattened, gen);
                    // Compute roughly the sqrt of this expression
                    let sqrt = Expr::Infix(
                        InfixOp::Exponentiate,
                        Box::new(out1_term.to_expr()),
                        Box::new(Expr::Constant(v2/2).into())
                    );
                    let out2_term = flatten_expr_to_3ac(None, &sqrt.into(), flattened, gen);
                    // Now square the value to obtain roughly this expression
                    let mut rhs = infix_op(
                        InfixOp::Multiply,
                        out2_term.to_expr(),
                        out2_term.to_expr()
                    );
                    // Multiply by the base once more in order to obtain
                    // original value
                    if v2%2 == 1 {
                        rhs = infix_op(
                            InfixOp::Multiply,
                            rhs,
                            out1_term.to_expr()
                        );
                    }
                    flatten_expr_to_3ac(out, &rhs, flattened, gen)
                },
                Expr::Constant(v2) => {
                    // Compute the reciprocal of this expression
                    let recip = Expr::Infix(
                        InfixOp::Exponentiate,
                        Box::new(*e1.clone()),
                        Box::new(Expr::Constant(-v2).into())
                    );
                    let out1_term = flatten_expr_to_3ac(None, &recip.into(), flattened, gen);
                    // Now invert the value to obtain this expression
                    let rhs = infix_op(
                        InfixOp::Divide,
                        Expr::Constant(1).into(),
                        out1_term.to_expr()
                    );
                    flatten_expr_to_3ac(out, &rhs, flattened, gen)
                }
                _ => panic!("variables are not permitted in expression exponents"),
            }
        },
        (out, Expr::Infix(op, e1, e2)) => {
            let out1_term = flatten_expr_to_3ac(None, e1, flattened, gen);
            let out2_term = flatten_expr_to_3ac(None, e2, flattened, gen);
            let rhs = infix_op(
                *op,
                out1_term.to_expr(),
                out2_term.to_expr(),
            );
            let out_var = Variable::new(gen.generate_id());
            let out = out.unwrap_or(Pattern::Variable(out_var.clone()));
            push_constraint_def(flattened, out.clone(), rhs);
            out
        },
        _ => panic!("encountered unexpected expression: {}", expr),
    }
}

/* Flatten the given definition into three-address form. */
fn flatten_def_to_3ac(
    def: &Definition,
    flattened: &mut Module,
    gen: &mut VarGen,
) {
    flatten_expr_to_3ac(Some(def.0.0.clone()), &*def.0.1, flattened, gen);
}

/* Flatten all definitions and expressions in this module into three-address
 * form. */
pub fn flatten_module_to_3ac(
    module: &Module,
    prover_defs: &HashSet<VariableId>,
    flattened: &mut Module,
    gen: &mut VarGen,
) {
    for def in &module.defs {
        match &def.0.0 {
            Pattern::Variable(var) if !prover_defs.contains(&var.id) =>
                flatten_def_to_3ac(def, flattened, gen),
            Pattern::Variable(_) => { flattened.defs.push(def.clone()); },
            _ => unreachable!("encountered unexpected pattern: {}", def.0.0)
        }
    }
    for expr in &module.exprs {
        if let Expr::Infix(InfixOp::Equal, lhs, rhs) = &expr.v {
            // Flatten this equality constraint into a series of definitions.
            // The last inserted definition is always an encoding of an equality
            // constraint.
            match (lhs, &lhs.v, rhs, &rhs.v) {
                (_, Expr::Variable(var), ohs, _) |
                (ohs, _, _, Expr::Variable(var)) => {
                    flatten_expr_to_3ac(
                        Some(Pattern::Variable(var.clone())),
                        ohs,
                        flattened,
                        gen
                    );
                },
                (_, Expr::Constant(val), ohs, _) |
                (ohs, _, _, Expr::Constant(val)) => {
                    flatten_expr_to_3ac(
                        Some(Pattern::Constant(*val)),
                        ohs,
                        flattened,
                        gen
                    );
                },
                (_, _, _, _) => {
                    let lhs = flatten_expr_to_3ac(None, lhs, flattened, gen);
                    let rhs = flatten_expr_to_3ac(None, rhs, flattened, gen);
                    flatten_expr_to_3ac(
                        Some(lhs),
                        &rhs.to_expr(),
                        flattened,
                        gen
                    );
                }
            }
            // Remove the last definition because it is solely an equality
            // constraint.
            flattened
                .defs
                .pop()
                .expect("a definition should have been made for the current expression");
        }
    }
}

/* Compile the given module down into three-address codes. */
pub fn compile(mut module: Module) -> Module {
    let mut vg = VarGen::new();
    let mut globals = HashMap::new();
    let mut bindings = HashMap::new();
    let mut prog_types = HashMap::new();
    register_fresh_intrinsic(&mut globals, &mut bindings, &mut prog_types, &mut vg);
    register_iter_intrinsic(&mut globals, &mut bindings, &mut prog_types, &mut vg);
    number_module_variables(&mut module, &mut globals, &mut vg);
    // Save this type environment for when we repeat type inference
    let mut types = prog_types.clone();
    infer_module_types(&mut module, &globals, &mut prog_types, &mut vg);
    println!("** Inferring types...");
    print_types(&module, &prog_types);
    let mut prover_defs = HashSet::new();
    apply_module_functions(&mut module, &mut bindings, &mut prover_defs, &mut vg);
    // Unitize all function expressions now that they are all now applied
    unitize_module_functions(&mut module, &mut prog_types);
    // Now that inlining is complete, lists are equivalent to tuples
    module_lists_to_tuples(&mut module);
    infer_module_types(&mut module, &globals, &mut types, &mut vg);
    // Expand all tuple variables
    expand_module_variables(&mut module, &mut types, &mut vg);
    // Unitize all remaining function expressions using type information
    unitize_module_functions(&mut module, &mut types);
    // Start generating arithmetic constraints
    let mut constraints = Module::default();
    flatten_module(&module, &mut constraints);
    let mut module_3ac = Module::default();
    flatten_module_to_3ac(&constraints, &prover_defs, &mut module_3ac, &mut vg);
    // Start doing basic optimizations
    copy_propagate(&mut module_3ac, &prover_defs);
    eliminate_dead_equalities(&mut module_3ac);
    eliminate_dead_definitions(&mut module_3ac);
    module_3ac
}

/* Apply all the substitutions in the given map to the given expression. */
pub fn copy_propagate_expr(
    expr: &mut TExpr,
    substitutions: &HashMap<VariableId, TExpr>,
) {
    match &mut expr.v {
        Expr::Variable(v2) if substitutions.contains_key(&v2.id) => {
            *expr = substitutions[&v2.id].clone();
            copy_propagate_expr(expr, substitutions);
        },
        Expr::Sequence(exprs) |
        Expr::Intrinsic(Intrinsic { args: exprs, .. }) => {
            for expr in exprs {
                copy_propagate_expr(expr, substitutions);
            }
        },
        Expr::Infix(_, expr1, expr2) | Expr::Application(expr1, expr2) |
        Expr::Product(expr1, expr2) | Expr::Cons(expr1, expr2) => {
            copy_propagate_expr(expr1, substitutions);
            copy_propagate_expr(expr2, substitutions);
        },
        Expr::Negate(expr1) | Expr::Function(Function(_, expr1)) => {
            copy_propagate_expr(expr1, substitutions);
        },
        Expr::LetBinding(binding, expr2) => {
            copy_propagate_expr(&mut binding.1, substitutions);
            copy_propagate_expr(expr2, substitutions);
        },
        Expr::Match(matche) => {
            copy_propagate_expr(&mut matche.0, substitutions);
            for expr2 in &mut matche.2 {
                copy_propagate_expr(expr2, substitutions);
            }
        },
        Expr::Constant(_) | Expr::Variable(_) | Expr::Unit | Expr::Nil => {},
    }
}

/* Apply the given substitutions into the given definition's expression. And if
 * the result is a variable or constant, then make a new substitution for the
 * LHS. This optimization will reduce the number of variables in the circuit. */
pub fn copy_propagate_def(
    def: &mut Definition,
    substitutions: &mut HashMap<VariableId, TExpr>,
    prover_defs: &HashSet<VariableId>,
) {
    match &mut def.0.0 {
        Pattern::Variable(v1) => {
            copy_propagate_expr(&mut def.0.1, &substitutions);
            match &def.0.1.v {
                Expr::Variable(_) | Expr::Constant(_) if !prover_defs.contains(&v1.id) => {
                    substitutions.insert(v1.id, *def.0.1.clone());
                },
                _ => {},
            }
        },
        _ => panic!("only variable patterns should be present at this stage"),
    }
}

/* Replace all variables defined to be equal with a single representative.
 * If a variable is proven to be equal to a constant, then replace its
 * occurences with the constant. */
pub fn copy_propagate(module: &mut Module, prover_defs: &HashSet<VariableId>) {
    let mut substitutions: HashMap<VariableId, TExpr> = HashMap::new();
    for def in &mut module.defs {
        copy_propagate_def(def, &mut substitutions, prover_defs);
    }
    for expr in &mut module.exprs {
        copy_propagate_expr(expr, &substitutions);
    }
}

/* Eliminate equalities that are obviously true from the constraint set. This
 * will reduce the number of gates in the circuit. */
pub fn eliminate_dead_equalities(module: &mut Module) {
    let mut new_exprs = vec![];
    for expr in &mut module.exprs {
        match &expr.v {
            Expr::Infix(InfixOp::Equal, expr1, expr2) if
                matches!((&expr1.v, &expr2.v), (Expr::Constant(c1), Expr::Constant(c2)) if
                         c1 == c2) => {},
            Expr::Infix(InfixOp::Equal, expr1, expr2) if
                matches!((&expr1.v, &expr2.v), (Expr::Variable(v1), Expr::Variable(v2)) if
                         v1.id == v2.id) => {},
            _ => {
                new_exprs.push(expr.clone());
            },
        }
    }
    module.exprs = new_exprs;
}

/* Eliminate those definitions that are not directly or indirectly used in the
 * moudle constraints. Achieve this by doing a breadth first search for
 * variables starting with those used in the module constraints. */
pub fn eliminate_dead_definitions(module: &mut Module) {
    // To ease the lookup of definitions by the variables they define
    let mut defs = HashMap::new();
    for def in &module.defs {
        if let Pattern::Variable(v1) = &def.0.0 {
            defs.insert(v1.id, &def.0.1);
        } else {
            panic!("only variable patterns should be present at this stage");
        }
    }
    // The current set of variables being searched
    let mut active_vars = HashMap::new();
    for expr in &mut module.exprs {
        collect_expr_variables(expr, &mut active_vars);
    }
    let mut explored = HashSet::new();
    let mut next_vars = HashMap::new();
    // Find the set of all the variables reachable from the current active set
    while active_vars.len() > 0 {
        // Collect the set of variables depended upon by the current active set
        for (var, _) in active_vars.drain() {
            if !explored.contains(&var) {
                explored.insert(var);
                if let Some(expr) = defs.get(&var) {
                    collect_expr_variables(expr, &mut next_vars);
                }
            }
        }
        active_vars = next_vars;
        next_vars = HashMap::new();
    }
    // Now eliminate those definitions that are not reachable from the
    // constraint set
    let mut new_defs = Vec::new();
    for def in &module.defs {
        if let Pattern::Variable(v1) = &def.0.0 {
            if explored.contains(&v1.id) {
                new_defs.push(def.clone());
            }
        } else {
            panic!("only variable patterns should be present at this stage");
        }
    }
    module.defs = new_defs;
}

/* Register the fresh intrinsic in the compilation environment. */
fn register_fresh_intrinsic(
    globals: &mut HashMap<String, VariableId>,
    bindings: &mut HashMap<VariableId, TExpr>,
    types: &mut HashMap<VariableId, Type>,
    gen: &mut VarGen,
) {
    let fresh_func_id = gen.generate_id();
    let fresh_arg = Variable::new(gen.generate_id());
    // Register the range function in global namespace
    globals.insert("fresh".to_string(), fresh_func_id);
    // Describe the intrinsic's type, arity, and implementation
    let fresh_intrinsic = Intrinsic::new(
        1,
        Type::Forall(
            fresh_arg.clone(),
            Box::new(Type::Function(
                Box::new(Type::Variable(fresh_arg.clone())),
                Box::new(Type::Variable(fresh_arg)),
            )),
        ),
        expand_fresh_intrinsic,
    );
    // Register the intrinsic descriptor with the global binding
    types.insert(fresh_func_id, fresh_intrinsic.imp_typ.clone());
    bindings.insert(fresh_func_id, Expr::Intrinsic(fresh_intrinsic).into());
}

/* fresh x returns a fresh unconstrained variable whose prover definition equals
 * the supplied expression. */
fn expand_fresh_intrinsic(
    args: &Vec<TExpr>,
    _bindings: &HashMap<VariableId, TExpr>,
    prover_defs: &mut HashSet<VariableId>,
    gen: &mut VarGen,
) -> TExpr {
    if let [val] = &args[..] {
        // Make a new prover definition that is equal to the argument
        let fresh_arg = Variable::new(gen.generate_id());
        prover_defs.insert(fresh_arg.id);
        TExpr {
            t: val.t.clone(),
            v: Expr::LetBinding(
                LetBinding(
                    Pattern::Variable(fresh_arg.clone()),
                    Box::new(val.clone()),
                ),
                Box::new(TExpr {
                    t: val.t.clone(),
                    v: Expr::Variable(fresh_arg)
                })
            ),
        }
    } else {
        panic!("unexpected arguments to fresh: {:?}", args);
    }
}

/* Register the iter intrinsic in the compilation environment. */
fn register_iter_intrinsic(
    globals: &mut HashMap<String, VariableId>,
    bindings: &mut HashMap<VariableId, TExpr>,
    types: &mut HashMap<VariableId, Type>,
    gen: &mut VarGen,
) {
    let iter_func_id = gen.generate_id();
    let iter_arg = Variable::new(gen.generate_id());
    let iter_func = Type::Function(
        Box::new(Type::Variable(iter_arg.clone())),
        Box::new(Type::Variable(iter_arg.clone())),
    );
    // Register the iter function in global namespace
    globals.insert("iter".to_string(), iter_func_id);
    // Describe the intrinsic's type, arity, and implementation
    let iter_intrinsic = Intrinsic::new(
        1,
        Type::Forall(
            iter_arg,
            Box::new(Type::Function(
                Box::new(Type::Int),
                Box::new(Type::Function(
                    Box::new(iter_func.clone()),
                    Box::new(iter_func)
                )),
            )),
        ),
        expand_iter_intrinsic,
    );
    // Register the intrinsic descriptor with the global binding
    types.insert(iter_func_id, iter_intrinsic.imp_typ.clone());
    bindings.insert(iter_func_id, Expr::Intrinsic(iter_intrinsic).into());
}

/* iter x returns the Church numeral corresponding to the given integer x. */
fn expand_iter_intrinsic(
    args: &Vec<TExpr>,
    bindings: &HashMap<VariableId, TExpr>,
    prover_defs: &mut HashSet<VariableId>,
    gen: &mut VarGen,
) -> TExpr {
    match &args[..] {
        [TExpr { v: Expr::Constant(val), .. }] => {
            let iter_arg = Variable::new(gen.generate_id());
            let iter_func_var = Variable::new(gen.generate_id());
            let iter_func = TExpr {
                v: Expr::Variable(iter_func_var.clone()),
                t: Some(Type::Function(
                    Box::new(Type::Variable(iter_arg.clone())),
                    Box::new(Type::Variable(iter_arg.clone())),
                ))
            };
            let mut body = TExpr {
                v: Expr::Variable(iter_arg.clone()),
                t: Some(Type::Variable(iter_arg.clone()))
            };
            for _ in 0..*val {
                body = TExpr {
                    v: Expr::Application(
                        Box::new(iter_func.clone()),
                        Box::new(body.clone()),
                    ),
                    t: body.t,
                };
            }
            TExpr {
                t: Some(Type::Function(
                    Box::new(iter_func.t.clone().unwrap()),
                    Box::new(iter_func.t.unwrap()),
                )),
                v: Expr::Function(Function(
                    vec![
                        Pattern::Variable(iter_func_var),
                        Pattern::Variable(iter_arg),
                    ],
                    Box::new(body),
                )),
            }
        },
        [TExpr { v: Expr::Variable(Variable { id, .. }), .. }]
            if bindings.contains_key(id) =>
        {
            expand_iter_intrinsic(
                &vec![bindings[id].clone()],
                bindings,
                prover_defs,
                gen,
            )
        },
        _ => panic!("unexpected arguments to iter: {:?}", args),
    }
}
