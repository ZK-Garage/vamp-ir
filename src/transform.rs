use crate::ast::{
    Definition, Expr, Function, InfixOp, Intrinsic, LetBinding, Module, Pat, Rule, TExpr, TPat,
    VampirParser, Variable, VariableId,
};
use crate::error::*;
use crate::pest::Parser;
use crate::qprintln;
use crate::typecheck::{
    expand_expr_variables, expand_pattern_variables, infer_module_types, print_types,
    strip_module_types, Type,
};
use crate::util::Config;
use ark_ff::{One, Zero};
use num_bigint::BigInt;
use num_traits::sign::Signed;
use num_traits::ToPrimitive;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::io::Write;

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
        Expr::Intrinsic(Intrinsic { params, .. }) => {
            let mut map = map.clone();
            for param in params.iter_mut() {
                refresh_pattern_variables(param, &mut map, prover_defs, gen);
            }
        }
        Expr::Sequence(exprs) => {
            for expr in exprs {
                refresh_expr_variables(expr, map, prover_defs, gen);
            }
        }
        Expr::Infix(_, expr1, expr2)
        | Expr::Application(expr1, expr2)
        | Expr::Product(expr1, expr2)
        | Expr::Cons(expr1, expr2) => {
            refresh_expr_variables(expr1, map, prover_defs, gen);
            refresh_expr_variables(expr2, map, prover_defs, gen);
        }
        Expr::Match(matche) => {
            refresh_expr_variables(&mut matche.0, map, prover_defs, gen);
            for (pat, expr2) in matche.1.iter_mut().zip(matche.2.iter_mut()) {
                let mut map = map.clone();
                refresh_pattern_variables(pat, &mut map, prover_defs, gen);
                refresh_expr_variables(expr2, &map, prover_defs, gen);
            }
        }
        Expr::Negate(expr) => {
            refresh_expr_variables(expr, map, prover_defs, gen);
        }
        Expr::Constant(_) | Expr::Unit | Expr::Nil => {}
        Expr::Variable(var) => {
            if let Some(id) = map.get(&var.id) {
                var.id = *id;
            }
        }
        Expr::Function(fun) => {
            let mut map = map.clone();
            for param in &mut fun.params {
                refresh_pattern_variables(param, &mut map, prover_defs, gen);
            }
            refresh_expr_variables(&mut fun.body, &map, prover_defs, gen);
        }
        Expr::LetBinding(binding, expr) => {
            refresh_expr_variables(&mut binding.1, map, prover_defs, gen);
            let mut map = map.clone();
            refresh_pattern_variables(&mut binding.0, &mut map, prover_defs, gen);
            refresh_expr_variables(expr, &map, prover_defs, gen);
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum Tribool {
    False,
    Indeterminate,
    True,
}

/* Match the given expression against the given pattern. */
fn match_pattern_expr(
    pat: &TPat,
    expr: &TExpr,
    env: &mut HashMap<VariableId, TExpr>,
    ext: &mut HashMap<VariableId, TExpr>,
    prover_defs: &mut HashSet<VariableId>,
    gen: &mut VarGen,
) -> Result<Tribool, Error> {
    match (&pat.v, &expr.v) {
        (_, Expr::Variable(var)) if env.contains_key(&var.id) => {
            match_pattern_expr(pat, &env[&var.id].clone(), env, ext, prover_defs, gen)
        }
        (Pat::As(pat, var), _) => {
            let res = match_pattern_expr(pat, expr, env, ext, prover_defs, gen);
            ext.insert(var.id, expr.clone());
            res
        }
        (Pat::Variable(var), _) => {
            ext.insert(var.id, expr.clone());
            Ok(Tribool::True)
        }
        (Pat::Product(pat1, pat2), Expr::Product(expr1, expr2))
        | (Pat::Cons(pat1, pat2), Expr::Cons(expr1, expr2)) => {
            let inner_res1 = match_pattern_expr(pat1, expr1, env, ext, prover_defs, gen)?;
            let inner_res2 = match_pattern_expr(pat2, expr2, env, ext, prover_defs, gen)?;
            Ok(std::cmp::min(inner_res1, inner_res2))
        }
        (Pat::Product(_, _), Expr::Variable(var)) => {
            let new_var1 = Variable::new(gen.generate_id());
            let new_var2 = Variable::new(gen.generate_id());
            if prover_defs.contains(&var.id) {
                prover_defs.insert(new_var1.id);
                prover_defs.insert(new_var2.id);
            }
            let typ1 = Type::Variable(new_var1.clone());
            let typ2 = Type::Variable(new_var2.clone());
            let inner_expr1 = Box::new(Expr::Variable(new_var1).type_expr(Some(typ1.clone())));
            let inner_expr2 = Box::new(Expr::Variable(new_var2).type_expr(Some(typ2.clone())));
            env.insert(
                var.id,
                Expr::Product(inner_expr1, inner_expr2)
                    .type_expr(Some(Type::Product(Box::new(typ1), Box::new(typ2)))),
            );
            match_pattern_expr(pat, expr, env, ext, prover_defs, gen)
        }
        (Pat::Cons(_, _), Expr::Variable(var)) => {
            let new_var1 = Variable::new(gen.generate_id());
            let new_var2 = Variable::new(gen.generate_id());
            if prover_defs.contains(&var.id) {
                prover_defs.insert(new_var1.id);
                prover_defs.insert(new_var2.id);
            }
            let typ1 = Type::Variable(new_var1.clone());
            let typ2 = Type::List(Box::new(typ1.clone()));
            let inner_expr1 = Box::new(Expr::Variable(new_var1).type_expr(Some(typ1)));
            let inner_expr2 = Box::new(Expr::Variable(new_var2).type_expr(Some(typ2.clone())));
            env.insert(
                var.id,
                Expr::Cons(inner_expr1, inner_expr2).type_expr(Some(typ2)),
            );
            match_pattern_expr(pat, expr, env, ext, prover_defs, gen)
        }
        (Pat::Unit, Expr::Unit) | (Pat::Nil, Expr::Nil) => Ok(Tribool::True),
        (Pat::Constant(a), Expr::Constant(b)) if a == b => Ok(Tribool::True),
        (Pat::Constant(a), Expr::Constant(b)) if a != b => Ok(Tribool::False),
        (Pat::Constant(_), Expr::Variable(_) | Expr::Infix(_, _, _)) => Ok(Tribool::Indeterminate),
        _ => Err(Error::StaticMatchError {
            e: expr.clone(),
            p: pat.clone(),
        }),
    }
}

/* Refresh all the variables occurring in the given pattern. */
fn refresh_pattern_variables(
    pat: &mut TPat,
    map: &mut HashMap<VariableId, VariableId>,
    prover_defs: &mut HashSet<VariableId>,
    gen: &mut VarGen,
) {
    match &mut pat.v {
        Pat::As(pat, var) => {
            refresh_pattern_variables(pat, map, prover_defs, gen);
            map.insert(var.id, gen.generate_id());
            if prover_defs.contains(&var.id) {
                prover_defs.insert(map[&var.id]);
            }
            var.id = map[&var.id];
        }
        Pat::Product(pat1, pat2) | Pat::Cons(pat1, pat2) => {
            refresh_pattern_variables(pat1, map, prover_defs, gen);
            refresh_pattern_variables(pat2, map, prover_defs, gen);
        }
        Pat::Variable(var) => {
            map.insert(var.id, gen.generate_id());
            if prover_defs.contains(&var.id) {
                prover_defs.insert(map[&var.id]);
            }
            var.id = map[&var.id];
        }
        Pat::Constant(_) | Pat::Unit | Pat::Nil => {}
    }
}

/* Gives each variable occurring in the pattern a unique ID. Assumes that no
 * variable is used more than once in the pattern. */
fn number_pattern_variables(
    pat: &mut TPat,
    map: &mut HashMap<String, VariableId>,
    gen: &mut VarGen,
) {
    match &mut pat.v {
        Pat::As(pat, var) => {
            number_pattern_variables(pat, map, gen);
            if let Some(name) = &var.name {
                var.id = gen.generate_id();
                map.insert(name.clone(), var.id);
            }
        }
        Pat::Product(pat1, pat2) | Pat::Cons(pat1, pat2) => {
            number_pattern_variables(pat1, map, gen);
            number_pattern_variables(pat2, map, gen);
        }
        Pat::Variable(var) => {
            if let Some(name) = &var.name {
                var.id = gen.generate_id();
                map.insert(name.clone(), var.id);
            }
        }
        Pat::Constant(_) | Pat::Unit | Pat::Nil => {}
    }
}

/* Numbers the variable according to the binding in local. If there is no such
 * binding, then the global variable map is searched. If not found, then a new
 * global variable binding is made. */
fn number_variable(
    var: &mut Variable,
    locals: &HashMap<String, VariableId>,
    globals: &mut HashMap<String, VariableId>,
    gen: &mut VarGen,
) {
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
}

/* Numbers each variable occurring in the expression according to the binding in
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
        Expr::Sequence(exprs) => {
            for expr in exprs {
                number_expr_variables(expr, locals, globals, gen);
            }
        }
        Expr::Intrinsic(Intrinsic { params, .. }) => {
            let mut locals = locals.clone();
            for param in params {
                number_pattern_variables(param, &mut locals, gen);
            }
        }
        Expr::Infix(_, expr1, expr2)
        | Expr::Application(expr1, expr2)
        | Expr::Product(expr1, expr2)
        | Expr::Cons(expr1, expr2) => {
            number_expr_variables(expr1, locals, globals, gen);
            number_expr_variables(expr2, locals, globals, gen);
        }
        Expr::Negate(expr) => {
            number_expr_variables(expr, locals, globals, gen);
        }
        Expr::Constant(_) | Expr::Unit | Expr::Nil => {}
        Expr::Variable(var) => {
            number_variable(var, locals, globals, gen);
        }
        Expr::Function(fun) => {
            let mut locals = locals.clone();
            for param in &mut fun.params {
                number_pattern_variables(param, &mut locals, gen);
            }
            number_expr_variables(&mut fun.body, &locals, globals, gen);
        }
        Expr::LetBinding(binding, expr) => {
            let mut locals = locals.clone();
            number_expr_variables(&mut binding.1, &locals, globals, gen);
            number_pattern_variables(&mut binding.0, &mut locals, gen);
            number_expr_variables(expr, &locals, globals, gen);
        }
        Expr::Match(matche) => {
            number_expr_variables(&mut matche.0, locals, globals, gen);
            for (pat, expr2) in matche.1.iter_mut().zip(matche.2.iter_mut()) {
                let mut locals = locals.clone();
                number_pattern_variables(pat, &mut locals, gen);
                number_expr_variables(expr2, &locals, globals, gen);
            }
        }
    }
}

/* Numbers the variables occurring in the definition. Essentially numbers the
 * inner expression, and then numbers the definition pattern variables in global
 * scope. */
fn number_def_variables(
    def: &mut Definition,
    locals: &mut HashMap<String, VariableId>,
    globals: &mut HashMap<String, VariableId>,
    gen: &mut VarGen,
) {
    number_expr_variables(&mut def.0 .1, locals, globals, gen);
    number_pattern_variables(&mut def.0 .0, locals, gen);
}

/* Numbers the variables occurring in the module definitions and then those
 * occurring in the module expressions. */
pub fn number_module_variables(
    module: &mut Module,
    globals: &mut HashMap<String, VariableId>,
    gen: &mut VarGen,
    locals: &mut HashMap<String, u32>,
) {
    for var in &mut module.pubs {
        number_variable(var, locals, globals, gen);
    }
    for def in &mut module.defs {
        number_def_variables(def, locals, globals, gen);
    }
    for expr in &mut module.exprs {
        number_expr_variables(expr, locals, globals, gen);
    }
}

/* For each Some value in the extension, exchange it with the corresponding
 * value in map. If ext does not contain the corresponding key, then replace the
 * original value with None. For each None value in the extension, move the
 * corresponding key from map into the extension, leaving no entry behind. */
fn exchange_map<U, V>(map: &mut HashMap<U, V>, ext: &mut HashMap<U, Option<V>>)
where
    U: Eq + Hash + Clone,
{
    for (k, evo) in ext {
        let mut evor = None;
        std::mem::swap(&mut evor, evo);
        if let Some(ev) = evor {
            *evo = map.insert(k.clone(), ev);
        } else {
            *evo = map.remove(k);
        }
    }
}

/* Defines an interface for completing various arithmetic operations over a
 * field without exposing the underlying field. */
pub trait FieldOps {
    // Puts the given big integer in canonical form
    fn canonical(&self, num: BigInt) -> BigInt;
    // Negates the given big integer over the given field
    fn negate(&self, num: BigInt) -> BigInt;
    // Completes the given infix operation over the given field
    fn infix(&self, op: InfixOp, lhs: BigInt, rhs: BigInt) -> BigInt;
}

/* Evaluate the given binding emitting constraints as necessary. Returns the new
 * bindings created by this program fragment. */
fn evaluate_binding(
    binding: &LetBinding,
    capture: HashMap<VariableId, TExpr>,
    flattened: &mut Option<Module>,
    bindings: &mut HashMap<VariableId, TExpr>,
    prover_defs: &mut HashSet<VariableId>,
    field_ops: &dyn FieldOps,
    gen: &mut VarGen,
) -> HashMap<VariableId, TExpr> {
    // Evaluate the binding expression in the current environment
    let mut val = evaluate(&binding.1, flattened, bindings, prover_defs, field_ops, gen).unwrap();
    // Allow binding value to carry around its own context
    capture_env(&mut val, capture).unwrap();
    // Now make a let binding for the expanded value whilst making sure that the
    // pattern is fully expanded
    let mut new_binding = Definition(LetBinding(binding.0.clone(), Box::new(val)));
    let mut pat_exps = HashMap::new();
    expand_pattern_variables(&mut new_binding.0 .0, &new_binding.0 .1, &mut pat_exps, gen).unwrap();
    // Now decompose the let-binding into a flattened form
    flatten_binding(&new_binding.0 .0, &new_binding.0 .1, flattened);
    // Now expand the environment to reflect the binding that has been effected
    let mut new_bindings = HashMap::new();
    for (var, pat) in pat_exps {
        if let Some(pat) = pat {
            new_bindings.insert(var, pat);
        }
    }
    match_pattern_expr(
        &new_binding.0 .0,
        &new_binding.0 .1,
        bindings,
        &mut new_bindings,
        prover_defs,
        gen,
    )
    .unwrap();
    new_bindings
}

/* Weakly add the given bindings to the environment of the given expression if
 * it is a function or an intrinsic. The general idea is to incrementally add to
 * the object's environment as it escapes more lexical scopes, instead of
 * copying all captured bindings at once. */
fn capture_env(val: &mut TExpr, new_bindings: HashMap<VariableId, TExpr>) -> Result<(), Error> {
    match &mut val.v {
        Expr::Function(fun) => {
            for (k, v) in new_bindings {
                fun.env.entry(k).or_insert(v);
            }
            Ok(())
        }
        Expr::Intrinsic(intr) => {
            for (k, v) in new_bindings {
                intr.env.entry(k).or_insert(v);
            }
            Ok(())
        }
        Expr::Product(expr1, expr2) | Expr::Cons(expr1, expr2) => {
            capture_env(expr1, new_bindings.clone())?;
            capture_env(expr2, new_bindings)?;
            Ok(())
        }
        Expr::Unit
        | Expr::Infix(_, _, _)
        | Expr::Negate(_)
        | Expr::Constant(_)
        | Expr::Variable(_)
        | Expr::Nil => Ok(()),
        Expr::Application(_, _) | Expr::Sequence(_) | Expr::LetBinding(_, _) | Expr::Match(_) => {
            Err(Error::UnexpectedExpression { e: val.clone() })
        }
    }
}

/* Evaluate the given expression emitting constraints as necessary. Returns the
 * value that the given expression evaluates to. */
fn evaluate(
    expr: &TExpr,
    flattened: &mut Option<Module>,
    bindings: &mut HashMap<VariableId, TExpr>,
    prover_defs: &mut HashSet<VariableId>,
    field_ops: &dyn FieldOps,
    gen: &mut VarGen,
) -> Result<TExpr, Error> {
    match &expr.v {
        Expr::Application(expr1, expr2) => {
            let mut expr1 = evaluate(expr1, flattened, bindings, prover_defs, field_ops, gen)?;
            refresh_expr_variables(&mut expr1, &HashMap::new(), prover_defs, gen);
            match &mut expr1.v {
                Expr::Intrinsic(intr) => {
                    // Now that the current parameter is filled, move onto the
                    // next position
                    let param1 = intr.params[intr.pos].clone();
                    intr.pos += 1;
                    // The specific binding that needs to be added to
                    // environment
                    let new_bind = LetBinding(param1, Box::new(*expr2.clone()));
                    // Make sure that the argument's environment does not get
                    // overridden by that of the function by producing
                    // alternatives sourced from this context
                    let mut implicit_env = HashMap::new();
                    for var in intr.env.keys() {
                        if let Some(val) = bindings.get(var) {
                            implicit_env.insert(*var, val.clone());
                        }
                    }
                    // Setup the environment in which to evaluate body
                    let new_bindings = evaluate_binding(
                        &new_bind,
                        implicit_env,
                        flattened,
                        bindings,
                        prover_defs,
                        field_ops,
                        gen,
                    );
                    // Apply the new environment to the body
                    intr.env.extend(new_bindings.clone());
                    // Modify function type to account for the partial
                    // application that has just happened
                    expr1.t = None;
                    // Finally evaluate the body
                    let mut val =
                        evaluate(&expr1, flattened, bindings, prover_defs, field_ops, gen)?;
                    // Enable closures by storing the required environment
                    // modifications inside the evaluation result
                    capture_env(&mut val, new_bindings)?;
                    Ok(val)
                }
                Expr::Function(fun) if fun.params.is_empty() => Err(Error::NoParameterInFunction),
                Expr::Function(fun) => {
                    // Now that we have an assignment, move the function
                    // parameter into the environment
                    let param1 = fun.params.remove(0);
                    // The specific binding that needs to be added to
                    // environment
                    let new_bind = LetBinding(param1, Box::new(*expr2.clone()));
                    // Make sure that the argument's environment does not get
                    // overridden by that of the function by producing
                    // alternatives sourced from this context
                    let mut implicit_env = HashMap::new();
                    for var in fun.env.keys() {
                        if let Some(val) = bindings.get(var) {
                            implicit_env.insert(*var, val.clone());
                        }
                    }
                    // Setup the environment in which to evaluate body
                    let new_bindings = evaluate_binding(
                        &new_bind,
                        implicit_env,
                        flattened,
                        bindings,
                        prover_defs,
                        field_ops,
                        gen,
                    );
                    // Apply the new environment to the body
                    fun.env.extend(new_bindings.clone());
                    // Modify function type to account for the partial
                    // application that has just happened
                    expr1.t = None;
                    // Finally evaluate the body
                    let mut val =
                        evaluate(&expr1, flattened, bindings, prover_defs, field_ops, gen)?;
                    // Enable closures by storing the required environment
                    // modifications inside the evaluation result
                    capture_env(&mut val, new_bindings)?;
                    Ok(val)
                }
                _ => Err(Error::ApplicationError {
                    e2: *expr2.clone(),
                    e1: expr1,
                }),
            }
        }
        Expr::LetBinding(_, _) => {
            let mut acc_bindings = HashMap::new();
            let mut expr = expr;
            // Instead of recursively evaluating let-bindings, iteratively
            // evaluate them to reduce stack usage.
            while let Expr::LetBinding(binding, body) = &expr.v {
                // Evaluate binding expression and get new bindings
                let new_bindings = evaluate_binding(
                    binding,
                    HashMap::new(),
                    flattened,
                    bindings,
                    prover_defs,
                    field_ops,
                    gen,
                );
                let mut new_bindings = new_bindings
                    .into_iter()
                    .map(|(k, v)| (k, Some(v)))
                    .collect();
                // Insert new bindings into environment and get old bindings
                exchange_map(bindings, &mut new_bindings);
                // Store the old bindings, prioritizing the oldest bindings
                for (k, v) in new_bindings {
                    acc_bindings.entry(k).or_insert(v);
                }
                // Now move onto the body expression
                if let Expr::Sequence(seq) = &body.v {
                    // Iteratively evaluate a sequence expression here in order
                    // to avoid leaving this call frame
                    for expr in &seq[0..seq.len() - 1] {
                        evaluate(expr, flattened, bindings, prover_defs, field_ops, gen)?;
                    }
                    // Hence the let's body is now effectively this sequence's
                    // last expression
                    expr = seq.last().unwrap();
                } else {
                    expr = body;
                }
            }
            // Now evaluate the inner-most body
            let mut val = evaluate(expr, flattened, bindings, prover_defs, field_ops, gen)?;
            // Now restore the old environment before this entire let expression
            exchange_map(bindings, &mut acc_bindings);
            let acc_bindings = acc_bindings
                .into_iter()
                .map(|(k, v)| (k, v.unwrap()))
                .collect();
            // Capture the environment modifications required to evaluate body
            // inside the body. Necessary for closures.
            capture_env(&mut val, acc_bindings)?;
            Ok(val)
        }
        Expr::Sequence(seq) => {
            let mut val = None;
            for expr in seq {
                val = Some(evaluate(
                    expr,
                    flattened,
                    bindings,
                    prover_defs,
                    field_ops,
                    gen,
                ));
            }
            val.expect("encountered empty sequence")
        }
        Expr::Product(expr1, expr2) => {
            let expr1 = evaluate(expr1, flattened, bindings, prover_defs, field_ops, gen)?;
            let expr2 = evaluate(expr2, flattened, bindings, prover_defs, field_ops, gen)?;
            Ok(Expr::Product(Box::new(expr1), Box::new(expr2)).type_expr(expr.t.clone()))
        }
        Expr::Cons(expr1, expr2) => {
            let expr1 = evaluate(expr1, flattened, bindings, prover_defs, field_ops, gen)?;
            let expr2 = evaluate(expr2, flattened, bindings, prover_defs, field_ops, gen)?;
            Ok(Expr::Cons(Box::new(expr1), Box::new(expr2)).type_expr(expr.t.clone()))
        }
        Expr::Infix(InfixOp::Equal, expr1, expr2) => {
            let expr1 = evaluate(expr1, flattened, bindings, prover_defs, field_ops, gen)?;
            let expr2 = evaluate(expr2, flattened, bindings, prover_defs, field_ops, gen)?;
            flatten_equals(&expr1, &expr2, flattened);
            if flattened.is_none() {
                // To Do: Some way for repl to see constraint results?
                Ok(Expr::Unit.type_expr(Some(Type::Unit)))
            } else {
                Ok(Expr::Unit.type_expr(Some(Type::Unit)))
            }
        }
        Expr::Infix(InfixOp::Exponentiate, e1, e2) => {
            // Compute the base once and for all
            let e1 = evaluate(e1, flattened, bindings, prover_defs, field_ops, gen)?;
            let e2 = evaluate(e2, flattened, bindings, prover_defs, field_ops, gen)?;
            match (&e1.v, &e2.v) {
                (Expr::Constant(a), Expr::Constant(b)) => Ok(Expr::Constant(field_ops.infix(
                    InfixOp::Exponentiate,
                    a.clone(),
                    b.clone(),
                ))
                .type_expr(Some(Type::Int))),
                (_, Expr::Constant(c)) if c.is_zero() => {
                    Ok(Expr::Constant(One::one()).type_expr(Some(Type::Int)))
                }
                (_, Expr::Constant(c)) if c.is_one() => Ok(e1),
                (_, Expr::Constant(v2)) if v2.is_positive() => {
                    // Compute roughly the sqrt of this expression
                    let sqrt = Expr::Infix(
                        InfixOp::Exponentiate,
                        Box::new(e1.clone()),
                        Box::new(Expr::Constant(v2 / 2i8).type_expr(Some(Type::Int))),
                    )
                    .type_expr(Some(Type::Int));
                    let out2_term =
                        evaluate(&sqrt, flattened, bindings, prover_defs, field_ops, gen)?;
                    // Now square the value to obtain roughly this expression
                    let mut rhs = infix_op(InfixOp::Multiply, out2_term.clone(), out2_term);
                    // Multiply by the base once more in order to obtain
                    // original value
                    if v2 % 2i8 == One::one() {
                        rhs = infix_op(InfixOp::Multiply, rhs, e1);
                    }
                    evaluate(&rhs, flattened, bindings, prover_defs, field_ops, gen)
                }
                (_, Expr::Constant(v2)) => {
                    // Compute the reciprocal of this expression
                    let recip = Expr::Infix(
                        InfixOp::Exponentiate,
                        Box::new(e1),
                        Box::new(Expr::Constant(-v2).type_expr(Some(Type::Int))),
                    );
                    // Now invert the value to obtain this expression
                    let rhs = infix_op(
                        InfixOp::Divide,
                        Expr::Constant(One::one()).type_expr(Some(Type::Int)),
                        recip.type_expr(Some(Type::Int)),
                    );
                    evaluate(&rhs, flattened, bindings, prover_defs, field_ops, gen)
                }
                _ => Err(Error::VariableExponentError),
            }
        }
        Expr::Infix(op, expr1, expr2) => {
            let expr1 = evaluate(expr1, flattened, bindings, prover_defs, field_ops, gen)?;
            let expr2 = evaluate(expr2, flattened, bindings, prover_defs, field_ops, gen)?;
            match (&expr1.v, &expr2.v) {
                (Expr::Constant(c1), Expr::Constant(c2)) => {
                    Ok(Expr::Constant(field_ops.infix(*op, c1.clone(), c2.clone()))
                        .type_expr(expr.t.clone()))
                }
                (_, _) => {
                    let val = infix_op(*op, expr1, expr2);
                    let var = Variable::new(gen.generate_id());
                    let binding = Definition(LetBinding(
                        Pat::Variable(var.clone()).type_pat(expr.t.clone()),
                        Box::new(val),
                    ));
                    if let Some(flat) = flattened {
                        flat.defs.push(binding);
                    }
                    Ok(Expr::Variable(var).type_expr(expr.t.clone()))
                }
            }
        }
        Expr::Negate(expr1) => {
            let expr1 = evaluate(expr1, flattened, bindings, prover_defs, field_ops, gen)?;
            match expr1.v {
                Expr::Constant(c1) => {
                    Ok(Expr::Constant(field_ops.negate(c1)).type_expr(expr.t.clone()))
                }
                _ => Ok(Expr::Negate(Box::new(expr1)).type_expr(expr.t.clone())),
            }
        }
        Expr::Constant(c) => {
            Ok(Expr::Constant(field_ops.canonical(c.clone())).type_expr(expr.t.clone()))
        }
        Expr::Unit | Expr::Nil => Ok(expr.clone()),
        Expr::Variable(var) => match bindings.get(&var.id) {
            Some(val) if !prover_defs.contains(&var.id) => Ok(val.clone()),
            _ => Ok(expr.clone()),
        },
        Expr::Function(Function {
            params, body, env, ..
        }) if params.is_empty() => {
            let mut ext = env.clone().into_iter().map(|(k, v)| (k, Some(v))).collect();
            // Supplement the partially captured environment with bindings
            exchange_map(bindings, &mut ext);
            let val = evaluate(body, flattened, bindings, prover_defs, field_ops, gen);
            exchange_map(bindings, &mut ext);
            val
        }
        Expr::Intrinsic(
            intr @ Intrinsic {
                pos, params, env, ..
            },
        ) if *pos == params.len() => {
            let mut ext = env.clone().into_iter().map(|(k, v)| (k, Some(v))).collect();
            // Supplement the partially captured environment with bindings
            exchange_map(bindings, &mut ext);
            let expr1 = intr.execute(bindings, prover_defs, gen)?;
            let val = evaluate(&expr1, flattened, bindings, prover_defs, field_ops, gen)?;
            exchange_map(bindings, &mut ext);
            Ok(val)
        }
        Expr::Function(_) | Expr::Intrinsic(_) => Ok(expr.clone()),
        Expr::Match(matche) => {
            let val = evaluate(&matche.0, flattened, bindings, prover_defs, field_ops, gen)?;
            for (pat, expr2) in matche.1.iter().zip(matche.2.iter()) {
                let res =
                    match_pattern_expr(pat, &val, bindings, &mut HashMap::new(), prover_defs, gen)?;
                match res {
                    Tribool::True => {
                        let expr = TExpr {
                            v: Expr::LetBinding(
                                LetBinding(pat.clone(), matche.0.clone()),
                                Box::new(expr2.clone()),
                            ),
                            t: expr.t.clone(),
                        };
                        return evaluate(&expr, flattened, bindings, prover_defs, field_ops, gen);
                    }
                    Tribool::Indeterminate => {
                        return Err(Error::StaticMatchError {
                            e: expr.clone(),
                            p: pat.clone(),
                        })
                    }
                    Tribool::False => continue,
                }
            }
            Err(Error::MatchError {
                e1: *matche.0.clone(),
                e2: expr.clone(),
            })
        }
    }
}

/* Evaluate the given definition emitting the implied constraints. The binding
 * environment is modified as necessary. */
fn evaluate_def(
    def: &Definition,
    flattened: &mut Option<Module>,
    bindings: &mut HashMap<VariableId, TExpr>,
    prover_defs: &mut HashSet<VariableId>,
    field_ops: &dyn FieldOps,
    gen: &mut VarGen,
) {
    let ext = evaluate_binding(
        &def.0,
        HashMap::new(),
        flattened,
        bindings,
        prover_defs,
        field_ops,
        gen,
    );
    bindings.extend(ext);
}

/* Evaluate the given module emitting the constraints that it implies. */
pub fn evaluate_module(
    module: &Module,
    oflattened: &mut Option<Module>,
    bindings: &mut HashMap<VariableId, TExpr>,
    prover_defs: &mut HashSet<VariableId>,
    field_ops: &dyn FieldOps,
    gen: &mut VarGen,
) {
    if let Some(flattened) = oflattened {
        flattened.pubs.extend(module.pubs.clone());
    }
    for def in &module.defs {
        evaluate_def(def, oflattened, bindings, prover_defs, field_ops, gen);
    }
    for expr in &module.exprs {
        evaluate(expr, oflattened, bindings, prover_defs, field_ops, gen).unwrap();
    }
}

/* Collect all the variables occurring in the given pattern. */
pub fn collect_pattern_variables(pat: &TPat, map: &mut HashMap<VariableId, Variable>) {
    match &pat.v {
        Pat::Variable(var) => {
            map.insert(var.id, var.clone());
        }
        Pat::As(pat, var) => {
            map.insert(var.id, var.clone());
            collect_pattern_variables(pat, map);
        }
        Pat::Product(pat1, pat2) | Pat::Cons(pat1, pat2) => {
            collect_pattern_variables(pat1, map);
            collect_pattern_variables(pat2, map);
        }
        Pat::Constant(_) | Pat::Unit | Pat::Nil => {}
    }
}

/* Collect all the variables occurring in the given expression. */
fn collect_expr_variables(expr: &TExpr, map: &mut HashMap<VariableId, Variable>) {
    match &expr.v {
        Expr::Variable(var) => {
            map.entry(var.id).or_insert_with(|| var.clone());
        }
        Expr::Sequence(exprs) => {
            exprs
                .iter()
                .for_each(|expr| collect_expr_variables(expr, map));
        }
        Expr::Intrinsic(Intrinsic { params, .. }) => {
            params
                .iter()
                .for_each(|param| collect_pattern_variables(param, map));
        }
        Expr::Infix(_, expr1, expr2)
        | Expr::Application(expr1, expr2)
        | Expr::Product(expr1, expr2)
        | Expr::Cons(expr1, expr2) => {
            collect_expr_variables(expr1, map);
            collect_expr_variables(expr2, map);
        }
        Expr::Negate(expr1) => {
            collect_expr_variables(expr1, map);
        }
        Expr::Function(fun) => {
            fun.params
                .iter()
                .for_each(|param| collect_pattern_variables(param, map));
            collect_expr_variables(&fun.body, map);
        }
        Expr::LetBinding(binding, body) => {
            collect_expr_variables(&binding.1, map);
            collect_pattern_variables(&binding.0, map);
            collect_expr_variables(body, map);
        }
        Expr::Match(matche) => {
            collect_expr_variables(&matche.0, map);
            matche.1.iter().zip(&matche.2).for_each(|(pat, expr2)| {
                collect_pattern_variables(pat, map);
                collect_expr_variables(expr2, map);
            });
        }
        Expr::Constant(_) | Expr::Unit | Expr::Nil => {}
    }
}

/* Collect all the variables occurring in the given definition. */
fn collect_def_variables(def: &Definition, map: &mut HashMap<VariableId, Variable>) {
    collect_expr_variables(&def.0 .1, map);
    collect_pattern_variables(&def.0 .0, map);
}

/* Collect all the public variables occurring in the given module. */
pub fn collect_public_module_variables(module: &Module, map: &mut HashMap<VariableId, Variable>) {
    map.reserve(module.pubs.len());
    map.extend(module.pubs.iter().map(|var| (var.id, var.clone())));
}

/* Collect all the variables occurring in the given module. */
pub fn collect_module_variables(module: &Module, map: &mut HashMap<VariableId, Variable>) {
    collect_public_module_variables(module, map);

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
        (InfixOp::Multiply, Expr::Constant(c), _) if c.is_one() => e2,
        (InfixOp::Multiply, _, Expr::Constant(c)) if c.is_one() => e1,
        (InfixOp::Multiply, Expr::Constant(c), _) if c.is_zero() => e1,
        (InfixOp::Multiply, _, Expr::Constant(c)) if c.is_zero() => e2,
        (InfixOp::Divide, _, Expr::Constant(c)) if c.is_one() => e1,
        (InfixOp::DivideZ, _, Expr::Constant(c)) if c.is_one() => e1,
        (InfixOp::DivideZ, Expr::Constant(c), _) if c.is_zero() => e1,
        (InfixOp::IntDivide, _, Expr::Constant(c)) if c.is_one() => e1,
        (InfixOp::Modulo, _, Expr::Constant(c)) if c.is_one() => TExpr {
            v: Expr::Constant(Zero::zero()),
            t: Some(Type::Int),
        },
        (InfixOp::Add, Expr::Constant(c), _) if c.is_zero() => e2,
        (InfixOp::Add, _, Expr::Constant(c)) if c.is_zero() => e1,
        (InfixOp::Subtract, _, Expr::Constant(c)) if c.is_zero() => e1,
        (InfixOp::Equal, _, _) => TExpr {
            v: Expr::Infix(op, Box::new(e1), Box::new(e2)),
            t: Some(Type::Unit),
        },
        (
            InfixOp::Multiply
            | InfixOp::Divide
            | InfixOp::DivideZ
            | InfixOp::Add
            | InfixOp::Subtract
            | InfixOp::Exponentiate
            | InfixOp::IntDivide
            | InfixOp::Modulo,
            _,
            _,
        ) => TExpr {
            v: Expr::Infix(op, Box::new(e1), Box::new(e2)),
            t: Some(Type::Int),
        },
    }
}

/* Flatten the given binding down into the set of constraints it defines. */
fn flatten_binding(pat: &TPat, expr: &TExpr, oflattened: &mut Option<Module>) {
    if let Some(flattened) = oflattened {
        match (&pat.v, &expr.v) {
            (Pat::Variable(_), Expr::Function(_) | Expr::Intrinsic(_)) => {}
            (
                Pat::Variable(_),
                Expr::Variable(_) | Expr::Constant(_) | Expr::Infix(_, _, _) | Expr::Negate(_),
            ) => {
                flattened
                    .defs
                    .push(Definition(LetBinding(pat.clone(), Box::new(expr.clone()))));
            }
            (
                Pat::Constant(pat),
                Expr::Variable(_) | Expr::Constant(_) | Expr::Infix(_, _, _) | Expr::Negate(_),
            ) => {
                flattened.exprs.push(
                    Expr::Infix(
                        InfixOp::Equal,
                        Box::new(Expr::Constant(pat.clone()).type_expr(Some(Type::Int))),
                        Box::new(expr.clone()),
                    )
                    .type_expr(Some(Type::Unit)),
                );
            }
            (Pat::As(pat, _name), _) => {
                flatten_binding(pat, expr, oflattened);
            }
            (Pat::Unit, Expr::Unit) | (Pat::Nil, Expr::Nil) => {}
            (Pat::Product(pat1, pat2), Expr::Product(expr1, expr2)) => {
                flatten_binding(pat1, expr1, oflattened);
                flatten_binding(pat2, expr2, oflattened);
            }
            (Pat::Cons(pat1, pat2), Expr::Cons(expr1, expr2)) => {
                flatten_binding(pat1, expr1, oflattened);
                flatten_binding(pat2, expr2, oflattened);
            }
            _ => unreachable!("encountered unexpected binding: {} = {}", pat, expr),
        }
    }
}

/* Flatten the given equality down into the set of constraints it defines. */
fn flatten_equals(expr1: &TExpr, expr2: &TExpr, oflattened: &mut Option<Module>) {
    if let Some(flattened) = oflattened {
        match (&expr1.v, &expr2.v) {
            (Expr::Unit, Expr::Unit) | (Expr::Nil, Expr::Nil) => {}
            (Expr::Product(expr11, expr12), Expr::Product(expr21, expr22))
            | (Expr::Cons(expr11, expr12), Expr::Cons(expr21, expr22)) => {
                flatten_equals(expr11, expr21, oflattened);
                flatten_equals(expr12, expr22, oflattened);
            }
            (
                Expr::Variable(_) | Expr::Negate(_) | Expr::Infix(_, _, _) | Expr::Constant(_),
                Expr::Variable(_) | Expr::Negate(_) | Expr::Infix(_, _, _) | Expr::Constant(_),
            ) => {
                flattened.exprs.push(
                    Expr::Infix(
                        InfixOp::Equal,
                        Box::new(expr1.clone()),
                        Box::new(expr2.clone()),
                    )
                    .type_expr(Some(Type::Unit)),
                );
            }
            _ => unreachable!("encountered unexpected equality: {} = {}", expr1, expr2),
        }
    }
}

/* Make an equality expression to constrain the values that satisfy the circuit.
 * Simultaneously also make a variable definition to enable provers to generate
 * the necessary auxiliary variables. */
fn push_constraint_def(module: &mut Module, out: TPat, expr: TExpr) {
    module.exprs.push(
        Expr::Infix(
            InfixOp::Equal,
            Box::new(out.to_expr()),
            Box::new(expr.clone()),
        )
        .type_expr(Some(Type::Unit)),
    );
    module
        .defs
        .push(Definition(LetBinding(out, Box::new(expr))));
}

/* Flatten the given expression down to a single term and place the definitions
 * of its parts into the given module. The parts always take the following form:
 * term1 = -term2 or term1 = term2 OP term3 */
fn flatten_expr_to_3ac(
    out: Option<TPat>,
    expr: &TExpr,
    flattened: &mut Module,
    gen: &mut VarGen,
) -> Result<TPat, Error> {
    match (out, &expr.v) {
        (None, Expr::Constant(val)) => Ok(Pat::Constant(val.clone()).type_pat(expr.t.clone())),
        (None, Expr::Variable(var)) => Ok(Pat::Variable(var.clone()).type_pat(expr.t.clone())),
        (Some(pat), Expr::Constant(_) | Expr::Variable(_)) => {
            push_constraint_def(flattened, pat.clone(), expr.clone());
            Ok(pat)
        }
        (out, Expr::Negate(n)) => {
            let out1_term = flatten_expr_to_3ac(None, n, flattened, gen)?;
            let rhs = Expr::Negate(Box::new(out1_term.to_expr()));
            let out_var = Variable::new(gen.generate_id());
            let out = out.unwrap_or(Pat::Variable(out_var).type_pat(expr.t.clone()));
            push_constraint_def(flattened, out.clone(), rhs.type_expr(Some(Type::Int)));
            Ok(out)
        }
        (out, Expr::Infix(op, e1, e2)) if *op != InfixOp::Exponentiate => {
            let out1_term = flatten_expr_to_3ac(None, e1, flattened, gen)?;
            let out2_term = flatten_expr_to_3ac(None, e2, flattened, gen)?;
            let rhs = infix_op(*op, out1_term.to_expr(), out2_term.to_expr());
            let out_var = Variable::new(gen.generate_id());
            let out = out.unwrap_or(Pat::Variable(out_var).type_pat(expr.t.clone()));
            push_constraint_def(flattened, out.clone(), rhs);
            Ok(out)
        }
        _ => Err(Error::UnexpectedExpression { e: expr.clone() }),
    }
}

/* Flatten the given definition into three-address form. */
fn flatten_def_to_3ac(def: &Definition, flattened: &mut Module, gen: &mut VarGen) {
    flatten_expr_to_3ac(Some(def.0 .0.clone()), &def.0 .1, flattened, gen).unwrap();
}

/* Flatten all definitions and expressions in this module into three-address
 * form. */
pub fn flatten_module_to_3ac(
    omodule: &Option<Module>,
    prover_defs: &HashSet<VariableId>,
    flattened: &mut Module,
    gen: &mut VarGen,
) {
    if let Some(module) = omodule {
        flattened.pubs.extend(module.pubs.clone());
        for def in &module.defs {
            match &def.0 .0.v {
                Pat::Variable(var) if !prover_defs.contains(&var.id) => {
                    flatten_def_to_3ac(def, flattened, gen)
                }
                Pat::Variable(_) => {
                    flattened.defs.push(def.clone());
                }
                Pat::Unit => {}
                _ => unreachable!("encountered unexpected pattern: {}", def.0 .0),
            }
        }
        for expr in &module.exprs {
            if let Expr::Infix(InfixOp::Equal, lhs, rhs) = &expr.v {
                // Flatten this equality constraint into a series of definitions.
                // The last inserted definition is always an encoding of an equality
                // constraint.
                match (lhs, &lhs.v, rhs, &rhs.v) {
                    (_, Expr::Variable(var), ohs, _) | (ohs, _, _, Expr::Variable(var)) => {
                        flatten_expr_to_3ac(
                            Some(Pat::Variable(var.clone()).type_pat(ohs.t.clone())),
                            ohs,
                            flattened,
                            gen,
                        )
                        .unwrap();
                    }
                    (_, Expr::Constant(val), ohs, _) | (ohs, _, _, Expr::Constant(val)) => {
                        flatten_expr_to_3ac(
                            Some(Pat::Constant(val.clone()).type_pat(ohs.t.clone())),
                            ohs,
                            flattened,
                            gen,
                        )
                        .unwrap();
                    }
                    (_, _, _, _) => {
                        let lhs = flatten_expr_to_3ac(None, lhs, flattened, gen).unwrap();
                        let rhs = flatten_expr_to_3ac(None, rhs, flattened, gen).unwrap();
                        flatten_expr_to_3ac(Some(lhs), &rhs.to_expr(), flattened, gen).unwrap();
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
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug)]
enum Usage {
    Never,
    Witness,
    Constraint,
}

/* Classify definitions according to whether they define a constraint (i.e
 * corresponds to a gate in the circuit), are a witness (i.e. only used by the
 * prover to generate witnesses), or are unused. */
pub fn classify_defs(omodule: &mut Option<Module>, prover_defs: &mut HashSet<VariableId>) {
    if let Some(module) = omodule {
        let mut classifier = HashMap::new();
        // Start by assuming that all variables occurring in constraint expressions
        // have constraint definitions.
        for expr in &module.exprs {
            let mut constraint_vars = HashMap::new();
            collect_expr_variables(expr, &mut constraint_vars);
            for var in constraint_vars.keys() {
                classifier.insert(*var, Usage::Constraint);
            }
        }
        for def in module.defs.iter().rev() {
            if let Pat::Variable(var) = &def.0 .0.v {
                // Override the usage of this variable to witness if it is actually
                // used and occurs in prover_defs
                let val = classifier.entry(var.id).or_insert(Usage::Never);
                if *val != Usage::Never && prover_defs.contains(&var.id) {
                    classifier.insert(var.id, Usage::Witness);
                }

                if classifier[&var.id] == Usage::Witness {
                    // If this is a witness definition, then every variable on the
                    // right-hand-side at least has a witness definition
                    let mut vars = HashMap::new();
                    collect_expr_variables(&def.0 .1, &mut vars);
                    for prover_var in vars.keys() {
                        let val = *classifier.entry(*prover_var).or_insert(Usage::Never);
                        classifier.insert(*prover_var, std::cmp::max(val, Usage::Witness));
                    }
                } else if classifier[&var.id] == Usage::Constraint {
                    // If this is a constraint definition, then every variable on
                    // the right-hand-side at least has a constraint definition
                    let mut vars = HashMap::new();
                    collect_expr_variables(&def.0 .1, &mut vars);
                    for constraint_var in vars {
                        let val = *classifier.entry(constraint_var.0).or_insert(Usage::Never);
                        classifier.insert(constraint_var.0, std::cmp::max(val, Usage::Constraint));
                    }
                }
            }
        }
        // Update prover_defs with our classification
        for (var, usage) in &classifier {
            if *usage == Usage::Witness {
                prover_defs.insert(*var);
            }
        }
        // Now eliminate those definitions that are never used
        module.defs.retain(|def| {
            if let Pat::Variable(v1) = &def.0 .0.v {
                classifier[&v1.id] != Usage::Never
            } else if let Pat::Unit = &def.0 .0.v {
                false
            } else {
                panic!("only variable patterns should be present at this stage");
            }
        });
    }
}

/* Fully expand out references to global variables using the available type
 * information. */
fn expand_global_variables(
    module: &mut Module,
    globals: &HashMap<String, VariableId>,
    vars: &HashMap<VariableId, Type>,
    types: &mut HashMap<VariableId, Type>,
    bindings: &HashMap<VariableId, TExpr>,
    gen: &mut VarGen,
) {
    let mut expansions = HashMap::new();
    // Use the derived type information to figure out the form of each global
    // variable
    for (name, id) in globals {
        if !bindings.contains_key(id) {
            let mut expr = Expr::Variable(Variable {
                name: Some(name.clone()),
                id: *id,
            })
            .type_expr(Some(vars[id].clone()));
            expand_expr_variables(&mut expr, &mut expansions, types, gen).unwrap();
        }
    }
    // Now substitute each reference to a global variable with its inner
    // structure
    for def in &mut module.defs {
        copy_propagate_expr(&mut def.0 .1, &expansions);
    }
    for expr in &mut module.exprs {
        copy_propagate_expr(expr, &expansions);
    }
}

/* Compile the given module down into three-address codes. */
pub fn compile(mut module: Module, field_ops: &dyn FieldOps, config: &Config) -> Module {
    let mut vg = VarGen::new();
    let mut globals = HashMap::new();
    let mut bindings = HashMap::new();
    let mut prog_types = HashMap::new();
    let mut global_types = HashMap::new();
    register_fresh_intrinsic(&mut globals, &mut global_types, &mut bindings, &mut vg);
    register_iter_intrinsic(&mut globals, &mut global_types, &mut bindings, &mut vg);
    register_fold_intrinsic(&mut globals, &mut global_types, &mut bindings, &mut vg);
    number_module_variables(&mut module, &mut globals, &mut vg, &mut HashMap::new());
    infer_module_types(
        &mut module,
        &globals,
        &mut global_types,
        &mut prog_types,
        &mut vg,
    );
    qprintln!(config, "** Inferring types...");
    print_types(&module, &prog_types, config);
    // Global variables may have further internal structure, determine this
    // using derived type information
    expand_global_variables(
        &mut module,
        &globals,
        &global_types,
        &mut prog_types,
        &bindings,
        &mut vg,
    );
    // Type information is no longer required since we do symbolic
    // execution from now on
    strip_module_types(&mut module);
    let mut prover_defs = HashSet::new();
    let mut constraints = Some(Module::default());
    // Start generating arithmetic constraints
    evaluate_module(
        &module,
        &mut constraints,
        &mut bindings,
        &mut prover_defs,
        field_ops,
        &mut vg,
    );
    // Classify each definition that occurs in the constraints
    classify_defs(&mut constraints, &mut prover_defs);
    let mut module_3ac = Module::default();
    flatten_module_to_3ac(&constraints, &prover_defs, &mut module_3ac, &mut vg);
    // Start doing basic optimizations
    copy_propagate(&mut module_3ac, &prover_defs);
    eliminate_dead_equalities(&mut module_3ac);
    module_3ac
}

/* Apply all the substitutions in the given map to the given expression. */
pub fn copy_propagate_expr(expr: &mut TExpr, substitutions: &HashMap<VariableId, TExpr>) {
    match &mut expr.v {
        Expr::Variable(v2) if substitutions.contains_key(&v2.id) => {
            *expr = substitutions[&v2.id].clone();
            copy_propagate_expr(expr, substitutions);
        }
        Expr::Sequence(exprs) => {
            for expr in exprs {
                copy_propagate_expr(expr, substitutions);
            }
        }
        Expr::Infix(_, expr1, expr2)
        | Expr::Application(expr1, expr2)
        | Expr::Product(expr1, expr2)
        | Expr::Cons(expr1, expr2) => {
            copy_propagate_expr(expr1, substitutions);
            copy_propagate_expr(expr2, substitutions);
        }
        Expr::Negate(expr1) | Expr::Function(Function { body: expr1, .. }) => {
            copy_propagate_expr(expr1, substitutions);
        }
        Expr::LetBinding(binding, expr2) => {
            copy_propagate_expr(&mut binding.1, substitutions);
            copy_propagate_expr(expr2, substitutions);
        }
        Expr::Match(matche) => {
            copy_propagate_expr(&mut matche.0, substitutions);
            for expr2 in &mut matche.2 {
                copy_propagate_expr(expr2, substitutions);
            }
        }
        Expr::Intrinsic(_) | Expr::Constant(_) | Expr::Variable(_) | Expr::Unit | Expr::Nil => {}
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
    match &mut def.0 .0.v {
        Pat::Variable(v1) => {
            copy_propagate_expr(&mut def.0 .1, substitutions);
            match &def.0 .1.v {
                Expr::Variable(_) | Expr::Constant(_) if !prover_defs.contains(&v1.id) => {
                    substitutions.insert(v1.id, *def.0 .1.clone());
                }
                _ => {}
            }
        }
        _ => panic!("only variable patterns should be present at this stage"),
    }
}

/* Replace all variables defined to be equal with a single representative.
 * If a variable is proven to be equal to a constant, then replace its
 * occurrences with the constant. */
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
    module.exprs.retain(|expr| match &expr.v {
        Expr::Infix(InfixOp::Equal, expr1, expr2)
            if matches!((&expr1.v, &expr2.v), (Expr::Constant(c1), Expr::Constant(c2)) if
                         c1 == c2) =>
        {
            false
        }
        Expr::Infix(InfixOp::Equal, expr1, expr2)
            if matches!((&expr1.v, &expr2.v), (Expr::Variable(v1), Expr::Variable(v2)) if
                         v1.id == v2.id) =>
        {
            false
        }
        _ => true,
    });
}

/* Register the fresh intrinsic in the compilation environment. */
fn register_fresh_intrinsic(
    globals: &mut HashMap<String, VariableId>,
    global_types: &mut HashMap<VariableId, Type>,
    bindings: &mut HashMap<VariableId, TExpr>,
    gen: &mut VarGen,
) {
    let fresh_func_id = gen.generate_id();
    let fresh_arg_id = gen.generate_id();
    let fresh_arg = Variable::new(fresh_arg_id);
    let fresh_arg_type = Type::Variable(fresh_arg.clone());
    let fresh_arg_pat = Pat::Variable(fresh_arg.clone()).type_pat(Some(fresh_arg_type.clone()));
    // Register the range function in global namespace
    globals.insert("fresh".to_string(), fresh_func_id);
    // Describe the intrinsic's parameters and implementation
    let fresh_intrinsic = Intrinsic::new(vec![fresh_arg_pat], expand_fresh_intrinsic);
    // Describe the intrinsic's type
    let imp_typ = Type::Function(Box::new(fresh_arg_type.clone()), Box::new(fresh_arg_type));
    // Register the intrinsic descriptor with the global binding
    global_types.insert(
        fresh_func_id,
        Type::Forall(fresh_arg, Box::new(imp_typ.clone())),
    );
    // Register this as a binding to contextualize evaluation
    bindings.insert(
        fresh_func_id,
        Expr::Intrinsic(fresh_intrinsic).type_expr(Some(imp_typ)),
    );
}

/* fresh x returns a fresh unconstrained expression whose prover definition
 * equals the supplied expression. */
fn expand_fresh_intrinsic(
    params: &Vec<TPat>,
    bindings: &HashMap<VariableId, TExpr>,
    prover_defs: &mut HashSet<VariableId>,
    gen: &mut VarGen,
) -> Result<TExpr, Error> {
    match &params[..] {
        [param]
            if matches!(param.v, Pat::Variable(param_var) if {
                let val = bindings[&param_var.id].clone();
                // Make a new prover definition that is equal to the argument
                let fresh_arg = Variable::new(gen.generate_id());
                let mut fresh_pat = Pat::Variable(fresh_arg).type_pat(val.t.clone());
                let mut pat_exps = HashMap::new();
                // Expand the pattern using our knowledge of the expression's form
                expand_pattern_variables(&mut fresh_pat, &val, &mut pat_exps, gen).expect("Pattern variable expantion shouldn't fail.");
                // Make sure every part of expanded expression is a prover variable
                for var in pat_exps.keys() {
                    prover_defs.insert(*var);
                }
                return Ok(TExpr {
                    t: val.t.clone(),
                    v: Expr::LetBinding(
                        LetBinding(
                            fresh_pat.clone(),
                            Box::new(val.clone()),
                        ),
                        Box::new(fresh_pat.to_expr())
                    ),
                })
            }) =>
        {
            unreachable!()
        }
        _ => Err(Error::UnexpectedFreshParameters {
            params: params.clone(),
        }),
    }
}

/* Register the fresh intrinsic in the compilation environment.
For the REPL, fresh is essentially the identity function */
fn register_fresh_intrinsic_repl(
    globals: &mut HashMap<String, VariableId>,
    global_types: &mut HashMap<VariableId, Type>,
    bindings: &mut HashMap<VariableId, TExpr>,
    gen: &mut VarGen,
) {
    let fresh_func_id = gen.generate_id();
    let fresh_arg_id = gen.generate_id();
    let fresh_arg = Variable::new(fresh_arg_id);
    let fresh_arg_type = Type::Variable(fresh_arg.clone());
    let fresh_arg_pat = Pat::Variable(fresh_arg.clone()).type_pat(Some(fresh_arg_type.clone()));
    // Register the range function in global namespace
    globals.insert("fresh".to_string(), fresh_func_id);
    // Describe the intrinsic's parameters and implementation
    let fresh_ident: Function = Function {
        params: vec![fresh_arg_pat],
        body: Box::new(TExpr {
            v: Expr::Variable(fresh_arg.clone()),
            t: None,
        }),
        env: HashMap::new(),
    };
    // Describe the intrinsic's type
    let imp_typ = Type::Function(Box::new(fresh_arg_type.clone()), Box::new(fresh_arg_type));
    // Register the intrinsic descriptor with the global binding
    global_types.insert(
        fresh_func_id,
        Type::Forall(fresh_arg, Box::new(imp_typ.clone())),
    );
    // Register this as a binding to contextualize evaluation
    bindings.insert(
        fresh_func_id,
        Expr::Function(fresh_ident).type_expr(Some(imp_typ)),
    );
}

/* Register the iter intrinsic in the compilation environment. */
fn register_iter_intrinsic(
    globals: &mut HashMap<String, VariableId>,
    global_types: &mut HashMap<VariableId, Type>,
    bindings: &mut HashMap<VariableId, TExpr>,
    gen: &mut VarGen,
) {
    let iter_id = gen.generate_id();
    let iter_arg = Variable::new(gen.generate_id());
    let iter_arg_pat = Pat::Variable(iter_arg).type_pat(Some(Type::Int));
    let iter_func_arg = Variable::new(gen.generate_id());
    let iter_func = Type::Function(
        Box::new(Type::Variable(iter_func_arg.clone())),
        Box::new(Type::Variable(iter_func_arg.clone())),
    );
    // Register the iter function in global namespace
    globals.insert("iter".to_string(), iter_id);
    // Describe the intrinsic's type, arity, and implementation
    let iter_intrinsic = Intrinsic::new(vec![iter_arg_pat], expand_iter_intrinsic);
    let imp_typ = Type::Function(
        Box::new(Type::Int),
        Box::new(Type::Function(
            Box::new(iter_func.clone()),
            Box::new(iter_func),
        )),
    );
    // Register the intrinsic descriptor with the global binding
    global_types.insert(
        iter_id,
        Type::Forall(iter_func_arg, Box::new(imp_typ.clone())),
    );
    // Register the intrinsic descriptor with the global binding
    bindings.insert(
        iter_id,
        Expr::Intrinsic(iter_intrinsic).type_expr(Some(imp_typ)),
    );
}

/* iter x returns the Church numeral corresponding to the given integer x. */
fn expand_iter_intrinsic(
    params: &Vec<TPat>,
    bindings: &HashMap<VariableId, TExpr>,
    _prover_defs: &mut HashSet<VariableId>,
    gen: &mut VarGen,
) -> Result<TExpr, Error> {
    match &params[..] {
        [TPat {
            v: Pat::Variable(param_var),
            ..
        }] => {
            let iter_arg = Variable::new(gen.generate_id());
            let iter_arg_typ = Type::Variable(iter_arg.clone());
            let iter_func_var = Variable::new(gen.generate_id());
            let iter_func = TExpr {
                v: Expr::Variable(iter_func_var.clone()),
                t: Some(Type::Function(
                    Box::new(iter_arg_typ.clone()),
                    Box::new(iter_arg_typ.clone()),
                )),
            };
            let mut body = TExpr {
                v: Expr::Variable(iter_arg.clone()),
                t: Some(iter_arg_typ.clone()),
            };
            let val = if let Expr::Constant(c) = &bindings[&param_var.id].v {
                c
            } else {
                return Err(Error::NonConstantIterArgumentError);
            };
            for _ in 0..val.to_i8().expect("specified iteration count is too large") {
                body = TExpr {
                    v: Expr::Application(Box::new(iter_func.clone()), Box::new(body.clone())),
                    t: body.t,
                };
            }
            Ok(TExpr {
                t: Some(Type::Function(
                    Box::new(iter_func.t.clone().unwrap()),
                    Box::new(iter_func.t.clone().unwrap()),
                )),
                v: Expr::Function(Function {
                    params: vec![
                        Pat::Variable(iter_func_var).type_pat(iter_func.t),
                        Pat::Variable(iter_arg).type_pat(Some(iter_arg_typ)),
                    ],
                    body: Box::new(body),
                    env: HashMap::new(),
                }),
            })
        }
        _ => Err(Error::UnexpectedIterArguments {
            params: params.to_vec(),
        }),
    }
}

/* Register the fold intrinsic in the compilation environment. */
fn register_fold_intrinsic(
    globals: &mut HashMap<String, VariableId>,
    global_types: &mut HashMap<VariableId, Type>,
    bindings: &mut HashMap<VariableId, TExpr>,
    gen: &mut VarGen,
) {
    let fold_id = gen.generate_id();
    let fold_elt = Variable::new(gen.generate_id());
    let fold_list = Type::List(Box::new(Type::Variable(fold_elt.clone())));
    let fold_arg = Variable::new(gen.generate_id());
    let fold_arg_pat = Pat::Variable(fold_arg).type_pat(Some(fold_list.clone()));
    let fold_acc = Variable::new(gen.generate_id());
    let fold_func_func = Type::Function(
        Box::new(Type::Variable(fold_acc.clone())),
        Box::new(Type::Variable(fold_acc.clone())),
    );
    let fold_func = Type::Function(
        Box::new(Type::Function(
            Box::new(Type::Variable(fold_elt.clone())),
            Box::new(fold_func_func.clone()),
        )),
        Box::new(fold_func_func),
    );
    // Register the iter function in global namespace
    globals.insert("fold".to_string(), fold_id);
    // Describe the intrinsic's type, arity, and implementation
    let fold_intrinsic = Intrinsic::new(vec![fold_arg_pat], expand_fold_intrinsic);
    let imp_typ = Type::Function(Box::new(fold_list), Box::new(fold_func));
    // Register the intrinsic descriptor with the global binding
    global_types.insert(
        fold_id,
        Type::Forall(
            fold_elt,
            Box::new(Type::Forall(fold_acc, Box::new(imp_typ.clone()))),
        ),
    );
    // Register the intrinsic descriptor with the global binding
    bindings.insert(
        fold_id,
        Expr::Intrinsic(fold_intrinsic).type_expr(Some(imp_typ)),
    );
}

/* fold [a0, a1, ..., aN] f b = f a0 (f a1 (... (f aN b) ...)). */
fn expand_fold_intrinsic(
    params: &Vec<TPat>,
    bindings: &HashMap<VariableId, TExpr>,
    _prover_defs: &mut HashSet<VariableId>,
    gen: &mut VarGen,
) -> Result<TExpr, Error> {
    match &params[..] {
        [TPat {
            v: Pat::Variable(param_var),
            ..
        }] => {
            let fold_arg = Variable::new(gen.generate_id());
            let fold_arg_typ = Type::Variable(fold_arg.clone());
            let fold_func_var = Variable::new(gen.generate_id());
            let fold_func_func = Type::Function(
                Box::new(fold_arg_typ.clone()),
                Box::new(fold_arg_typ.clone()),
            );
            let fold_elt = Variable::new(gen.generate_id());
            let fold_func = TExpr {
                v: Expr::Variable(fold_func_var.clone()),
                t: Some(Type::Function(
                    Box::new(Type::Variable(fold_elt)),
                    Box::new(fold_func_func.clone()),
                )),
            };
            let mut param_val = &bindings[&param_var.id];
            let mut param_list = Vec::new();
            let param_list = loop {
                if let Expr::Cons(hd, tl) = &param_val.v {
                    param_list.push(hd.clone());
                    param_val = tl;
                } else if let Expr::Nil = &param_val.v {
                    break param_list;
                } else {
                    return Err(Error::NonListArgumentsInFoldError);
                };
            };
            let mut body = TExpr {
                v: Expr::Variable(fold_arg.clone()),
                t: Some(fold_arg_typ.clone()),
            };
            for param_elt in param_list.into_iter().rev() {
                body = TExpr {
                    v: Expr::Application(
                        Box::new(TExpr {
                            v: Expr::Application(Box::new(fold_func.clone()), param_elt),
                            t: Some(fold_func_func.clone()),
                        }),
                        Box::new(body.clone()),
                    ),
                    t: body.t,
                };
            }
            Ok(TExpr {
                t: Some(Type::Function(
                    Box::new(fold_func.t.clone().unwrap()),
                    Box::new(fold_func_func),
                )),
                v: Expr::Function(Function {
                    params: vec![
                        Pat::Variable(fold_func_var).type_pat(fold_func.t),
                        Pat::Variable(fold_arg).type_pat(Some(fold_arg_typ)),
                    ],
                    body: Box::new(body),
                    env: HashMap::new(),
                }),
            })
        }
        _ => Err(Error::UnexpectedArgumentsInFold {
            params: params.clone(),
        }),
    }
}

/* Version of compile for repl. Does everything compile does to evaluate a module, but split between repl interactions. */
pub fn compile_repl(module: &mut Module, field_ops: &dyn FieldOps) -> Result<(), Error> {
    let mut vg = VarGen::new();
    let mut globals = HashMap::new();
    let mut bindings = HashMap::new();
    let mut prog_types = HashMap::new();
    let mut global_types = HashMap::new();
    register_fresh_intrinsic_repl(&mut globals, &mut global_types, &mut bindings, &mut vg);
    register_iter_intrinsic(&mut globals, &mut global_types, &mut bindings, &mut vg);
    register_fold_intrinsic(&mut globals, &mut global_types, &mut bindings, &mut vg);

    let mut locals = HashMap::new();
    let mut prover_defs = HashSet::new();
    if !module.defs.is_empty() || !module.exprs.is_empty() || !module.pubs.is_empty() {
        number_module_variables(module, &mut globals, &mut vg, &mut locals);
        infer_module_types(
            module,
            &globals,
            &mut global_types,
            &mut prog_types,
            &mut vg,
        );
        println!("** Inferring types...");
        print_types(module, &prog_types, &Config { quiet: false });
        // Global variables may have further internal structure, determine this
        // using derived type information
        expand_global_variables(
            module,
            &globals,
            &global_types,
            &mut prog_types,
            &bindings,
            &mut vg,
        );
        // Type information is no longer required since we do symbolic
        // execution from now on
        strip_module_types(module);
        // Start generating arithmetic constraints

        evaluate_module(
            module,
            &mut None,
            &mut bindings,
            &mut prover_defs,
            field_ops,
            &mut vg,
        );
    }

    loop {
        print!("In : ");
        std::io::stdout().flush().expect("Error flushing stdout");

        let mut input: String = String::new();
        std::io::stdin()
            .read_line(&mut input)
            .expect("Error reading from stdin");

        if input.trim() == "quit" || input.trim() == "exit" {
            break;
        }

        let mut module = Module {
            defs: vec![],
            exprs: vec![],
            pubs: vec![],
        };

        match VampirParser::parse(Rule::moduleItems, &input) {
            Ok(mut pairs) => {
                for pair in pairs.by_ref() {
                    match pair.as_rule() {
                        Rule::expr => {
                            let expr: TExpr = TExpr::parse(pair).expect("expected expression");
                            module.exprs.push(expr);
                        }
                        Rule::definition => {
                            let definition: Definition =
                                Definition::parse(pair).expect("expected definition");
                            module.defs.push(definition);
                        }
                        Rule::declaration => {
                            let pairs: pest::iterators::Pairs<Rule> = pair.into_inner();
                            for pair in pairs {
                                let var: Variable =
                                    Variable::parse(pair).expect("expected variable");
                                module.pubs.push(var);
                            }
                        }
                        Rule::EOI => continue,
                        _ => unreachable!(
                            "module item should either be expression, definition, or EOI"
                        ),
                    }
                }

                number_module_variables(&mut module, &mut globals, &mut vg, &mut locals);

                // Only look at types if new definitions are added.
                if !module.defs.is_empty() {
                    infer_module_types(
                        &mut module,
                        &globals,
                        &mut global_types,
                        &mut prog_types,
                        &mut vg,
                    );
                    println!("** Inferring types...");
                    print_types(&module, &prog_types, &Config { quiet: false });
                    // Global variables may have further internal structure, determine this
                    // using derived type information
                    expand_global_variables(
                        &mut module,
                        &globals,
                        &global_types,
                        &mut prog_types,
                        &bindings,
                        &mut vg,
                    );
                    // Type information is no longer required since we do symbolic
                    // execution from now on
                    strip_module_types(&mut module);
                }

                for def in &module.defs {
                    evaluate_def(
                        def,
                        &mut None,
                        &mut bindings,
                        &mut prover_defs,
                        field_ops,
                        &mut vg,
                    );
                }
                for expr in &module.exprs {
                    let res = evaluate(
                        expr,
                        &mut None,
                        &mut bindings,
                        &mut prover_defs,
                        field_ops,
                        &mut vg,
                    );

                    if let Err(e) = res {
                        println!("Evaluation Error: {e:?}")
                    } else {
                        println!("Out: {}", res.unwrap())
                    };
                }
            }
            Err(e) => eprintln!("Parse Error: {e:?}"),
        }
    }

    Ok(())
}
