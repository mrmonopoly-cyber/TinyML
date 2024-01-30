(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

exception NotImplemented

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

// functions to apply substitutions to types, schemes or environments
//

let rec apply_subst_type (s: subst) (t: ty) : ty = raise NotImplemented

let apply_subst_scheme (s: subst) (Forall(tvs, t)) : scheme = raise NotImplemented

let rec apply_subst_env (subst: subst) (env: scheme env) : scheme env = raise NotImplemented

// Martelli-Montanari's unification algorithm
//

let rec compose_substs (s2: subst) (s1: subst) : subst = raise NotImplemented

let rec unify (t1: ty) (t2: ty) : subst = raise NotImplemented

// functions to retrieve free variables occuring in types, schemes or environments
//

let rec ftv_type (t: ty) : Set<tyvar> = raise NotImplemented

let rec ftv_environment (env: scheme env) : Set<tyvar> = raise NotImplemented

// function to generalize a type
//

let gen env t = raise NotImplemented

// function to instantiate a type
//

let inst (Forall(tvs, t)) = raise NotImplemented

// basic environment: add builtin operators at will
//

let gamma0 = []

// type checker
//

let rec typecheck_expr (tenv: ty env) (e: expr) : ty =
    match e with
    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

// type inference
//

let rec typeinfer_expr (env: scheme env) (e: expr) : ty * subst =
    match e with
    | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
