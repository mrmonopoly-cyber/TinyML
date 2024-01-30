(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

// evaluator
//

let rec eval_expr (venv : value env) (e : expr) : value =
    match e with
    | Lit lit -> VLit lit

    | Var x when (List.exists (fun (x', _) -> x' = x) venv) -> let _, v = List.find (fun (x', _) -> x = x') venv in v
    | Var x -> unexpected_error "name %s doesn't belong to any binding inside in the environment" x

    | Lambda (x, _, e) -> Closure (venv, x, e)

    | App (e1, e2) -> 
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        match v1 with
        | Closure (venv', x, e) ->
            let venv' = (x, v2) :: venv'
            eval_expr venv' e
        | RecClosure (venv', f, x, e) -> 
            let venv' = (x, v2) :: (f, v1) :: venv'
            eval_expr venv' e
        | _ -> unexpected_error "non-closure on left hand of application"

    | IfThenElse (e1, e2, e3) ->
        let v1 = eval_expr venv e1
        match v1 with
        | VLit (LBool true) -> eval_expr venv e2
        | VLit (LBool false) ->           
            match e3 with
            | None -> VLit LUnit
            | Some e3 -> eval_expr venv e3
        | _ -> unexpected_error "non-boolean argument used as if-then-else construct guard: %s" (pretty_expr e1)

    | Tuple es -> VTuple (List.map (eval_expr venv) es)

    | Let (x, _, e1, e2) ->
        let v1 = eval_expr venv e1
        let venv' = (x, v1) :: venv
        eval_expr venv' e2

    | LetRec (f, _, e1, e2) ->
        let v1 = eval_expr venv e1
        match v1 with
        | Closure (venv', x, e) -> 
            let venv' = (f, RecClosure (venv', f, x, e)) :: venv
            eval_expr venv' e2
        | _ -> unexpected_error "non-closure as right hand of let-rec binding: %s" (pretty_expr e1)

    | UnOp ("-", e) ->
        let v = eval_expr venv e
        match v with
        | VLit (LInt n) -> VLit (LInt -n)
        | _ -> unexpected_error "non-numeric argument for unary operator -: %s" (pretty_expr e)

    | BinOp (e1, ("+" | "-" | "*" | "/" | "%" as op), e2) ->
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        let actual_op =
            fun n1 n2 -> 
                match op with
                | "+" -> n1 + n2
                | "-" -> n1 - n2
                | "*" -> n1 * n2
                | "/" -> n1 / n2
                | _ -> n1 % n2
        match v1, v2 with
        | VLit (LInt n1), VLit (LInt n2) -> VLit (LInt (actual_op n1 n2))
        | _ -> unexpected_error "non-numeric values for operator %s: %s and %s" op (pretty_expr e1) (pretty_expr e2)

    | UnOp ("not", e) ->
        let v = eval_expr venv e
        match v with
        | VLit (LBool b) -> VLit (LBool (not b))
        | _ -> unexpected_error "non-boolean argument for operator not: %s" (pretty_expr e)

    | BinOp (e1, ("or" | "and" as op), e2) ->
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        let actual_op =
            fun b1 b2 -> 
                match op with
                | "or" -> b1 || b2
                | _ -> b1 && b2
        match v1, v2 with
        | VLit (LBool b1), VLit (LBool b2) -> VLit (LBool (actual_op b1 b2))
        | _ -> unexpected_error "non-boolean argument for operator %s: %s and %s" op (pretty_expr e1) (pretty_expr e2)

    | BinOp (e1, "=", e2) ->
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        VLit (LBool (v1 = v2))

    | BinOp (e1, ("<" | ">" | "<=" | ">=" as op), e2) ->
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        let actual_op =
            fun x y -> 
                match op with
                | "<" -> x < y
                | ">" -> x > y
                | "<=" -> x <= y
                | _ -> x >= y
        match v1, v2 with
        | VLit (LInt n1), VLit (LInt n2) -> VLit (LBool (actual_op n1 n2))
        | (v1, v2) -> unexpected_error "non-boolean values for operator %s: %s %s" op (pretty_value v1) (pretty_value v2)

    | _ -> unexpected_error "eval_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
