(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

exception NotFound

let lookup env x = 
    let _, v = List.find (fun (x', v) -> x = x') env
    v

let eval_if_else eg e1 v2 =
    let vg = eval_expr venv eg
    let v1 = eval_expr venv e1
    match vg with 
    | True -> v1
    | False -> v2

type op_fun =
    | int_int_bool of (int->int->bool)
    | int_int_int of (int->int->int)
    | bool_bool_bool of (bool->bool->bool)
    | bool_bool of (bool->bool)
    | int_bool of (int->bool)


let eval_op v1 v2 op_f =
    match op_f with
    | (int_int_bool op) -> VLit(LBool(op v1 v2))
    | (int_int_int op) -> VLit(LInt(op v1 v2))
    | (bool_bool_bool op) -> VLit(LBool(op v1 v2))
    | (bool_bool op) -> VLit(LBool(op v1))
    | (int_bool op) -> VLit(LInt(op v1))

// evaluator
//

let rec eval_expr (venv : value env) (e : expr) : value =
    match e with
    | Lit lit -> VLit lit

    | Lambda (x, _, e) -> Closure (venv, x, e)

    | App (e1, e2) -> 
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        match v1 with
        | Closure (venv', x, e) ->
            let venv' = (x, v2) :: venv'
            eval_expr venv' e

        | _ -> unexpected_error "non-closure on left hand of application"

    | Var x -> lookup venv x
    
    | LetIn (b,e) ->
        let _,s,_,e1 = b
        let v1 = eval_expr venv e1
        let venv' = (s, v1) :: venv
        eval_expr venv' e

    | IfThenElse (eg,e1,None) -> eval_if_else eg e1 (VLit(LUnit))

    | IfThenElse (eg,e1,Some(e2)) -> eval_if_else eg e1 (eval_expr venv e2)

    | Tuple(el) -> List.map (eval_expr venv) el

    | BinOp (e1,op,e2) ->
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        let cur_eval_op = eval_op v1 v2
        match op with
        | "+" -> cur_eval_op (int_int_int (+))
        | "-" -> cur_eval_op (int_int_int (-))
        | "*" -> cur_eval_op (int_int_int (*))
        | "/" -> cur_eval_op (int_int_int (/))
        | "%" -> cur_eval_op (int_int_int (%))
        | "=" -> cur_eval_op (int_int_bool (=))
        | ">=" -> cur_eval_op (int_int_bool (>=))
        | "<=" -> cur_eval_op (int_int_bool (<=))
        | "and" -> cur_eval_op (int_int_bool (&&))
        | "or" -> cur_eval_op (int_int_bool (||))

    | UnOp(op,e1) ->
        let v1 = eval_expr venv e1
        let cur_eval_op = eval_op v1 v2
        match op with
        | "!" -> cur_eval_op (bool_bool(!))
        | "-" -> cur_eval_op (int_int(-))
