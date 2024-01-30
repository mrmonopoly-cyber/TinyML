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

type op_fun =
    | Int_int_bool of (int->int->bool)
    | Int_int_int of (int->int->int)
    | Bool_bool_bool of (bool->bool->bool)
    | Bool_bool of (bool->bool)
    | Int_bool of (int->bool)

let eval_op v1 v2 op_f =
    match v1,v2,op_f with
    | VLit(LInt(v1)), Some(VLit(LInt(v2))), (Int_int_bool op) -> VLit(LBool(op v1 v2))
    | VLit(LInt(v1)), Some(VLit(LInt(v2))), (Int_int_int op) -> VLit(LInt(op v1 v2))
    | VLit(LBool(v1)), Some(VLit(LBool(v2))), (Bool_bool_bool op) -> VLit(LBool(op v1 v2))
    | VLit(LBool(v1)), None , (Bool_bool op) -> VLit(LBool(op v1))
    | VLit(LInt(v1)), None ,(Int_bool op) -> VLit(LBool(op v1))
    | _,_,_ ->  unexpected_error "impossible case"

    
let eval_if_else (vg:value) v1 v2 =
    match vg with 
    | VLit(LBool(g)) -> 
        match g with
        | true -> v1
        | false -> v2
    | _ ->  unexpected_error "impossible case"

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

    | IfThenElse (eg,e1,None) -> 
        let vg = eval_expr venv eg
        let v1 = eval_expr venv e1
        eval_if_else vg v1 (VLit(LUnit))

    | IfThenElse (eg,e1,Some(e2)) -> 
        let vg = eval_expr venv eg
        let v1 = eval_expr venv e1
        let v2 = eval_expr venv e2
        eval_if_else vg v1 v2

    | Tuple(el) -> VTuple(List.map (eval_expr venv) el)

    | BinOp (e1,op,e2) ->
        let v1 = eval_expr venv e1
        let v2 = Some(eval_expr venv e2)
        match op with
        | "+" -> eval_op v1 v2 (Int_int_int (+))
        | "-" -> eval_op v1 v2 (Int_int_int (-))
        | "*" -> eval_op v1 v2 (Int_int_int (*))
        | "/" -> eval_op v1 v2 (Int_int_int (/))
        | "%" -> eval_op v1 v2 (Int_int_int (%))
        | "=" -> eval_op v1 v2 (Int_int_bool (=))
        | ">=" -> eval_op v1 v2  (Int_int_bool (>=))
        | "<=" -> eval_op v1 v2 (Int_int_bool (<=))
        | "and" -> eval_op v1 v2 (Bool_bool_bool (&&))
        | "or" -> eval_op v1 v2 (Bool_bool_bool (||))
        | _ -> unexpected_error "impossible case"

    | UnOp(op,e1) ->
        let v1 = eval_expr venv e1
        match op with
        | "not" -> eval_op v1 None (Bool_bool(not))
        | "-" -> eval_op (VLit(LInt(0))) (Some(v1)) (Int_int_int(-))
        | _ -> unexpected_error "impossible case"


   