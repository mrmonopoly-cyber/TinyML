(*
* TinyML
* Eval.fs: evaluator
*)

module TinyML.Eval

open Ast

exception NotFound

let lookup env x = 
    let _, v = List.find (fun (x', _) -> x = x') env
    v

type ty =
    | Float of float
    | Int of int

type op_fun =
    | Int_int_bool of (int->int->bool)
    | Int_int_int of (int->int->int)
    | Bool_bool_bool of (bool->bool->bool)
    | Bool_bool of (bool->bool)
    | Int_bool of (int->bool)



    
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
        
        let match_eq v1 v2 (opi,opf,opb,opc,ops)=
            match v1,v2 with
            | VLit(LInt(v1)), Some(VLit(LInt(v2))) -> VLit(LBool(opi v1 v2))
            | VLit(LFloat(v1)), Some(VLit(LFloat(v2))) -> VLit(LBool(opf v1 v2))
            | VLit(LBool(v1)), Some(VLit(LBool(v2))) -> VLit(LBool(opb v1 v2))
            | VLit(LChar(v1)), Some(VLit(LChar(v2))) -> VLit(LBool(opc v1 v2))
            | VLit(LString(v1)), Some(VLit(LString(v2))) -> VLit(LBool(ops v1 v2))
            | _ -> unexpected_error "invalid evaluation with ="


        let match_diseg v1 v2 (opi,opf)=
            match v1,v2 with
            | VLit(LInt(v1)), Some(VLit(LInt(v2))) -> VLit(LBool(opi v1 v2))
            | VLit(LFloat(v1)), Some(VLit(LFloat(v2))) -> VLit(LBool(opf v1 v2))
            | _ -> unexpected_error "invalid evaluation with ="


        let match_num_expr v1 v2 (opi,opf) =
            match v1,v2 with
            | VLit(LInt(v1)), Some(VLit(LInt(v2))) -> VLit(LInt(opi v1 v2))
            | VLit(LFloat(v1)), Some(VLit(LFloat(v2))) -> VLit(LFloat(opf v1 v2))
            | _ -> unexpected_error "invalid evaluation with ="


        let match_log_op v1 v2 opb =
            match v1,v2 with
            | VLit(LBool(v1)), Some(VLit(LBool(v2))) -> VLit(LBool(opb v1 v2))
            | _ -> unexpected_error "invalid evaluation with ="


        match op with
        | "="  -> match_eq v1 v2 ((=),(=),(=),(=),(=))
        | "<>" -> match_eq v1 v2 ((<>),(<>),(<>),(<>),(<>))
        | "+" -> match_num_expr v1 v2 ((+),(+))
        | "-" -> match_num_expr v1 v2 ((-),(-))
        | "/" -> match_num_expr v1 v2 ((/),(/))
        | "*" -> match_num_expr v1 v2 ((*),(*))
        | "%" -> match_num_expr v1 v2 ((%),(%))
        | "and" -> match_log_op v1 v2 (&&)
        | "or" -> match_log_op v1 v2 (||)
        | ">" -> match_diseg v1 v2 ((>),(>))
        | ">=" -> match_diseg v1 v2 ((>=),(>=))
        | "<" -> match_diseg v1 v2 ((<),(<))
        | "<=" -> match_diseg v1 v2 ((<=),(<=))
        | _ -> unexpected_error "impossible case"

    | UnOp(op,e1) ->

        let match_not v1 op_i =
            match v1 with
            | VLit(LBool(v1)) -> VLit(LBool(op_i v1))
            | _ ->  unexpected_error "impossible case"

        let match_negation v1  =
            match v1 with
            | VLit(LInt(v1)) -> VLit(LInt(- v1))
            | VLit(LFloat(v1)) -> VLit(LFloat(- v1))
            | _ -> unexpected_error "invalid evaluation with ="

        let v1 = eval_expr venv e1
        match op with
        | "not" -> match_not v1 not
        | "-" -> match_negation v1 
        | _ -> unexpected_error "impossible case"


   
