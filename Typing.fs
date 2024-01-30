(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list

// TODO implement this
let rec unify (t1 : ty) (t2 : ty) : subst = 
    match t1,t2 with
    | TyName ts1, TyName ts2 -> 
        if ts1 = ts2 
        then []
        else type_error "ambiguous type for expression: %O %O " ts1 ts2
    | TyName t, TyVar a | TyVar a, TyName t -> 
        [a, (TyName t)]
    | TyArrow(t1,t2), TyArrow(t3,t4) -> 
        (unify t1 t3) @ (unify t2 t4)
    
    | TyTuple(t1h::t1t) , TyTuple (t2h::t2t) -> 
        (unify t1h t2h) @ (unify (TyTuple t1t) (TyTuple t2t))
    
    | _ -> type_error "debug"

// TODO implement this
let rec apply_subst (t : ty) (s : subst) : ty = 
   
    match t,s with
    | TyName e,_ -> ty
    | Tyvar _,((tyv,tyt) :: tail) -> 
        if ty = tyv 
        then TyArrow (ty, tyt)
        else apply_subst ty tail
    | Tyvar _, [] -> ty
    | TyArrow(t1,t2),_ -> 
        let rect1 = apply_subst t1 s
        let rect2 = apply_subst t2 s
        TyArrow (rect1, rect2)

    | TyTuple(tylist) ->
        let newlist = List.map (fun x -> apply_subst x s) tylist
        TyTuple newlist




// TODO implement this
let compose_subst (s1 : subst) (s2 : subst) : subst = s1 @ s2

// TODO implement this
let rec freevars_ty t = 
    match t with 
    | TyArrow(ta,tb) -> 
        let fta = freevars_ty ta
        let ftb = freevars_ty tb
        Set.union fta ftb      
    | TyTuple(thead::ttail) -> 
        Set.union (freevars_ty thead) (freevars_ty (TyTuple(ttail))) 

    | TyName _ -> Set.empty 

    | TyVar _ -> Set.empty.Add(t)
    | _ -> type_error "debug"
    

// TODO implement this
let freevars_scheme (Forall (tvs, t)) =
    let full_ty_list = freevars_ty t
    let conv = Set.map (fun x -> TyVar(x)) tvs
    Set.difference conv full_ty_list

// TODO implement this
let rec freevars_scheme_env (env : scheme env) = 
    match env with
    | head :: tail -> 
        let _,sc = head
        Set.union  (freevars_scheme sc) (freevars_scheme_env tail)
    | _ -> Set.empty

// basic environment: add builtin operators at will
//

//let gamma0 = [
//    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
//    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
//    ("*", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
//    ("/", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
//    ("<", TyArrow (TyInt, TyArrow (TyInt, TyBool)))
//]

let gamma0 = []

// type inference
//

let rec apply_subst_env (env : scheme env) (sub : subst) : (scheme env) = 
    match env with
    | (var_x, Forall (vars, tyt)) :: tail ->
        let new_sch = Forall(vars,(apply_subst tyt sub))
        (var_x, new_sch) :: (apply_subst_env tail sub)
    | _ -> []

let if_else_e2 env e2 sub5 inf_fun  =
    match e2 with
    | Some e2 -> 
        let t2,sub6 =  inf_fun env e2
        let sub7 = compose_subst sub6 sub5
        t2,sub7
    | _ -> TyUnit,[]


let ty_if_else env eg e1 e2 inf_fun= 
    let tg,sub1 = inf_fun env eg
    if tg<>TyBool then type_error "wrong type guard if then else: %O" tg
        
    let sub2 = unify tg TyBool
    let sub3 = compose_subst sub2 sub1
        
    let env = apply_subst_env env sub3
        
    let t1,sub4 = inf_fun env e1
    let sub5 = compose_subst sub4 sub3
        
    let env = apply_subst_env env sub5
    
    let t2,sub6 = if_else_e2 env e2 sub5 inf_fun
    
    let sub7 = compose_subst sub6 sub5
    let sub8 = unify (apply_subst t1 sub7) (apply_subst t2 sub7)

    let tf = apply_subst t1 sub8 
        
    let sub9 = compose_subst sub8 sub7 

    TyArrow (TyArrow (tg, t1), t2), sub9

let lookup (env : scheme env) (var : TyVar) : scheme = 
    Forall (Set.empty, TyUnit)


let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, [] 
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, [] 
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, [] 
    | Lit LUnit -> TyUnit, []

    //| Var(s) ->

    | Lambda(s,Some(typ),e) ->
        let env' = (s,Forall(Set.empty,typ)) :: env
        let te2,sub = typeinfer_expr env' e
        (TyArrow(typ,te2)), sub
    
    | IfThenElse(eg,e1, e2) ->
        ty_if_else env eg e1 e2 typeinfer_expr

    | BinOp (e1, op, e2) ->
        typeinfer_expr env (App (App (Var op, e1), e2))

    // TODO complete this implementation

    | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

// type checker
//
// optionally, a simple type checker (without type inference) could be implemented
// you might start implementing this for simplicity and eventually write the type inference once you gain familiarity with the code

let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Let (x, None, e1, e2) ->
        let t1 = typecheck_expr env e1
        let env' = (x, t1) :: env
        typecheck_expr env' e2

    | Let (x, Some t, e1, e2) ->
        let t1 = typecheck_expr env e1
        if t <> t1 then type_error "type %O differs from type %O in let-binding" t1 t 
        let env' = (x, t1) :: env
        typecheck_expr env' e2

    | Lambda (x, Some t, e) ->
        let env' = (x, t) :: env
        let te = typecheck_expr env' e
        TyArrow (t, te)

    | Lambda (x, None, e) ->
        type_error "unannotated lambdas are not supported by the type checker"

    | App (e1, e2) ->
        let t2 = typecheck_expr env e2
        match typecheck_expr env e1 with
        | TyArrow (ta, tb) -> 
            if ta <> t2 then type_error "argument has type %O while function parameter has type %O in application" t2 ta
            tb
        | t1 -> type_error "left hand of application is not an arrow type: %O" t1

    | IfThenElse (e1, e2, Some e3) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "bool expected in if guard, but got %O" t1
        let t2 = typecheck_expr env e2
        let t3 = typecheck_expr env e3
        if t2 <> t3 then type_error "then and else branches have different types: %O and %O" t2 t3
        t2

    | BinOp (e1, ("+" | "-" | "*" | "/" as op), e2) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyInt then type_error "left hand of (%s) operator is not an int: %O" op t1
        let t2 = typecheck_expr env e2
        if t2 <> TyInt then type_error "right hand of (%s) operator is not an int: %O" op t2
        TyInt

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "operand of not-operator is not a bool: %O" t
        TyBool
        
    | BinOp (e1, "=", e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        if t1 <> t2 then type_error "left and right hands of equality operator are different: %O and %O" t1 t2
        TyBool

    | BinOp (e1, ("<" | ">" | "<=" | ">=" as op), e2) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyInt then type_error "left hand of (%s) operator is not an int: %O" op t1
        let t2 = typecheck_expr env e2
        if t2 <> TyInt then type_error "right hand of (%s) operator is not an int: %O" op t2
        TyBool

    | Tuple es -> TyTuple (List.map (typecheck_expr env) es)









    // TODO optionally complete this implementation

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
