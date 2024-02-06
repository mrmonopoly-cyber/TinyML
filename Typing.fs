(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list
        
// TODO implement this
let rec apply_subst_ty (t : ty) (s : subst) : ty = 

    let rec exist (b : tyvar)  (li : subst) =
        match li with
        | ((a,typ)::tail) -> 
            if  a = b
            then typ 
            else exist b tail
        | [] -> TyVar b 

    let cur_apply x = apply_subst_ty x s
    match t with
    | TyName _ -> t
    | TyVar a -> exist a s
    | TyArrow(t1,t2) -> 
        TyArrow((cur_apply t1),(cur_apply t2))
    | TyTuple (tyl) ->
        let res_l = List.map (cur_apply) tyl
        TyTuple res_l

let apply_subst_scheme (Forall(ty_s,typ): scheme ) (s : subst) : scheme =
    
    let predicate ((tv,_): tyvar * ty) : bool = not (Set.exists (fun x -> x = tv) ty_s)
    let res_ty  : subst = List.filter (predicate) s
    let res_sub = apply_subst_ty typ res_ty

    Forall(ty_s,res_sub)
    
let rec apply_subst_env (env : scheme env) (s : subst) : scheme env = 
    match env with
    | (str,sch)::tail ->
        (str,(apply_subst_scheme sch s))::(apply_subst_env tail s)
    | [] -> []
    
// TODO implement this
let rec compose_subst (s1 : subst) (s2 : subst) : subst = 
    let rec apply_sub  (si:subst) (so:subst) : subst =
        match si with
        | [] -> s2
        | ((a : tyvar),(tp : ty)) :: (tail :subst) ->
            (a,apply_subst_ty tp so) :: (apply_sub tail so)
    
    let first = apply_sub s1 s2
    apply_sub first s1

// TODO implement this
let rec unify (t1 : ty) (t2 : ty) : subst = 
    match t1,t2 with
    | TyName c1, TyName c2 -> 
        if c1 = c2 
        then []
        else type_error "invalid case unification function with type %O %O" t1 t2
    | TyVar a, t | t , TyVar a ->
        [a,t]
    | TyArrow(t1,t2), TyArrow(t3,t4) ->
        compose_subst (unify t1 t3) (unify t2 t4)
    | TyTuple (head1::tail1), TyTuple(head2::tail2) ->
        let res_h = unify head1 head2
        let res_tail = unify (TyTuple tail1) (TyTuple tail2)
        compose_subst res_h res_tail
    | _ -> type_error "invalid case unification function with type %O %O" t1 t2

// TODO implement this
let rec freevars_ty (t:ty) : tyvar Set = 
    match t with 
    | TyName _ -> Set.empty
    | TyVar t -> Set.empty.Add t
    | TyArrow (t1,t2) -> Set.union (freevars_ty t1) (freevars_ty t2)
    | TyTuple (list) -> 
        match list with
        | head :: tail ->
            Set.union (freevars_ty head) (freevars_ty (TyTuple tail))
        | [] -> Set.empty


// TODO implement this
let freevars_scheme (Forall (tvs, t)) : tyvar Set = 
    let ftv_ty = freevars_ty t
    Set.difference ftv_ty tvs

// TODO implement this
let rec freevars_scheme_env (env : scheme env) : tyvar Set= 
    match env with
    | (_,sch):: tail ->
        Set.union (freevars_scheme sch) (freevars_scheme_env tail)
    | [] -> Set.empty

let gen (env : scheme env) (t : ty) : scheme = 
    let ftv_ty = freevars_ty t
    let ftv_env = freevars_scheme_env env
    let pol_var = Set.difference ftv_ty ftv_env
    Forall(pol_var,t)

let rec lookup_scheme_env (env : scheme env) (x : string) : scheme =
    match env with
    | (str,sch) :: tail ->
        if str = x 
        then sch
        else lookup_scheme_env tail x
    | [] -> type_error "variable %O not declared" x


let mutable new_var :tyvar= 0

let c_new_var (): tyvar=
    new_var <- new_var + 1
    new_var


let inst (Forall (tvs,t): scheme) : ty =  
    let rec re (tyi:ty) (ty_l:((tyvar * tyvar) Set)) : ty = 
        match tyi with
        | TyName _ -> tyi
        | TyVar a -> 
            let sub = Set.filter (fun (x,_) -> x=a) ty_l
            if sub.IsEmpty 
            then 
                tyi
            else
                let res = Set.minElement sub
                let _,t = res
                TyVar t
        | TyArrow (t1,t2) ->
            TyArrow ((re t1 ty_l),(re t2 ty_l))
        | TyTuple (tylist) ->
            let fr_list = List.map (fun x -> re x ty_l) tylist
            TyTuple fr_list

    let tvs_new = Set.map (fun x -> (x,x + c_new_var ())) tvs
    
    re t tvs_new

// basic environment: add builtin operators at will
//

let gamma0 = []
//    ("+", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
//    ("-", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
//    ("*", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
//    ("/", TyArrow (TyInt, TyArrow (TyInt, TyInt)))
//    ("<", TyArrow (TyInt, TyArrow (TyInt, TyBool)))


// type inference
//


let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, [] 
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, [] 
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, [] 
    | Lit LUnit -> TyUnit, []

    | Var varty ->
        let rec exist (l : scheme env) (var : string) : bool =
                match l with
                | (vart,_)::tail ->
                    if vart = var 
                    then true
                    else exist tail var
                | [] -> false

        if not ( exist env varty) then type_error "variable %O not found" varty

        let sch = lookup_scheme_env env varty
        let sch_ty = inst sch 
        sch_ty,[]

    | Lambda(str,t,e) ->
        let a = TyVar(c_new_var ())
        let l_scheme = Forall(Set.empty,a)
        let env = (str,l_scheme) :: env
        let t2,s1 = typeinfer_expr env e
        let t1 = apply_subst_ty a s1
        match t with
        | Some ti ->
            TyArrow (t1,t2),(unify t1 ti)
        | None -> TyArrow(t1,t2),s1

    | App(e1,e2) ->
        let t1,s1 = typeinfer_expr env e1
        let env = apply_subst_env env s1
        let t2,s2 = typeinfer_expr env e2
        let fresh_var = TyVar (c_new_var ())
        let s3 = unify t1 (TyArrow(t2,fresh_var))
        let sf = compose_subst s3 s2
        let tf = apply_subst_ty fresh_var s3
        tf,sf

    | IfThenElse(e1,e2,e3) ->
        let else_branch e env s5 =
            match e with
            | Some e3 ->
                let t3,s6 = typeinfer_expr env e3
                let s7 = compose_subst s6 s5
                t3,s7
            | None ->
                TyUnit,s5

        let t1,s1 = typeinfer_expr env e1
        let s2 = unify t1 TyBool
        let s3 = compose_subst s2 s1
        let env = apply_subst_env env s3
        let t2,s4 = typeinfer_expr env e2
        let s5 = compose_subst s4 s3
        let env = apply_subst_env env s5
        let t3,s7 = else_branch e3 env s5
        let s8 = unify (apply_subst_ty t2 s7) (apply_subst_ty t3 s7)
        let s_res = compose_subst s8 s7
        let ty_res = apply_subst_ty t2 s_res
        ty_res,s_res
    
    | Tuple(e_list) ->
        let rec tu_lis (e_list : expr list) (s:subst) : (ty list) * subst =
            match e_list with
            | (head::tail) ->
                let env = apply_subst_env env s
                let ti,si = typeinfer_expr env head
                let tlj,sj = tu_lis tail (compose_subst si s)
                (tlj@[ti]),(compose_subst sj si)
            | [] -> [],s

        let ts,s = tu_lis e_list []
        let tr = apply_subst_ty (TyTuple ts) s
        tr,s

    //| Let(n_var,t,e_let,e_in) ->
    | LetIn((false,n_var,t,e_let),e_in) ->
        let t1,s1 = typeinfer_expr env e_let
        match t with
        | Some tf -> if tf<>t1 then type_error "invalid type, expected %O tf, given %O" tf t1
        | None -> ()
        let env = apply_subst_env env s1
        let scheme1 = gen env t1
        let env = (n_var,scheme1):: env
        let t2,s2 = typeinfer_expr env e_in 
        let s3 = (compose_subst s2 s1)
        t2,s3
    
    | LetIn((true,n_var,t,e_let),e_in) ->
        let main = 
            let fresh = TyVar (c_new_var ())
            let new_con = n_var,(Forall(Set.empty,fresh))
            let env = new_con :: env
            let t1,s1 = typeinfer_expr env e_let
            match t with
            | Some tf -> if tf<>t1 then type_error "invalid type, expected %O tf, given %O" tf t1
            | None -> ()
            let env = apply_subst_env env s1
            let sch1 = gen env t1
            let context1 = n_var,sch1
            let env = context1 :: env
            let t2,s2 = typeinfer_expr env e_in
            let s3 = unify fresh (apply_subst_ty t1 s1)
            let s4 = compose_subst s3 (compose_subst s2 s1)
            t2,s4

        match e_let with
        | Lambda(_,_,_) -> main
        | _ -> type_error "expected Lambda expresion with let rec"


    | BinOp (e1, op, e2) ->
        
        let st_fun (op:string) (supp_types : ty list) (ty_res:ty option) : ty*subst=
            
            let t1,s1 = typeinfer_expr env e1
            let env = apply_subst_env env s1
            let t2,s2 = typeinfer_expr env e2
            let s3 = compose_subst s2 s1 
            let s4 = unify t1 t2
            let s5 = compose_subst s4 s3
            let t1 = apply_subst_ty t1 s5
            let t2 = apply_subst_ty t2 s5
            if t1<>t2 then type_error "types in %s does not coincide , given %O %O " op t1 t2
            if not(List.exists (fun x -> x = t1) supp_types)
            then type_error "invalid types for operator %s, given %O %O, supported %O" op t1 t2 supp_types
            match ty_res with
            | None -> t1,s5
            | Some t -> t,s5
            
                    
        match op with
        |( "+" | "-" | "*" | "/" | "%") as op -> st_fun op [TyInt;TyFloat] None
        |( "and" | "or") as op -> st_fun op [TyBool] (Some TyBool)
        |(">=" | "<=" | "<" | ">") as op-> st_fun op [TyInt;TyFloat] None
        |("=" | "<>") as op -> st_fun op [TyFloat;TyInt;TyBool;TyChar;TyString] (Some TyBool)
        | _ -> unexpected_error "operator not supported"

    | UnOp(op,e) ->
        let t1,s1 = typeinfer_expr env e
        match op with
        | "not" ->
            let s2 = unify t1 TyBool
            TyArrow(t1,TyBool),compose_subst s2 s1
        | "-" ->
            let s2 = unify t1 TyInt
            TyArrow(t1,TyInt),compose_subst s2 s1
        | _ -> type_error "invalid unary operator %O" op

    // | _ -> unexpected_error "typeinfer_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e

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
