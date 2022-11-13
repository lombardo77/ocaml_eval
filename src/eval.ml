open Ast

exception TypeError
exception UndefinedVar
exception DivByZeroError

(* Remove shadowed bindings *)
let prune_env (env : environment) : environment =
  let binds = List.sort_uniq compare (List.map (fun (id, _) -> id) env) in
  List.map (fun e -> (e, List.assoc e env)) binds

(* Env print function to stdout *)
let print_env_std (env : environment): unit =
  List.fold_left (fun _ (var, value) ->
      match value with
        | Int_Val i -> Printf.printf "- %s => %s\n" var (string_of_int i)
        | Bool_Val b -> Printf.printf "- %s => %s\n" var (string_of_bool b)
        | Closure _ -> ()) () (prune_env env)

(* Env print function to string *)
let print_env_str (env : environment): string =
  List.fold_left (fun acc (var, value) ->
      match value with
        | Int_Val i -> acc ^ (Printf.sprintf "- %s => %s\n" var (string_of_int i))
        | Bool_Val b -> acc ^ (Printf.sprintf "- %s => %s\n" var (string_of_bool b))
        | Closure _ -> acc
      ) "" (prune_env env)


(***********************)
(****** Your Code ******)
(***********************)



(******************************)
(********Helper Functions******)
(******************************)

(* evaluate an arithmetic expression in an environment *)
let vtoi (iv : value) : int = 
    match iv with 
        | Int_Val(n) -> n
        | _ -> raise TypeError

let vtob (iv : value) : bool = 
    match iv with 
        | Bool_Val(s) -> s
        | _ -> raise TypeError


let vtoe (v : value) = match v with
    | Int_Val a -> Number a
    | Bool_Val true -> True
    | Bool_Val false -> False
    | Closure(en,f,ex) -> Fun(f, ex)
    



(*
* tuple helper functions
* t' gets first item
* t'' gets second item
 *)
let t' = (fun (a,b) -> a) 
let t'' = (fun (a,b) -> b) 

(*returns a number from environtment*)
let rec getn (env : environment) (a : string) : value=
    match env with 
        | [] -> Int_Val 0
        | h::t -> if t' h = a then t'' h else getn t a

(*returns a boolean from environment*)
let rec getbool (env: environment) (a : string) : value = 
    match env with 
        | [] -> Bool_Val false
        | h::t -> if t' h = a then t'' h else getbool t a

        
        
(*returns a closure from environment*)
let rec getcls (env: environment) (a : string) = 
    match env with
        | [] -> raise TypeError 
        | h::t -> if t' h = a then t'' h else getcls t a


(*returns the variable's value*)
let rec get_var (env : environment) (x : string) = 
    match env with
    | [] -> raise UndefinedVar
    | h::t -> if t' h = x then t'' h else get_var t x

(*returns true if value is an int_val*)
let is_intv (ex : value) = 
    match ex with
    | Int_Val(a) -> true
    | _ -> false

    
(*returns true if value is an bool_val*)
let is_boolv (ex : value) = 
    match ex with
    | Bool_Val(a) -> true
    | _ -> false


(*returns true if value is an cls_val*)
let is_clsv (ex : value) = 
    match ex with
    | Closure(_,_,_) -> true
    | _ -> false


 


(*converts expression to a value*)
let exptobool (e: exp) : bool = 
    match e with
    | True -> true
    | False -> false
    | _ -> raise TypeError

 (*returns true if its an integer, false if not*)
let isiv (e: exp) : bool = 
    match e with
    | Number(n) -> true
    | Var(x) -> true
    | True -> false
    | False -> false
    | Plus(a, b) -> true
    | Times(a, b) -> true
    | Minus(a, b) -> true 
    | Mod(a, b) -> true 
    | Div(a, b) -> true 
    | Eq(a, b) -> false
    | Leq(a, b) -> false 
    | Lt(a, b) -> false 
    | Not(a) -> false 
    | Or(a,b) -> false 
    | And(a,b) -> false 
    | Fun(fp, ex) -> false
    | App(_, arg) -> false

let ctof cl = 
    match cl with
    | Closure(a,b,c) -> Fun(b, c)
    | _ -> raise TypeError

let get_env cl = 
    match cl with
    | Closure(a,b,c) -> a
    | _ -> raise TypeError


exception Env

(******************************)
(**********eval_expr***********)
(******************************)

let rec eval_expr (e: exp) (env : environment) : value =
    let pred a b = isiv a && isiv b in
    let common0 v = vtoi(eval_expr v env) in
    let common1 v = vtob(eval_expr v env) in
    let cond0 v a b = if pred a b then v else raise TypeError in
    let cond1 v a b= if not (pred a b) then v else raise TypeError in
    let cond2 v a = if not (isiv a) then v else raise TypeError in
    match e with
    | Number(n) -> Int_Val(n)
    | Var(x) -> 
            if is_intv (get_var env x) then getn env x 
            else if is_boolv (get_var env x) then getbool env x
            else getcls env x
    | True -> Bool_Val true
    | False -> Bool_Val false
    | Plus(a, b) -> cond0 (Int_Val(common0 a + common0 b)) a b
    | Times(a, b) -> cond0 (Int_Val(common0 a * common0 b)) a b
    | Minus(a, b) -> cond0 (Int_Val(common0 a - common0 b)) a b
    | Mod(a, b) -> cond0 (Int_Val(common0 a mod common0 b)) a b
    | Div(a, b) -> 
            if common0 b = 0 then raise DivByZeroError 
            else cond0 (Int_Val(common0 a / common0 b)) a b
    | Eq(a, b) -> cond0 (Bool_Val(common0 a = common0 b)) a b 
    | Leq(a, b) -> cond0 (Bool_Val(common0 a <= common0 b)) a b
    | Lt(a, b) -> cond0 (Bool_Val(common0 a < common0 b)) a b
    | Not(a) -> cond2 (Bool_Val (not (common1 a))) a
    | Or(a,b) ->cond1 (Bool_Val ((common1 a || common1 b))) a b
    | And(a,b) -> cond1 (Bool_Val ((common1 a && common1 b))) a b
    | Fun(fp, ex) -> Closure(env, fp, ex)
    | App(e0, e1) -> 
            (let arg = (eval_expr e1 env) in
            let fev ex fp = eval_expr ex ((fp, eval_expr (vtoe arg) env)::env) in
            let cl = eval_expr e0 env in
                (match e0 with
                | Fun(fp, ex) -> fev ex fp
                | _ -> eval_expr (App((ctof cl), vtoe arg)) (get_env cl)))
                

(* evaluate a command in an environment *)

(*function that takes in a dtype and returns a value type*)
let dttovt (dt: dtype) (env : environment): value = 
    match dt with
    |Int_Type -> Int_Val 0
    |Bool_Type -> Bool_Val false
    |Lambda_Type -> Closure(env, "x", Var "x")

(*checks to see if var is declared*)
let rec isd env st v= 
    match env with
    | [] -> false
    | (a,b)::t -> if st = a then 
        (match v, b with
        | Int_Val _, Int_Val _ -> true
        | Bool_Val _, Bool_Val _ -> true
        | Closure(_,_,_), Closure(_,_,_) -> true
        | _ -> raise TypeError
    ) 
    else isd t st v

    
    
(******************************)
(*********eval_command*********)
(******************************)


let rec eval_command (c : com) (env : environment) : environment =
    match c with
    | Declare(dt, st) -> (st, dttovt dt env)::env
    | Assg(st, e) -> 
            (let a' = eval_expr e env in
            if (isd env st a') then (st, a')::env else raise UndefinedVar
            )
    | While(g, c0) -> if vtob (eval_expr g env) then eval_command (While(g, c0)) (eval_command c0 env) else env
    | Cond(g, e0, e1) -> if vtob (eval_expr g env) then eval_command e0 env else eval_command e1 env
    | Comp(c0, c1) -> eval_command c1 (eval_command c0 env)
    | Skip -> env
    | For(g, c0) -> (
        let p = vtoi (eval_expr g env) in 
        if not(p = 0) then eval_command 
            (While(Lt(Var "n", Number p), Comp(Assg("n", Plus(Var "n", Number(1))), c0))) (("n", Int_Val 0)::env )
        else env)




