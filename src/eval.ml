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

(* evaluate an arithmetic expression in an environment *)
let vtoi (iv : value) : int = 
    match iv with 
        | Int_Val(n) -> n
        | _ -> 0

let vtob (iv : value) : bool = 
    match iv with 
        | Bool_Val(s) -> s
(*
* tuple helper functions
* t' gets first item
* t'' gets second item
 *)
let t' = (fun (a,b) -> a) 
let t'' = (fun (a,b) -> b) 

(*returns a number from environtment*)
let rec getn (env : environment) (a : string) : int =
    match env with 
        | [] -> 0
        | h::t -> if t' h = a then vtoi(t'' h) else getn t a

(*returns a boolean from environment*)
let rec getbool (env: environment) (a : string) : bool = 
    match env with 
        | [] -> false
        | h::t -> if t' h = a then vtob(t'' h) else getbool t a

(*returns the variable's value*)
let rec get_var (env : environment) (x : string) = 
    match env with
    | h::t -> if t' h = x then t'' h else get_var t x

(*returns true if value is an int_val*)
let is_intv (ex : value) = 
    match ex with
    | Int_Val(a) -> true
    | _ -> false


(*converts expression to a value*)
let exptov (e: exp) : value = 
    match e with
    | Number(i) -> Int_Val(i)
    | True -> Bool_Val(true)
    | False -> Bool_Val(false)


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
    | App(Fun(fp, ex), arg) -> false


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
            if is_intv (get_var env x) then Int_Val(getn env x) 
            else Bool_Val(getbool env x)
    | True -> Bool_Val true
    | False -> Bool_Val false
    | Plus(a, b) -> cond0 (Int_Val(common0 a + common0 b)) a b
    | Times(a, b) -> cond0 (Int_Val(common0 a * common0 b)) a b
    | Minus(a, b) -> cond0 (Int_Val(common0 a - common0 b)) a b
    | Mod(a, b) -> cond0 (Int_Val(common0 a mod common0 b)) a b
    | Div(a, b) -> cond0 (Int_Val(common0 a / common0 b)) a b
    | Eq(a, b) -> cond0 (Bool_Val(common0 a = common0 b)) a b 
    | Leq(a, b) -> cond0 (Bool_Val(common0 a <= common0 b)) a b
    | Lt(a, b) -> cond0 (Bool_Val(common0 a < common0 b)) a b
    | Not(a) -> cond2 (Bool_Val (not (common1 a))) a
    | Or(a,b) ->cond1 (Bool_Val ((common1 a || common1 b))) a b
    | And(a,b) -> cond1 (Bool_Val ((common1 a && common1 b))) a b
    | Fun(fp, ex) -> Closure(env, fp, ex)
    | App(Fun(fp, ex), arg) -> eval_expr ex ((fp, eval_expr arg env)::env)
            
            (*1) add (fp: arg) to env, then evaluate ex*)


(*test functions*)

let rec zip l1 l2 = 
    match l1, l2 with
    |[], [] -> []
    |h::t, j::y -> (h,Int_Val(j))::zip t y

let e = zip ["x";"y";"b"] [-(100);23;10];;
let e = ("z", Bool_Val true)::e
let e0 = Not
    (Lt(Plus(Times(Var("a"), Number(10)), Var("x")), Number(2)));;

let e1 = App(Fun("a", e0), Number 9)

let e2 = Div(Number 9, Number 0


)



(* evaluate a command in an environment *)

(*function that takes in a dtype and returns a value type*)
let dttovt (dt: dtype) (env : environment): value = 
    match dt with
    |Int_Type -> Int_Val 0
    |Bool_Type -> Bool_Val false
    |Lambda_Type -> Closure(env, "x", Var "x")


let rec eval_command (c : com) (env : environment) : environment =
    match c with
    | Declare(dt, st) -> (st, dttovt dt env)::env
    | Assg(st, e) -> prune_env ((st, eval_expr e env)::env)
    | While(g, c0) -> if vtob (eval_expr g env) then eval_command (While(g, c0)) (eval_command c0 env) else env
    | Cond(g, e0, e1) -> if vtob (eval_expr g env) then eval_command e0 env else eval_command e1 env
    | Comp(c0, c1) -> eval_command c1 (eval_command c0 env)

















