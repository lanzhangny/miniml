(* 
                         CS 51 Final Project
                         MiniML -- Evaluation
*)

(* This module implements a small untyped ML-like language under
   various operational semantics.
 *)
    
open Expr ;;
  
(* Exception for evaluator runtime, generated by a runtime error *)
exception EvalError of string ;;
(* Exception for evaluator runtime, generated by an explicit "raise" 
   construct 
 *)
exception EvalException ;;

(*......................................................................
  Environments and values 
 *)

module type Env_type = sig
    type env
    type value =
      | Val of expr
      | Closure of (expr * env)
    val create : unit -> env
    val close : expr -> env -> value
    val lookup : env -> varid -> value
    val extend : env -> varid -> value ref -> env
    val env_to_string : env -> string
    val value_to_string : ?printenvp:bool -> value -> string
  end

module Env : Env_type =
  struct
    type env = (varid * value ref) list
     and value =
       | Val of expr
       | Closure of (expr * env)

    (* Creates an empty environment *)
    let create () : env = [] ;;

    (* Creates a closure from an expression and the environment it's
       defined in *)
    let close (exp : expr) (env : env) : value =
      Closure (exp, env) ;;

    (* Looks up the value of a variable in the environment *)
    let lookup (env : env) (varname : varid) : value =
      try !(List.assoc varname env) 
      with Not_found -> raise (EvalError "Unbound Variable")

    (* Returns a new environment just like env except that it maps the
       variable varid to loc *)
    let extend (env : env) (varname : varid) (loc : value ref) : env =
      (varname, loc) :: (List.remove_assoc varname env)

    (* Returns a printable string representation of a value; the flag
       printenvp determines whether to include the environment in the
       string representation when called on a closure *)
    let rec value_to_string ?(printenvp : bool = true) (v : value) : string =
      match v with
      | Val e -> exp_to_concrete_string e
      | Closure (e, env) -> if printenvp then "[Expr: "  
                              ^ (exp_to_concrete_string e) ^ ", " 
                              ^ "Env: " ^ (env_to_string env) ^ "]"
                            else exp_to_concrete_string e

    (* Returns a printable string representation of an environment *)
    and env_to_string (env : env) : string =
      "{" ^
      let rec env_string_helper (env : env) : string =
      (match env with
      | [] -> ""
      | hd :: tl -> let (var, valref) = hd in 
                    "(" ^ var ^ ", " ^ (value_to_string !valref) ^ ")"
                      ^ (if (List.length tl) >= 1 then "; " 
                         else "") ^ env_string_helper tl) in
      env_string_helper env ^ "}" ;;
  end
;;

(*......................................................................
  Evaluation functions

  Each of the evaluation functions below, evaluates an expression exp
  in an enviornment env returning a result of type value. We've
  provided an initial implementation for a trivial evaluator, which
  just converts the expression unchanged to a value and returns it,
  along with "stub code" for three more evaluators: a substitution
  model evaluator and dynamic and lexical environment model versions.

  Each evaluator is of type expr -> Env.env -> Env.value for
  consistency, though some of the evaluators don't need an
  environment, and some will only return values that are "bare
  values" (that is, not closures). 

  DO NOT CHANGE THE TYPE SIGNATURES OF THESE FUNCTIONS. Compilation
  against our unit tests relies on their having these signatures. If
  you want to implement an extension whose evaluator has a different
  signature, implement it as eval_e below.  *)

(* The TRIVIAL EVALUATOR, which leaves the expression to be evaluated
   essentially unchanged, just converted to a value for consistency
   with the signature of the evaluators. *)
   
let eval_t (exp : expr) (_env : Env.env) : Env.value =
  (* coerce the expr, unchanged, into a value *)
  Env.Val exp ;;

(* Opening Env module *)
open Env ;;

(* Helper function for unary operation evaluation *)
let unopeval (op : unop) (e : expr) : expr =
  match op, e with
  | Negate, Num x -> Num (~-x)
  | Negate_f, Float x -> Float (~-. x)
  | Negate, _ | Negate_f, _ -> raise (EvalError "Invalid Negation") ;;

(* Helper function for binomial operation evaluation *)
let binopeval (op : binop) (e1 : expr) (e2 : expr) : expr =
  match op, e1, e2 with
  | Plus, Num x, Num y -> Num (x + y)
  | Plus_f, Float x, Float y -> Float (x +. y)
  | Plus, _, _ | Plus_f, _, _ -> raise (EvalError "Invalid Addition")
  | Minus, Num x, Num y -> Num (x - y)
  | Minus_f, Float x, Float y -> Float (x -. y)
  | Minus, _, _ | Minus_f, _, _ -> raise (EvalError "Invalid Subtraction")
  | Times, Num x, Num y -> Num (x * y)
  | Times_f, Float x, Float y -> Float (x *. y)
  | Times, _, _ | Times_f, _, _ -> raise (EvalError "Invalid Multiplication")
  | Divide, Num x, Num y -> if y = 0 then raise (EvalError "Div by Zero") 
                            else Num (x / y)
  | Divide_f, Float x, Float y -> if y = 0. then raise (EvalError "Div by Zero")
                                  else Float (x /. y)
  | Divide, _, _ | Divide_f, _, _ -> raise (EvalError "Invalid Division")
  | Equals, Num x, Num y -> Bool (x = y)
  | Equals, Float x, Float y -> Bool (x = y)
  | Equals, Bool x, Bool y -> Bool (x = y)
  | Equals, _, _ -> raise (EvalError "Invalid Equality")
  | LessThan, Num x, Num y -> Bool (x < y)
  | LessThan, Float x, Float y -> Bool (x < y)
  | LessThan, _, _ -> raise (EvalError "Invalid LessThan")
  | GreaterThan, Num x, Num y -> Bool (x > y)
  | GreaterThan, Float x, Float y -> Bool (x > y)
  | GreaterThan, _, _ -> raise (EvalError "Invalid GreaterThan") ;;

(* The SUBSTITUTION MODEL evaluator *)
let eval_s (exp : expr) (_env : Env.env) : Env.value =
  let rec eval_helper (exp : expr) : expr =
  match exp with
  | Var _ -> raise (EvalError "Unbound Variable")
  | Num _ | Float _ | Bool _ | Fun (_, _) -> exp
  | Unop (op, e) -> unopeval op (eval_helper e)
  | Binop (op, e1, e2) -> binopeval op (eval_helper e1) (eval_helper e2)
  | Conditional (e1, e2, e3) -> (match eval_helper e1 with
                                 | Bool b -> if b then eval_helper e2 
                                             else eval_helper e3
                                 | _ -> raise (EvalError "Invalid Conditional"))
  | Let (x, def, body) -> eval_helper (subst x (eval_helper def) body)
  | Letrec (x, def, body) -> let v_d = eval_helper def in
                             eval_helper (subst x (subst x 
                               (Letrec (x, v_d, Var x)) v_d) body)
  | App (e1, e2) -> (match eval_helper e1 with
                     | Fun (x, e) -> eval_helper (subst x (eval_helper e2) e)
                     | _ -> raise (EvalError "Invalid App"))
  | Raise -> raise EvalException
  | Unassigned -> raise (EvalError "Unassigned") in
  Val (eval_helper exp) ;;
     
(* Helper function that combines both the dynamic and lexical model 
   evaluators. If using the dynamic model evaluator, the input dyn_eval = true, 
   and if using the lexical model, the input dyn_eval = false *)
let eval_both (dyn_eval : bool) (exp : expr) (env : Env.env) : Env.value =
  let rec eval_helper (exp : expr) (env : Env.env) : Env.value =
    let app_d (exp1 : expr) (exp2 : expr) : Env.value =
      match eval_helper exp1 env with
      | Val (Fun (v, e)) -> let v_e2 = eval_helper exp2 env in
                            let new_env = extend env v (ref v_e2) in
                            eval_helper e new_env
      | _ -> raise (EvalError "Invalid App") in
    let app_l (exp1 : expr) (exp2 : expr) : Env.value =
      match eval_helper exp1 env with
      | Closure (Fun (v, e), env1) -> let v_e2 = eval_helper exp2 env in
                                      let new_env = extend env1 v (ref v_e2) in
                                      eval_helper e new_env
      | _ -> raise (EvalError "Invalid App") in
    match exp with
    | Var v -> lookup env v
    | Num _ | Float _ | Bool _ -> Val (exp)
    | Unop (op, e) -> (match eval_helper e env with
                       | Val expr -> Val (unopeval op expr)
                       | _ -> raise (EvalError "Invalid Unop"))
    | Binop (op, e1, e2) ->  (match eval_helper e1 env, eval_helper e2 env with
                              | Val x, Val y -> Val (binopeval op x y)
                              | _, _ -> raise (EvalError "Invalid Binop"))
    | Conditional (e1, e2, e3) -> (match eval_helper e1 env with
                                   | Val (Bool b) -> 
                                       if b then eval_helper e2 env 
                                       else eval_helper e3 env
                                   | _ -> 
                                       raise (EvalError "Invalid Conditional"))
    | Fun (_v, _e) -> if dyn_eval then Val (exp) else close exp env
    | Let (x, def, body) -> eval_helper body 
                              (extend env x (ref (eval_helper def env)))
    | Letrec (x, def, body) -> 
        let temp_val = ref (Val Unassigned) in
        let new_env = extend env x temp_val in
        let evaluated = eval_helper def (new_env) in
        if evaluated = Val Unassigned then raise (EvalError "Invalid Letrec")
        else temp_val := evaluated; eval_helper body (new_env)
    | App (e1, e2) -> if dyn_eval then app_d e1 e2 else app_l e1 e2
    | Raise -> raise EvalException
    | Unassigned -> raise (EvalError "Unassigned")
  in eval_helper exp env ;;

(* The DYNAMICALLY-SCOPED ENVIRONMENT MODEL evaluator *)
let eval_d (exp : expr) (env : Env.env) : Env.value =
  eval_both true exp env ;;
  
(* The LEXICALLY-SCOPED ENVIRONMENT MODEL evaluator --
   completed as (part of) extension *)
let eval_l (exp : expr) (env : Env.env) : Env.value =
  eval_both false exp env ;;

(* The EXTENDED evaluator -- if you want, you can provide your
   extension as a separate evaluator, or if it is type- and
   correctness-compatible with one of the above, you can incorporate
   your extensions within eval_s, eval_d, or eval_l. *)

let eval_e _ =
  failwith "eval_e not implemented" ;;
  
(* Connecting the evaluators to the external world. The REPL in
   miniml.ml uses a call to the single function evaluate defined
   here. Initially, evaluate is the trivial evaluator eval_t. But you
   can define it to use any of the other evaluators as you proceed to
   implement them. (We will directly unit test the four evaluators
   above, not the evaluate function, so it doesn't matter how it's set
   when you submit your solution.) *)
   
let evaluate = eval_l ;;
