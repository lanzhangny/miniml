(* 
                         CS 51 Final Project
                        MiniML -- Expressions
*)

(*......................................................................
  Abstract syntax of MiniML expressions 
 *)

type unop =
  | Negate
  | Negate_f
;;
    
type binop =
  | Plus
  | Plus_f
  | Minus
  | Minus_f
  | Times
  | Times_f
  | Divide
  | Divide_f
  | Equals
  | LessThan
  | GreaterThan
;;

type varid = string ;;
  
type expr =
  | Var of varid                         (* variables *)
  | Num of int                           (* integers *)
  | Float of float                       (* floats *)
  | Bool of bool                         (* booleans *)
  | Unop of unop * expr                  (* unary operators *)
  | Binop of binop * expr * expr         (* binary operators *)
  | Conditional of expr * expr * expr    (* if then else *)
  | Fun of varid * expr                  (* function definitions *)
  | Let of varid * expr * expr           (* local naming *)
  | Letrec of varid * expr * expr        (* recursive local naming *)
  | Raise                                (* exceptions *)
  | Unassigned                           (* (temporarily) unassigned *)
  | App of expr * expr                   (* function applications *)
;;
  
(*......................................................................
  Manipulation of variable names (varids)
 *)

(* varidset -- Sets of varids *)
module SS = Set.Make (struct
                       type t = varid
                       let compare = String.compare
                     end ) ;;

type varidset = SS.t ;;

(* same_vars :  varidset -> varidset -> bool
   Test to see if two sets of variables have the same elements (for
   testing purposes) *)
let same_vars : varidset -> varidset -> bool =
  SS.equal;;

(* vars_of_list : string list -> varidset
   Generate a set of variable names from a list of strings (for
   testing purposes) *)
let vars_of_list : string list -> varidset =
  SS.of_list ;;
  
(* free_vars : expr -> varidset
   Return a set of the variable names that are free in expression
   exp *)
let rec free_vars (exp : expr) : varidset =
  match exp with
  | Var x -> SS.singleton x
  | Num _ | Float _ | Bool _ | Raise | Unassigned -> SS.empty
  | Unop (_, e) -> free_vars e
  | Binop (_, e1, e2) -> SS.union (free_vars e1) (free_vars e2)
  | Conditional (e1, e2, e3) -> SS.union (free_vars e1) 
                                  (SS.union (free_vars e2) (free_vars e3))
  | Fun (x, e) -> SS.remove x (free_vars e)
  | Let (x, def, body) -> SS.union (free_vars def) 
                            (SS.remove x (free_vars body))
  | Letrec (x, def, body) -> SS.remove x 
                               (SS.union (free_vars def) (free_vars body))
  | App (e1, e2) -> SS.union (free_vars e1) (free_vars e2) ;;

(* new_varname : unit -> varid
   Return a fresh variable, constructed with a running counter a la
   gensym. Assumes no variable names use the prefix "var". (Otherwise,
   they might accidentally be the same as a generated variable name.) *)

let new_varname : unit -> varid =
  let ctr = ref 0 in
  fun () -> let new_var = "var" ^ string_of_int !ctr in
            ctr := !ctr + 1;
            new_var ;;

(*......................................................................
  Substitution 

  Substitution of expressions for free occurrences of variables is the
  cornerstone of the substitution model for functional programming
  semantics.
 *)

(* subst : varid -> expr -> expr -> expr
   Substitute repl for free occurrences of var_name in exp *)
let rec subst (var_name : varid) (repl : expr) (exp : expr) : expr =
  match exp with
  | Var x -> if x = var_name then repl else exp
  | Num _ | Float _ | Bool _ | Raise | Unassigned -> exp

  | Unop (op, arg) -> Unop (op, subst var_name repl arg)
  | Binop (op, arg1, arg2) -> Binop (op, subst var_name repl arg1, 
                                      subst var_name repl arg2)
  | Conditional (e1, e2, e3) -> Conditional (subst var_name repl e1, 
                                             subst var_name repl e2, 
                                             subst var_name repl e3)
  | Fun (x, e) ->
      if x = var_name then exp
      else if SS.mem x (free_vars repl) then 
        let z = new_varname() in
        Fun (z, subst var_name repl (subst x (Var z) e))
      else Fun (x, subst var_name repl e)
  | Let (x, def, body) ->
      if x = var_name then Let (x, subst var_name repl def, body)
      else if SS.mem x (free_vars repl) then
        let z = new_varname() in
        Let (z, subst var_name repl def, 
          subst var_name repl (subst x (Var z) body))
      else Let (x, subst var_name repl def, subst var_name repl body)
  | Letrec (x, def, body) ->
      if x = var_name then exp
      else Letrec (x, subst var_name repl def, subst var_name repl body)
  | App (e1, e2) -> App (subst var_name repl e1, subst var_name repl e2) ;;

(*......................................................................
  String representations of expressions
 *)
    
(* exp_to_concrete_string : expr -> string
   Returns a concrete syntax string representation of the expr *)
let rec exp_to_concrete_string (exp : expr) : string =
  match exp with
  | Var v -> v
  | Num i -> string_of_int i
  | Float f -> string_of_float f
  | Bool b -> string_of_bool b
  | Unop (op, e) -> (match op with
                     | Negate -> "~- "
                     | Negate_f -> "~-. ") ^ (exp_to_concrete_string e)
  | Binop (op, e1, e2) -> (exp_to_concrete_string e1) ^
                         (match op with
                          | Plus -> " + "
                          | Plus_f -> " +. "
                          | Minus -> " - "
                          | Minus_f -> " -. "
                          | Times -> " * "
                          | Times_f -> " *. "
                          | Divide -> " / "
                          | Divide_f -> " /. "
                          | Equals -> " = "
                          | LessThan -> " < "
                          | GreaterThan -> " > "
                          ) ^ (exp_to_concrete_string e2)
  | Conditional (e1, e2, e3) -> "if " ^ (exp_to_concrete_string e1) ^
                                " then " ^ (exp_to_concrete_string e2) ^
                                " else " ^ (exp_to_concrete_string e3)
  | Fun (v, e) -> "fun " ^ v ^ " -> " ^ (exp_to_concrete_string e)
  | Let (v, def, body) -> "let " ^ v ^ " = " ^ (exp_to_concrete_string def) ^
                          " in " ^ (exp_to_concrete_string body)
  | Letrec (v, def, body) -> "let rec " ^ v ^ " = " ^ 
                             (exp_to_concrete_string def) ^
                             " in " ^ (exp_to_concrete_string body)
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (e1, e2) -> (exp_to_concrete_string e1) ^ " (" ^
                    (exp_to_concrete_string e2) ^ ")" ;;

(* exp_to_abstract_string : expr -> string
   Returns a string representation of the abstract syntax of the expr *)
let rec exp_to_abstract_string (exp : expr) : string =
  match exp with
  | Var v -> "Var (" ^ v ^ ")"
  | Num i -> "Num (" ^ (string_of_int i) ^ ")"
  | Float f -> "Float (" ^ (string_of_float f) ^ ")"
  | Bool b -> "Bool (" ^ (string_of_bool b) ^ ")"
  | Unop (op, e) -> "Unop (" ^ (match op with
                                 | Negate -> "Negate"
                                 | Negate_f -> "Negate_f") ^ ", " ^ 
                      (exp_to_abstract_string e) ^ ")"
  | Binop (op, e1, e2) -> "Binop (" ^ (match op with
                                     | Plus -> "Plus"
                                     | Plus_f -> "Plus_f"
                                     | Minus -> "Minus"
                                     | Minus_f -> "Minus_f"
                                     | Times -> "Times"
                                     | Times_f -> "Times_f"
                                     | Divide -> "Divide"
                                     | Divide_f -> "Divide_f"
                                     | Equals -> "Equals"
                                     | LessThan -> "LessThan"
                                     | GreaterThan -> "GreaterThan") ^ ", " ^
                          (exp_to_abstract_string e1) ^ ", " ^ 
                          (exp_to_abstract_string e2) ^ ")"
  | Conditional (e1, e2, e3) -> "Conditional (" ^ 
                                (exp_to_abstract_string e1) ^ ", " ^
                                (exp_to_abstract_string e2) ^ ", " ^ 
                                (exp_to_abstract_string e3) ^ ")"
  | Fun (v, e) -> "Fun (" ^ v ^ ", " ^ (exp_to_abstract_string e) ^ ")"
  | Let (v, def, body) -> "Let (" ^ v ^ ", " ^ (exp_to_abstract_string def) ^
                          ", " ^ (exp_to_abstract_string body) ^ ")"
  | Letrec (v, def, body) -> "Letrec (" ^ v ^ ", " ^ 
                             (exp_to_abstract_string def) ^ ", " ^ 
                             (exp_to_abstract_string body) ^ ")"
  | Raise -> "Raise"
  | Unassigned -> "Unassigned"
  | App (e1, e2) -> "App (" ^ (exp_to_abstract_string e1) ^ ", " ^ 
                      (exp_to_abstract_string e2) ^ ")" ;;
