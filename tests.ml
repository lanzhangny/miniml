(* 
                				  MiniML
                          	CS51 Final Project
                          	    All Tests
                         -.-. ... ..... .----
 *)

 open Expr ;;
 open Evaluation ;;

(* free_vars test expressions *)
let exp_1 = Num (100) ;;
let exp_2 = Float (100.) ;;
let exp_3 = Var ("x") ;;
let exp_4 = Bool (true) ;;
let exp_5 = Unop (Negate, Var("x")) ;;
let exp_6 = Let ("x", Num (3), Let ("y", Var("x"), App (Var("f"), App (Var("x"), Var("y"))))) ;;
let exp_7 = Let ("x", Var("x"), Let ("y", Var("x"), App (Var("f"), App (Var("x"), Var("y"))))) ;;
let exp_8 = Let ("x", Var("y"), Let ("y", Var("x"), App (Var("f"), App (Var("x"), Var("y"))))) ;;
let exp_9 = Let ("x", Fun ("y", Var("x")), Var("x")) ;;
let exp_10 = App (Fun ("x", Binop (Plus, Var("x"), Var("y"))), Var("z")) ;;
let exp_11 = Let ("x", Binop (Minus, Var("x"), Var("y")), Binop (Times, Var("z"), Num(15))) ;;

(* free_vars tests *)
let free_vars_tests() =
  assert (same_vars (free_vars exp_1) (vars_of_list [])) ;
  assert (same_vars (free_vars exp_2) (vars_of_list [])) ;
  assert (same_vars (free_vars exp_3) (vars_of_list ["x"])) ;
  assert (same_vars (free_vars exp_4) (vars_of_list [])) ;
  assert (same_vars (free_vars exp_5) (vars_of_list ["x"])) ;
  assert (same_vars (free_vars exp_6) (vars_of_list ["f"])) ;
  assert (same_vars (free_vars exp_7) (vars_of_list ["f"; "x"])) ;
  assert (same_vars (free_vars exp_8) (vars_of_list ["f"; "y"])) ;
  assert (same_vars (free_vars exp_9) (vars_of_list ["x"])) ;
  assert (same_vars (free_vars exp_10) (vars_of_list ["y"; "z"])) ;
  assert (same_vars (free_vars exp_11) (vars_of_list ["x"; "y"; "z"])) ;;

(* subst expressions *)
let exp_12 = Binop (Plus, Var("x"), Num(1)) ;;
let exp_13 = Binop (Times, Var("x"), Var("x")) ;;
let exp_14 = Let ("x", Binop (Times, Var("y"), Var("y")), Binop (Plus, Var("x"), Var("x"))) ;;
let exp_15 = Fun ("y", Binop (Plus, Var("x"), Var("y"))) ;;
let exp_16 = Let ("x", Binop (Plus, Var "x", Var "y"), Binop (Times, Var "z", Var "x")) ;;

(* subst tests *)
let subst_tests() =
  assert (subst ("x") (Num(50)) (exp_12) = Binop (Plus, Num(50), Num(1))) ;
  assert (subst ("y") (Num(50)) (exp_12) = exp_12) ;
  assert (subst ("x") (Num(2)) (exp_13) = Binop (Times, Num(2), Num(2))) ;
  assert (subst ("x") (Num(3)) (exp_14) = exp_14) ;
  assert (subst ("y") (Num(3)) (exp_14) = Let ("x", Binop (Times, Num 3, Num 3), Binop (Plus, Var "x", Var "x"))) ;
  assert (subst ("x") (Var("y")) (exp_15) = Fun ("var0", Binop (Plus, Var "y", Var "var0"))) ;
  assert (subst ("x") (Num(42)) (exp_16) = Let ("x", Binop (Plus, Num 42, Var "y"), Binop (Times, Var "z", Var "x"))) ;
  assert (subst ("y") (Float(42.)) (exp_16) = Let ("x", Binop (Plus, Var "x", Float 42.), Binop (Times, Var "z", Var "x"))) ;;

(* eval expressions *)
let exp_17 = Num 18 ;;
let exp_18 = Float 18. ;;
let exp_19 = Bool false ;;
let exp_20 = Unop (Negate, Num 13) ;;
let exp_21 = Unop (Negate_f, Float 13.) ;;
let exp_22 = Binop (Plus, Num 3, Num 4) ;;
let exp_23 = Binop (Plus_f, Float 3., Float 4.) ;;
let exp_24 = Binop (Minus, Num 5, Num 32) ;;
let exp_25 = Binop (Minus_f, Float 32., Float 5.) ;;
let exp_26 = Binop (Times, Num(~-2), Num 28) ;;
let exp_27 = Binop (Times_f, Float(~-.2.), Float 28.) ;;
let exp_28 = Binop (Divide, Num 3, Num 2) ;;
let exp_29 = Binop (Divide_f, Float 3., Float 8.) ;;
let exp_30 = Binop (Equals, Num 5, Num 6) ;;
let exp_31 = Binop (LessThan, Float 3., Float 6.) ;;
let exp_32 = Binop (LessThan, Num 5, Num 2) ;;
let exp_33 = Binop (GreaterThan, Float 3., Float 6.) ;;
let exp_34 = Binop (GreaterThan, Num 8, Num 2) ;;
let exp_35 = Let ("x", Num 8, Conditional(Binop(Equals, Var "x", Num 3), Num 1, Num 0)) ;;
let exp_36 = Let ("x", Bool true, Conditional(Var "x", Num 1, Num 0)) ;;
let exp_37 = App ((Fun ("x", Binop (Plus, Var "x", Var "x"))), Num 5) ;;
let exp_38 = Let ("x", Num 30, Let ("x", Let ("x", Num 3, Binop (Times, Var "x", Num 10)), 
  Binop (Plus, Var "x", Var "x"))) ;;
let exp_39 = Let ("x", Num 3, Let ("y", Binop (Times, Var "x", Var "x"), Var "y")) ;;
let exp_40 = Letrec ("f", Fun ("n", Conditional (Binop(Equals, Var "n", Num 0), Num 1, 
  Binop (Times, Var "n", App (Var "f", Binop(Minus, Var "n", Num 1))))), App (Var "f", Num 4)) ;;
let exp_41 = Letrec ("f", Fun ("n", Conditional (Binop(Equals, Var "n", Float 0.), Float 1., 
  Binop(Times_f, Var "n", App (Var "f", Binop(Minus_f, Var "n", Float 1.))))), 
    App (Var "f", Float 4.)) ;;
let exp_42 = Letrec ("f", Fun ("x", Conditional (Binop (LessThan, Var "x", Num 1), Num 1, 
  Binop (Plus, (App(Var "f", Binop (Minus, Var "x", Num 1))), (App(Var "f", 
	Binop (Minus, Var "x", Num 2)))))), App(Var "f", Num 5)) ;;
let exp_43 = Let ("x", Num 1, Let ("f", Fun ("y", Binop (Plus, Var "x", Var "y")), 
  Let ("x", Num 2, App(Var "f", Num 3)))) ;;
let exp_44 = Let ("x", Num 5, Let ("f", Fun ("y", Binop (Times, Num 2, Binop (Times, Var "x", Var "y"))), 
  Let ("x", Num 3, App (Var "f", Num 4)))) ;;
let exp_45 = Let ("x", Float 1., Let ("f", Fun ("y", Binop (Plus_f, Var "x", Var "y")), 
  Let ("x", Float 2., App(Var "f", Float 3.)))) ;;
let exp_46 = Let ("x", Float 5., Let ("f", Fun ("y", Binop (Times_f, Float 2., 
  Binop (Times_f, Var "x", Var "y"))), Let ("x", Float 3., App (Var "f", Float 4.)))) ;;

(* open Env ;;

let expressions_list = [exp_17; exp_18; exp_19; exp_20; exp_21; exp_22; exp_23; exp_24;
                        exp_25; exp_26; exp_27; exp_28; exp_29; exp_30; exp_31; exp_32;
                        exp_33; exp_34; exp_35; exp_36; exp_37; exp_38; exp_39; exp_40;
                        exp_41; exp_42; exp_43; exp_44; exp_45; exp_46] ;;
let solutions_1_list = [Val (Num 18); Val (Float 18.); Val (Bool false); Val (Num (~-13)); 
                        Val (Float (~-.13.)); Val (Num 7); Val (Float 7.); Val (Num (~-27)); 
                        Val (Float 27.); Val (Num (~-56)); Val (Float (~-.56.)); Val (Num 1);
                        Val (Float 0.375); Val (Bool false); Val (Bool true); Val (Bool false);
                        Val (Bool false); Val (Bool true); Val (Num 0); Val (Num 1); Val (Num 10);
                        Val (Num 60); Val (Num 9); Val (Num 24); Val (Float 24.); Val (Num 13);
                        Val (Num 4); Val (Num 40); Val (Float 4.); Val (Float 40.)] ;;


let rec eval_tester (eval : expr -> Env.env -> Env.value) 
                	(exp_list : expr list)
                	(sol_list : Env.value list)
                	(counter : int)
                	: unit =
  let empty = Env.create() in
  match exp_list, sol_list with
  | [], [] -> ()
  | [], _ | _, [] -> failwith "expressions and solutions lists of different length"
  | exp1 :: tl1, sol1 :: tl2 -> if (eval exp1 empty = sol1) then eval_tester eval tl1 tl2 (counter + 1)
                                else failwith ("the expression in position " ^
                                (string_of_int counter) ^ " does not match the solution.") ;; *)
 
let empty = Env.create() ;;

let eval_s_tests() =
(*   eval_tester eval_s expressions_list solutions_1_list 0;; *)
  assert (eval_s exp_17 empty = Env.Val (Num 18)) ;
  assert (eval_s exp_18 empty = Env.Val (Float 18.)) ;
  assert (eval_s exp_19 empty = Env.Val (Bool false)) ;
  assert (eval_s exp_20 empty = Env.Val (Num (~-13))) ;
  assert (eval_s exp_21 empty = Env.Val (Float (~-.13.))) ;
  assert (eval_s exp_22 empty = Env.Val (Num 7)) ;
  assert (eval_s exp_23 empty = Env.Val (Float 7.)) ;
  assert (eval_s exp_24 empty = Env.Val (Num (~-27))) ;
  assert (eval_s exp_25 empty = Env.Val (Float 27.)) ;
  assert (eval_s exp_26 empty = Env.Val (Num (~-56))) ;
  assert (eval_s exp_27 empty = Env.Val (Float (~-.56.))) ;
  assert (eval_s exp_28 empty = Env.Val (Num 1)) ;
  assert (eval_s exp_29 empty = Env.Val (Float 0.375)) ;
  assert (eval_s exp_30 empty = Env.Val (Bool false)) ;
  assert (eval_s exp_31 empty = Env.Val (Bool true)) ;
  assert (eval_s exp_32 empty = Env.Val (Bool false)) ;
  assert (eval_s exp_33 empty = Env.Val (Bool false)) ;
  assert (eval_s exp_34 empty = Env.Val (Bool true)) ;
  assert (eval_s exp_35 empty = Env.Val (Num 0)) ;
  assert (eval_s exp_36 empty = Env.Val (Num 1)) ;
  assert (eval_s exp_37 empty = Env.Val (Num 10)) ;
  assert (eval_s exp_38 empty = Env.Val (Num 60)) ;
  assert (eval_s exp_39 empty = Env.Val (Num 9)) ;
  assert (eval_s exp_40 empty = Env.Val (Num 24)) ;
  assert (eval_s exp_41 empty = Env.Val (Float 24.)) ;
  assert (eval_s exp_42 empty = Env.Val (Num 13)) ;
  assert (eval_s exp_43 empty = Env.Val (Num 4)) ;
  assert (eval_s exp_44 empty = Env.Val (Num 40)) ;
  assert (eval_s exp_45 empty = Env.Val (Float 4.)) ;
  assert (eval_s exp_46 empty = Env.Val (Float 40.)) ;;

(* Env Module tests *)
let env_mod_tests() =
  let env = Env.create() in
  let env = Env.extend env "x" (ref (Env.Val (Num 3))) in
  let env = Env.extend env "y" (ref (Env.Val (Num 5))) in
  assert (Env.lookup env "x" = Env.Val(Num 3)) ;
  assert (Env.lookup env "y" = Env.Val(Num 5)) ;
  assert (Env.env_to_string env = "{(y, 5); (x, 3)}") ;
  let env = Env.extend env "y" (ref (Env.Val (Bool true))) in
  assert (Env.lookup env "y" = Env.Val(Bool true)) ;
  assert (Env.env_to_string env = "{(y, true); (x, 3)}") ;
  let closure = Env.close (exp_38) (env) in
  assert (Env.value_to_string closure = "[Expr: let x = 30 in let x = let x = 3 in x * 10 in x + x, Env: {(y, true); (x, 3)}]") ;
  assert (Env.value_to_string ~printenvp: false closure = "let x = 30 in let x = let x = 3 in x * 10 in x + x") ;;

let eval_d_tests() =
  assert (eval_d exp_17 empty = Env.Val (Num 18)) ;
  assert (eval_d exp_18 empty = Env.Val (Float 18.)) ;
  assert (eval_d exp_19 empty = Env.Val (Bool false)) ;
  assert (eval_d exp_20 empty = Env.Val (Num (~-13))) ;
  assert (eval_d exp_21 empty = Env.Val (Float (~-.13.))) ;
  assert (eval_d exp_22 empty = Env.Val (Num 7)) ;
  assert (eval_d exp_23 empty = Env.Val (Float 7.)) ;
  assert (eval_d exp_24 empty = Env.Val (Num (~-27))) ;
  assert (eval_d exp_25 empty = Env.Val (Float 27.)) ;
  assert (eval_d exp_26 empty = Env.Val (Num (~-56))) ;
  assert (eval_d exp_27 empty = Env.Val (Float (~-.56.))) ;
  assert (eval_d exp_28 empty = Env.Val (Num 1)) ;
  assert (eval_d exp_29 empty = Env.Val (Float 0.375)) ;
  assert (eval_d exp_30 empty = Env.Val (Bool false)) ;
  assert (eval_d exp_31 empty = Env.Val (Bool true)) ;
  assert (eval_d exp_32 empty = Env.Val (Bool false)) ;
  assert (eval_d exp_33 empty = Env.Val (Bool false)) ;
  assert (eval_d exp_34 empty = Env.Val (Bool true)) ;
  assert (eval_d exp_35 empty = Env.Val (Num 0)) ;
  assert (eval_d exp_36 empty = Env.Val (Num 1)) ;
  assert (eval_d exp_37 empty = Env.Val (Num 10)) ;
  assert (eval_d exp_38 empty = Env.Val (Num 60)) ;
  assert (eval_d exp_39 empty = Env.Val (Num 9)) ;
  assert (eval_d exp_40 empty = Env.Val (Num 24)) ;
  assert (eval_d exp_41 empty = Env.Val (Float 24.)) ;
  assert (eval_d exp_42 empty = Env.Val (Num 13)) ;
  assert (eval_d exp_43 empty = Env.Val (Num 5)) ;
  assert (eval_d exp_44 empty = Env.Val (Num 24)) ;
  assert (eval_d exp_45 empty = Env.Val (Float 5.)) ;
  assert (eval_d exp_46 empty = Env.Val (Float 24.)) ;;

let eval_l_tests() =
  assert (eval_l exp_17 empty = Env.Val (Num 18)) ;
  assert (eval_l exp_18 empty = Env.Val (Float 18.)) ;
  assert (eval_l exp_19 empty = Env.Val (Bool false)) ;
  assert (eval_l exp_20 empty = Env.Val (Num (~-13))) ;
  assert (eval_l exp_21 empty = Env.Val (Float (~-.13.))) ;
  assert (eval_l exp_22 empty = Env.Val (Num 7)) ;
  assert (eval_l exp_23 empty = Env.Val (Float 7.)) ;
  assert (eval_l exp_24 empty = Env.Val (Num (~-27))) ;
  assert (eval_l exp_25 empty = Env.Val (Float 27.)) ;
  assert (eval_l exp_26 empty = Env.Val (Num (~-56))) ;
  assert (eval_l exp_27 empty = Env.Val (Float (~-.56.))) ;
  assert (eval_l exp_28 empty = Env.Val (Num 1)) ;
  assert (eval_l exp_29 empty = Env.Val (Float 0.375)) ;
  assert (eval_l exp_30 empty = Env.Val (Bool false)) ;
  assert (eval_l exp_31 empty = Env.Val (Bool true)) ;
  assert (eval_l exp_32 empty = Env.Val (Bool false)) ;
  assert (eval_l exp_33 empty = Env.Val (Bool false)) ;
  assert (eval_l exp_34 empty = Env.Val (Bool true)) ;
  assert (eval_l exp_35 empty = Env.Val (Num 0)) ;
  assert (eval_l exp_36 empty = Env.Val (Num 1)) ;
  assert (eval_l exp_37 empty = Env.Val (Num 10)) ;
  assert (eval_l exp_38 empty = Env.Val (Num 60)) ;
  assert (eval_l exp_39 empty = Env.Val (Num 9)) ;
  assert (eval_l exp_40 empty = Env.Val (Num 24)) ;
  assert (eval_l exp_41 empty = Env.Val (Float 24.)) ;
  assert (eval_l exp_42 empty = Env.Val (Num 13)) ;
  assert (eval_l exp_43 empty = Env.Val (Num 4)) ;
  assert (eval_l exp_44 empty = Env.Val (Num 40)) ;
  assert (eval_l exp_45 empty = Env.Val (Float 4.)) ;
  assert (eval_l exp_46 empty = Env.Val (Float 40.)) ;;

let _ =
  free_vars_tests() ;
  subst_tests() ;
  eval_s_tests() ;
  env_mod_tests() ;
  eval_d_tests() ;
  eval_l_tests() ;;