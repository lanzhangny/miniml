(* 
                				MiniML
                          	CS51 Final Project
                          	     All Tests
                         -.-. ... ..... .----
 *)

 open Expr ;;
 open Evaluation ;;


let exp_1 = Let ("x", Num (3), Let ("y", Var("x"), App (Var("f"), App (Var("x"), Var("y"))))) ;;
let exp_2 = Let ("x", Num (30), Let ("x", Let ("x", Num (3), Binop (Times, Var("x"), Num(10))), Binop (Plus, Var("x"), Var("x")))) ;;
let exp_3 = App (Fun ("x", Binop (Plus, Var("x"), Var("y"))), Var("z")) ;;
let exp_4 = Let ("x", Binop (Minus, Var("x"), Var("y")), Binop (Times, Var("z"), Num(15))) ;;
let exp_5 = Letrec ("f", Fun ("n", Conditional (Binop(Equals, Var("n"), Num(0)), Num(1), 
	Binop(Times, Var("n"), App (Var("f"), Binop(Minus, Var("n"), Num(1)))))), App (Var("f"), Num(3))) ;;
let exp_6 = Let ("x", Var("x"), Let ("y", Var("x"), App (Var("f"), App (Var("x"), Var("y"))))) ;;
let exp_7 = Let ("x", Binop (Times, Var("y"), Var("y")), Binop (Plus, Var("x"), Var("x"))) ;;
let exp_8 = Fun ("y", Binop (Plus, Var("x"), Var("y"))) ;;

(* free_vars tests *)
let free_vars_tests() =
  assert (free_vars (Num (100)) = vars_of_list []) ;
  assert (free_vars (Var ("x")) = vars_of_list ["x"]) ;
  assert (free_vars (Bool (true)) = vars_of_list []) ;
  assert (free_vars (Unop (Negate, Var("x"))) = vars_of_list ["x"]) ;
  assert (free_vars exp_1 = vars_of_list ["f"]) ;
  assert (free_vars exp_2 = vars_of_list []) ;
  assert (free_vars exp_3 = vars_of_list ["y"; "z"]) ;
  assert (free_vars exp_4 = vars_of_list ["x"; "y"; "z"]) ;
  assert (free_vars exp_5 = vars_of_list []) ;
  assert (free_vars exp_6 = vars_of_list ["f"; "x"]) ;;

(* subst tests *)
let subst_tests() = 
  assert (subst ("x") (Num(3)) (exp_7) = Let ("x", Binop (Times, Var "y", Var "y"), Binop (Plus, Var "x", Var "x"))) ;
  assert (subst ("y") (Num(3)) (exp_7) = Let ("x", Binop (Times, Num 3, Num 3), Binop (Plus, Var "x", Var "x"))) ;
  assert (subst ("x") (Var("y")) (exp_8) = Fun ("var0", Binop (Plus, Var "y", Var "var0"))) ;;

let _ =
  free_vars_tests() ;
  subst_tests() ;;