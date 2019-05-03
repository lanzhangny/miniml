(* 
                				  MiniML
                          	CS51 Final Project
                          	    All Tests
                         -.-. ... ..... .----
 *)

 open Expr ;;
 open Evaluation ;;

(* defining different expressions *)
let exp_1 = Let ("x", Num (3), Let ("y", Var("x"), App (Var("f"), App (Var("x"), Var("y"))))) ;;
let exp_2 = Let ("x", Num (30), Let ("x", Let ("x", Num (3), Binop (Times, Var("x"), Num(10))), 
  Binop (Plus, Var("x"), Var("x")))) ;;
let exp_3 = App (Fun ("x", Binop (Plus, Var("x"), Var("y"))), Var("z")) ;;
let exp_4 = Let ("x", Binop (Minus, Var("x"), Var("y")), Binop (Times, Var("z"), Num(15))) ;;
let exp_5 = Letrec ("f", Fun ("n", Conditional (Binop(Equals, Var("n"), Num(0)), Num(1), 
  Binop (Times, Var("n"), App (Var("f"), Binop(Minus, Var("n"), Num(1)))))), App (Var("f"), Num(4))) ;;
let exp_6 = Let ("x", Var("x"), Let ("y", Var("x"), App (Var("f"), App (Var("x"), Var("y"))))) ;;
let exp_7 = Let ("x", Binop (Times, Var("y"), Var("y")), Binop (Plus, Var("x"), Var("x"))) ;;
let exp_8 = Fun ("y", Binop (Plus, Var("x"), Var("y"))) ;;
let exp_9 = Let ("x", Binop (Plus, Var "x", Var "y"), Binop (Times, Var "z", Var "x")) ;;
let exp_10 = Letrec ("f", Fun ("x", Conditional (Binop (LessThan, Var("x"), Num(1)), Num(1), 
  Binop (Plus, (App(Var("f"), Binop (Minus, Var("x"), Num(1)))), (App(Var("f"), 
	Binop (Minus, Var("x"), Num(2))))))), App(Var("f"), Num(5))) ;;
let exp_11 = Let ("x", Num(1), Let ("f", Fun ("y", Binop (Plus, Var("x"), Var("y"))), 
  Let ("x", Num(2), App(Var("f"), Num(3))))) ;;
let exp_12 = Let ("x", Num(5), Let ("f", Fun ("y", Binop (Times, Num(2), Binop (Times, Var("x"), Var("y")))), 
  Let ("x", Num(3), App (Var("f"), Num(4))))) ;;

(* with floats *)
let exp_13 = Let ("x", Binop(Times_f, Float (3.), Float (4.)), Binop (Plus_f, Var("x"), Float (1.))) ;;
let exp_14 = Letrec ("f", Fun ("n", Conditional (Binop(Equals, Var("n"), Float(0.)), Float(1.), 
  Binop(Times_f, Var("n"), App (Var("f"), Binop(Minus_f, Var("n"), Float(1.)))))), 
    App (Var("f"), Float(4.))) ;;
let exp_15 = Let ("x", Float(1.), Let ("f", Fun ("y", Binop (Plus_f, Var("x"), Var("y"))), 
  Let ("x", Float(2.), App(Var("f"), Float(3.))))) ;;
let exp_16 = Let ("x", Float(5.), Let ("f", Fun ("y", Binop (Times_f, Float(2.), 
  Binop (Times_f, Var("x"), Var("y")))), Let ("x", Float(3.), App (Var("f"), Float(4.))))) ;;


(* free_vars tests *)
let free_vars_tests() =
  assert (same_vars (free_vars (Num (100))) (vars_of_list [])) ;
  assert (same_vars (free_vars (Float (100.))) (vars_of_list [])) ;
  assert (same_vars (free_vars (Var ("x"))) (vars_of_list ["x"])) ;
  assert (same_vars (free_vars (Bool (true))) (vars_of_list [])) ;
  assert (same_vars (free_vars (Unop (Negate, Var("x")))) (vars_of_list ["x"])) ;
  assert (same_vars (free_vars exp_1) (vars_of_list ["f"])) ;
  assert (same_vars (free_vars exp_2) (vars_of_list [])) ;
  assert (same_vars (free_vars exp_3) (vars_of_list ["y"; "z"])) ;
  assert (same_vars (free_vars exp_4) (vars_of_list ["x"; "y"; "z"])) ;
  assert (same_vars (free_vars exp_5) (vars_of_list [])) ;
  assert (same_vars (free_vars exp_6) (vars_of_list ["f"; "x"])) ;;

(* subst tests *)
let subst_tests() = 
  assert (subst ("x") (Num(3)) (exp_7) = Let ("x", Binop (Times, Var "y", Var "y"), Binop (Plus, Var "x", Var "x"))) ;
  assert (subst ("y") (Num(3)) (exp_7) = Let ("x", Binop (Times, Num 3, Num 3), Binop (Plus, Var "x", Var "x"))) ;
  assert (subst ("x") (Var("y")) (exp_8) = Fun ("var0", Binop (Plus, Var "y", Var "var0"))) ;
  assert (subst ("n") (Num(4)) (exp_5) = exp_5) ;
  assert (subst ("x") (Num(42)) (exp_9) = Let ("x", Binop (Plus, Num 42, Var "y"), Binop (Times, Var "z", Var "x"))) ;
  assert (subst ("y") (Num(42)) (exp_9) = Let ("x", Binop (Plus, Var "x", Num 42), Binop (Times, Var "z", Var "x"))) ;;

(* eval_s tests *)
let eval_s_tests() =
  assert (eval_s (Num (3)) (Env.create()) = Env.Val (Num (3))) ;
  assert (eval_s (Binop (Plus, Num (3), Num (4))) (Env.create()) = Env.Val (Num (7))) ;
  assert (eval_s (exp_5) (Env.create()) = Env.Val (Num (24))) ;
  assert (eval_s (exp_2) (Env.create()) = Env.Val (Num (60))) ;
  assert (eval_s (Let ("x", Num(3), Let ("y", Binop (Times, Var "x", Var "x"), Var "y"))) (Env.create()) = Env.Val (Num (9))) ;
  assert (eval_s (Let ("x", Num(8), Conditional(Binop(Equals, Var "x", Num(3)), Num(1), Num(0)))) (Env.create()) = Env.Val (Num (0))) ;
  assert (eval_s (Let ("x", Bool(true), Conditional(Var("x"), Num(1), Num(0)))) (Env.create()) = Env.Val(Num(1))) ;
  assert (eval_s (App ((Fun ("x", Binop (Plus, Var("x"), Var("x")))), Num(5))) (Env.create()) = Env.Val (Num(10))) ;
  assert (eval_s (exp_10) (Env.create()) = Env.Val (Num(13))) ;
  
  (* floats *)
  assert (eval_s (exp_13) (Env.create()) = Env.Val (Float 13.)) ;
  assert (eval_s (exp_14) (Env.create()) = Env.Val (Float 24.)) ;;

(* Env Module tests *)
let env_mod_tests() =
  let env = Env.create() in
  let env = Env.extend env "x" (ref (Env.Val (Num (3)))) in
  let env = Env.extend env "y" (ref (Env.Val (Num (5)))) in
  assert (Env.lookup env "x" = Env.Val(Num (3))) ;
  assert (Env.lookup env "y" = Env.Val(Num (5))) ;
  assert (Env.env_to_string env = "{(y, 5); (x, 3)}") ;
  let env = Env.extend env "y" (ref (Env.Val (Bool (true)))) in
  assert (Env.lookup env "y" = Env.Val(Bool (true))) ;
  assert (Env.env_to_string env = "{(y, true); (x, 3)}") ;
  let closure = Env.close (exp_1) (env) in
  assert (Env.value_to_string closure = "[Expr: let x = 3 in let y = x in f (x (y)), Env: {(y, true); (x, 3)}]") ;
  let closure2 = Env.close (exp_2) (env) in
  assert (Env.value_to_string closure2 = "[Expr: let x = 30 in let x = let x = 3 in x * 10 in x + x, Env: {(y, true); (x, 3)}]") ;;

(* eval_d tests *)
let eval_d_tests() =
  assert (eval_d (exp_11) (Env.create()) = Env.Val (Num(5))) ;
  assert (eval_d (exp_12) (Env.create()) = Env.Val (Num(24))) ;
  assert (eval_d (exp_10) (Env.create()) = Env.Val (Num(13))) ;
  assert (eval_d (exp_5) (Env.create()) = Env.Val (Num (24))) ;

  (* floats *)
  assert (eval_d (exp_15) (Env.create()) = Env.Val (Float(5.))) ;
  assert (eval_d (exp_16) (Env.create()) = Env.Val (Float(24.))) ;;

(* eval_l tests *)
let eval_l_tests() =
  assert (eval_l (exp_11) (Env.create()) = Env.Val (Num(4))) ;
  assert (eval_l (exp_12) (Env.create()) = Env.Val (Num(40))) ;
  assert (eval_l (exp_10) (Env.create()) = Env.Val (Num(13))) ;
  assert (eval_l (exp_5) (Env.create()) = Env.Val (Num (24))) ;

  (* floats *)
  assert (eval_l (exp_15) (Env.create()) = Env.Val (Float(4.))) ;
  assert (eval_l (exp_16) (Env.create()) = Env.Val (Float(40.))) ;;

let _ =
  free_vars_tests() ;
  subst_tests() ;
  eval_s_tests() ;
  env_mod_tests() ;
  eval_d_tests() ;
  eval_l_tests() ;;