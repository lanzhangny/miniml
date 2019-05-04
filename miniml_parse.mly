/*
                         CS 51 Final Project
                           MiniML -- Parser
*/
                  
%{
  open Printf ;;
  open Expr ;;
%}

%token EOF
%token OPEN CLOSE
%token LET DOT IN REC
%token NEG NEG_F
%token PLUS PLUS_F MINUS MINUS_F
%token TIMES TIMES_F DIVIDE DIVIDE_F
%token LESSTHAN EQUALS GREATERTHAN
%token IF THEN ELSE 
%token FUNCTION
%token RAISE
%token <string> ID
%token <int> INT 
%token <float> FLOAT
%token TRUE FALSE

%nonassoc LESSTHAN GREATERTHAN
%nonassoc EQUALS
%left PLUS PLUS_F MINUS MINUS_F
%left TIMES TIMES_F DIVIDE DIVIDE_F
%left NEG NEG_F

%start input
%type <Expr.expr> input

/* Grammar follows */
%%
input:  exp EOF                 { $1 }

exp:    exp expnoapp            { App($1, $2) }
        | expnoapp              { $1 }

expnoapp: INT                   { Num $1 }
        | FLOAT                 { Float $1 }
        | TRUE                  { Bool true }
        | FALSE                 { Bool false }
        | ID                    { Var $1 }
        | exp PLUS exp          { Binop(Plus, $1, $3) }
        | exp PLUS_F exp        { Binop(Plus_f, $1, $3) }
        | exp MINUS exp         { Binop(Minus, $1, $3) }
        | exp MINUS_F exp       { Binop(Minus_f, $1, $3) }
        | exp TIMES exp         { Binop(Times, $1, $3) }
        | exp TIMES_F exp       { Binop(Times_f, $1, $3) }
        | exp DIVIDE exp        { Binop(Divide, $1, $3) }
        | exp DIVIDE_F exp      { Binop(Divide_f, $1, $3) }
        | exp EQUALS exp        { Binop(Equals, $1, $3) }
        | exp LESSTHAN exp      { Binop(LessThan, $1, $3) }
        | exp GREATERTHAN exp   { Binop(GreaterThan, $1, $3) }
        | NEG exp               { Unop(Negate, $2) }
        | NEG_F exp             { Unop(Negate_f, $2) }
        | IF exp THEN exp ELSE exp      { Conditional($2, $4, $6) }
        | LET ID EQUALS exp IN exp      { Let($2, $4, $6) }
        | LET REC ID EQUALS exp IN exp  { Letrec($3, $5, $7) }
        | FUNCTION ID DOT exp   { Fun($2, $4) } 
        | RAISE                 { Raise }
        | OPEN exp CLOSE        { $2 }
;

%%
