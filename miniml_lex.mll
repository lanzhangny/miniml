(* 
                         CS 51 Final Project
                      MiniML -- Lexical Analyzer

 *)

{
  open Printf ;;
  open Miniml_parse ;; (* need access to parser's token definitions *)

  let create_hashtable size init =
    let tbl = Hashtbl.create size in
    List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
    tbl

  let keyword_table = 
    create_hashtable 8 [
                       ("if", IF);
                       ("in", IN);
                       ("then", THEN);
                       ("else", ELSE);
                       ("let", LET);
                       ("raise", RAISE);
                       ("rec", REC);
                       ("true", TRUE);
                       ("false", FALSE);
                       ("lambda", FUNCTION);
                       ("fun", FUNCTION);
                       ("function", FUNCTION)
                     ]
                     
  let sym_table = 
    create_hashtable 8 [
                       ("=", EQUALS);
                       ("<", LESSTHAN);
                       (">", GREATERTHAN);
                       (".", DOT);
                       ("->", DOT);
                       (";;", EOF);
                       ("~-", NEG);
                       ("~-.", NEG_F);
                       ("+", PLUS);
                       ("+.", PLUS_F);
                       ("-", MINUS);
                       ("-.", MINUS_F);
                       ("*", TIMES);
                       ("*.", TIMES_F);
                       ("/", DIVIDE);
                       ("/.", DIVIDE_F);
                       ("(", OPEN);
                       (")", CLOSE)
                     ]
}

let digit = ['0'-'9']
let frac = "." digit*
let float = digit* frac? 
let id = ['a'-'z'] ['a'-'z' '0'-'9']*
let sym = ['(' ')'] | (['+' '-' '*' '.' '=' '~' ';' '<' '>' '/']+)

rule token = parse
  | digit+ as inum
        { let num = int_of_string inum in
          INT num
        }
  | float as fnum
        { let fl = float_of_string fnum in
          FLOAT fl
        }
  | id as word
        { try
            let token = Hashtbl.find keyword_table word in
            token 
          with Not_found ->
            ID word
        }
  | sym as symbol
        { try
            let token = Hashtbl.find sym_table symbol in
            token
          with Not_found ->
            printf "Ignoring unrecognized token: %s\n" symbol;
            token lexbuf
        }
  | '{' [^ '\n']* '}'   { token lexbuf }    (* skip one-line comments *)
  | [' ' '\t' '\n']     { token lexbuf }    (* skip whitespace *)
  | _ as c                                  (* warn and skip unrecognized characters *)
        { printf "Ignoring unrecognized character: %c\n" c;
          token lexbuf
        }
  | eof
        { raise End_of_file }
