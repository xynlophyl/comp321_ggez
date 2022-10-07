(* A parser and evaluator for a toy boolean language 
   Some defs set up for expansion to NB = boolean + arith language
   EXERCISE:  expand parser+evaluator to NB. Both small-step and 
              big-step evaluator.

   IMPORTANT: very useful hints provided below, identified with the words
    'YOUR TASK: '  and also  'ADD arith CASES HERE' or something
    similar

  Your work starts with 
  (1) expanding the type 'term', below ** TERM DEF STARTS HERE **

  then skip to:

  (2)
  the many mutually recursive parsing functions
  following ****** PARSER STARTS HERE ********, below. 
  (hints included there)

  (3)
  expand the def of is_a_value as indicated below
  and then 

  (4) expand eval_step to include arithmetic

  (5) expand the two big_step implementations

  (6) add a nice list of non-trivial examples, nicely labeled, to test
  your code to your satisfaction!
*)

(*
 *
 * concrete syntax:
 * tm --> if tm then tm else tm|true|false
 *
 *typical concrete syntax: 
 *  if (if true then false) then false else 
    (if true then false else (if true then false else false))
 

 * abstract syntax:
 * tm --> TmTrue|TmFalse|TmIf(tm,tm,tm)
 *
 * when extended to system (NB), it will be:
 * tm --> TmTrue|TmFalse|TmIf(tm,tm,tm)|TmZero|TmSucc(tm)|
 *        TmPred(tm)|TmIsZero(tm)
 *)

(* utility functions *)

(* converts a string to a list of chars: 
   stolen from SML because it's so handy *)
let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

(* list of chars to string *)
let rec implode l =
  match l with
  |[] -> ""
  |c::l1 -> let ch = String.make 1 c
            in
            ch^(implode l1);;



(* print a list of strings *)
let rec aux_print_list = function
  |[] -> print_string ""
  |(x::xs) -> (print_string x;print_string ":";aux_print_list xs);;

let print_list x =
  (print_string "<";aux_print_list x;print_string ">");;

(* boolean   **TERM DEF STARTS HERE**
 * YOUR TASK : add arith terms
*)
type term =
    TmTrue
  |TmFalse
  |TmIf of (term * term * term)
  |Tm0
  |TmSucc of (term)
  |TmPred of (term)
  |TmIszero of (term)
  |TmError;;

exception BAD_TERM of term;;

(* to display terms *)
exception NOT_A_VALUE;;
  
     


(* lexer: breaks up a string into a list of so-called tokens:
   "if true then false else (if true then false else true)" |-->
   ["if";"true";"then";"false";"else";"(";"if";"true";...]
 *) 

(* Here tokens just meant strings, but in many lexers, one transforms 
   a program to a list of more informative terms, 
   e.g. x |-->  ("x", VARIABLE) or ( |--> ("(",LPAREN)
   where VARIABLE and LPAREN are members of a new type called token
      token ::= LPAREN|RPAREN|VARIABLE|BOOLEAN_VALUE   etc.
 *)

(* alph x = true when char x is alphabetical 
   you can add new characters, e.g. '_', if you 
   want to allow underscores in variable names *)
let alph x = 
  let n = Char.code x in
  (96< n && n < 123) || n = 48;;


exception BAD_CHAR;;


(* token boundaries *)
let bdry x = (x='(') || (x= ')') ;;

(* accumulate characters until you reach a blank or a token boundary:
'e' ['l';'s';'e';'(';...] |--> ("else" ['('...])
 *)
let rec grab_chars_until_bdry ch rest =
  match rest with
    |[] -> (String.make 1 ch,rest)
    |(head::tail) ->
       if (head = ' ')
       then (String.make 1 ch,tail)
       else if (bdry head)
       then (String.make 1 ch,rest)
       else let (x,l) = (grab_chars_until_bdry head tail)
       in
	 ((String.make 1 ch)^x,l)
;;

(* char list |--> list of token strings *)
let rec aux_lexx chars =
  match chars with
    |[] -> []
    |(ch::rest) ->
       if (ch=' ')
       then aux_lexx rest
       else if (bdry ch)
       then (String.make 1 ch)::(aux_lexx rest)
       else if (alph ch)
       then
	 let (str, remainder) = grab_chars_until_bdry ch rest
	 in str::(aux_lexx remainder)
       else raise BAD_CHAR;;

(* explode input and apply aux_lexx to the result *)
let lexx x = aux_lexx (explode x);;
	
exception EMPTY;;
exception BAD_IF of string;;

(* ******************** PARSER STARTS HERE **************  *)

(* parser: expand to include arithmetic *)
(*
 * parse applies aux_parse to result of lexx.
 * aux_parse: string list -> term * string list
 * aux_parse calls aux_parse_subterm
 * which checks for parentheses and identifiers and 
 * calls aux_parse on de-parenthesized terms
 *)


(* aux_parse : string list -> term * string list = <fun> *)

(***************************YOUR TASK***********************************)
(* YOUR TASK : 
 *  (1) add the following cases to aux_parse tokens where it
 * says REMAINING CASES, below 

   |("pred"::rest) -> parse_pred rest
   |("succ"::rest) -> parse_succ rest
   |("iszero"::rest) -> parse_iszero

and then at the very end, remove the ;; and add definitions for the 
functions just named, using 'and' to connect them, as follows

and
   parse_pred rest = (* your code *)
and
   parse_succ rest = (* your code *)
and 
   parse_is_zero rest =  (* your code *)

finishing with -->  ;;

  (2) add, to aux_parse_subterm, the cases for the new atomic constant in
  arithmetic, e.g. 0. 
*)

let rec  aux_parse tokens = (* parse if..then..else terms *)
  match tokens with
  |[] -> raise EMPTY
  |("if"::rest) -> parse_if rest    (* I wrote _tokens_ instead of _rest_ :(  *)
  |("("::rest) -> parse_paren rest
  (* REMAINING CASES *)
  |("pred"::rest) -> parse_pred rest
  |("succ"::rest) -> parse_succ rest                    
  |("iszero"::rest) -> parse_iszero rest
  |x ->aux_parse_subterm x
and
  aux_parse_subterm tokens = (* handles atomic constants: true,false,etc *)
  match tokens with
    |[] -> raise EMPTY
    |("true"::tokens_rest) -> (TmTrue,tokens_rest)
    |("false"::tokens_rest) -> (TmFalse,tokens_rest)
    (* ADD REMAINING VALUE for arithmetic *)
    |("0"::tokens_rest) -> (Tm0,tokens_rest)                               
    |x -> ((print_list (["x = "]@x)); (TmError,[])) (* debug errors *)
and
  parse_if rest =
   (* find and parse the three subterms in IF *)
  let (t1,rest1) = aux_parse rest in
  match rest1 with
  |("then"::rest2) -> let (t2,rest3) = aux_parse rest2 in
    (match rest3 with
     |("else"::rest4) -> let (t3,rest5) = aux_parse rest4 in
       (TmIf(t1,t2,t3),rest5)
     |_ -> raise (BAD_IF "missing ELSE")
    )
  | _ -> raise (BAD_IF "missing THEN")
and
  parse_paren rest =
      let (tm, remainder) = aux_parse rest in
      if remainder = [] then raise EMPTY else                     
        let (tok_rparen::remainder_after_rparen) = remainder in
	(tm,remainder_after_rparen) (* throw away right parenthesis *)
and
  parse_pred rest =
  let (tm, remainder) = aux_parse rest in
  (TmPred(tm), remainder)
and
  parse_succ rest =
  let (tm, remainder) = aux_parse rest in
  (TmSucc(tm), remainder)
and
  parse_iszero rest =
  let (tm, remainder) = aux_parse rest in
  (TmIszero(tm), remainder)

(* parse:string -> term *)
let parse str =  fst (aux_parse (lexx str));;

(*** evaluation ***)

(* *********************** YOUR TASK : VALUES ****************************
 * the following functions identify which terms are values: 
 * YOUR TASK : expand to arithmetic,
 * 0 and succ nv, which requires a prior HELPER FUNCTION: is_a_num_value

let rec is_a_num_value x = etc. etc.

*)

let rec is_a_num_value x =
   match x with 
   |Tm0 -> true
   |TmSucc(tm) -> is_a_num_value tm
   |_ -> false

let is_a_value x = 
   match x with
   |TmTrue -> true
   |TmFalse -> true
   (* ADD NEW CASES  for arith HERE *)
   |Tm0 -> true
   |TmSucc(_) -> is_a_num_value x
   |x -> false;;



exception NO_RULE;;

(* single small step eval:
***********************
***************YOUR TASK : EXPAND TO INCLUDE arithmetic******** *)
(* eval_step:term -> term *)
let rec eval_step t =
  match t with
  |TmIf(TmTrue,t2,t3) -> t2
  |TmIf(TmFalse,t2,t3) -> t3
  |TmIf(t1,t2,t3) ->
     let t1' = eval_step t1 in
       TmIf(t1',t2,t3)
  |TmSucc(t1) ->
     let t1' = eval_step t1 in 
       TmSucc(t1')
  |TmPred(Tm0) -> Tm0
  |TmPred(TmSucc(t1)) when (is_a_num_value t1) -> t1 
  |TmPred(t1) ->
     let t1' = eval_step t1 in
       TmPred(t1')
  |TmIszero(Tm0) -> TmTrue
  |TmIszero(TmSucc(t1)) when (is_a_num_value t1) -> TmFalse
  |TmIszero(t1) ->
     let t1' = eval_step t1 in
       TmIszero(t1')

  |_ -> raise NO_RULE;;

(* and now,  the evaluation sequences it induces *)
(* eval : term -> term *)
let rec eval t =
  if (is_a_value t)
  then t
  else let t' = eval_step t in
    eval t';;

(* works for all normal forms, not just values *)
(* eval_all : term -> term *)
let rec eval_all t =
  try let t' = eval_step t
  in eval_all t'
  with NO_RULE -> t;;



(* **************big step******************* 
 * YOUR TASK :  expand to include arithmetic
*)

exception BAD_GUARD of term;; (* if statement with bad condition *)

let rec big_step t =
  match t with
    |TmTrue -> TmTrue
    |TmFalse -> TmFalse
    |TmIf(t1,t2,t3) when (big_step t1 = TmTrue) ->
	     big_step t2
    |TmIf(t1,t2,t3) when (big_step t1 = TmFalse) ->
       big_step t3
     (* ADD ARITH CASES HERE *)
    |TmSucc(t1) when (is_a_num_value (big_step t1)) ->
       TmSucc(big_step t1)
    |TmPred(t1) when (big_step t1 = Tm0) -> Tm0
    |TmPred(TmSucc(t1)) when (is_a_num_value (big_step t1)) ->
       big_step t1
    |TmPred(TmPred(t1)) when (is_a_num_value (big_step t1)) ->
        TmPred(TmPred(big_step t1))
    |TmIszero(t1) when (big_step t1 = Tm0) -> TmTrue
    |TmIszero(t1) when (is_a_num_value (big_step t1)) -> TmFalse
    | x when is_a_value(x) -> x
    |_ -> raise NO_RULE;;

(* doesn't raise exceptions *)
let rec ne_big_step t =
    match t with
    |TmTrue -> TmTrue
    |TmFalse -> TmFalse
    |TmIf(t1,t2,t3)  when (ne_big_step t1 = TmTrue) ->
       (ne_big_step t2)
    |TmIf(t1,t2,t3) when (ne_big_step t1 = TmFalse) ->
       (ne_big_step t3)
    |TmSucc(t1) when (is_a_num_value (ne_big_step t1)) ->
        TmSucc(ne_big_step t1)
    |TmPred(t1) when (ne_big_step t1 = Tm0) -> Tm0
    |TmPred(TmSucc(t1)) when (is_a_num_value (ne_big_step t1)) ->
        ne_big_step t1
    |TmIszero(t1) when (ne_big_step t1 = Tm0) -> TmTrue
    |TmIszero(t1) when (is_a_num_value (ne_big_step t1)) -> TmFalse
    |_ -> TmError;;  (* return an error term so as show a way to not raise an
                      * exception which aborts VScode *) 

(* some examples *)
print_string "\n\n******* SOME EXAMPLES ************";;
is_a_value TmTrue;;
is_a_value (TmIf(TmTrue,TmFalse,TmTrue));;

print_string "\nBIG STEP";;
big_step TmTrue;;
big_step (TmIf(TmTrue,TmFalse,TmTrue));;
big_step (TmIf(TmIf(TmTrue,TmFalse,TmTrue),TmTrue,TmFalse));;
eval (TmIf(TmIf(TmTrue,TmFalse,TmTrue),TmTrue,TmFalse));;



(* infix composition *)
let ($) f g x = f (g x);;

(* parse and then evaluate *)
print_string "\nPARSE examples";;

let eval_parse = eval $ parse;;  (* parses and then evaluates *)
let eval_all_parse = eval_all $ parse;;  (* same but returns values OR stuck states *)
let big_eval_parse = big_step $ parse;;  (* parses and then big_step evaluates *)
let ne_big_eval_parse = ne_big_step $ parse;; (* same with no-exception code *)


(* some examples to work with *)
(* example 0 : test parser *)
print_string "\nEx. *0*";;
parse "if (if (if true then false else (if true then false else true)) then true else false) then false else true";;

(* example 1 : parse and evaluate *)
print_string "\nEx. *1*";;
eval_parse "if (if true then false else true) then true else false";;

(* example 2 : parse and big-step evaluate *)
print_string "\nEx. *2*";;
big_eval_parse "if (if true then false else true) then false else true";;

(* example_3 : same with the exception-less ne_big_step *)
print_string "\nEx. *3*";;
ne_big_eval_parse "if (if true then false else true) then true else false";;

(* example 4 *)
print_string "\nEx. *4*";;
ne_big_eval_parse "if (if (if false then false else (if true then false else true)) then true else false) then false else true";;

print_string "\n";;

let pp = ne_big_step $ parse;;

(* example 5 : should raise an exception *)
print_string "\nEx. *5*";;
pp "if";; (* generates an exception *)
(*   !!!!!  NOTICE ===> so aborts in VScode. 
 * You can remove it when you add examples below *)


(* YOUR TASK : add interesting examples including arithmetic. include mixed
 * boolean and numerical: if (iszero (succ 0)) then succ(succ(0)) etc....  *)     

print_string "\narith example 1";;
parse "if (iszero (succ 0)) then succ(succ(0)) else succ(0)";;				  

eval_parse "if (iszero (succ 0)) then succ(succ(0)) else succ(0)";;				  


print_string "\narith example 2";;
eval_parse "succ 0";;

print_string "\narith example 3";;
big_eval_parse "pred 0";;

print_string "\narith example 4";;
ne_big_eval_parse "isZero( (pred(succ(pred(succ(0))))) )";;

print_string "\narith example 5";;
pp "if (iszero (pred(pred(succ(succ(0)))))) then succ(succ(0)) else succ(0)";;
big_eval_parse "if (iszero (pred(pred(succ(succ(0)))))) then succ(succ(0)) else succ(0)";;


print_string "\narith example 6";;
pp "succ (pp if (iszero (pred(pred(succ(succ(0))))) then succ(succ(0)) else pred(0))";;

