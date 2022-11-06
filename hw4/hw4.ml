(* Parsing+eval+type inference for TYPED BH (Bool+Arith) *)

(* READ THE FILE AS A GOOD REVIEW FOR TEST *)

(* YOU *ONLY* HAVE TO COMPLETE THE FEW (commented out) LINES CLOSE TO THE END
 * to define *type inference* where it says 
 * *COMPLETE THIS CODE* 5-10 minutes of coding!!
 * let rec typeof tm = etc.
 * The examples at the end will return errors until *typeof* is implemented
*)

(* *************PRELIMINARY stuff*************** *)

(* DEF of TYPES AND TERMS *)
(*abstract syntax
ty -> TyBool|TyNat|TyArr(ty,ty)
tm -> TmIf(tm,tm,tm)|TmTrue|TmFalse|TmIsZero(Tm)|TmZero|TmSucc(tm)|TmPred(Tm)
*)

(* utility functions *)

(* explode:string -> char list  *)
let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;


let rec aux_print_list = function
  |[] -> print_string ""
  |(x::xs) -> (print_string x;print_string ":";aux_print_list xs);;

(* print list of strings *)
let print_list x =
  (print_string "<";aux_print_list x;print_string ">");;

(* DEFINITION OF TYPES *)
type ty =
  TyBool
  |TyNat;;

exception TYPE_ERROR;;
  
(* bool+arith terms *)
type term =
  TmTrue
  |TmFalse
  |TmIf of (term * term * term)
  |TmIsZero of term
  |TmZero
  |TmSucc of term
  |TmPred of term;;

(* to display terms *)

(* show:term -> string *)
let rec show x =
  match x with
  |TmTrue -> "true"
  |TmFalse -> "false"
  |TmIf(t1,t2,t3) -> "(if "^(show t1)^" then "^(show t2)^" else "^(show t3)^")"
  |TmZero -> "0"
  |TmSucc(t1) -> "(succ "^(show t1)^")"
  |TmPred(t1) -> "(pred "^(show t1)^")"
  |TmIsZero(t1) -> "(isZero "^(show t1)^")";;

let print_value x = print_string (show x);;

(* is a numerical value *)
let rec nv v =
  match v with
  |TmZero -> true
  |TmSucc(x) -> nv x
  |_ -> false

let is_a_value x = 
  x = TmTrue || x = TmFalse ||nv x;;
(* alph x = true when char x is lower case alphabetical
   you can add new characters, e.g. '_', if you 
   want to allow underscores in variable names *)

let alph x = 
  let n = Char.code x in
  (96< n && n < 122);;

(* in case you want to distinguish alphanumerics from alphabeticals. 
 * not needed now. When we use variables it will 
 * allow a 0 or a 1 in a variable name.
*)
let alph_num x =
  alph x || List.mem x ['0';'1'];;


  
exception BAD_CHAR
exception BAD_IDENT


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
       else if (alph_num ch)
       then
	 let (str, remainder) = grab_chars_until_bdry ch rest
	 in str::(aux_lexx remainder)
       else raise BAD_CHAR;;

(* explode input and apply aux_lexx to the result *)
let lexx x = aux_lexx (explode x);;
	

(* parser: expand to include arithmetic *)
(*
 * parse applies aux_parse to result of lexx.
 * aux_parse: string list -> term * string list
 * it checks for parentheses and identifiers and 
 * calls helper parsers on de-parenthesized terms
 * aux_parse calls parse_if,parse_succ,parse_pred,parse_iszero
 * which calls aux_parse on on the arguments
 *)
(* aux_parse : string list -> term * string list = <fun> *)

exception DANGLING_PAREN;;
exception DANGLING_SUCC;;
exception DANGLING_PRED;;
exception DANGLING_ISZERO;;
exception DANGLING_IF;;
exception DANGLING_THEN;;
exception DANGLING_ELSE;;

exception BAD_TOKEN;;
exception NO_TOKEN;;


(* aux_parse:string list -> term*string list *)
let rec   aux_parse tokens = (* parse if..then..else terms *)
  match tokens with
  |[] -> raise NO_TOKEN
  |("("::rest) ->
    if snd (aux_parse rest) = []
    then raise DANGLING_PAREN
    else
      let (tm, remainder) = aux_parse rest in
      let (tok_rparen::remainder_after_rparen) = remainder in
	(tm,remainder_after_rparen) (* throw away right parenthesis *)
  |("true"::rest) -> (TmTrue,rest)
  |("false"::rest) -> (TmFalse,rest)
  |("0"::rest) -> (TmZero,rest)
  |("if"::rest) -> parse_if rest
  |("succ"::rest) -> parse_succ rest
  |("pred"::rest) -> parse_pred rest
  |("isZero"::rest) -> parse_iszero rest
  |_ -> raise BAD_TOKEN
and
  parse_if x =
  match x with
  |[] -> raise DANGLING_IF
  |rest ->
    let (t1, rest1) = aux_parse rest in
    if rest1=[] then raise DANGLING_THEN else
      let (tok_then::rest_then) = rest1 in (* throw away then *)
      let (t2, rest2) = aux_parse rest_then in
      if rest2=[] then raise DANGLING_ELSE else
      let (tok_else::rest_else) = rest2 in (* throw away else *)
      let (t3,rest3) = aux_parse rest_else
      in (TmIf (t1,t2,t3),rest3)
and
  parse_succ x =
  match x with
  |[] -> raise DANGLING_SUCC
  |rest -> let (t1,rest1) = aux_parse rest in
    (TmSucc(t1),rest1)
and
  parse_pred x =
  match x with
  |[] -> raise DANGLING_PRED
  |rest -> let (t1,rest1) = aux_parse rest in
    (TmPred(t1),rest1)
and
  parse_iszero x =
  match x with
  |[] -> raise DANGLING_ISZERO
  |rest -> let (t1,rest1) = aux_parse rest in
    (TmIsZero(t1),rest1);;


(* parse:string -> term *)
let parse str =  fst (aux_parse (lexx str));;

(*** evaluation ***)

(* recognize numerical values *)
let rec is_nv x =
  match x with
  |TmZero -> true
  |TmSucc(t) ->  is_nv t
  |_ -> false;;

let is_a_value x = 
   match x with
   |TmTrue -> true
   |TmFalse -> true
   |v when is_nv v -> true
   |_ -> false

exception NO_RULE of string;;

(* single small step eval EXPAND TO INCLUDE arithmetic *)
let rec eval_step t =
  match t with
  |TmIf(TmTrue,t2,t3) -> t2
  |TmIf(TmFalse,t2,t3) -> t3
  |TmIf(t1,t2,t3) ->
     let t1' = eval_step t1 in
     TmIf(t1',t2,t3)
  |TmSucc(t) when not (is_a_value t) ->
    let t' = eval_step t in
    TmSucc(t')
  |TmPred(t') when t = TmZero -> TmZero
  |TmPred(t1) -> (match t1 with TmSucc(t2) when (is_nv t2) -> t2
             |TmSucc(t2) when is_a_value t2 -> raise (NO_RULE (show t))
             |_ ->let t2 = eval_step t1 in 
             TmPred(t2))
  |TmIsZero(t1) when t1 = TmZero -> TmTrue
  |TmIsZero(t1) -> (match t1 with
      |TmSucc(t') when is_nv t'-> TmFalse
      |x-> let x' = eval_step x in
        TmIsZero(x'))
  |_ -> raise (NO_RULE (show t));;

(* and now, the evaluation sequence it induces *)

let rec eval t =
  try 
    let t' = eval_step t in
    eval t'
  with NO_RULE _ -> t
;;

(* returns all normal forms, not just values *)

let rec eval_all t =
  try
    let t' = eval_step t
    in eval_all t'
  with (NO_RULE _) -> t

(* example of use

eval (parse "if (if (if true then false else (if true then false else true)) then true else false) then false else true");;
- : term = TmTrue
*)

(* big step *)
    
exception BAD_GUARD (* if statement with bad condition *)

let rec big_step t =
  match t with
    |TmTrue -> TmTrue
    |TmFalse -> TmFalse
    |TmIf(t1,t2,t3) ->
       if (big_step t1 = TmTrue) then
	 big_step t2
       else
	 if (big_step t1 = TmFalse)
	 then big_step t3
	 else raise BAD_GUARD
    |_ -> raise (NO_RULE (show t));;

(* slightly slicker *)
let rec ss_big_step t =
    match t with
    |TmTrue -> TmTrue
    |TmFalse -> TmFalse
    |TmIf(t1,t2,t3)  when (ss_big_step t1 = TmTrue) ->
       (ss_big_step t2)
    |TmIf(t1,t2,t3) when (ss_big_step t1 = TmFalse) ->
       (ss_big_step t3)
    |_ -> raise (NO_RULE (show t));;

(* some examples *)
print_string "\n\n******* SOME EXAMPLES ************";;
is_a_value TmTrue;;
is_a_value (TmIf(TmTrue,TmFalse,TmTrue));;
big_step TmTrue;;
big_step (TmIf(TmTrue,TmFalse,TmTrue));;
big_step (TmIf(TmIf(TmTrue,TmFalse,TmTrue),TmTrue,TmFalse));;
eval (TmIf(TmIf(TmTrue,TmFalse,TmTrue),TmTrue,TmFalse));;
eval (parse "if (if (if true then false else (if true then false else true)) then true else false) then false else true");;
						  
let t1 =  "if (if (if true then false else (if true then false else true)) then true else false) then false else true";;

parse t1;;



(* infix composition associated to the right *)
let ($) f g x = f (g x)

(* parse and then evaluate *)
let eval_parse = eval $ parse;;
let eval_all_parse = eval_all $ parse;;
let big_eval_parse = big_step $ parse;;
let ss_big_eval_parse = ss_big_step $ parse;;


(* some examples to work with *)

eval_parse "if (if true than false else true) then false else true";;
big_eval_parse "if (if true than false else true) then false else true";;
ss_big_eval_parse "if (if true than false else true) then false else true";;

ss_big_eval_parse "if (if (if true then false else (if true then false else true)) then true else false) then false else true";;
    
let ppbig = print_value $ ss_big_step $ parse;;
let pp = print_value $ eval_parse;;


pp "if (if (if true then false else (if true then false else true)) then true else false) then false else true";;


pp "if";; (* generates a match failure *)
(print_string "if-then fail==>";pp "if isZero (succ 0) then 0");;


(* add examples including arithmetic *)     

print_string "\n************ arith ************\n\n";;

let sta1 =  "if (if (if true then succ(succ(succ 0)) else (if isZero(succ(0)) then 0 else succ(0))) then true else false) then 0 else succ(0)";;

let ta1 = parse sta1;;

let sta2 =  "if (if isZero(if true then succ(succ(succ 0)) else (if isZero(succ(0)) then 0 else succ(0))) then true else false) then 0 else succ(0)";;

let ta2 = parse sta2;;
  
(pp sta2;print_string "\n (succ 0) expected\n");;
(print_string "\n EXC expected ===> ";pp sta1);;


pp "succ (succ (succ 0))";;

(* type inference *)
(* COMPLETE THIS CODE *)

let rec typeof tm =
  match tm with
  |TmTrue -> TyBool
  |TmFalse -> TyNat
  |TmIf(b,t1,t2) when typeof b = TyBool ->(* what's required for this to have a type? *)
    if (typeof t1 = typeof t2)
      then typeof t1 
    else raise (TYPE_ERROR)
  |TmIsZero t1 when typeof t1 = TyNat -> TyBool
  |TmZero -> TyNat
  |TmSucc t1 when typeof t1 = TyNat -> TyNat
  |TmPred t1 when typeof t1 = TyNat -> TyNat
  |_ -> raise (TYPE_ERROR);;

(* testing type inference *)

typeof ta2;; (* TyNat *)

let st4 = "if (if (if true then false else (if true then false else true)) then true else false) then false else true";;

let ta4 = parse st4;;

typeof ta4;; (* TyBool *)

let st5 = "if succ 0 then 0 else succ 0";;
let ta5 = parse st5;;

pp st5;;
typeof ta5;; (* should return a type error exception *)

