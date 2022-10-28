(* TEMPLATE FOR evaluating lambda+bool calculus *)
(* included: lexer + parser and small-step evaluators for 
 *lambda-calc+booleans, both
 * normal order and call-by-value 
 * MISSING: substition and evaluators for both strategies and
  some utility functions 
         no = Normal Order    cbv = Call By Value

THE Parts you have to complete are marked with a ===>
*)

(* required: implementation of 


-- subst
-- is_a_nf (determines whether or not a term is in normal form)
-- is_val (determines whether or not a term is a VALUE, i.e. an abstraction)
-- big_step_cbv

You only have to complete those pieces of code where it says 
'to be completed by YOU



-- is_a_nf:tm -> bool
that determines whether a lambda term is in normal form

At the bottom of the file are several utility functions to do
 * arithmetic with Church numerals. You should add some examples      
 * to compute, say  2+5, 15*3 3**4
 *)


(* lexer, parser and evaluator for the untyped lambda calculus + booleans*)
(* uses a single reference variable to keep track of fresh-variable renaming *)
(* note that 'if' has been reduced to a single word: no 'then', 'else' *)

(* concrete syntax
   lam -> x|lam lam|\\x.lam

   abstract syntax
   tm-> TmVar(string)|TmApp(tm,tm)|TmAbs(string,tm)

To this we add a lazy if
tm -> if tm tm tm |false|true
(I dropped the 'then' and 'else')

abstract syntax
tm -> TmIf(tm,tm,tm)|TmTrue|TmFalse
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

(* lambda terms *)
type term =
   TmVar of string
  |TmApp of (term * term)
  |TmAbs of (string * term)
  |TmTrue
  |TmFalse
  |TmIf of (term * term * term)
  |TmError (* for debugging *)

     

(* show:term -> string *)
let rec show tm =
  match tm with
    |(TmVar x) -> x
    |(TmApp(t1,t2)) -> "("^(show t1)^" "^(show t2)^")"
    |(TmAbs(x,t)) -> "(\\"^x^"."^(show t)^")"
    |TmIf(t1,t2,t3) -> "(if "^(show t1)^" "^(show t2)^" "^(show t3)^")"
    |TmTrue -> "true"
    |TmFalse -> "false"
    |TmError -> "TM_ERROR";;

 (* display_term: term -> string. shows term in
    abstract syntax form *)
let rec display_term tm =
   match tm with
    |(TmVar x) -> "TmVar"^"("^x^")"
    |(TmApp(t1,t2)) -> "TmApp("^(display_term t1)^","^(display_term t2)^")"
    |(TmAbs(x,t)) ->  "TmAbs("^x^","^(display_term t)^")"
    |TmIf(t1,t2,t3) -> "TmIf("^(display_term t1)^","^(display_term t2)^","^
			 (display_term t3)^")"
    |TmTrue -> "true"
    |TmFalse -> "false"
    |TmError -> "TM_ERROR";;

(* dt: term -> unit. Has side effect of printing the term in abstract
   syntax string form *)
let dt tm = print_string(display_term tm);;
  
 

(* lexer: breaks up a string into a list of tokens:

   \\x1.(\\x2.x1 x2) x1 |-->
   ["\\";"x1";".";"(";"\\";"x2";".";"x1";"x2";")";"x1"]
 *)

let print_term t = print_string (show t);;

(* test whether char x is alphanumerical--lower case with =, (, ), period, ; and : for later stuff *)
let alph x = 
  let n = Char.code x in
  94< n && n < 123 || 39<n && n <62;;


exception BAD_CHAR;;


(* token boundaries *)
let bdry x = (x='(') || (x= ')') || (x = '\\') || (x='.');;

(* accumulate characters until you reach a blank or a token boundary:
'e' ['l';'s';'e';'(';...] |--> ("else" ['('...])
 *)
let rec grab_chars_until_bdry ch rest =
  match rest with
    |[] -> (String.make 1 ch,rest)  (* 'String.make 1 x' takes char x to string x *)
    |(head::tail) ->
       if (head = ' ')
       then (String.make 1 ch,tail)
       else if (bdry head)
       then (String.make 1 ch,rest)
       else let (x,l) = (grab_chars_until_bdry head tail)
       in
	 ((String.make 1 ch)^x,l)
;;

(* String.make n c returns a fresh string of length n, filled with the
 * character c.*)



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
       else (print_char ch;print_string": ";raise BAD_CHAR);;

let lexx x = aux_lexx (explode x);;

(* end lexer *)

exception EMPTY of string
exception PAREN_EXCEPTION
exception BAD_TERM

  
(*  PARSER to deal with:
input: a list of strings (output by lexx)
output (t,ls) where t is a term and ls is the remaining list of
  unparsed strings that should be empty if the input represents a
  complete term 
*)

  (* in an application sequence "t1 t2 t3 ..." parseOneL will 
   only parse the first term and return the remainder as a string
   list *)

let rec parseOneL lt =
  match lt with
  |[] -> (TmError,[])
  |("true"::rest) -> (TmTrue,rest)
  |("false"::rest) -> (TmFalse,rest)
  |("("::rest) ->
    let (tm',rest') = (parseL rest) in
	 if rest'=[]
	 then
	    (TmError,[])
	 else
	     let (rparen::after_paren) = rest' in
	   (tm',after_paren)
  |("\\"::rest) -> parseL lt    
  |("if"::rest) ->    let (t1,rest1) = parseOneL rest in
		   let (t2,rest2) = parseOneL rest1 in
		   let (t3,rest3) = parseOneL rest2 in
		   (TmIf(t1,t2,t3),rest3)
  |(")"::t) -> raise PAREN_EXCEPTION (* for debugging *)
  |(s::t) -> (TmVar(s),t)

and (* this is for mutually recursive defs *)
    (* parseL is the top-level parser *)
  parseL lt =
  match lt with
  |[] ->(TmError,[])
  |["true"] -> (TmTrue,[])
  |["false"] -> (TmFalse,[])
  |("true"::rest) -> aux_parseA TmTrue rest
  |("false"::rest) -> aux_parseA TmFalse rest    
  |("("::rest) -> parse_paren rest (* parenthesized term *)
  |("\\"::rest) -> (* abstraction *)
    (match rest with
     |[] -> raise (EMPTY "after lambda")
     |(tok_var::"."::after_dot) ->  let (tm,rest') = (parseL after_dot) in
       aux_parseA (TmAbs(tok_var,tm)) rest'
     |(_::_::after_dot) -> raise (EMPTY "no dot")
     |[_] -> raise (EMPTY "nothing after \\var")
    )
  |("if"::rest) -> let (t1,rest1) = parseOneL rest in
		   let (t2,rest2) = parseOneL rest1 in
		   let (t3,rest3) = parseOneL rest2 in
		   aux_parseA (TmIf(t1,t2,t3)) rest3
  |(s::t) -> aux_parseA (TmVar(s)) t (* single var or application *)
  and
    (* grabs terms in an application one at a time and associates 
     *  applications to the left *)
  aux_parseA tm lt =
  match lt with
  |[] -> (tm,[])
  |("true"::rest) -> aux_parseA (TmApp(tm,TmTrue)) rest
                    
  |("false"::rest) -> aux_parseA (TmApp(tm,TmFalse)) rest
  |("("::rest) -> 
    let (tm',rest') = parseOneL lt in
    aux_parseA (TmApp(tm,tm')) rest'
  |("\\"::rest) ->
    let (tm',rest') = parseL lt in
    aux_parseA (TmApp(tm,tm')) rest'
  |("if"::rest) -> let (tm',rest') = parseOneL lt in
		   aux_parseA (TmApp(tm,tm')) rest'
  |(")"::t) -> (tm,lt)
  |[s] -> (TmApp(tm,TmVar(s)),[])
  |(s::t) ->
    (match t with
     |[] -> raise (EMPTY "body")
     |(a::t') when a = ")" -> (TmApp(tm,TmVar(s)),t)
     |(a :: t') -> (aux_parseA (TmApp(tm,TmVar(s))) t)
    )
and
  parse_paren rest =
  let (tm',rest') = (parseL rest) in
  match rest' with
  |[] -> raise  PAREN_EXCEPTION  (* error because there should have been at least a
                                    right parenthesis there*)
  |(")"::after_paren) -> aux_parseA tm' after_paren
  |_ -> raise BAD_TERM ;;
    


 	 
let parse text = fst (parseL (lexx text));;
let see_parse text = let (a,b) = parseL (lexx text) in
  (print_string (show a);print_string "--> ";print_list b);;

(* end parser *)

(********* EVALUATION *********)  

(* substitution into lambda terms *)

(* utility. Included just for fun. You don't need these.
   also List.mem is a built-in version of member
 *)
let rec member x lst =
  match lst with
      [] -> false
    |(y::ys) -> x=y || member x ys;;

(* eliminate repetitions in list *)
let rec elim_reps = function
  |[] -> []
  |(x::xs) -> if member x xs
    then elim_reps xs
    else x::(elim_reps xs);;

let rec union l1 l2 = elim_reps(l1@l2);;

(* return list lst with all occurrences of 'x' removed *)
let rec delete x lst =
  match lst with
      [] -> []
    |(y::ys) -> if (x=y)
      then delete x ys
      else y::(delete x ys);;
      

(* free_vars: term -> string list *)
let rec free_vars t =
  match t with
    |TmVar s -> [s]
    |TmAbs(x,t) -> let fvlist = free_vars t in
	delete x fvlist
    |TmApp(t1,t2) -> union (free_vars t1) (free_vars t2)
    |TmIf(t1,t2,t3)
      -> union (free_vars t1) (union (free_vars t2) (free_vars t3))
    |TmError -> []
    |_ -> []

(* end utility *)

(* rename free variables. newname is to be a fresh name.
   Therefore capture cannot occur, so we do not consider the problem.
    i.e. reame name newname tm REPLACES every free occurrence of name 
   by newname in tm, without trying to avoid capture. It must be used to
   define subst.
   rename:string -> string -> term -> term
 *)
let rec rename name newname tm =
  match tm with
  |TmTrue -> TmTrue
  |TmFalse -> TmFalse
  |TmVar s -> if(s=name)
      then TmVar newname
      else TmVar s
    |TmApp(t1,t2) ->
       TmApp(rename name newname t1, rename name newname t2)
    |TmAbs(x,t) ->
       if(x=name) then TmAbs(x,t)
       else TmAbs(x,rename name newname t)
    |TmIf(t1,t2,t3) ->
      let t1' = rename name newname t1 in
      let t2' = rename name newname t2 in
      let t3' = rename name newname t3 in
      TmIf(t1',t2',t3')
    |TmError -> TmError
		       

(* counter for fresh variables *)
let x = ref 0;;

  
(* used to generate fresh variable name: uses assignment *)
let make_fresh_var () =
  x := !x+1;
  "_x"^(string_of_int !x);;
	 
(* You may want to define the following function to 
   just rename all bound vars in a term with fresh names *)

(*rename_all_bd_with_fresh: term -> term *)
let rec rename_all_bd_with_fresh tm =
  match tm with
    TmVar x -> TmVar x
  |TmApp (u,v) -> TmApp ((rename_all_bd_with_fresh u),(rename_all_bd_with_fresh v))
  |TmAbs(varstring,u) -> let fresh = make_fresh_var () in
    let u' = rename varstring fresh u in
    TmAbs(fresh,rename_all_bd_with_fresh u')
  |t -> t

(*  ===> UNCOMMENT THIS SECTION BEFORE COMPLETING

 SUBSTITION
 ^^^^^^^^^^^: 
subst:string -> term -> term -> term
computes the result of substituting 's' (a term) for TmVar(var) in 'term'
AVOIDING CAPTURE
 *)
(* to be completed by YOU *)

let rec subst var s term = 
  match term with
  |TmTrue ->  TmTrue
  |TmFalse -> TmFalse
  |TmVar y -> if (y=var)
	      then s 
	      else term
  |TmApp(t1,t2) -> TmApp(subst var s t1, subst var s t2)
  |TmAbs(y,t) -> if (y=var)
        then TmAbs(y, t)
        else 
    (* here is where you must avoid capture by generating *)
                 (* a new var and renaming. Remember to check if y=var *)
  |TmIf(t1,t2,t3) ->
  |TmError -> TmError



(*  EVALUATION *)


(* Call By Value *)

exception NO_RULE;;
exception NO_RULE1;;
  
exception BAD_GUARD;;

(* ===> THE REST OF THE CODE WILL cause ERRORS, SINCE IT IS INCOMPLETE!!
for now it has been COMMENTED OUT! UNCOMMENT IT. *)

(* is a value*)
(* is_val: term -> bool *)
(* to be completed by YOU *)
let is_val tm = true (* you have to remove the true and write the code for this *)

(* computes one step of evaluation using call-by-value rules *)
  (* you need to complete this, using substitution for the redex case
   *  TmApp (TmAbs (x,t1),t2) when is_val t2 ->   *)

(* lots to fill in below

let rec eval_step_cbv t =
  match t with
  | TmIf(TmTrue,t1,t2) -> 
  | TmIf(TmFalse,t1,t2) -> 
  | TmIf(b,t1,t2) -> 
  | TmApp (TmAbs (x,t1),t2) when is_val t2 -> 
  | TmApp (t1,t2) when is_val t1 -> 
  | TmApp (t1,t2) -> 
  | _ -> raise NO_RULE;;

(* eval_cbv 
 * a value is an abstraction
 * *)
let rec cbv_eval t =
  try
    if is_val t then t else cbv_eval (eval_step_cbv t)
  with NO_RULE -> t
  

(* resets the free-variable counter to 0 before evaluating *)
let top_cbv_eval t =
  x:= 0;
  cbv_eval t



(* Normal order evaluation *)
s
(* tests whether or not input term is in normal form: to be completed by YOU.
TmTrue,TmFalse are considered normal forms *)
	   
let rec is_a_nf tm = 
  match tm with
  |TmTrue -> 
  |TmFalse ->
  |TmIf(v,_,_) -> (* only a normal form if v is a normal form and is
  NOT true or false, i.e. it's garbage *) 
  |TmVar( _ ) ->
  |TmApp(TmAbs(_,_),_) 
  |TmApp(v,w) -> (* careful *)
  |TmAbs(_,t) -> 


exception TM_ERROR
  
  (* one evaluation step in normal order: it will never be applied to
   * normal forms , hence the values true and false should return errors *)
let rec no_step tm = 
  match tm with
  (* you can delete the first two lines if you want, they don't 
   * really help *)
  |TmTrue -> raise TM_ERROR
  |TmFalse -> raise TM_ERROR
  |TmIf(TmTrue,t1,t2) ->
  |TmIf(TmFalse,t1,t2) -> 
  |TmIf(b,t1,t2) -> (* evaluate b for one step *)
  |TmAbs(x,t) -> (* evaluate t for one step. t can't be a normal form *)
  |TmApp(TmAbs(x,t),u) -> (* apply beta-reduction *)
  |TmApp(t1,t2) ->  (* t1 is not an abstraction: else this would have
  matched the preceding line *)
    if (is_a_nf t1)  
    then let t2'=no_step t2 in
	 TmApp(t1,t2')
    else
      let t1' = no_step t1 in
      TmApp(t1',t2)
  |v -> (print_string "===> ";print_string (show v);print_string "\n";raise NO_RULE);;

(* normal order evaluation *)
let rec no_eval t =
  if(is_a_nf t)
  then t
  else let t'=no_step t in
       no_eval t';;


(* resets fresh variable counter at start of computation *)
let top_no_eval t =
  x := 0;
  no_eval t;;

(* Put in tons of examples to test this stuff *)



(* I added some Church numeral utilities *)

(* make_num_body: nat -> term   2 |--> TmApp(TmVar("s"),TmApp(TmVar("s"),TmVar("z"))) *)
let rec make_num_body x =
  match x with
    |0 -> TmVar "z"
    |n -> TmApp(TmVar "s",make_num_body (n-1));;

(* num2church:nat --> term  2 |--> TmAbs("s",TmAbs("z",TmApp(TmVar("s"),TmApp(TmVar("s"),TmVar("z"))))) *)

let num2church x = TmAbs("s",TmAbs("z",make_num_body x));;

exception BAD_NUMERAL;;

(* convert Church numerals to integers *)
(* helper for next funtion *)
let rec translate_church_body s z x =
  match x with
    |TmVar(z) -> 0
    |(TmApp(f,t))  when (f=TmVar(s)) -> 1+(translate_church_body s z t)
    |_ -> raise BAD_NUMERAL;;

(* church2num:int -> Term *)
let church2num x =
  let x' = no_eval x in
  match x' with
  |(TmAbs(s,TmAbs(z,t))) -> translate_church_body s z t
  |_ -> raise BAD_NUMERAL;;


(* create +t1 t2 term in lambda caluclus *)
(* makeplus:int -> int -> term  *)
let makeplus t1 t2 =
  let t1' = num2church t1 in
  let t2' = num2church t2 in 
  let text_plus = "\\m.\\n.\\s.\\z.((m s) ((n s) z))" in
  let plus = parse text_plus in
    TmApp(TmApp(plus,t1'),t2');;

(* create * t1 t2 term in \-calculus *)
(* maketimes:int -> int -> term  *)
let maketimes t1 t2 =
  let t1' = num2church t1 in
  let t2' = num2church t2 in 
  let text_times = "\\m.\\n.\\z.(m (n z))"
  in let times = parse text_times in
    TmApp(TmApp(times, t1'),t2');;
	     
       

(***************)

(* create the term (exp t1 t2) *)
(* makeexp:int -> int -> term  *)
let makexp t1 t2 =
  let t1' = num2church t1 in
  let t2' = num2church t2 in
    TmApp(TmApp (TmAbs("x",TmAbs("y",TmApp(TmVar "y",TmVar "x"))),t1'),t2');;
	     

(* create (succ t) *)
(* makesucc:int -> Term *)
let makesucc t =
  let t' = num2church t in
  let succ = (parse "\\n.\\s.\\z.(s ((n s) z))") in
    TmApp(succ,t');;

(* testing *)
print_string "some tests of the code : add your own examples"
let l1 = "(\\x.\\y.x (\\x.x)) (y x)";;
let t1 = parse l1;;

rename_all_bd_with_fresh t1;;
*)


