(* *********final 321 fall 2022*******************************
    GROUP: ggez
    Andres Cojuangco acojuangco@wesleyan.edu
    Stanley Markman smarkman@wesleyan.edu
    Nelson Lin nlin01@wesleyan.edu
    Skye Gao sgao01@wesleyan.edu
  ********************************************************* *)

(* The ocaml types we have to define *)
(* 1: UNTYPED lambda terms *)
type term =
   TmVar of string
  |TmApp of (term * term)
  |TmAbs of (string * term)  


(* 2: TYPE EXPRESSIONS: like A1 -> A2  *)
type arrow_type = Var of string
                |Arr of (arrow_type*arrow_type)

(* 3: TYPED lambda terms *)
type tylam = TyVar of string|TyApp of (tylam*tylam) |
             TyAbs of (string*arrow_type*tylam);;

(* 4: Equations *)
type eqn = Eq of (arrow_type*arrow_type)


(* to convert these objects to human-readable strings *)
let rec show tm =
  match tm with
    |(TmVar x) -> x
    |(TmApp(t1,t2)) -> "("^(show t1)^" "^(show t2)^")"
    |(TmAbs(x,t)) -> "(\\"^x^"."^(show t)^")";;

let sshow tm = print_string (show tm);;

(* convert type expressions into strings *)
let rec showtype ty =
  match ty with
  |Var(y) -> y
  |Arr (t1,t2) -> "("^(showtype t1)^"->"^(showtype t2)^")"

(* convert typed lambda calculus terms to strings *)
let rec showtylam tylm =
  match tylm with
    |TyVar y -> y
    |TyApp (t1,t2) -> "("^(showtylam t1)^" "^(showtylam t2)^")"
    |TyAbs (s,a,t) -> "("^"\\"^s^":"^(showtype a)^"."^(showtylam
                                                         t)^")"

(* contexts are never defined as a type. They are just lists of
 * (variable_string,arrow_type) pairs [(x,a);(y,b);...]
*)
(* convert contexts to strings *)
let rec show_ctx ctx =
  match ctx with
  |[] -> ""
  |[(x,tyx)] ->  x^":"^(showtype tyx)^" "
  |((x,tyx)::k) -> x^":"^(showtype tyx)^","^(show_ctx k)

(* create a judgment string
\Gamma |- t: T
 *)
let show_judgment ctx tytm ty =
  (show_ctx ctx)^" |- "^ (showtylam tytm)^" : "^(showtype ty)



(* convert equations to strings *)
let showeq eq =
  match eq with
    Eq(t1,t2) -> (showtype t1)^"="^(showtype t2)

(* convert lists of equations to strings *)
let rec showeq_list eqlist =
  match eqlist with
  |[] -> ""
  |[Eq(t1,t2)] -> showeq (Eq(t1,t2))
  |(e::es) -> (showeq e)^","^(showeq_list es)
                          
(* lexer and parser for the lambda calculus *)
(* from older programs *)
(* new stuff starts where it says *type inference* below *)

(* NOW: LEXING AND PARSING *)


(* utility functions *)

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

let implode l =
  let res = Bytes.create (List.length l) in
  let rec imp i = function
  | [] -> res
  | c :: l -> res.[i] <- c; imp (i + 1) l in
  imp 0 l;;

let rec aux_print_list = function
  |[] -> print_string ""
  |(x::xs) -> (print_string x;print_string ":";aux_print_list xs);;

(* print list of strings *)
let print_list x =
  (print_string "<";aux_print_list x;print_string ">");;


      (* lexer: breaks up a string into a list of tokens:
   "if true then false else (if true then false else true)" |-->
   ["if";"true";"then";"false";"else";"(";"if";"true";...]
      *)



(* char x is alphabetical *)
let alph x =
  let n = Char.code x in
  94< n && n < 123 || 47<n && n <58;;


exception BAD_CHAR;;


(* token boundaries *)
let bdry x = (x='(') || (x= ')') || (x = '\\') || (x='.') || (x = '@');;

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

exception PAREN_EXCEPTION;;
exception LAMBDA_EXCEPTION;;
exception EMPTYLIST;;
exception ERROR of string;; (* the string explains the error *)

(* messy parser to deal with:
  1.- eliminating left recursion in t-> x|\x.t|tt
  2.- left associativity of application
input: a list of strings (output by lexx)
output (t,ls) where t is a term and ls is the remaining list of tokens
that should be empty if the input represents a complete term
*)

  (* in an application sequence "t1 t2 t3 ..." parseOneL will
   only parse the first term and return the remainder as a string list *)
let rec parseOneL lt =
  match lt with
  |[] -> raise EMPTYLIST
  |("("::rest) ->
    let (tm',rest') = (parseL rest) in
    (match rest' with
	 [] -> raise PAREN_EXCEPTION
     |(rparen::after_paren) ->
       (tm',after_paren)
    )
  |("\\"::rest) -> parseL lt
  |(")"::t) -> raise PAREN_EXCEPTION
  |(s::t) -> (TmVar(s),t)

  and
    (* parseL is the top-level parser *)
  parseL lt =
  match lt with
    |[] -> raise EMPTYLIST
    |("("::rest) ->  (* parenthesized term *)
    let (tm',rest') = (parseL rest) in
    if rest'=[]
    then
      raise (ERROR "nothing after lparen")
    else
      (match rest' with
       |[] -> raise PAREN_EXCEPTION  (* error because there should
                  have been at least a right parenthesis there*) 
       |(rparen::after_paren) ->
      aux_parseA tm' after_paren)
  |("\\"::rest) -> (* abstraction *)
    (match rest with
       [] -> raise LAMBDA_EXCEPTION
     |[tok_var] -> raise LAMBDA_EXCEPTION
     |[tok_var;tok_dot] -> raise LAMBDA_EXCEPTION
     |(tok_var :: tok_dot::after_dot) -> 
    let (tm,rest') = (parseL after_dot) in
    aux_parseA (TmAbs(tok_var,tm)) rest')
   |(s::t) -> aux_parseA (TmVar(s)) t (* single var or applocation *)
  and
    (* grabs terms one at a time and associates applications to the left *)
  aux_parseA tm lt =
  match lt with
  |[] -> (tm,[])
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
  |(s::a::t') ->
    if a=")"
    then (TmApp(tm,TmVar(s)),a::t')
    else aux_parseA (TmApp(tm,TmVar(s))) (a::t')

(* end parser *)


let parse text = fst (parseL (lexx text));;
let see_parse text = let (a,b) = parseL (lexx text) in
  (sshow a;print_string "--> ";print_list b);;



(* counter for fresh variables *)
let x = ref 0;;

exception FAIL




  (* ********************** type inference ******* *)


(* manipulation of SUBSTITUTIONS *)
(* substitutions look like this:
[X1 -> T1,...,Xn->Tn]
formalize them as lists of pairs of terms
 *)
type subst =  (arrow_type*arrow_type) list


(* showsub: (arrow_type*arrow_type) list -> string *)
(* turn substitutions into strings that look like this
x1 -> T1,...,Xn-> Tn
*)
    
(* is_subL eq list -> bool *)
let rec is_sub eqlst =
  match eqlst with
    [] -> true
  |((Var(x),ty2) ::rest) -> is_sub rest
  |_ -> false;;

exception NOT_SUB;;
(* showsub:subst -> string *)
let rec showsub sub =
  if (is_sub sub)
  then       
  (match sub with
  |[] ->""
  |(Var x,ty)::rest -> x^" = "^(showtype ty)^","^(showsub rest)
  |_ -> raise NOT_SUB)
  else raise NOT_SUB;;





(* utility: member *)
let member x l = List.mem x l

(* get:arrow_type -> subst -> term
   apply only to type vars, and
   retrieve value of var in sub
 *)
let rec get x s =
  match s with
      [] -> x
    |((Var y),tm)::ys ->
       (match x with
         |(Var z) when z = y -> tm
         |(Var z) -> get x ys
         |_ -> raise NOT_SUB)
    |_ -> raise NOT_SUB;;

       

(* apply:subst -> arrow_type -> arrow_type *)
(* This means apply a type-substitution to a type expression *)
let rec apply sub ty =
  match ty with
  | (Var x) -> get (Var x) sub
  | (Arr(a1,a2)) -> Arr(apply sub a1,apply sub a2);;
                        

(* apply2term: subst -> tylam -> tylam *)
(* apply a type substitution to a typed lambda term *)
let rec apply2term sub tytm =
  match tytm with
  |(TyVar(x)) -> TyVar(x)
  |(TyApp(t1,t2)) -> TyApp(apply2term sub t1,apply2term sub t2)
  |(TyAbs(x,tyx,t)) -> let a = apply sub tyx in
		       let t' = apply2term sub t in
    TyAbs(x,a,t');;


(* apply a subst to single equation *)

let apply_eq sub (Eq(t1,t2)) =
    Eq(apply sub t1, apply sub t2)

(* apply_to_list APPLIES A SUBST to a list of equations:
 * apply_to_list:subst eqn list -> eqn list *)
let rec  apply_to_list sub lst =
  match lst with
    |  [] -> []
    | (Eq(t1,t2)::rest) ->
	(apply_eq sub (Eq(t1,t2)))::(apply_to_list sub rest)


(* composition of substitutions, ultimately defined as infix $ *)
(* USE the infix $, NOT the word 'compose' *)


(* remove:term list -> sub -> sub
   use: remove (list_of_vars_as_strings,subst) = subst with all
         bindings for variables in the list_of_vars removed
   e.g. utop[34]> remove ["A1"] [(Var("A1"),(Var("B")));(Var("A2"),(Var("B")))];;
- : (arrow_type * arrow_type) list = [(Var "A2", Var "B")]

  We start with 4 helper functions needed to define compose
 *)

let rec remove lst sub =
  match (lst,sub) with
    | ([],sub) -> sub
    | (list_of_vars, []) -> []
    | (list_of_vars, ((Var(y),tm):: bindings)) ->
      if member y list_of_vars
      then remove list_of_vars bindings
      else (Var y,tm)::(remove list_of_vars bindings)
    |_ -> raise NOT_SUB;;



let rec domain lst =
  match lst with
    |[] -> []
    | ((Var y,t)::xs) -> y::(domain xs)
    |_ -> raise NOT_SUB;;

(* remove_ids: sub -> sub
   remove all trivial bindings of the form (x,x)
*)
let rec remove_ids lst =
  match lst with
    |[] -> []
  | ((y,t)::xs) ->
    if y=t
    then remove_ids xs
    else ((y,t)::(remove_ids xs));;

(* apply_to_range: sub -> sub -> sub
   apply 2nd argument to values of bindings in 1st arg
  e.g. sub{(x1,t1),...} |===>  {(x1,(sub t1)),...}
*)
let rec apply_to_range lst sub =
  match lst with
    |[] -> []
  | ((y,t)::xs) ->
    ((y,(apply sub t))::(apply_to_range xs sub));;

(* compose: subst -> subst -> subst *)
let rec compose sub1 sub2 =
  let dom = domain sub1 in
  let sub1_sub2_applied = apply_to_range sub1 sub2 in
  let clean_sub2 = remove dom sub2 in
  let s12 = sub1_sub2_applied@clean_sub2
  in
    remove_ids s12

(* USE THE INFIX DOLLAR SIGN TO compose substitutions, instead of the
 * function COMPOSE
 *)
let ($) x y = compose x y;;

(* occurs: CHECKS TO SEE if an equation of the form 
 * A =  arrow_type 
 * has an occurrence of A on the right, which will cause FAILURE in
 * the unification algorithm. *)

let rec occurs x t =
  match (x,t) with
    |(Var z, Var u) -> z=u
    |(Var z, Arr(t1,t2)) -> occurs x t1 || occurs x t2
    |_ -> false

(* if you want to raise an exception which displays a pair of type
 * expressions that caused trouble *) 
exception ERR of (arrow_type * arrow_type)

(* unify a list of equations: you must FINISH two of the cases *)
let rec unify lst =
  match lst with
      [] -> []
  | (Eq(x,y)::rest) when x=y -> unify rest(* you FINISH this. Just skip this
                                 * identity equation *)
  | (Eq(Var(x),t)::rest) when occurs (Var(x)) (t) -> raise FAIL
  | (Eq(Var(x),t) :: rest) -> [(Var(x),t)] $ (unify (apply_to_list [(Var(x),t)] rest)) (* FINISH: x does NOT OCCUR in t so COMPOSE
       * the subst [(Var(x),t)] with UNIFY the result of applying  [(Var(x),t)]
                                 * to the rest of the list
                                *)
        
  | (Eq(t,Var(x))::rest) -> unify (Eq(Var(x), t)::rest)
  | (Eq (Arr(a1,a2),Arr(b1,b2))::rest)
    -> (unify [Eq(a1,b1);Eq(a2,b2)]) $ (unify rest)
  |_ -> raise FAIL;;


let sub2string sub =
  "["^(showsub sub)^"]";;

exception NO_TYPED_TERM;;

(* decorate untyped lambda terms with type variables *)


let x = ref 0

let make_new_var () =
  x:=!x+1;
  "A"^(string_of_int !x)

(* decorate:term -> tylam
   the first step in type inference. 
   FINISH
   USE make_new_var() *)
let rec decorate tm =
  x:=0;
  match tm with
    |(TmVar y) -> TyVar y
    |(TmApp (t1,t2)) -> TyApp(decorate t1, decorate t2)
    |(TmAbs (y,t)) -> TyAbs(y, Var(make_new_var()), decorate t)


exception ARROW_TYPE_EXPECTED
exception VAR_NOT_IN_CONTEXT
exception ERROR of string


(* lookup the value of a variable in a context [(x,a),(y,b)...] *)
let rec look varstring ctx =
  match ctx with
    |[] -> raise (ERROR ("no type for "^varstring^" in context."))
    |((s,a)::rest) -> if (s=varstring) then a
      else look varstring rest;;

(* compute the type of a simply typed lambda term in a given context *)

let rec typeof ctx tylm =
  match tylm with
  |(TyVar y) -> look y ctx
  |(TyApp (t1,t2)) -> 
    (match typeof ctx t1 with
      | Arr(ty_11, ty_12) -> let ty_2 = typeof ctx t2 in
        if ty_11 = ty_2
        then ty_12
        else raise (ERROR ("invalid input type; term is untypable."))
      | _ -> raise ARROW_TYPE_EXPECTED)
  |TyAbs (s,a,t) -> Arr(a, typeof ((s,a)::ctx) t)
  |_ -> raise (ERROR ("invalid input type; term is untypable."));;



(*
make_constraints: context -> tylam -> arrow type -> eqn list
i.e.
(string * arrow_type) list -> tylam -> arrow_type -> eqn list

 * takes a DECORATED judgment: \Gamma |- tylam : ty  and generates a list of
 * equations between types to be unified. This will be passed to
 * unify, below.
 * IT traverses the proof tree above the decorated starting judgment
 * The exceptions shouldn't happen. Just for debugging.
*)
let rec make_constraints ctx tylm ty =
  match tylm with
  |TyVar y -> [Eq((look y ctx), ty)]
  |TyApp(t1,t2) ->                  
    let new_ty = Var(make_new_var()) in
    List.concat [make_constraints ctx t1 (Arr(new_ty, ty)) ;
                 make_constraints ctx t2 new_ty]
  |TyAbs(x,tyx,t) ->
    (match ty with
     | Arr(inp, outp) ->
       (Eq(inp, tyx))::(make_constraints ((x, tyx)::ctx) t outp)
     | Var(abs_t) -> let new_ty = Var(make_new_var()) in
       (Eq(Var(abs_t), Arr(tyx,new_ty)))
       ::(make_constraints ((x, tyx)::ctx) t new_ty)
     | _ -> raise (ERROR("???")))
  |_ -> raise (ERROR "For lambda arrow ONLY");;
    

(* THE BIG DADDY: the top level type inference function *)

(* FINISH!  what do do: 
 * let type_inf ctx str = [[followed by 5 let terms]]
 * 1: parse the string. Creates an untyped lambda term t1
 * 2: decorate the result. Creates a typed lambda term t2
 * 3: let u  =  make_constraints [] t2 (Var("A")) in
 * 4: unify u. Call the resulting subst u'
 * 5: Apply this subst to t2 (so the types are now correct) to get t'
 * 6: show your work! use show_judgment using ctx and t' and at the
 *      end the actual type of the whole term using typof
 *)

let type_inf ctx str =  (* FINISH IT *)
  let t1 = parse str in 
  let t2 = decorate t1 in 
  let u = make_constraints [] t2 (Var("A")) in
  let u' = unify u in 
  let t' = apply2term u' t2 in
  show_judgment ctx t' (typeof ctx t');;

(* tests *)
print_string "\n******************* TESTS *************\n";;
print_string "(* A QUICK TEST *)";;
print_string "qtest 1 \n";;
let t1 = (parse "\\x.\\y.x y") in 
    let t2 = decorate t1 in
    let u = make_constraints [] t2 (Var("A")) in
    let u' = unify u in
    let t' = apply2term u' t2 in
    (showtylam t',showtype (typeof [] t'));;

let t1 = (parse "\\x.\\y.x y") in 
    let t2 = decorate t1 in
    let u = make_constraints [] t2 (Var("A")) in
    let u' = unify u in
    let t' = apply2term u' t2 in
    print_string (showtylam t');;
  
let t1 = (parse "\\x.\\y.x y") in 
    let t2 = decorate t1 in
    let u = make_constraints [] t2 (Var("A")) in
    let u' = unify u in
    let t' = apply2term u' t2 in
    print_string (showtype (typeof [] t'));;

print_string "\n******** type inference test problems********\n ";;
print_string(type_inf [] "\\x.x");;
print_string("\n");;
print_string(type_inf [] "\\x.\\y.x (y x)");;
print_string "#1 : INFERTYPE \\x.\\y.\\z.(x z) (y z)\n";;
type_inf [] "\\x.\\y.\\z.(x z) (y z)";;
print_string(type_inf [] "\\x.\\y.\\z.(x z) (y z)");;
print_string "#2 : INFERTYPE \\x.x x\n";;
  (*type_inf [] "\\x.x x";;
  print_string(type_inf [] "\\x.x x");;*)
print_string "#3 : INFERTYPE \\x.\\y.y(x y)\n";;
    type_inf [] "\\x.\\y.y(x y)";;
    print_string(type_inf [] "\\x.\\y.y(x y)");;
print_string "#4 : INFERTYPE \\x.\\y.(y x) y\n";;
      (*type_inf [] "\\x.\\y.(y x) y";;
      print_string(type_inf [] "\\x.\\y.(y x) y");;*)
print_string "#5 : INFERTYPE \\x.\\y.x (x y)\n";;
type_inf [] "\\x.\\y.x (x y)";;
print_string(type_inf [] "\\x.\\y.x (x y)");;

print_string "#6 : INFERTYPE \\x.\\y.x y x\n";;
	type_inf [] "\\x.\\y.x y x";;
  print_string(type_inf [] "\\x.\\y.x y x");;



