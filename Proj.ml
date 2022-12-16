
(** Projet LTPF **)

(** 1.1.1 **)

type v = A | B | C | D;;

type b = Zero | Un;;

type e =
  | Variable of v
  | Booleen of b
  | Conjonction of e * e
  | Disjonction of e * e
  | Negation of e;;  

type i =
  | Skip
  | Sequence of i * i
  | Affectation of v * e
  | While of e * i
  | If of e * i * i


(** 1.1.2 **)

(* Grammaire
   Variables :
   V ::= a | b | c | d (variable)
   B ::= 0 | 1 (booléen)
   E ::= V | B (expression)        
   Instructions :
   I ::=
     | I;I
     | V:=E
     | w(E){I}
     | i(E){I}{I}
     | epsilon
     
 *)

(** 1.1.3 **)

(* Nouvelle grammaire
   Variables similaires        
   Instructions :
   S ::= I;S | epsilon
   I ::= 
   | V:=E 
   | i(E){S}{S} 
   | w(E){S}    
   | epsilon
   
 *)

(** 1.2.1 **)
(*
                      P
[expr]S1 =true    S1 ---->S2
----------------------------
  if expr then P else Q  
S1 ---------------------->S2
*****************************************
                       Q
[expr]S1 =false    S1 ---->S3
----------------------------
  if expr then P else Q  
S1 ----------------------->S3
 *)


(*EXO 2.1*)

let list_of_string s =
  let n = String.length s in
  let rec boucle i =
    if i = n then []
    else s.[i] :: boucle (i+1)
  in boucle 0;;


type 'term analist = 'term list -> 'term list
type ('r, 'term) ranalist = 'term list -> 'r * 'term list
exception Echec

(* Combinateurs d'analyseurs purs *)

(* partie utile pour les analist*)

let terminal (c : 'term) : 'term analist = function
  | x :: l when x = c -> l
  | _ -> raise Echec

let terminal_cond (p : 'term -> b) : 'term analist = function
  | x :: l when (p x = Zero) -> l
  | _ -> raise Echec

let epsilon : 'term analist = fun l -> l
  
let (-->) (a : 'term analist) (b : 'term analist) : 'term analist =
  fun l -> let l = a l in b l

let (-|) (a : 'term analist) (b : 'term analist) : 'term analist =
  fun l -> try a l with Echec -> b l

let rec star (a : 'term analist) : 'term analist = fun l -> l |>
  ( a --> star a ) -| epsilon

(*partie utile pour les ranaliste *)

let epsilon_res (info : 'res) : ('res, 'term) ranalist =
  fun l -> (info, l)
  
let terminal_res (f : 'term -> 'res option) : ('res, 'term) ranalist =
  fun l -> match l with
  | x :: l -> (match f x with Some y -> y, l | None -> raise Echec)
  | _ -> raise Echec
  
let (+|) (a : ('res, 'term) ranalist) (b : ('res, 'term) ranalist) : ('res, 'term) ranalist =
  fun l -> try a l with Echec -> b l

let ( -+>) (a :'term analist) (b : ('res, 'term) ranalist) : ('res, 'term) ranalist =
  fun l -> let l = a l in b l

let (+->) (a : ('res, 'term) ranalist) (b : 'term analist) : 'term analist =
  fun l -> let (x, l) = a l in b l

let (++>) (a : ('resa, 'term) ranalist) (b : 'resa -> ('resb, 'term) ranalist) : ('resb, 'term) ranalist =
  fun l -> let (x, l) = a l in b x l
(*les deux parties seront traitées séparément*)

(* partie 2.1.1 *)
(* 2.1.2 -> une ou deux fonction test sont écrites à chaque partie leurs résultat après exécution est à chaque fois cohérent *)
(*commençons avec les analist *)

let pa_C = (terminal '1' -| terminal '0')

let pa_V = (terminal 'a' -| terminal 'b' -| terminal 'c' -| terminal 'd')

let pa_CV = (pa_C -| pa_V)

let rec pa_Seq : 'term analist = fun l ->  l |>
  ( ( pa_A -| pa_I -| pa_W )--> ((terminal ';' --> pa_Seq ) -| epsilon ))
  and pa_A : 'term analist = fun l -> l |>
           (pa_V --> terminal ':' --> terminal '=' --> pa_CV)
  and pa_I : 'term analist = fun l -> l |>
           ( terminal 'i' --> terminal '(' --> pa_CV --> terminal ')' --> terminal '{' --> pa_Seq --> terminal '}' --> terminal '{' --> pa_Seq --> terminal '}' )
  and pa_W : 'term analist = fun l -> l |>
           ( terminal 'w' --> terminal '(' --> pa_CV --> terminal ')' --> terminal '{' --> pa_Seq --> terminal '}' )
  
let _=pa_Seq (list_of_string "a:=b;b:=c;c:=0;w(1){i(1){c:=0;a:=1}{b:=0;c:=1}}");;
  
(* version ranalist maintenant *)

let pr_V = (terminal 'a' -+> epsilon_res A) +| (terminal 'b' -+> epsilon_res B) +|(terminal 'c' -+> epsilon_res C) +| (terminal 'd' -+> epsilon_res D)

let pr_C = (terminal '1' -+> epsilon_res (Un)) +| (terminal '0' -+> epsilon_res (Zero))

let pr_CV: (e, char) ranalist = fun l -> l |> (pr_C ++> fun a -> epsilon_res (Booleen a)) +| (pr_V ++> fun b -> epsilon_res (Variable b))

let pr_A : ('res, 'term) ranalist = fun l -> l |>
              pr_V ++> fun v -> terminal ':' --> terminal '=' -+> pr_CV ++> fun a -> epsilon_res (Affectation(v,a))

let rec pr_I :  ('res, 'term) ranalist = fun l ->  l |>
              terminal 'i' --> terminal '(' -+> pr_CV ++> fun cond -> terminal ')' --> terminal '{' -+> pr_Seq ++> fun the -> terminal '}' --> terminal '{' -+> pr_Seq ++> fun els -> terminal '}' -+> epsilon_res(If(cond,the,els))
    and pr_W:('res, 'term) ranalist = fun l ->  l |>
              terminal 'w' --> terminal '(' -+> pr_CV ++> fun cond -> terminal ')' --> terminal '{' -+> pr_Seq ++> fun the -> terminal '}' -+> epsilon_res(While(cond,the))
    and pr_Seq:('res, 'term) ranalist = fun l ->  l |>
    (pr_A +| pr_W +| pr_I) ++> fun a -> ((terminal ';' -+> pr_Seq ++> fun suite -> epsilon_res (Sequence(a,suite))) +| epsilon_res (Sequence(a,Skip)));;

      

let _=pr_Seq (list_of_string "a:=b;b:=c;c:=0;w(1){i(1){c:=0;a:=1}{b:=0;c:=1}}");;

(* 2.1.3 analist *)

let rec star (a : 'term analist) : 'term analist = fun l -> l |>
  ( a --> star a ) -| epsilon

(*let pa_E = star (terminal ' ' -| terminal ('/n'))

let pa_N = (pa_E -| epsilon)
           *)

let rec pa_Ope : 'term analist = fun l -> l |>
           ((terminal '!' --> pa_Ope) -|(pa_CV)-| (terminal '+' --> pa_Ope) -|(terminal '(' --> pa_plus --> terminal ')')-| (terminal '.' --> pa_Ope )) --> (pa_Ope  -| epsilon )
and pa_point : 'term analist = fun l -> l |>
           (((pa_Ope --> terminal '.' --> pa_Ope) -| pa_Ope )--> (pa_Ope  -| epsilon ))
and pa_plus : 'term analist = fun l -> l |>
           (((pa_Ope --> terminal '+' --> pa_Ope) -| pa_Ope)--> (pa_Ope  -| epsilon )) 




let rec pa_Seq2 : 'term analist = fun l ->  l |>
  (( pa_A2 -| pa_I2 -| pa_W2 -| pa_Ope)--> ((terminal ';' --> pa_Seq2 ) -| epsilon ))
  and pa_A2 : 'term analist = fun l -> l |>
           (pa_V --> terminal ':' --> terminal '=' --> pa_Ope)
  and pa_I2 : 'term analist = fun l -> l |>
           ( terminal 'i' --> terminal '(' --> pa_Ope --> terminal ')' --> terminal '{' --> pa_Seq2 --> terminal '}' --> terminal '{' --> pa_Seq2 --> terminal '}' )
  and pa_W2 : 'term analist = fun l -> l |>
           ( terminal 'w' --> terminal '(' --> pa_Ope --> terminal ')' --> terminal '{' --> pa_Seq2 --> terminal '}' );;

let _=pa_Seq2 (list_of_string "c:=a.b");;
let _=pa_Seq2 (list_of_string "a:=b;b:=c;c:=0;w(1){i(1){c:=0;a:=1}{b:=0;c:=1}}");;
let _=pa_Seq2 (list_of_string "(!1)")

(* 2.1.3 ranalist*)

let rec (pr_Ope: (e, char) ranalist) = fun l -> l |> 
(terminal '!' -+> pr_Ope ++> fun a -> epsilon_res (Negation a)) +| 
(pr_CV ++> fun a -> epsilon_res a) +| 
(terminal '(' -+> pr_Ope ++> fun b -> terminal ')' -+> epsilon_res b )
and pr_point (exp : e) : (e, char) ranalist = fun l -> l |> 
(terminal '.' -+> pr_Ope ++> fun a -> pr_point (Conjonction (exp,a))) +| epsilon_res exp
and pr_plus (exp : e) : (e, char) ranalist = fun l -> l |> 
(terminal '+' -+> pr_Ope ++> fun a -> pr_plus (Disjonction (exp,a))) +| epsilon_res exp


let _=pr_Ope (list_of_string "c:=a.b");;
let _=pr_Ope (list_of_string "(!1)");;

(* EXO 2.2 *)


type state = 
  | Nil
  | Cons of state * v * b;; 

let rec (get : v -> state -> b) = fun c s ->
  match s with
  |Nil -> Zero
  |Cons(s2, var, va) -> if c==var then va else get c s2;;

let rec update ...


let rec conj (b1:b) (b2:b) : b = 
  match b1 with
  |Zero -> Zero
  |Un -> match b2 with
          |Zero -> Zero
          |Un -> Un
;;

let rec disj (b1:b) (b2:b) : b = 
  match b1 with
  |Un -> Un
  |Zero -> match b2 with
            |Zero -> Zero
            |Un -> Un
;;

let rec non (b1:b) : b = if b1=Un then Zero else Un
;;

let rec eval (s:state) (exp:e) : b = 
  match exp with
  | Variable v -> get s v
  | Boolean b -> b
  | Conjonction (e1, e2) -> conj (eval s e1) (eval s e2)
  | Disjonction (e1, e2) -> disj (eval s e1) (eval s e2)
  | Negation e -> non (eval s e)
;;

let rec sn (s:state) (ast:i) : state = match ast with
  | Skip -> s
  | Seq(i1, i2) -> sn (sn s i1) i2
  | Assign(v,e) -> update s v e
  | While(e,i1) -> if (eval s e)=Un then sn s i1 else s
  | If(e,i1,i2) -> if (eval s e)=Un then sn s i1 else sn s i2;;
