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

let terminal_cond (p : 'term -> boool) : 'term analist = function
  | x :: l when (p x = Z) -> l
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

let ( -+>) (a : analist) (b : ('res, 'term) ranalist) : ('res, 'term) ranalist =
  fun l -> let l = a l in b l

let (+->) (a : ('res, 'term) ranalist) (b : analist) : analist =
  fun l -> let (x, l) = a l in b l

let (++>) (a : ('resa, 'term) ranalist) (b : 'resa -> ('resb, 'term) ranalist) : ('resb, 'term) ranalist =
  fun l -> let (x, l) = a l in b x l

(*les deux parties seront traitées séparément*)

(* partie 2.1.1 *)

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
           ( terminal 'w' --> terminal '(' --> pa_CV --> terminal ')' --> terminal '{' --> p_Seq --> terminal '}' )
  
let _=pa_Seq (list_of_string "a:=1;b:=1;c:=1;w(a){i(c){c:=0;a:=b}{b:=0;c:=a}}")
  
(* version ranalist maintenant *)

let pa_V2 = (terminal 'a' -+> epsilon_res 'a' -| terminal 'b' -+> epsilon_res 'b' -| terminal 'c' -+> epsilon_res 'c' -| terminal 'd' -+> epsilon_res 'd')

let pa_C2 = (terminal '1' -+> epsilon_res (True) -| terminal '0' -+> epsilon_res (False))

let pa_C2V2 = (pa_C2 -| pa_V2)

let rec pa_Seq2: i ranalist = fun l ->  l |>
    (pa_A2 +| pa_W2 +| pa_I2) ++> fun a -> ((terminal ';' -+> pa_Seq2 ++> fun suite -> epsilon_res (Seq(i,reste))) +| epsilon_res (Seq(a,Skip)))
    and pa_A2 : i ranalist = fun l -> l |>
              pa_V2 ++> fun v -> terminal ':' --> terminal '=' -+> pa_C2V2 ++> fun a -> epsilon_res (Assign(v,a));; 
    and pa_I2 : i ranalist = fun l ->  l |>
              terminal 'i' --> terminal '(' -+> pa_C2V2 ++> fun cond -> terminal ')' --> terminal '{' -+> pa_Seq2 ++> fun the -> terminal '}' --> terminal '{' -+> pa_Seq2 ++> fun els -> terminal '}' -+> epsilon_res(If(cond,the,els))
    and pa_W2: i ranalist = fun l ->  l |>
              terminal 'w' --> terminal '(' -+> pa_C2V2 ++> fun cond -> terminal ')' --> terminal '{' -+> pa_Seq2 ++> fun the -> terminal '}' -+> epsilon_res(While(cond,the))

pa_Seq2 (list_of_string "a:=1;b:=1;c:=1;w(1){i(1){c:=0;a:=1}{b:=0;c:=1}}");;
(* EXO 2.2 *)


type state = (var*int) list;;

let rec (get : var -> state -> int) = fun c s ->
  match s with
  |(var,value) :: suite -> if var=c then value else get c suite
  |[] -> raise Echec;;

 let rec (update: state -> int -> var -> state) = fun s i v ->
   match s with
   | [] -> (v,i) :: []
   | (var,value) :: suite -> if var=v then (v,i)::suite else (var,value)::(update suite i v)
 ;;
  
let rec eval (s:state) (exp:e) : b = 
  match exp with
  | Variable v -> get s v
  | Boolean b -> b
  | Conjonction (b1, b2) -> 
  match b1 with
    |Zero -> Zero
    |Un -> 
    match b2 with
          |Zero -> Zero
          |Un -> Un
  | Disjonction (b1, b2) -> 
  match b1 with
    |Un -> Un
    |Zero -> 
    match b2 with
          |Zero -> Zero
          |Un -> Un
  | Negation e -> b = if b1=Un then Zero else Un
;;
