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


type analist = char list -> char list
type ('r, 'term) ranalist = 'term list -> 'r * 'term list;;
exception Echec

let terminal c : analist = fun l -> match l with
  | x :: l when x = c -> l
  | _ -> raise Echec

let terminal_cond (p : char -> bool) : analist = fun l -> match l with
  | x :: l when p x -> l
  | _ -> raise Echec

let epsilon : analist = fun l -> l

let ( -->) (a : analist) (b : analist) : analist =
  fun l -> let l = a l in b l

let (-|) (a1 : analist) (a2 : analist) : analist =
  fun l -> try a1 l with Echec -> a2 l

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

let pa_C = (terminal '1' -| terminal '0');;

let pa_V = (terminal 'a' -| terminal 'b' -| terminal 'c' -| terminal 'd');;

let pa_CV = (pa_C -| pa_V);;

let pa_A = (pa_V --> terminal ':' --> terminal '=' --> pa_CV);;

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
