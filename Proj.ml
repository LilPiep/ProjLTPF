(** Projet LTPF **)

(** 1.1.1 **)

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

type v = A | B | C | D;;

type b = Zero | Un;;

type e =
  | Variable of v
  | Booleen of b;;

type i =
  | Sequence of i * i
  | Affectation of v * e
  | While of e * i
  | If of e * i * i
  | EpsilonI;;
