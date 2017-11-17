Section One.


(** Similar exercises can be found: http://www-sop.inria.fr/members/Enrico.Tassi/coqws15/coq-master1-1-exercises.v or here https://github.com/vlopezj/coq-course *)

Require Import Bool Arith List.

(*Define a function that takes a month and a season argument and returns true in case month and season match, False otherwise**)
    

(* Define a recursive function that takes as input a list of numbers
   and returns the sum  of these numbers, *)

Fixpoint sumlist (ns : list nat) := unit. 


Compute sumlist nil.
Compute sumlist (0 :: 3 :: 7 :: nil).
Compute sumlist (3 :: 4 :: 2 :: nil).

(*Define a recursive function that takes as input a list of entities
   and returns the length of this list. *)
Definition e:=Set. 
Fixpoint length (ns : list e) :=unit.             

Parameter John Mary : e. 
Compute length nil.
Compute length (John :: Mary :: John:: nil).

(** Define a function that subtracts 2 for every nat**)
Definition minustwo (n : nat) := unit.

(**)
Inductive Gender:Set:= Fem|Masc|Neut.
Inductive Case:Set:= Nom|Acc.
Parameter he she it him her they I me we  you: e. 
Definition  pronoun (g: Gender) (c:Case):=
  match g, c with
|Fem, Nom=> she
|Fem, Acc => her
|Masc, Nom=> he
|Masc, Acc=> him
|Neut, _=> it
  end.
Compute pronoun Neut Acc.

(** extend the above function to all pronouns: use the extra features Number and Person**)
End One. 