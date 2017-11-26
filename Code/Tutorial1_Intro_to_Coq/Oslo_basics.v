(**Some of the theorems are taken from Bertot and Casteran 2004**)
Require Import Omega.
(**Type Checking of the Universes**)
Check Prop.
Check Set.
Check Type.

(** Type Checking with Explicit Universes**)
Set Printing Universes.
Check Prop. 
Check Set.
Check Type.
Check forall P:Prop, Prop.
Check Prop.
Check forall P:Type, Type. 
Check nat.
Check 1.
Check plus.
Check plus 3.
Check plus 3 4.


(** Assumptions**)
Parameter H:Set.
Section H1.
Variable H1:Set.
End H1.
Hypothesis H2: Set.

(** Definition**)
Definition three:nat:= S (S(S((0)))).
Check three. 
Theorem three3: 3 = three. cbv.  reflexivity. Qed.

Eval compute in  S (S(S((0)))).
Parameter Montague_Grammar: Set. 
Definition MG:= Montague_Grammar.

(** Functions: simple function types and definitions using lambda abstraction**)
Parameter nat_1: nat->Prop.
Definition square:= fun n: nat=> n*n. (** fun is lambda. Note that Coq can infer the type nat->nat here.**)
Definition square1: nat->nat:= fun n: nat=> n*n.
Theorem SQUARE: square = square1.
cbv. reflexivity. Qed.
(** Define a function that takes two nat arguments and returns their sum multiplied by the first nat**)
Definition sum_times:= fun n m: nat=> (n+m)*n.
Eval compute in sum_times 2 3.

(** Inductive Types withour Recursion**)
Unset Printing Universes. 
Check bool. Print bool.
Inductive bool1 : Set := true | false. Print bool1_rect.
Inductive nat1 : Set :=
| O : nat1
| S1 : nat1 -> nat1.
Print nat1_ind. Print nat1_rect. Print nat1_rec. (**Peano's induction**)



(** Propositional logic proofs**)
Variables A B P Q R: Prop. 
Theorem trans: (P->Q)->(Q->R)->(P->R). 
                                         intro. intro. 
intro. 
apply H1. apply H0. assumption. Qed.
Definition lem:= A \/ ~ A.
Definition Peirce:= ((A->B)->A)->A.
Theorem lemP: lem -> Peirce.  
  unfold lem. unfold Peirce. intros.
elim H0.
intros. assumption. 
intro. apply H1.
intro.   absurd A. assumption. assumption. Qed.


(**Tactics**)
Theorem CONJ: A/\B->A.
intro.  elim H0. (** applies the elimination rule for conjunction**) intros. assumption. Qed
. 
Theorem CONJ2: B/\(A/\P)->A/\B.
intro. 
elim  H0.
intros. 
elim H3. intros. split. 
assumption. assumption. Qed.
Theorem DISJ: (B\/(B\/P))/\(A/\B)->A\/B.
intro. 
destruct H0. destruct H1.  left. (**or right**)  assumption. Qed.


Theorem IMPL: forall P: Prop, ( P -> Q) -> R -> P -> Q.
intros. apply   H0.
assumption. 
Qed.


Theorem NAT: exists x: nat, le 0 x.
exists 1. 
omega.  Qed.

(**Exact and Proof tactic**)
Theorem D: (P->P->Q)->P->Q.
exact (**or Proof**) (fun (H:P->P->Q)(p:P)=>H p p).
Qed. 

(**Idtac and try**)
Theorem PQQ: P->Q->P.
intros.   try elim H0.   try apply H0. Qed.
Variable T: Prop.
Theorem PQPR: (P->Q)->(P->R)->(P->Q->R->T)->P->T.  intros H H0 H1 H2.  idtac.  apply H1; [idtac|idtac |idtac]; idtac. assumption.  apply H;[idtac]; assumption. apply H0. assumption. Qed. 

Theorem PQPR2: (P->Q)->(P->R)->(P->Q->R->T)->P->T.
intros H H0 H1 H2. apply H1;[idtac|apply H|apply H0]; assumption. Qed.

Theorem PQPR3: (P->Q)->(P)->P. intros. assert Q. intuition. assumption. Qed.
(**Assert**)

Section assert.
Hypotheses (H : P -> Q)
(H0 : Q -> R)
(H1 : (P -> R) -> T -> Q)
(H2 : (P -> R) -> T).
Lemma L8 : Q.
assert (PR : P -> R). intro p; apply H0; apply H; assumption. apply H1; [ assumption | apply H2;assumption]. Qed. (**assert saves some time here, otherwise we would have to prove P->R twice**)
End assert.

Section generalize.
Hypotheses (x:nat)(y:nat).
Lemma GENERALIZE:   0 <= x + y + y.  omega. Qed.
End generalize.
Lemma GENERALIZE2: forall x y  :nat, 0 <=  x + y + y. 
intro. intro. omega. Qed. 

Section cut.
Hypotheses (H : P->Q)
(H0: Q->R)
(H1 : (P->R)->T->Q)
(H2 : (P->R)->T).

Theorem cut: Q.
cut (P->R). intros. apply H1. assumption. apply H2. assumption. intro. apply H0. apply H. assumption. Qed.
End cut.
