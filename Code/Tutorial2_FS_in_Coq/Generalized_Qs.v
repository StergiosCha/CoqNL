Load Set_theoretic_Defs.
Require Import Omega.
Definition t:= Prop.
Parameter CARD: (e->t)  -> nat.

Definition every:= fun P Q: e->t=>  forall x, P x-> Q x. 
Definition some:= fun P Q: e->t=> exists x,  P x /\ Q x.
Definition no:=  fun P Q: e->t=> forall x, not (P x -> Q x).

Definition most:=  fun P Q: e->t=> some P Q /\ gt (CARD (intersection P Q)) (CARD(complement(intersection P Q))).
Definition many:=  fun P Q: e->t=> some P Q /\ ge (CARD (intersection P Q)) (CARD(complement(intersection P Q))).
Definition three:=  fun P Q: e->t=> some P Q /\  (CARD (intersection P Q)) = 3.
Definition at_least_three:=  fun P Q: e->t=> some P Q /\ ge (CARD (intersection P Q)) 3.
Parameter walk cats animals: e->t.




(** Some theorems**)
  Theorem SOMEMOST: most cats walk -> some cats walk. cbv. intuition. Qed.
Theorem MOST1: (exists x, cats x /\ walk x /\ CARD(complement (intersection cats walk)) = 4 /\ CARD(intersection cats walk) = 5)-> most cats walk. 
  cbv. firstorder. Qed.
Theorem MOST2: (exists x, cats x /\ walk x /\ CARD(complement (intersection cats walk)) = 6 /\ CARD(intersection cats walk) = 5)-> most cats walk. 
  cbv. firstorder.

Theorem MOST2: (exists x, cats x /\ walk x /\  CARD(intersection cats walk) = 5)-> at_least_three  cats walk. 
  cbv. firstorder.
Qed.

Definition Conservativity:= fun Q:(e->t)->(e->t)->t => fun A B:e->t=>  Q A B <-> Q A (intersection A B).

 