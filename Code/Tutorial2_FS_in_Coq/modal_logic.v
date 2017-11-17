Parameter W: Type. (* Type for worlds *)
Parameter e: Type. (* Typefor individuals *)
Definition MProp := W  -> Prop. (* Type of modal propositions *)
Parameter R: W -> W -> Prop. (* Accessibility relation for worlds *)

(**Defining the modal connectives**)
Definition mnot (p: MProp)(w: W) := ~ (p w).
Notation "m~ p" := (mnot p) (at level 74, right associativity).

Definition mand (p q:MProp)(w: W) := (p w) /\ (q w).
Notation "p m/\ q" := (mand p q) (at level 79, right associativity).
Definition mor (p q:MProp)(w: W) := (p w) \/ (q w).
Notation "p m\/ q" := (mor p q) (at level 79, right associativity).
Definition mimplies (p q:MProp)(w:W) := (p w) -> (q w).
Notation "p m-> q" := (mimplies p q) (at level 99, right associativity).
Definition mequiv (p q:MProp)(w:W) := (p w) <-> (q w).
Notation "p m<-> q" := (mequiv p q) (at level 99, right associativity).
Definition mequal (x y: MProp)(w: W) := x = y.
Notation "x m= y" := (mequal x y) (at level 99, right associativity).

Definition A {t: Type}(p: t -> MProp)(w: W) := forall x, p x w.
Notation "’mforall’ x , p" := (A (fun x => p))
(at level 200, x ident, right associativity) : type_scope.

Definition E {t: Type}(p: t -> MProp)(w: W) := exists x, p x w.
Notation "’mexists’ x , p" := (E (fun x => p))(at level 200, x ident, right associativity) : type_scope.

Definition box (p: MProp) := fun w:W => forall w1, (R w w1) -> (p w1).
Definition dia (p: MProp) := fun w:W => exists w1, (R w w1) /\ (p w1).

Definition V (p: MProp) := forall w, p w.

Notation "[ p ]" := (V p).

(** A bit of Montague**)
Parameter Man Human Walk : (e->MProp).


Definition man:=  fun x:e=> Man  x.
Definition human:= fun x:e=> Human  x.
Definition walk:= fun x:e=> Walk  x.

Parameter w_c:W.
Check E.
Definition a:= fun CN: (e->MProp)=>  fun VP:(e->MProp)=> fun w:W=> exists x,  
                                                                           (VP x w).
Check a. 
Check a.
Check (a man)  walk.
Check box.
Definition neccessarily:= fun P:MProp=>   box (P).
Definition possibly:= fun P:MProp=>  dia(P). 
Theorem NEC: neccessarily ((a man) walk) w_c-> exists w: W, R w_c w->  ((a man) walk w).
  cbv. intros. exists w_c. intro. elim H with w_c. intros. exists x. apply H1. assumption. Qed.

Theorem NEC2: neccessarily ((a man) walk) w_c-> forall w: W, R w_c w->  ((a man) walk w). cbv. intros.  apply H. assumption. Qed.

Section POSS.
  Variable refl: forall w: W,  R w w.
  Variable trans: forall w w1 w2, R w w1 /\ R w1 w2 -> R w w2.
  Variable x:e.
  (**Axiom M, needs refl**)
Theorem NECW:  neccessarily ((a man) walk) w_c->   ((a man) walk) w_c. cbv. 
                                                                       firstorder.            Qed.
(**Axiom D, needs refl**) 
Theorem NECPOSS:  neccessarily ((a man) walk) w_c->  possibly  ((a man) walk) w_c. cbv. firstorder. Qed.

(**dia dia -> dia,  needs transitivity**)
Theorem POSSPOSS:  possibly (possibly ((a man) walk)) w_c->  possibly  ((a man) walk) w_c. cbv. firstorder. Qed.

(**Other theorems can be proven depending on the properties defined on the accessibility relation**)
End POSS. 