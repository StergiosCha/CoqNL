Set Implicit Arguments.

Ltac jauto_set_hyps :=
  repeat match goal with H: ?T |- _ => 
    match T with
    | _ /\ _ => destruct H
    | exists a, _ => destruct H 
    | _ => generalize H; clear H
    end
  end.

Ltac jauto_set_goal :=
  repeat match goal with
  | |- exists a, _ => esplit
  | |- _ /\ _ => split
  end.

Ltac jauto_set :=
  intros; jauto_set_hyps; 
  intros; jauto_set_goal;
  unfold not in *.

Tactic Notation "jauto" :=
  try solve [ jauto_set; eauto ].                          
Tactic Notation "jauto_fast" :=
  try solve [ auto | eauto | jauto ].

Ltac destructs H :=
  let X := fresh in let Y := fresh in 
  first [ destruct H as [X Y]; destructs X; destructs Y | idtac ].
Tactic Notation "rewrite" "~" constr(H) :=
  rewrite H; auto.
Tactic Notation "rewrite" "~" "<-" constr(H) :=
  rewrite <- H; auto.
Tactic Notation "apply" "~" constr(H) :=
  first [ apply H | eapply H ]; auto.




