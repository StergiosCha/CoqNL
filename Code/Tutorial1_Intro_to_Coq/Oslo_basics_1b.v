Load Lib.
(**Using the exists tactic**)
Parameter P: nat -> Prop. 
Theorem EXISTS: P 5-> exists n: nat, P n. 
  intro. exists 5. assumption. Qed.

(**Using the equality tactics**)
Theorem symmetry_transitivity: forall n m n1: nat,  n=m/\m=n1-> n=n /\ n=n1 /\ m=n.
  intros. destruct H. splits. reflexivity. transitivity m. assumption. assumption. symmetry. assumption. Qed.


Theorem REPLACE:forall n m,  n=m /\ n=5 -> m=5.
  intros. replace 5 with n.  symmetry.   destruct H. assumption. destruct H. assumption.  Qed.


Variables  A B C D E:Prop.
Theorem DESTRUCTS: A/\B/\C/\D/\E->A.
  intro.   destructs H.
  assumption. Qed.




(**Ltac destructs_conjunction_tactic N T :=
  match N with
  | 2 => destruct T as [? ?]
  | 3 => destruct T as [? [? ?]]
  | 4 => destruct T as [? [? [? ?]]]
  | 5 => destruct T as [? [? [? [? ?]]]]
  | 6 => destruct T as [? [? [? [? [? ?]]]]]
  | 7 => destruct T as [? [? [? [? [? [? ?]]]]]]
  end. **)
(**jauto: powerful automated tactic that can exploit conjunctions, disjunctions and existentials in both the goal and the hypothesis**)
Theorem JAUTO : forall (f g : nat->Prop),
  (forall x, f x -> g x) ->
  (exists a, f a) ->
  (exists a, g a). auto. (**fails**) eauto. (**fails**) jauto. (**succeeds**) Qed.

(**false applies exfalso and tries to prove False but does more than that, it will prove the goal in case it involves absurd assumptions or contradictory assumptions**)
Lemma demo_false :
  forall n, S n = 1 -> n = 0.
Proof.
  intros. destruct n. reflexivity. false. (**exfalso does not prove this**)
Qed.

