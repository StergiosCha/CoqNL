Definition e:=Set.
Definition t:=Prop.
Parameter black: (e->t). 
Definition Black:= fun Q: (e->t)=> fun x:e=> black x /\ Q x. 
Parameter man: e->t.
Parameter John:e.
Theorem blackman: Black man John-> man John. cbv. intuition. Qed.
Parameter skillful: (e->t)->(e->t).
Definition Skillful:= fun Q: (e->t)=> fun x:e=> skillful Q x /\ Q x.


Section Postulate.
 Parameter ADJ_I ADJ_S ADJ_P ADJ_NC: (e->t)->(e->t).
 Parameter ADJ_i: e->t.
 Variable Int: forall  Q: (e->t), forall  x:e,  ADJ_I Q x <->ADJ_i  x /\ Q x.
 Variable Sub: forall  Q: (e->t), forall  x:e,  ADJ_S Q x -> Q x.
 Variable Pri: forall  Q: (e->t), forall  x:e,  ADJ_P Q x -> not (Q x).
 Variable NonC: forall  Q: (e->t), forall  x:e,  ADJ_NC Q x.

 (**using  postulates as  local assumptions**)
  
  
Theorem sman: ADJ_S  man John-> man John. cbv. intuition. apply Sub. assumption.  Qed.
Theorem iman: ADJ_I  man John-> ADJ_i  John.
  cbv. intuition. elim Int with man John.
  intros.      intuition.                                Qed.
Theorem pman: ADJ_P  man John->not ( man John). cbv. intuition. apply Pri with man John. assumption. assumption. Qed.
Theorem ncman: ADJ_NC  man John-> ( man John). cbv. intuition.  Abort all.


