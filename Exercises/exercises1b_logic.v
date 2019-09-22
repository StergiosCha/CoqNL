Section Logic.
Variables A B P Q R: Prop. 
Definition lem:=  A \/ ~ A.
Definition Peirce:=  ((A->B)->A)->A.
Theorem lemP: lem -> Peirce.
  unfold lem. unfold Peirce. intros. elim H. intro. assumption. intro. apply H0. intro. absurd A. assumption. assumption. Qed.

Theorem noncontradiction: not (P /\ not P). 


(**Prove the following**)
Theorem hilbert_axiom_S :  (P -> Q -> R) -> (P -> Q) -> P -> R.
Theorem andCom: P/\Q -> Q/\P.
Theorem noncontradiction: not (P /\ not P). 
Theorem  PQR : (P /\ Q) \/ R -> P \/ R.
Theorem distrandor : (P /\ Q)\/ (P /\ R) ->P /\ (Q \/ R).
Theorem  LEM :
(P -> (P /\ Q) -> R) -> P /\ (Q /\ P) -> R.
