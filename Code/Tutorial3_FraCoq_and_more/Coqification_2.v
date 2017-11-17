Definition S    : Type := Prop .
Definition Cl   : Type := Prop .
Definition Pol  : Type := Prop -> Prop .

Definition Pos : Pol := fun p => p.
Definition Neg : Pol := fun p => not p.
Definition UseCl : Pol -> Cl -> S :=
  fun pol c => pol c.

Parameter VP   : Type.
Parameter PN   : Type.
Parameter NP   : Type.
Parameter AP   : Type.
Parameter A    : Type.
Parameter CN   : Type.
Parameter Det  : Type.
Parameter N    : Type.
Parameter V    : Type.
Parameter V2   : Type.
Parameter AdA  : Type.
Parameter Conj : Type.

Parameter PredVP  : NP -> VP -> Cl. 
Parameter ComplV2 : V2 -> NP -> VP. 
Parameter DetCN   : Det -> CN -> NP. 
Parameter ModCN   : AP -> CN -> CN. 
Parameter CompAP  : AP -> VP. 
Parameter AdAP    : AdA -> AP -> AP. 
Parameter ConjS   : Conj -> S  -> S  -> S. 
Parameter ConjNP  : Conj -> NP -> NP -> NP. 
Parameter UsePN   : PN -> NP.
Parameter UseV    : V -> VP. 
Parameter UseN    : N -> CN. 
Parameter UseA    : A -> AP. 
Parameter some_Det : Det.
Parameter every_Det : Det. 
Parameter we_NP   : NP.
Parameter you_NP : NP. 
Parameter very_AdA : AdA. 
Parameter and_Conj : Conj.
Parameter or_Conj : Conj.

Parameter man_N :  N.
Parameter woman_N : N .
Parameter house_N :  N.
Parameter tree_N : N .
Parameter   big_A : A .
Parameter small_A : A .
Parameter green_A : A .
Parameter  walk_V : V  .
Parameter arrive_V : V .
Parameter love_V2 : V2  .
Parameter please_V2 : V2 .
Parameter john_PN : PN .
Parameter mary_PN : PN.

Theorem POL : UseCl Pos (PredVP (UsePN john_PN) (UseV walk_V)) ->
               UseCl Neg (PredVP (UsePN john_PN)(UseV walk_V)) -> False.
cbv.
intros P N.
exact (N P).
Qed.


