Parameter object : Type.
Definition PN   : Type := object.
Definition VP   : Type := object -> Prop.

Definition NP    : Type := VP -> Prop .   (* NP := (PN -> Prop) -> Prop *)
Definition UsePN : PN -> NP := fun pn vp => vp pn.
Definition Cl   : Type := Prop .

Definition PredVP  : NP -> VP -> Cl := fun np vp => np vp.
Definition V    : Type := object -> Prop.
Definition UseV  : V -> VP := fun v => v.
Definition S    : Type := Prop .




Definition CN   : Type := PN -> Prop .
Definition N   : Type := CN .

Definition Pol  : Type := Prop -> Prop .

Definition Pos : Pol := fun p => p.
Definition Neg : Pol := fun p => not p.
Definition UseCl : Pol -> Cl -> S :=
  fun pol c => pol c.

Parameter AP   : Type.
Parameter A    : Type.
Definition Det   : Type := CN -> NP .
Parameter V2   : Type.
Parameter AdA  : Type.
Parameter Conj : Type.

Parameter ComplV2 : V2 -> NP -> VP. 
Definition DetCN : Det -> CN -> NP := fun det cn => det cn.
Parameter ModCN   : AP -> CN -> CN. 
Parameter CompAP  : AP -> VP. 
Parameter AdAP    : AdA -> AP -> AP. 
Parameter ConjS   : Conj -> S  -> S  -> S. 
Parameter ConjNP  : Conj -> NP -> NP -> NP. 
Parameter UseN    : N -> CN. 
Parameter UseA    : A -> AP. 
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

Definition every_Det : Det := fun cn vp => forall x, cn x -> vp x.
Definition some_Det : Det := fun cn vp => exists x, cn x /\ vp x.

