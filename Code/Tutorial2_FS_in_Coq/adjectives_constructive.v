Require Import Reals.
Load MainCoq.

(** Dealing with multidimensional adjectives. Health as an inductive type where the dimensions are enumerated. This is just an enumerated type*)
Inductive Health: CN:= Heart|Blood|Cholesterol.
Parameter Degree:R.
Parameter Healthy: Health->human->Prop.
Definition sick:=fun y : human => ~ (forall x : Health, Healthy x y).
Definition healthy:= fun y : human => forall x : Health, Healthy x y.

(**This is sort of a hack. Given that in Coq, coercions do not propagate thrugh the constructors as in TTCS, we show the case of two Irish delegate entries, one where Human is the first projection and the other where IrishHuman is. Then, we define a unit type Irishdelegate that includes both types.*)
Record irishhuman : CN := mkirishhuman { l3 :> human; _ : irish l3 }.
Record Irishdelegate : CN := mkirishdelegate { c :> delegate; _ : irish c }.
Record Irishdelegate1 : CN := mkIrishdelegate1 { c3 :> irishhuman; _ : irish c3 }.
Inductive OneIrishdelegate : Set :=  IrishDelegate.
Definition Ir1 (r:OneIrishdelegate):CN:=Irishdelegate. Coercion Ir1: OneIrishdelegate>->CN.
Definition Ir2 (r:OneIrishdelegate) :Set:=Irishdelegate1. Coercion Ir2: OneIrishdelegate>->Sortclass.
Parameter black:object->Prop.
(** Same idea for black man*)
Record blackman : CN := mkBlackman { l4 :> man; _ : black l4 }.
Record blackhuman : CN := mkBlackhuman { l5 :> human; _ : black l5 }.
Record blackman1 : CN := mkBlackman1 { c4 :> blackhuman; _ : black c4 }.
Inductive OneBlackman : Set :=  blackMan.
Definition Br1 (r:OneBlackman):CN:=blackman. Coercion Br1: OneBlackman>->CN.
Definition Br2 (r:OneBlackman) :Set:=blackman1. Coercion Br2: OneBlackman>->Sortclass.
