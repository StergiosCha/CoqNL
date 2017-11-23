Check nat.
Check Prop.
Print nat.
Check Prop.
Check Set.
Check Type.
Check 1.
Check S 0.
Check plus.
Print plus.
Check plus 3.
Check plus 3 4.
Eval compute in plus 3 4.


Definition e:= Set.
Definition t:= Prop.
Parameter man: e->t.
Parameter human: Set ->Prop.
Parameter John: e.
Section MAN.
Variable MAN1: man John.
Check man John.
Theorem MAN: man John. apply MAN1.  