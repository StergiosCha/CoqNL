(**Pattern Matching**)
Inductive month:Set:= January|February|March|April|May|June|July|August|September|October|November|December.


Definition nbdays (m:month) :=
match m with
| April => 30
| June => 30
|September=> 30
|November=>30
|February=>28
| _ => 31
end.
Check nbdays.
Compute nbdays June.
Compute nbdays October.



(**Function that returns true in case a month is a winter month, false otherwise**)
Definition is_winter_month (m:month) :=
  match m with
|December => True
| January => True
|February => True
|_ => False
  end.
Compute is_winter_month July.
Compute is_winter_month February.
Inductive season:Set:= Winter|Spring|Summer|
                       Autumn.
Definition winter_season_month_match (s: season) (m:month) :=
  match s, m with
  | Winter, December => True
  | Winter, January => True
  | Winter, February => True
  |_ , _ => False
  end.

(**Pattern matching with recursive functions**) 
Fixpoint plus (n m : nat) : nat :=
match n with
O => m
| S p => S (plus p m)
end.
Compute plus 4 8.

Fixpoint minus (n m : nat) : nat :=
match n, m with
S p, S q => minus p q
| _, _ => n
end.
Compute minus 11 9.
Definition e:= Set.
Inductive Gender:Set:= Fem|Masc|Neut.
Inductive Case:Set:= Nom|Acc.
Parameter he she it him her they I me we  you: e. 
Definition  pronoun (g: Gender) (c:Case):=
  match g, c with
|Fem, Nom=> she
|Fem, Acc => her
|Masc, Nom=> he
|Masc, Acc=> him
|Neut, _=> it
  end.
Compute pronoun Neut Acc.


(** Some record examples. Defining Entity as a more structured type**)
Parameter human walk: e->Prop. 
  Record Entity : Type := mkentity {x: e; z: human x}.
  Parameter John: Entity. 
  Check walk (John.(x)).
  Theorem en: Entity-> exists x, human x.
    intro.      decompose record X. exists x0. assumption. Qed.
  Theorem WALK: walk (John.(x))-> exists x:e, walk x. intro. decompose record John. exists John.(x). assumption. Qed. 