Definition e:=Set.
Set Implicit Arguments. 
Definition Ensemble :=(e -> Prop)->Prop.
Definition In (A:Ensemble) (x:e->Prop) : Prop := A x. 
Definition Included (B C:Ensemble) : Prop := forall x:e->Prop, In B x -> In C x.

Definition Strict_Included (B C:Ensemble) : Prop := Included B C /\ B <> C.



Inductive Empty_set : Ensemble :=.

Inductive Full_set : Ensemble :=
 Full_intro : forall x:e->Prop, In Full_set x.

Inductive Singleton (x:e->Prop) : Ensemble :=
    In_singleton : In (Singleton x) x.

Inductive Union (B C:Ensemble) : Ensemble :=
    | Union_introl : forall x:e->Prop, In B x -> In (Union B C) x
    | Union_intror : forall x:e->Prop, In C x -> In (Union B C) x.

Definition Add (B:Ensemble) (x:e->Prop) : Ensemble := Union B (Singleton x).

Inductive Intersection (B C:Ensemble) : Ensemble :=
    Intersection_intro :
    forall x:e->Prop, In B x -> In C x -> In (Intersection B C) x.

Inductive Couple (x y:e->Prop) : Ensemble :=
    | Couple_l : In (Couple x y) x
    | Couple_r : In (Couple x y) y.

Inductive Triple (x y z:e->Prop) : Ensemble :=
    | Triple_l : In (Triple x y z) x
    | Triple_m : In (Triple x y z) y
    | Triple_r : In (Triple x y z) z.

Definition Complement (A:Ensemble) : Ensemble := fun x:e->Prop => ~ In A x.

  Definition Setminus (B C:Ensemble) : Ensemble :=
    fun x:e->Prop => In B x /\ ~ In C x.

  Definition Subtract (B:Ensemble) (x:e->Prop) : Ensemble := Setminus B (Singleton x).

  Inductive Disjoint (B C:Ensemble) : Prop :=
    Disjoint_intro : (forall x:e->Prop, ~ In (Intersection B C) x) -> Disjoint B C.

 

  Definition Same_set (B C:Ensemble) : Prop := Included B C /\ Included C B.
    Axiom Extensionality_Ensembles : forall A B:Ensemble, Same_set A B -> A = B.

Definition ensemble :=e->Prop.
Definition In_s (A:ensemble) (x:e) : Prop := A x.
Definition included (B C:ensemble) : Prop := forall x:e, In_s B x -> In_s C x.

Definition strict_Included (B C:ensemble) : Prop := included B C /\ B <> C.


Inductive empty_set : ensemble :=.

Inductive full_set : ensemble :=
full_intro : forall x:e, In_s full_set x.

  Inductive singleton (x:e) : ensemble :=
    in_singleton : In_s (singleton x) x.


  Inductive union (B C:ensemble) : ensemble :=
    | union_introl : forall x:e, In_s B x -> In_s (union B C) x
    | union_intror : forall x:e, In_s C x -> In_s (union B C) x.

Definition add (B:ensemble) (x:e) : ensemble := union B (singleton x).

Inductive intersection (B C:ensemble) : ensemble :=
    intersection_intro :
    forall x:e, In_s B x -> In_s C x -> In_s (intersection B C) x.

Inductive couple (x y:e) : ensemble :=
    | couple_l : In_s (couple x y) x
    | couple_r : In_s (couple x y) y.

Inductive triple (x y z:e) : ensemble :=
    | triple_l : In_s (triple x y z) x
    | triple_m : In_s (triple x y z) y
    | triple_r : In_s (triple x y z) z.

Definition complement (A:ensemble) : ensemble := fun x:e => ~ In_s A x.

Definition setminus (B C:ensemble) : ensemble :=
    fun x:e => In_s B x /\ ~ In_s C x.


Definition subtract (B:ensemble) (x:e) : ensemble := setminus B (singleton x).

Inductive disjoint (B C:ensemble) : Prop :=
    disjoint_intro : (forall x:e, ~ In_s (intersection B C) x) -> disjoint B C.

Inductive inhabited (B:ensemble) : Prop :=
    inhabited_intro : forall x:e, In_s B x -> inhabited B.

Definition strict_included (B C:ensemble) : Prop := included B C /\ B <> C.

Definition same_set (B C:ensemble) : Prop := included B C /\ included C B.
    Axiom extensionality_ensembles : forall A B:ensemble, same_set A B -> A = B.

 

