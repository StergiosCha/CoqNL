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

Require Import Omega.
Require Import Arith. 
Theorem monthcase: forall m: month, le 28 (nbdays m). 
  intro. case ( m). simpl.  omega. simpl. omega. simpl. omega. simpl. omega. simpl. omega. simpl. omega. simpl. omega. simpl. omega. simpl. omega. simpl. omega. simpl. omega.  simpl. omega. 
Qed. (*we could use some autoamation here**)
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


  Section SUB.
 Definition CN:=Set.
 Parameters Woman  Man Human Animal Object: CN. (**CNs as types**)
 Axiom wh: Woman  ->Human. Coercion wh: Woman >->Human.
 Axiom mh: Man ->Human. Coercion mh: Man >->Human.
  Axiom ha: Human -> Animal. Coercion ha: Human>->Animal.
  Axiom ao: Animal -> Object. Coercion ao: Animal >-> Object.

  Parameter drive: Human -> Prop.
  Parameter George  : Man.
  Parameter Mary: Woman. 
  Check drive Mary.  (**work because of the subtyping**)
  Check and(drive George)(drive Mary). 
  (** some reasoning **)
  Theorem MARY: drive Mary -> exists x: Woman, drive x. 
  cbv.   intro. exists Mary. assumption. Qed. 

Theorem MARY1:  drive Mary -> exists x: Human, drive x.
  cbv.   intro. exists Mary. assumption. Qed.  (**subtyping**)

(**Monotonicity on the first argument for free with subtyping**)
Theorem MONIN: exists x: Man, drive x -> exists x: Human, drive x.
exists George.  intro. exists George. assumption. Qed. 
Theorem MONDEC: not (exists x: Human, drive x) -> not(exists x: Man, drive x).
cbv.   intros. apply H.   elim H0. intros. exists x0. assumption. Qed. (**bool in nat**)
Definition bool_in_nat (b:bool) := if b then 0 else 1.
Check bool_in_nat.
Coercion bool_in_nat : bool >-> nat.
Check (0 = true).
Set Printing Coercions.
Check (0 = true).


(**Co-induction**)
Set Implicit Arguments. 
CoInductive LList (A:Set) : Set :=
LNil : LList A
| LCons : A -> LList A -> LList A.
Implicit Arguments LNil [A].
Print LList.
Require Import Streams. 
Check Stream. Print Stream.

Check (LCons 1 (LCons 2 (LCons 3 LNil))).
Eval compute  in (LCons 1 (LCons 2 (LCons 3 LNil))).
(**Eval compute  in (Cons 1 (Cons 2 (Cons 3))).**) (**there is no Nil to provide the Stream nat argument**)
Definition next_month (m:month) :=
match m with
| January => February
| February => March 
| March => April
| April => May
| May => June 
| June => July
| July => August
| August => September
| September => October
| October => November
| November => December
| December => January
end.


Theorem next_august_then_july: forall m:month, next_month m = August -> m = July. intros m. case m. simpl. intros. discriminate H.  intros. discriminate H.  intros. discriminate H.  intros. discriminate H.  intros. discriminate H.  intros. discriminate H.  intros. reflexivity.   intros. discriminate H.  intros. discriminate H.  intros. discriminate H.  intros. discriminate H.  intros. discriminate H. Qed.
                                                                                                                                                                                                                                                                                                                                                                                                                          