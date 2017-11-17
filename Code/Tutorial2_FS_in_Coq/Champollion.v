Load  Set_theoretic_Defs.
(** This is a partial implementation of Champollion's paper "Ten Men and Women Got Married Today: Noun Coordination and the Intersective Theory of Conjunction". It goes up to approx. page 10 of the paper**)

(**Existential Raising**)
Definition ER:= fun P:(e->Prop)=>  fun Q:(e->Prop)=> exists x: e,In_s  (intersection P  Q) x.
Set Implicit Arguments.

(**Intersection**)
Definition INT:= fun P:(e->Prop)->Prop=>  fun Q:(e->Prop)->Prop=> fun X:(e->Prop)=>  P(X) /\ Q (X).
Definition and:=INT.
Parameter man woman: e->Prop.
Definition Man:= fun x:e=> man x.
Definition Woman:= fun x:e=>  woman x.

(**some type checking**)
Check ER man.
Check INT (ER woman).
Check ER woman. 
Check and(ER man)(ER woman). (**note that and = INT!**) 

(**the MIN operator**)
Definition MIN:= fun Q: (e->Prop)->Prop=> fun P: (e->Prop)=> In Q P/\ forall P':e->Prop, (strict_included P' P)->not(In Q P').
Definition a:= fun P: (e->Prop)->Prop=> fun Q:(e->Prop)->Prop=> exists X, P X /\ Q X.
Parameter date: (e->Prop)->Prop.
Definition dated:= fun P:e->Prop=>  date P.

(**some type checking and evaluaton**)
Check (a(MIN((and(ER Man)(ER Woman))))dated).
Eval cbv in  (a(MIN((and(ER Man)(ER Woman))))dated).
Check dated.
Theorem DATED:  (a(MIN((and(ER Man)(ER Woman))))dated).
cbv. 
Definition PDIST:= fun (P' P:e->Prop)=>not (Empty_set P)/\ included P P'.
Parameter beer: e->Prop. 
Definition Beer:= fun x=>  beer x.
Parameter have: e->e->Prop. 
Definition  have_a_beer:= fun x:e=>exists y:e, beer(y) /\ have(x)(y). (**introduced some non-compositionality, can be done compositionally easily though**)


Check  (a(MIN((and(ER Man)(ER Woman))))(PDIST(have_a_beer))).
Eval cbv in  (a(MIN((and(ER Man)(ER Woman))))(PDIST(have_a_beer))).
Eval cbv in  (MIN((and(ER Man)(ER Woman)))).

(**some theorems**)

(** A man and a woman have a beer -> a woman has a beer*) 
Theorem MANWOMAN:  (a(MIN((and(ER Man)(ER Woman))))(PDIST(have_a_beer)))->  (a((((ER Woman))))(PDIST(have_a_beer))).
  cbv. intro. firstorder. Qed.

(** a man and a woman have a beer-> a man has a beer and a woman has a beer**)

Theorem MANWOMAN1:  (a(MIN((and(ER Man)(ER Woman))))(PDIST(have_a_beer)))->  (a((((ER Woman))))(PDIST(have_a_beer)))/\ (a((((ER Man))))(PDIST(have_a_beer))).  cbv. intro. firstorder. Qed. 
