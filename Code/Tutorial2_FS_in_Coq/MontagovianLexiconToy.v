
(** Retore's 2013 toy semantic grammar including multi-sortedness and coercions to handle co-predication*)
Load LibTactics.
Ltac AUTO:= cbv delta;intuition;try repeat congruence;  jauto;intuition.
Definition e:=Set.
Parameters Physical_Object Informational_Object Human  People Place Book Town:e.
Let H:= Human.
Let Phi:=Physical_Object.
Let I:=Informational_Object.
Let P:= People.
Let Pl:= Place.
Let B:= Book.
Let T:= Town.
Definition t:= Prop. 
Parameters  Phi_ I_ P_ Pl_ T_: e->t.
Inductive OneBOOK : Set := BOOK.
Definition BSem1:= e->t.
Definition BSem2 := B->B.
Definition BSem3 := B->Phi.
Definition BSem4 := B->I.
Parameter B_ : BSem1.
Parameter IdB : BSem2.
Parameter t1 : BSem3.
Parameter t2 : BSem4.
Definition b1 (b:OneBOOK) : BSem1 := B_. Coercion b1 : OneBOOK >-> BSem1.
Definition b2 (b:OneBOOK) : BSem2 := IdB. Coercion b2 : OneBOOK >-> BSem2.
Definition b3 (b:OneBOOK) : BSem3 := t1. Coercion b3 : OneBOOK >-> BSem3.
Definition b4 (b:OneBOOK) : BSem4 := t2. Coercion b4 : OneBOOK >-> BSem4.
Parameter wide: Pl->t.
Parameter voted: P->t.
Parameter read: Human->I->Prop.
Parameter mastered: Human->I->Prop.
Parameter picked_up:Human->Phi->Prop.
Parameter ksi:e.
Unset Implicit Arguments. 
Definition PAND:= fun a:e=>fun b: e=> fun P:a->t=>fun Q:b->t=>fun x:e=>fun y:x=>fun f: x->a=>fun g:x->b=> and(P(f(y)))(Q(g(y))).
Parameter John:H. 
Parameter War_and_Peace: B .
Check b4.
Check mastered John (t2  War_and_Peace).
Check picked_up John (t1 War_and_Peace).
Print PAND. 
Check PAND Phi I (picked_up John)(mastered  John)B War_and_Peace (t1)(t2).
Theorem PAND1: PAND Phi I (picked_up John)(mastered  John)B War_and_Peace (t1)(t2)-> and (picked_up John (t1 War_and_Peace))(mastered John(t2 War_and_Peace)). (**AUTO fully automates the proof*)
cbv. intro. assumption. Qed. 