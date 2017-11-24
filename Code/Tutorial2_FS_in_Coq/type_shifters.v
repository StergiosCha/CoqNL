Definition e:=Set.
Definition t:= Prop.
Definition Ident:= fun x:e=>  fun y:e=>  x=y.
Check Ident. 
Definition Lift:= fun x: e=> fun P:e->t=>  P x.
Definition THE:= fun P Q:e->t=>  exists x: e, (forall y,  P y <-> x=y /\ Q x).
(**Lowering**)
Definition BE:= fun P:(e->t)->t=> fun x:e=> P (fun y:e=>(y=x)).
Check BE. 

(**Polymorphic BE**)
Inductive Onebe : Set := be.
Definition BSem1 := e->e->t.
Definition BSem2 := (e->t)->e->t.
Definition be1 : BSem1:= fun x y=> x = y. 
Definition be2 : BSem2:= fun P:e->t=>  fun x:e=>  P x. 
Definition b1 (b:Onebe) : BSem1 := be1. Coercion b1 : Onebe >-> BSem1.
Definition b2 (b:Onebe) : BSem2 := be2. Coercion b2 : Onebe >-> BSem2.

(**In action, checking lift ident and BE**)
Parameter man woman human: e->t.
Parameter j m h: e.
Check Lift j.
Eval compute in Ident j.
Definition a:= fun P Q:e->t=> exists x:e, P x /\ Q x.
Check BE (a man) j.
Eval compute in BE (a man) j.
Definition every:= fun P Q:e->t=> forall x, P x->Q x.
Eval compute in BE (every man) j.

(**Checking Polymorphism**)
Eval compute in (be:BSem1) (m) j. 
Eval compute in (be:BSem2) (man) j.


