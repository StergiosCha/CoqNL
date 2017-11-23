Require Import Bvector.
Require Import Coq.Lists.List.
Require Import Omega.
Load Lib.
Unset Implicit Arguments.
Inductive vector (A : Type) : nat -> Type :=
    Vnil : vector A 0
  | Vcons : A -> forall n : nat, vector A n -> vector A (S n).
Notation "a :: b" := (Vcons  a b).
Definition CN := Set.
Definition CNpl:= Set.
Parameters accountants men women:CNpl.
Parameters Bank Manager Accountant Car Meeting HumanTypes City Nobel_Prize Distance Mammal report student diamond delegate Location Time Duration Mouse survey Swede Scandinavian Contract Door Window Institution Phy Info factory Woman Man Object President Surgeon Animal Human: CN.
Parameter a_factory:factory.
Parameters t t1 t2 t3:Time.
Parameter Birmingham:City.
Parameter chairman_of_ITEL: Man.
Parameter cars: Car.
Parameter surgeon: Human->Prop.
Parameter scandinavian:Object->Prop.
Axiom do: diamond->Object. Coercion do: diamond >-> Object.
Axiom ph1: President->HumanTypes. Coercion ph1: President>->HumanTypes.
Axiom hh1: HumanTypes->Human. Coercion hh1: HumanTypes>->Human.
Axiom sw: Surgeon -> Human. Coercion sw: Surgeon >-> Human.
Axiom mo2: Meeting->Object. Coercion mo2: Meeting>->Object.
Axiom mh2: Manager->Human. Coercion mh2: Manager >-> Human.
Axiom co3: Car->Object. Coercion co3: Car>-> Object.
Axiom co2: City->Object. Coercion co2: City>-> Object.
Axiom maa: Mammal->Animal. Coercion maa: Mammal >-> Animal.
Axiom no1: Nobel_Prize ->Object. Coercion no1: Nobel_Prize>->Object.
Axiom sh1: student->Human. Coercion sh1: student>->Human.
Axiom dh:delegate->Human. Coercion dh: delegate>->Human.
Axiom dt: Duration->Time. Coercion dt:Duration>->Time.
Axiom fo:factory->Object. Coercion fo: factory>->Object.
Axiom ma: Mouse ->Animal. Coercion ma:Mouse>->Animal.
Axiom mh : Man->Human. Coercion mh : Man >-> Human.
Axiom wh : Woman->Human. Coercion wh : Woman >-> Human.
Axiom ha: Human-> Animal. Coercion ha: Human>-> Animal.
Axiom ao: Animal->Object. Coercion ao: Animal>-> Object.
Axiom DH: Door->Object. Coercion DH: Door>->Object.
 Axiom WH: Window->Object. Coercion WH: Window>->Object.
Axiom COB: Contract->Object. Coercion COB: Contract>->Object.
Axiom sh: Scandinavian->Human. Coercion sh: Scandinavian>->Human.
Axiom ss: Swede->Scandinavian. Coercion ss: Swede>-> Scandinavian.
Axiom so: survey->Object. Coercion so:survey>->Object.
Axiom cl: City->Location. Coercion cl: City>->Location.
Axiom ro1: report->Object. Coercion ro1: report>->Object.
Parameter opened: Human->Object->Prop.
Parameter has: Human->Object->Prop.
Parameter IN1: Object->Location.
Parameter four_legged: Animal->Prop.
Parameter precedes : Time -> Time -> Prop .
Definition reflexive_precedes:= fun  t:Time =>  precedes t t .
Parameter Signed: Object->Human->Prop.
Parameter won: Object->Human->Time->Prop.
Parameter Won:Object->Human->Prop. 
Parameter runs: Human->Prop.
Parameter animal: Animal->Prop.
Parameter Irish: Object->Prop.
Parameter John George Anderson Smith Jones:Man.
Parameter Mary: Woman.
Parameter Fido Dumbo: Animal. 
Parameter ITEL: Human.
Parameter Mickey: Mouse.
Parameter Large Normalsized: forall A:CN, A->Prop.
Definition Small:= fun A:CN=>fun a:A=> not (Large A(a))/\ not (Normalsized A(a)).
Parameter genuine: Object->Prop.
Parameter the: forall A:CN, A.
Parameter talk cycle drive: Human->Prop.
Parameter attack killed: Animal -> Animal -> Prop.
Definition all:= fun A:CN=> fun P:A->Prop=> forall x:A, P(x).
Definition no:= fun A:CN=> fun P:A->Prop=> forall x:A, not(P(x)).
Definition some:= fun A:CN=> fun P:A->Prop=> exists  x, P(x).

Parameter read : Human->Info->Prop.
Parameter finish: Object->Human->Prop. 
Parameter And: forall A:Type, A->A->A. 
Record PhyInfo : CN := mkPhyInfo { phy :> Phy; info :> Info }.
(* Book as Sigma-type with PhyInfo & BookQualia *)
Parameter Hold : Phy->Info->Prop.
Parameter R : PhyInfo->Prop.
Parameter W : Human->PhyInfo->Prop.
Record BookQualia (A:PhyInfo) : Set :=
mkBookQualia { Formal : Hold A A;
Telic : R A;
Agent : exists h, W h A }.
Record Book : Set := mkBook { Arg :> PhyInfo; Qualia : BookQualia Arg }.
Parameter boring : Info->Prop.
Record BBook : CN := mkBBook { b :> Book; _ : boring b }.
Record Irishdelegate : CN := mkIrishdelegate { c :> delegate; _ : Irish c }.
Record Scandinaviandelegate : CN := mkScandinaviandelegate { e :> delegate; _ : scandinavian e }.
Record genuine_diamond : CN := mkgenuine_diamond { f :> diamond; _ : genuine f}.
Parameter Won1:Object->Human->Prop.
Parameter Won2:((Object->Prop)->Prop)->Human->Prop.
Parameter hit: Human->Human->Prop.
Definition Not:= fun A:CN=> fun P:A->Prop=> fun x:A=> not(P x).
Set Implicit Arguments. 
Parameter ADV: forall (A : CN) (v : A -> Prop),sigT  (fun p : A -> Prop =>
 forall x : A, p x -> v x).
Definition on_time:= fun A:CN=> fun v:A->Prop=> projT1 (ADV(v)).
Parameter ADVS: forall ( v : Prop), sigT  (fun p : Prop => p  ->  v).
Definition fortunately:= fun v:Prop=>projT1 (ADVS v).
Unset Implicit Arguments. 
Inductive HUMAN : nat -> Type :=  HUMAN1 : forall n : nat, HUMAN n.
Parameter short:Human->Prop.
Definition height:= nat.
Parameter J G: sigT(fun x:height=> HUMAN x).
Definition j:= projT2 J.
Definition g:= projT2 G.
Set Implicit Arguments.
Parameter SHORTER_THAN: sigT(fun p:Human->Human->Prop=> forall h1:Human,forall h2:Human,forall h3:Human, (p(h1)(h2)/\ p(h2)(h3)->p(h1)(h3))/\     forall
h1 h2:Human, p h1 h2 -> (short(h2)-> short (h1))).
Definition shorter_than:=  projT1(SHORTER_THAN).
Parameter SHORTER_THAN1:forall i j : height, sigT( fun p : HUMAN i -> HUMAN j -> Prop =>forall (h1 : HUMAN i) (h2 : HUMAN j), p h1 h2 <-> gt i j).
Definition shorter_than1 :=fun i j : height => projT1 (SHORTER_THAN1 i j).
Unset Implicit Arguments.
Fixpoint nth3 (A : Type) (n g : nat) (l : vector A g) (default : A) {struct l}: A :=match n with | 0 => match l with| Vnil _ => default| Vcons _ x _ _ => x end | S m =>match l with| Vnil _ => default| Vcons _ x n0 t => nth3 A m n0 t x end end.  
Definition each_other1:=fun (n : nat) (P : Human -> Human -> Prop) (u : vector Human (n + 2))=>forall i j : nat,i <= n + 2 /\ j <= n + 2 /\ i <> j ->exists d,exists g, P (nth3 Human i (n + 2) u d) (nth3 Human j (n + 2) u g) /\P (nth3 Human j (n + 2) u g) (nth3 Human i (n + 2) u d). 
Parameter sign: Object->Human->Time->Prop.
Parameter Interval: list Time->Time.
Parameter fouryears:list Time.
Definition FOR:= fun T: list Time=> fun P:Time ->Prop=> fun t:Time=> P(t) /\ Interval(T) = t /\ forall t1:Time, In t1 T -> P(t1).
Definition Year:= nat.
Definition Month:= nat.
Definition Day:= nat.
Parameter default_y:Year.
Parameter default_m:Month.
Parameter default_d: Day.
Parameter DATE : Year -> Month -> Day -> Time.
Let default_t:= DATE default_y default_m default_d.
Definition currently:=fun P : Time -> Prop=>fun t:Time=> P default_t.
Parameter Have: Object->Human->Time->Prop.
Definition Has:=fun (x : Object)(y : Human) (t : Time)=>
Have x y t /\ t = default_t.
Parameter On_time: forall A:CN, (A->Prop)->(A->Prop). 
Parameter live: Location->Human->Time->Prop.


Parameter run : forall n : nat, vector Human n -> Prop.
Definition lived:= fun x:Location=> fun y:Human=> fun t:Time=> live x y t/\precedes t default_t.
Definition signed:=fun (x : Object) (y : Human) (t : Time) =>
sign x y t /\ precedes t (DATE default_y default_m
default_d).
Parameter FACTIVE: sigT (fun p: Human->Prop->Prop => forall h:Human, forall P:Prop, p h P -> P).
Definition know:= projT1 FACTIVE.
Definition saw:= projT1 FACTIVE.
Set Implicit Arguments.
Parameter AND: forall A:Type, forall x y :A, sigT(fun a:A=>forall p:A->Prop, p(a) ->p(x) /\p(y)).  
Definition and:= fun A:Type=> fun x y:A=>projT1(AND x y).
Parameter AND3: forall A:Type, forall x y z:A, sigT(fun a:A=>forall p:A->Prop, p(a) ->p(x) /\p(y)/\ p(z)).  
Definition and3:= fun A:Type=> fun x y z:A=>projT1(AND3 x y z).
Parameter DIS: forall A:Type, forall x y z:A, sigT(fun a:A=>forall p:A->Prop, p(a) -> p(x) \/p(y )\/ p(z)).  
Definition or3:= fun A:Type=> fun x y z:A=>projT1(DIS x y z).
Unset Implicit Arguments.
Parameters cycles drives: Human->Prop.
Parameter Stergios Zhaohui: Human.
Variable d: Swede. 
Variable n: Nobel_Prize.
Parameter walk:Animal->Prop.
Inductive PRESIDENT : Time -> Type :=  PRESIDENT1 : forall t : Time, PRESIDENT t.
Definition former:=fun x : Time -> CN =>(x default_t -> False) /\ (exists t, precedes t default_t /\ (PRESIDENT t -> True)).
Definition last_year1 :=fun (P : Time -> Prop) =>P (DATE (default_y - 1) default_m default_d).
Parameter meettr: Human->Human->Prop.

Definition last_year:= fun P : Time -> Prop => exists m , exists n , P (DATE (default_y - 1) m n) /\ m <= 30 /\ 7 <= n.
Ltac AUTO:= cbv delta;intuition;try repeat congruence;  jauto;intuition.
Definition NOW:= fun m: nat=> fun n:nat=> fun l:nat=> default_t = DATE m n l /\ default_y = m /\ default_m = n /\ default_d = l.
Ltac AUTOS :=fun H H0 H1 H2 H3 H4 x y z =>try exists x; try exists x; intuition;try repeat congruence; try destruct H; try destruct H0;try destruct H1; try destruct H2; try destruct H3;try destruct H4; try induction H with y z; try induction H0 with y z;try induction H1 with z y; try induction H2 with y z; try induction H3 with y z; try induction H4 with z y; try destruct ADV; jauto; intuition; repeat AUTO; repeat AUTO.
Ltac AUTO1a  x y z i j :=cbv; try destruct x; try destruct y;try destruct z;intro; try destruct i; try destruct i with j;AUTO.
Ltac AUTO1  x y z i j g h := cbv;try destruct x;try intro; try destruct y; try destruct z;try case i with j g;try case i with j g h; AUTO;  try eapply g; try omega; try case i with j; try case g with h; try apply y with z; AUTO; AUTO; intuition; try repeat congruence; jauto;intuition.
Ltac AUTO2  x y z i j g :=try unfold x; try unfold y; try unfold z; try destruct x; try destruct y;try destruct z; try eapply g; try omega; try case i with j g; AUTO; AUTO;cbv delta; intuition; try repeat congruence; jauto;intuition. 
Ltac AUTO3  a b c d e f g h i:=solve [ AUTO1 a b c d e f g |AUTO| AUTO2 a b d e f|AUTOS a b c d e f g h i]. 
Ltac AUTO4 a b c d e f g h i :=solve[ AUTO1 a b c d e f g| AUTO2 a b c d e f | AUTO ].
Ltac AUTO5 a b c d e f g h i :=solve[AUTO1a a b c d e| AUTO1 a b c d e f g| AUTO2 a b c d e f | AUTO ]. 
Ltac AUTOa  x i:= cbv;try destruct x;try intro;try ecase i;  AUTO;  try eapply i; try omega; AUTO; intuition; try repeat congruence; jauto;intuition.
Ltac GAUTO:= solve[AUTO|AUTOa].
