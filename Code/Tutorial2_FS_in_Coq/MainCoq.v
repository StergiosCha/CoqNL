Require Import Bvector.
Require Import Coq.Lists.List.
Require Import Omega.
Load LibTactics.
Unset Implicit Arguments.
Inductive vector (A : Type) : nat -> Type :=
    Vnil : vector A 0
  | Vcons : A -> forall n : nat, vector A n -> vector A (S n).
Notation "a :: b" := (Vcons  a b).
Definition CN:= Set.

(** Common Nouns as Types *)
Parameter bank manager accountant car meeting humantypes city nobel_prize distance mammal report student diamond delegate location time duration mouse survey swede scandinavian contract door window institution Phy Info factory woman man object president surgeon animal human:CN.

      (* *Book as a Sigma Type encoding Pustejovsky's qualias structure. The first projection is coerction, thus Book is a subtype of phy.info The and dot*)
Record PhyInfo : CN := mkPhyInfo { phy :> Phy; info :> Info }.
(* Book as Sigma-type with PhyInfo & BookQualia *)
Parameter Hold : Phy->Info->Prop.
Parameter R1 : PhyInfo->Prop.
Parameter W : human->PhyInfo->Prop.
Record BookQualia (A:PhyInfo) : Set :=
mkBookQualia { Formal : Hold A A;
Telic : R1 A;
Agent : exists h:human, W h A }.
Record Book : Set := mkBook { Arg :> PhyInfo; Qualia : BookQualia Arg }.

     (** Subtyping relations. Coercion ensures that in every situation requiring an object of type b, an object of type a can be used (with a<b) *)
Axiom do: diamond->object. Coercion do: diamond >-> object.
Axiom ph1: president->humantypes. Coercion ph1: president>->humantypes.
Axiom hh1: humantypes->human. Coercion hh1: humantypes>->human.
Axiom sw: surgeon -> human. Coercion sw: surgeon >-> human.
Axiom mo2: meeting->object. Coercion mo2: meeting>->object.
Axiom mh2: manager->human. Coercion mh2: manager >-> human.
Axiom co3: car->object. Coercion co3: car>-> object.
Axiom co2: city->object. Coercion co2: city>-> object.
Axiom maa: mammal->animal. Coercion maa: mammal >-> animal.
Axiom no1: nobel_prize ->object. Coercion no1: nobel_prize>->object.
Axiom sh1: student->human. Coercion sh1: student>->human.
Axiom dh:delegate->human. Coercion dh: delegate>->human.
Axiom dt: duration->time. Coercion dt:duration>->time.
Axiom fo:factory->object. Coercion fo: factory>->object.
Axiom ma: mouse ->animal. Coercion ma:mouse>->animal.
Axiom mh : man->human. Coercion mh : man >-> human.
Axiom wh : woman->human. Coercion wh : woman >-> human.
Axiom ha: human-> animal. Coercion ha: human>-> animal.
Axiom ao: animal->object. Coercion ao: animal>-> object.
Axiom DH: door->object. Coercion DH: door>->object.
 Axiom WH: window->object. Coercion WH: window>->object.
Axiom COB: contract->object. Coercion COB: contract>->object.
Axiom sh: scandinavian->human. Coercion sh: scandinavian>->human.
Axiom ss:swede->scandinavian. Coercion ss: swede>-> scandinavian.
Axiom so: survey->object. Coercion so:survey>->object.
Axiom cl: city->location. Coercion cl: city>->location.
Axiom ro1: report->object. Coercion ro1: report>->object.
(** Some quantifiers *)
Definition some:= fun A:CN=> fun P:A->Prop=> exists x:A, P(x). 
Definition all:= fun A:CN=> fun P:A->Prop=> forall x:A, P(x).
Definition no:= fun A:CN=> fun P:A->Prop=> forall x:A, not(P(x)).
Let a:= some.
Let each:=all.

(** Factive verbs as first projections of a general FACTIVE Sigma *)
Parameter FACTIVE: sigT (fun p: human->Prop->Prop => forall h:human, forall P:Prop, p h P -> P).
Definition know:= projT1 FACTIVE.
Definition saw:= projT1 FACTIVE.
(** Same for conjunction and disjunction. No general conjunction rule given here, this is for 2 place and three place conjunction *)
Set Implicit Arguments. 

Parameter AND: forall A:Type, forall x y :A, sigT(fun a:A=>forall p:A->Prop, p(a) ->p(x) /\p(y)).
Definition and:= fun A:Type=> fun x y:A=>projT1(AND x y).
Parameter AND3: forall A:Type, forall x y z:A, sigT(fun a:A=>forall p:A->Prop, p(a) ->p(x) /\p(y)/\ p(z)).  
Definition and3:= fun A:Type=> fun x y z:A=>projT1(AND3 x y z).
Parameter DIS: forall A:Type, forall x y z:A, sigT(fun a:A=>forall p:A->Prop, p(a) -> p(x) \/p(y )\/ p(z)).  
Definition or3:= fun A:Type=> fun x y z:A=>projT1(DIS x y z).
(** Regular VP conjunction if you do not like the above *)
Definition AND1:= fun A:CN=>  fun P: A->Prop=> fun Q:A->Prop=>fun x:A=>P(x) /\Q(x).
(** Adjectives, intersective as regular predicates, subsectives as polymorphic predicates, privative as disjoint union types and former as involving time parameters *)

(**Veridical Adverbs using Sigma types**)
Set Implicit Arguments. 
Parameter ADV: forall (A : CN) (v : A -> Prop),sigT  (fun p : A -> Prop =>
 forall x : A, p x -> v x).
Definition on_time:= fun A:CN=> fun v:A->Prop=> projT1 (ADV(v)).
Parameter ADVS: forall ( v : Prop), sigT  (fun p : Prop => p  ->  v).
Definition fortunately:= fun v:Prop=>projT1 (ADVS v).
Unset Implicit Arguments. 
Parameter boring : Info->Prop.
Parameter large normalsized: forall A:CN, A->Prop.
Definition small:= fun A:CN=>fun a:A=> not (large A(a))/\ not (normalsized A(a)).
Parameter genuine: object->Prop.
Parameter short:human->Prop.
Parameter irish: object->Prop.
Parameter scandinavian1:object->Prop.

(** Comparatives again involving an auxiliary Sigma. Two versions, one with height parameters one without. The one with height parameters presuspposes that Common Nouns can be indexed with height parameters. Here we shown the indexed type for Human, i.e. Humans indexed with heights *)
Definition height:= nat.
Inductive HUMAN : nat -> Type :=  HUMAN1 : forall n : nat, HUMAN n.
Parameter J G: sigT(fun x:height=> HUMAN x).
Definition j:= projT2 J.
Definition g:= projT2 G.
Parameter SHORTER_THAN: sigT(fun p:human->human->Prop=> forall h1:human,forall h2:human,forall h3:human, (p(h1)(h2)/\ p(h2)(h3)->p(h1)(h3))/\     forall
h1 h2:human, p h1 h2 -> (short(h2)-> short (h1))).
Definition shorter_than:=  projT1(SHORTER_THAN).
Parameter SHORTER_THAN1:forall i j : height, sigT( fun p : HUMAN i -> HUMAN j -> Prop =>forall (h1 : HUMAN i) (h2 : HUMAN j), p h1 h2 <-> gt i j).
Definition Shorter_than1 :=fun i j : height => projT1 (SHORTER_THAN1 i j).
(** experimenting with defining quantifiers using vectors *)
Definition three :=fun (A : CN)  (P :forall n:nat, vector A n ->Prop)=>exists x:nat, exists z : vector A x, P x z /\ ge x 3.
Definition NO:=fun (A : CN) (P : forall n : nat, vector A n -> Prop) =>forall (n : nat) (z : vector A n), ~ P n z.
Definition exactly_one :=fun (A : CN)  (P :forall n:nat, vector A n ->Prop)=>exists! x:nat, exists z : vector A x, P x z /\ x = 1/\ forall n:nat, forall z: vector A n, not (P n z).
(** Experimenting with a simple model of tense. A time parameter is assumed as an argument for verbs *)
Parameter sign: object->human->time->Prop.
Parameter Interval: list time->time.
Parameter fouryears:list time.
Definition FOR:= fun T: list time=> fun P:time ->Prop=> fun t:time=> P(t) /\ Interval(T) = t /\ forall t1:time, In t1 T -> P(t1).
Definition Year:= nat.
Definition Month:= nat.
Definition Day:= nat.
Parameter default_y:Year.
Parameter default_m:Month.
Parameter default_d: Day.
Parameter DATE : Year -> Month -> Day -> time.
Let default_t:= DATE default_y default_m default_d.
Definition currently:=fun P : time -> Prop=> P default_t.
Parameter have: object->human->time->Prop.
Definition has:=fun (x : object)(y : human) (t : time)=>
have x y t /\ t = default_t.
Parameter on_time1: forall A:CN, (A->Prop)->(A->Prop). 
Parameter live: location->human->time->Prop.
Parameter run : forall n : nat, vector human n -> Prop.
Parameter precedes : time -> time -> Prop .
Definition lived:= fun x:location=> fun y:human=> fun t:time=> live x y t/\precedes t default_t.
Definition signed:=fun (x : object) (y : human) (t : time) =>
sign x y t /\ precedes t (DATE default_y default_m
default_d).
