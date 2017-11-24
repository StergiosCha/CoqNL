Unset Implicit Arguments.
Definition CN:= Set.

Parameters  Swede Scandinavian Man Human Report Nobel_Prize Woman Animal Object Delegate Survey: CN.

(** Quantifier some and letting a be some**)
Definition some:= fun A:CN=> fun P:A->Prop=> exists  x, P(x).
Let a:= some.
(**the as regarding an object of type A**)
Parameter the: forall A:CN, A.


(**Declaring subtyping relations**)
Axiom ro: Report->Object. Coercion ro: Report>-> Object.
Axiom no1: Nobel_Prize -> Object. Coercion no1: Nobel_Prize>-> Object. 
Axiom mh : Man->Human. Coercion mh : Man >-> Human.
Axiom wh : Woman->Human. Coercion wh : Woman >-> Human.
Axiom ha: Human-> Animal. Coercion ha: Human>-> Animal.
Axiom ao: Animal->Object. Coercion ao: Animal>-> Object.
Axiom sh: Scandinavian->Human. Coercion sh: Scandinavian>->Human.
Axiom ss: Swede->Scandinavian. Coercion ss: Swede>-> Scandinavian.
Axiom dh:Delegate->Human. Coercion dh: Delegate>->Human.
Axiom so: Survey->Object. Coercion so:Survey>->Object.
(**adjectives, single predicate type**)
Parameter Irish scandinavian: Human -> Prop. 
(** the two won entries**)
Parameter Won:Object->Human->Prop. 
Parameter Won2:((Object->Prop)->Prop)->Human->Prop.

(**adjectival modification as sigmas, here dependent records**)
Record Irishdelegate : CN := mkIrishdelegate { c :> Delegate; C : Irish c }.
Record Scandinaviandelegate : CN := mkScandinaviandelegate { e :> Delegate; E : scandinavian e }.
Check mkIrishdelegate.

(**Adverb**)
Set Implicit Arguments. 
Parameter On_time: forall A:CN, (A->Prop)->(A->Prop). 
Parameter finish: Object->Human->Prop. 
Unset Implicit Arguments.

(** A yes case: some IDs finish the survey on time-> some Ds finish the survey on time**)
Theorem IRISH: (some Irishdelegate(On_time(finish(the Survey)))->(some Delegate)(On_time (finish(the Survey)))).
cbv. intro. elim H. intros. exists x. apply H0.  Qed.
  (** Another YES example, note that FraCaS gives an extra premise: Every Swede is Scandinavian. This is not needed, the subtyping takes care of it**)
  Theorem SWEDE1: (a Swede)(Won2 (a Nobel_Prize))->(a  Scandinavian (Won2(a Nobel_Prize))).
    cbv. intros. elim H. intros. exists x. assumption. Qed.
  (**Introducing Variables for types swede and nobel_prize. you can do this for evey type if we wanted**)
 Variables s1 s2: Swede.
 Variables n1 n2: Nobel_Prize.

 (**The SWEDE case with no type lifting**)
  Theorem SWEDE2: exists x:Swede, exists y:Nobel_Prize, Won(y)(x)->exists x:Scandinavian, exists y:Nobel_Prize, Won(y)(x).
    (**eauto fails**)  
    exists s1. exists n1. intro. exists s1. exists n1. assumption. Qed.
Definition no:= fun A:CN=>  fun P: A->Prop=>  not (exists x: A,  P x). 
(** A NO example: no delegate finished the report on time->some scandinavian delegate finished the report on time.**)
Theorem SCANDEL: (no Delegate)(On_time (finish(the Report)))->not((some Scandinaviandelegate)(On_time (finish(the Report)))).
  cbv. intro. intro. elim H0. intro. intro.  apply H. exists x. assumption. Qed.


Theorem IRISHDEL: (some Delegate)(On_time (finish(the Survey)))->(some Irishdelegate)(On_time (finish(the Survey))). cbv. intros. elim H. intros. (**exists x.**) Abort all. (**This cannot be proven, neither its negation. You can try the negation yourselves if you do not trust me!**)

                       (**Veridical Adverbs**)
Set  Implicit Arguments. 
Parameter ADV: forall (A : CN) (v : A -> Prop),sigT  (fun p : A -> Prop =>
 forall x : A, p x -> v x).
Definition on_time:= fun A:CN=> fun v:A->Prop=> projT1 (ADV(v)).

Theorem IRISH2: (some Delegate)(on_time(finish(the Survey)))->(some Delegate)((finish(the Survey))).
  cbv. destruct ADV. intro. elim  H. intros. exists x0. apply f.  assumption. Qed.

                  (**Sentence adverb veridicality**)
Parameter ADVS: forall ( v : Prop), sigT  (fun p : Prop => p  ->  v).
Definition fortunately:= fun v:Prop=>projT1 (ADVS v).

Parameter walk: Human -> Prop.
Parameter John: Man.

Theorem ADVSVER: fortunately (walk John)-> walk John. cbv. destruct ADVS. assumption. Qed.

(**some non-compositionality (playing no role in the proofs though**)
Parameter in_Europe: forall A:CN, (A->Prop)->(A->Prop).
Parameter right_to_live_in_Europe: CN.
Axiom roo: right_to_live_in_Europe-> Object. Coercion roo:right_to_live_in_Europe >-> Object.
Parameter can: forall A:CN, (A->Prop)->(A->Prop). 
Parameter travel: Object->Prop. 
Parameter freely: forall A:CN, (A->Prop)->(A->Prop).
Parameter within_Europe: forall A:CN, (A->Prop)->(A->Prop).
Unset Implicit Arguments. 
Let each:= all.
Parameter European: CN.
Axiom eh:  European -> Human. Coercion eh: European >-> Human.
Parameter have: Object->Human->Prop.
Let person:= Human. 
	Theorem EUROPEAN: ((each European)(have
(the right_to_live_in_Europe))/\forall x:person, ((have
				(the right_to_live_in_Europe)x)->can (within_Europe(freely 
				(travel)))x))->(each European)(can (within_Europe(freely
				(travel)))). cbv. intros. elim H. intros. elim H. intros. apply H3. apply H2. Qed. 