Load test.
Print some.
Let a:=some.
Parameter signed1: object->human->Prop. 
Theorem EX:(walk) john-> some man (walk). (**GAUTO  x x x* (here only AUTO is used which takes no arguments, "x x x" are used because GAUTO takes obligatory 3 arguments, they play no role for proofs involving only use of AUTO*)  intro. unfold some. exists john. assumption. Qed.


Theorem EX1: some man (walk) -> (walk) john. 
cbv. intro. elim H. intro. intro. replace john with x. 
assumption. (**this cannot be proven*)

  Theorem EX2:  all man (walk)->walk john. (**GAUTO x x x*) 
    cbv. intro. apply H. Qed.
  
 Theorem EX3: all man (walk)->walk john->some man (walk). (**GAUTO x x x*)
  cbv. intros.  exists john. assumption. Qed.


 
 Ltac EXTAC:= cbv; eauto.
 Ltac EXTAC1 x:= cbv; try exists x;EXTAC.

                                 
Theorem EX5  :         all man (walk)-> some man (walk).  (** AUTOa John x x (here John is needed to be used with exists*)EXTAC1 john. Qed.


                                 
Theorem IRISH: (some irishdelegate)(on_time1 human(finish(the survey)))->(some delegate)(on_time1 human(finish(the survey))). (**AUTOa x x x.*)
cbv. intro. elim H. intro. intro. exists x. auto. 
Qed.


Theorem SWE:(a swede)(won3(a nobel_prize))->(a  scandinavian)(won3(a nobel_prize)). (**AUTOa x x x.*) 
  cbv. intros. elim H. intros. exists x. assumption. Qed.
Check not1.
Theorem SWE2:not ((a scandinavian)(won2(the nobel_prize)))->not ((a swede)(won2(the  nobel_prize))). (**AUTOa x x x.*)
  cbv. intro. intro. elim H. elim H0. intros. exists x. assumption. Qed.

Theorem SCAN: (no delegate)(on_time1 human(finish(the report)))->not((some scandinaviandelegate)(on_time1 human(finish(the report)))).
(**AUTOa x x x.*)  cbv. intro. intro. elim H0. intro. apply H. Qed.

 
 
Theorem IRISH2: (some delegate)(on_time (finish(the survey)))->(some delegate)((finish
                                                                                  (the survey))). 
  (**AUTOa ADV  x x(ADV  is used so destruct ADV can take effect*) cbv. intro.  destruct ADV in H. elim H. intro. intro. exists x0. apply f0. assumption. Qed.  (** on time delegate finish the survey, the second component of VER delegate  finish the survey is a proof that forall x: delegate, on time delegate finish the survey  x -> finish the survey x *)

Theorem FORT: fortunately (walk john)-> walk john. (**AUTOa ADVS x x (similarly)*) 
cbv. destruct ADVS. apply w. Qed.

Parameter in_europe: forall A:CN, (A->Prop)->(A->Prop).
Parameter can: forall A:CN, (A->Prop)->(A->Prop). 
Parameter travel: object->Prop. 
Parameter freely: forall A:CN, (A->Prop)->(A->Prop).
Parameter within_Europe: forall A:CN, (A->Prop)->(A->Prop). 
Let each:= all.
Let person:= human.
Parameter european: CN.
Axiom eu: european->human. Coercion eu: european>->human.
Parameter right_to_live_in_europe:CN.
Check have.
Parameter have1: object->human->Prop.


Axiom ro2: right_to_live_in_europe->object. Coercion ro2: right_to_live_in_europe>->object.

Theorem EUROPEAN: ((each european)(have1
(the right_to_live_in_europe))/\forall x:person, ((have1
(the right_to_live_in_europe)x)->can human(within_Europe human (freely human
(travel)))x))->(each european)(can human(within_Europe human(freely human
                                                                    (travel)))).
(**AUTOa x x x*)   cbv.  intuition.  Qed.

Theorem GENUINE: (a genuine_diamond)(has john)->(a diamond)(has john).
(**AUTOa x x x*)   cbv.   intro. elim H. intros. exists x. assumption. Qed.

Theorem MICKEY: (small animal mickey) ->not( large animal mickey).
  (** The proof here works due to the lexical semantics of Small, defined as both not large and not normalsized *)(**AUTOa x x x.*)  cbv. unfold not. intro. apply H. Qed.



Theorem MICKEY2: (all mouse (small animal)/\ large mouse mickey)->not( large animal mickey). (**AUTOa H1 x H1.*)  cbv. intro. elim H. intro. intro. destruct H0 with mickey. assumption.  Qed.

Set Implicit Arguments. 
Parameter Fast : forall A : CN, A -> Prop.
Parameter FASTER_THAN : forall A : CN, {p : A -> A -> Prop & forall h1 h2 h3 : A, (p h1 h2 /\ p h2 h3 -> p h1 h3) /\ (forall h4 h5 : A, p h4 h5 -> Fast  h4 -> Fast  h5)}.
Definition faster_than:= fun A:CN=>projT1 (FASTER_THAN A).
Parameter pc6082 : object.
Parameter itelxz : object.
Variables  o1 o2 o3 : object.
Definition as_fast_as:= fun A:CN=> fun a:A=>fun b:A=> Fast   a ->Fast  b.
Theorem FAST2: faster_than itelxz pc6082  /\ Fast itelxz -> Fast pc6082. cbv. intro. destruct FASTER_THAN in H.   case  a0 with o1 o2 o3. intros. elim H. intros. apply H1 with itelxz. assumption. assumption. Qed. (**This can be semiautomated with the existing tactics:  cbv. intro. destruct FASTER_THAN in H.   case  a0 with o1 o2 o3. AUTOa x x x.*)

Theorem KNOW:know john((won2 (the contract) itel))-> (won2 (the contract) itel) .  
(**AUTOa FACTIVE A B(this makes use of all the arguments, given that the first argument is always destructed as A B, we use A and B for the next two arguments of AUTOa*)cbv. destruct FACTIVE. intro. apply p with john. assumption. Qed.

Theorem CONJ:(signed1(the contract)(and3 smith jones anderson)-> (signed1(the contract)smith)). 
(**AUTOa AND3 A B.*)   cbv. destruct AND3. intro. apply a0. assumption. 

  Theorem CURRENTLY: (has1 (a_factory)itel) t-> currently (((has1 (a_factory)itel)))t.
 (**AUTOa x x x.*)    cbv. intros. destruct H.  AUTO. Qed.

  Definition john':= fun P:man->Prop=> P john.
  Definition mary':= fun P:woman->Prop=> P mary.

Theorem JEANSTE: walk john-> john' walk. cbv. intro. assumption.
                                         Check hit.
                                                                                                                                Definition hit':= fun P:(human->Prop)->Prop=> fun x:human=>P (  fun y:human=> hit y x).  
                                                                                                                                      

Theorem dfdfdfd: (all  man) (hit' (some woman))->  forall x:man,exists y:woman,  hit y x .
cbv. 
intros. 
destruct H with x. elim H with x. intros.  exists x0. assumption.
Parameter  Card:  CN-> nat.
Parameter half:nat.
Unset Implicit Arguments.
Definition most:= fun A:CN=> fun P: A->Prop=> exists x:A, P x /\ le half (Card(A)).
Check most man.
Theorem sdfsd: most man (walk)->most human (walk).                      cbv.intros. AUTO. elim H. intros. destruct H0. exists x. split.assumption.
                                                                        Theorem IRISH1: (most  irishdelegate)(on_time (finish(the survey)))->(most irishdelegate)( (finish(the survey))). cbv. destruct ADV.  intros.elim  H. intros. exists x0. split. apply f0. AUTO. destruct H0. assumption. 