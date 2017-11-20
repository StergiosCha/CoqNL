
Require Import Setoid.
(**DomCN is the old CN, the universe of common nouns**)
Definition DomCN:=Set.

(**Equiv is an equivalence relation on elements of DomCN**)
Record Equiv (A:DomCN) : Type := mkEquiv { eq1:> A->A->Prop; _eq2: reflexive A(eq1)/\ symmetric A eq1/\ transitive A eq1}.
Check Equiv.
(**CN is a setoid, here expressed a record, second projection is the equiv relation on the type**)
Record CN := mkCN{ B:> DomCN; B2:Equiv B}.

(**small capitals for the types in DomCN**)
Parameter human  man : DomCN.
Parameter john: human.
Axiom mh: man->human. Coercion mh: man>->human.

(**IC for Human**)
Parameter IC_Human : Equiv(human).
(**This is the CN type in Capitals as a setoid**)
Definition HUMAN:= mkCN human IC_Human.

(**Given the IC for man as being inherited from human**)
Definition AIC_Man := fun x: man=>fun y:man=> IC_Human(x)(y).
(** We prove the equivalence of AIC_Man**)
Theorem EQ: reflexive  man  AIC_Man/\  symmetric man AIC_Man/\  transitive man AIC_Man. cbv. destruct  IC_Human. destruct _eq3. destruct H0. split. intro. unfold reflexive in H.  apply H. split. intro. unfold symmetric in H0. intuition. intro. unfold transitive in H1. intro. intro. intros. apply H1 with y. assumption. assumption. Qed.
Check eq1.
Check _eq2.
Check Equiv.

(**A first definition of three, prety standard but takes into account the IC, B and B2 are the two respective projections**)
Definition three:=fun A:CN=> fun P:A.(B)->Prop=>exists x:A.(B),P(x)/\exists y:A.(B), P(y)/\ exists z:A.(B), P(z)/\not((A.(B2))(x)(y))/\not((A.(B2))(y)(z)) /\not((A.(B2))(x)(z)).

(** Similarly for some**)
Definition some:=fun A:CN=> fun P:A.(B)->Prop=> exists x:A.(B), P(x).

(**Predicates are functions from the first projection of the CN to Prop**)
Parameter walk: HUMAN.(B)->Prop.
Check walk john.
Check (three HUMAN) walk.

(** Defining the IC for man and then MAN**)
Definition IC_Man:=  mkEquiv man AIC_Man EQ.
Definition MAN:= mkCN man IC_Man.
 

(**A proof that if three men walk, three humans walk**)
Theorem MANWALK: (three MAN) walk-> (three HUMAN) walk. cbv. intros. destruct H.
                                                        destruct H. destruct H0. destruct H0. destruct H1. destruct H1. destruct H2. destruct H3. exists x. split. intuition. exists x0. split. intuition. exists x1. split. intuition. intuition. Qed.

(** Defining the dot for PhyInfo and type book**)
Parameter Phy Info: DomCN.
Record PhyInfo : DomCN := mkPhyInfo { phy :> Phy; info :> Info }.
Parameter book: DomCN.
Axiom bf: book-> PhyInfo. Coercion bf: book >-> PhyInfo.

(** IC for Phy, Info and PhyInfo**)
Parameter IC_Phy: Equiv(Phy).
Parameter IC_Info: Equiv(Info).
Definition PHY:= mkCN Phy IC_Phy.
Definition INFO:= mkCN Info IC_Info.
Parameter IC_PhyInfo: Equiv PhyInfo. 
Definition PHYINFO:= mkCN PhyInfo  IC_PhyInfo.

(** Defining the IC criteria for book**)
Definition AIC_Book1 := fun x: book=>fun y:book=> IC_Phy(x)(y).
Definition AIC_Book2 := fun x: book=>fun y:book=> IC_Info(x)(y).
Theorem EQ1: reflexive  book  AIC_Book1/\  symmetric book AIC_Book1/\  transitive book AIC_Book1. cbv. destruct  IC_Phy. destruct _eq3. destruct H0. split. intro. unfold reflexive in H.  apply H. split. intro. unfold symmetric in H0. intuition. intro. unfold transitive in H1. intro. intro. intros. apply H1 with y. assumption. assumption. Qed.

Theorem EQ2: reflexive  book  AIC_Book2/\  symmetric book AIC_Book2/\  transitive book AIC_Book2. cbv. destruct  IC_Info. destruct _eq3. destruct H0. split. intro. unfold reflexive in H.  apply H. split. intro. unfold symmetric in H0. intuition. intro. unfold transitive in H1. intro. intro. intros. apply H1 with y. assumption. assumption. Qed.

Definition IC_Book1:=  mkEquiv book  AIC_Book1 EQ1.
Definition IC_Book2:=  mkEquiv book  AIC_Book2 EQ2.
Definition Book1:= mkCN book IC_Book1.
Definition Book2:= mkCN book IC_Book2.
Parameter picked_up: human->Phy->Prop.
Parameter mastered: human->Info->Prop.
Parameter the: forall A:DomCN, A.

(**mastered three books, mastered three INFO**)
Theorem MASTEREDINFO:(three Book2) (mastered john)-> (three INFO)(mastered john). cbv. intros. destruct H. destruct H. destruct H0. destruct H0. destruct H1. destruct H1. destruct H2. destruct H3. exists x. split.    intuition. exists x0. split. intuition. exists x1. split. intuition. split. intuition. split. intuition. intuition. Qed.

Theorem pickedupPHY:(three Book1) (picked_up john)-> (three PHY)(picked_up john). cbv. intros. destruct H. destruct H. destruct H0. destruct H0. destruct H1. destruct H1. destruct H2. destruct H3. exists x. split.    intuition. exists x0. split. intuition. exists x1. split. intuition. split. intuition. split. intuition. intuition. Qed.

Definition AND:= fun A:DomCN=>  fun P: A->Prop=>fun Q:A->Prop=> fun x:A=> P(x) /\ Q(x).

Theorem pickedupMasteredPHY:(three Book2) (AND(book)(picked_up john)(mastered john))-> (three INFO)(mastered  john). cbv. intros. destruct H. destruct H. destruct H. destruct H0. destruct H0. destruct H0. destruct H2. destruct H2. destruct H2. destruct H4. exists x. split. intuition. intuition.  exists x0. intuition. intuition. exists x1. split. intuition. intuition. Qed.

Section BOOK.
Variable BOOK1BOOK2: forall x:book, forall y:book, IC_Book1  x y-> IC_Book2 x y.
 Theorem pick1edupMasteredPHY:(three Book2) (AND(book)(picked_up john)(mastered john))-> (three PHY)(picked_up  john).
   cbv. intros. destruct H. destruct H. destruct H. destruct H0. destruct H0. destruct H0. destruct H2. destruct H2. destruct H2. destruct H4. exists x. split. intuition. intuition.  exists x0. intuition. intuition. exists x1. split. intuition.      split. destruct IC_Book2 in BOOK1BOOK2. destruct IC_Book1 in BOOK1BOOK2. destruct _eq3. destruct a. destruct _eq4. destruct a.      destruct IC_Info in H4. destruct IC_Phy. destruct IC_Info in H7. destruct IC_Info in H8. destruct _eq5. destruct _eq4. destruct _eq6. destruct H9. destruct _eq3. destruct H13. destruct H11. unfold transitive in H18. unfold symmetric in H11. unfold reflexive in H10. unfold transitive in H17. unfold symmetric in H13. unfold reflexive in H12. unfold transitive in H14. unfold symmetric in H9. unfold reflexive in H6. destruct H16. unfold transitive in H19. unfold symmetric in H16. unfold reflexive in H15. firstorder.  Abort all. 

 (** Definition of three for subtypes  **)
 Definition Three_v:= fun (A:CN)(D:CN)=>fun c: A.(B)->D.(B)=>fun P: D.(B)->Prop=>exists x y z:A.(B), not((D.(B2))(c(x))(c(y)))/\not((D.(B2))(c(y))(c(z))) /\not((D.(B2))(c(x))(c(z)))/\P (c(x))/\ P(c(y))/\P(c(z)).

 

 
 Definition Three_dot2:=fun c: Book1.(B)->PHYINFO.(B)=>fun P:PHYINFO.(B)->Prop=>exists x y z: Book1.(B), not((PHY.(B2))(c(x))(c(y)))/\not((PHY.(B2))(c(y))(c(z))) /\not((PHY.(B2))(c(x))(c(z)))/\not((INFO.(B2))(c(x))(c(y)))/\not((INFO.(B2))(c(y))(c(z))) /\not((INFO.(B2))(c(x))(c(z)))/\P (c(x))/\ P(c(y))/\P(c(z)). (**arbitrary A, WHEN SUBTYPING WORKS C SHOULD BE REDUNDANT, CHECK IT**)
 
Definition and:= fun A:DomCN=>  fun P: A->Prop=>fun Q: A->Prop=>fun x: A=>  P(x)/\Q(x).
Axiom c1: Book1.(B)->PHYINFO.(B). Axiom c2: Book2.(B)->PHYINFO.(B).
 (**John picked up and mastered three books->John mastered three informational objects**)
Theorem pickedmastered3m: (Three_dot2 c1)(and PHYINFO(picked_up john )(mastered john))-> exists x y z: Book1.(B),mastered (john)(c1 x)/\mastered (john)(c1 y)/\mastered (john)(c1 z)/\ not((INFO.(B2))(c1(x))(c1(y)))/\not((INFO.(B2))(c1(y))(c1(z)))/\not((INFO.(B2))(c1(x))(c1(z))). cbv. firstorder. Qed.

(**John picked up and mastered three books->John picked_up three physical objects**)                                                                                           
Theorem pickedmastered3p: (Three_dot2 c1)(and PHYINFO(picked_up john )(mastered john))-> exists x y z: Book1.(B),picked_up (john)(c1 x)/\picked_up (john)(c1 y)/\picked_up (john)(c1 z)/\ not((PHY.(B2))(c1(x))(c1(y)))/\not((PHY.(B2))(c1(y))(c1(z)))/\not((PHY.(B2))(c1(x))(c1(z))). cbv. firstorder. Qed.

 (**John picked up and mastered three books-> John picked up three physical objects and mastered three informational objects**)
Theorem pickedmastered3pm: (Three_dot2 c1)(and PHYINFO(picked_up john )(mastered john))-> exists x y z: Book1.(B),picked_up (john)(c1 x)/\picked_up (john)(c1 y)/\picked_up (john)(c1 z)/\ not((PHY.(B2))(c1(x))(c1(y)))/\not((PHY.(B2))(c1(y))(c1(z)))/\not((PHY.(B2))(c1(x))(c1(z)))/\mastered (john)(c1 x)/\mastered (john)(c1 y)/\mastered (john)(c1 z)/\ not((INFO.(B2))(c1(x))(c1(y)))/\not((INFO.(B2))(c1(y))(c1(z)))/\not((INFO.(B2))(c1(x))(c1(z))).
cbv. firstorder. Qed.

(**Collecting the previous examples plus new ones**)
 Theorem MANWALKSOME: (some MAN) walk-> (some  HUMAN) walk. cbv. intros.                                                       firstorder. Qed.
 Theorem BOOKPICKED:( (some Book1) ( picked_up john))-> (some PHY)( picked_up john).  
   cbv.  intro. firstorder. Qed. (**John picked up a book->John picked up a physical object**)
  Theorem BOOKMASTERED:( (some Book1) ( mastered john))-> (some INFO)( mastered john).  
    cbv.  intro. firstorder. Qed. (**John mastered  a book->John mastered an informational object**)
Parameter John: man.
Theorem MANEQUALHUMAN: (MAN.(B2) John John)-> (HUMAN.(B2) John John).  
  cbv. intro. assumption. Qed.

Parameter Heavy: PHY.(B)->Prop. 
Record heavybook :DomCN := mkheavybook { l3 :>book; L : Heavy l3 }.

Definition AIC_HBook1 := fun x: heavybook=>fun y:heavybook=> IC_Book1(x)(y).
Theorem EQ4: reflexive  heavybook  AIC_HBook1/\  symmetric heavybook AIC_HBook1/\  transitive heavybook AIC_HBook1. cbv. destruct  IC_Phy. destruct _eq3. destruct H0. split. intro. unfold reflexive in H.  apply H. split. intro. unfold symmetric in H0. intuition. intro. unfold transitive in H1. intro. intro. intros. apply H1 with y. assumption. assumption. Qed.

Definition IC_HBook1:=  mkEquiv heavybook  AIC_HBook1 EQ4.
Definition HBook1:= mkCN heavybook IC_HBook1.

Definition AIC_HBook2 := fun x: heavybook=>fun y:heavybook=> IC_Book2(x)(y).
Theorem EQ5: reflexive  heavybook  AIC_HBook2/\  symmetric heavybook AIC_HBook2/\  transitive heavybook AIC_HBook2. cbv. destruct  IC_Info. destruct _eq3. destruct H0. split. intro. unfold reflexive in H.  apply H. split. intro. unfold symmetric in H0. intuition. intro. unfold transitive in H1. intro. intro. intros. apply H1 with y. assumption. assumption. Qed.

Definition IC_HBook2:=  mkEquiv heavybook  AIC_HBook2 EQ5.
Definition HBook2:= mkCN heavybook IC_HBook2.

Theorem HEAVYBOOK:( (some HBook2) ( mastered john))-> (some INFO)( mastered john). firstorder. Qed.

Theorem HEAVYBOOK1:( (some HBook1) (picked_up john))-> (some PHY)( picked_up john). firstorder. Qed.
Theorem HEAVYBOOK2:( (three HBook1) (picked_up john))-> (three PHY)( picked_up john). cbv.  firstorder. Qed.

Theorem HEAVYBOOK3:( (three HBook2) ( mastered john))-> (three INFO)( mastered john). cbv. intros. firstorder. Qed.

Parameter informative: Info->Prop.
Axiom c3: HBook1.(B)->PHYINFO.(B). Axiom c4: HBook2.(B)->PHYINFO.(B).


Record heavyinfobook :DomCN := mkheavyinfobook { l4 :>heavybook; _ : informative l4 }.

Definition AIC_HIBook1 := fun x: heavyinfobook=>fun y:heavyinfobook=> IC_HBook1(x)(y).
Theorem EQ6: reflexive  heavyinfobook  AIC_HIBook1/\  symmetric heavyinfobook AIC_HIBook1/\  transitive heavyinfobook AIC_HIBook1. cbv. destruct  IC_Phy. destruct _eq3. destruct H0. split. intro. unfold reflexive in H.  apply H. split. intro. unfold symmetric in H0. intuition. intro. unfold transitive in H1. intro. intro. intros. apply H1 with y. assumption. assumption. Qed.

Definition IC_HIBook1:=  mkEquiv heavyinfobook  AIC_HIBook1 EQ6.
Definition HIBook1:= mkCN heavyinfobook IC_HIBook1.

Definition AIC_HIBook2 := fun x: heavyinfobook=>fun y:heavyinfobook=> IC_HBook2(x)(y).
Theorem EQ7: reflexive  heavyinfobook  AIC_HIBook2/\  symmetric heavyinfobook AIC_HIBook2/\  transitive heavyinfobook AIC_HIBook2. cbv. destruct  IC_Info. destruct _eq3. destruct H0. split. intro. unfold reflexive in H.  apply H. split. intro. unfold symmetric in H0. intuition. intro. unfold transitive in H1. intro. intro. intros. apply H1 with y. assumption. assumption. Qed.

Definition IC_HIBook2:=  mkEquiv heavyinfobook  AIC_HIBook2 EQ7.
Definition HIBook2:= mkCN heavyinfobook IC_HIBook2.


Theorem HEAVYIBOOK2:( (three HIBook1) (picked_up john))-> (three PHY)( picked_up john). cbv. firstorder. Qed.

Theorem HEAVYIBOOK3:( (three HIBook2) ( mastered john))-> (three INFO)( mastered john). cbv. intros. firstorder.                                                 Qed.
Theorem HEAVYIBOOK4:( (three HIBook1) (picked_up john))-> (three HBook1)( picked_up john). cbv.  firstorder. Qed.
Theorem HEAVYIBOOK5:( (three HIBook2) ( mastered john))-> (three HBook2)( mastered john). cbv. intros. firstorder.                                                 Qed.
Theorem HEAVYIBOOK6:( (three HBook1) (picked_up john))-> (three Book1)( picked_up john). cbv.  firstorder. Qed.
Theorem HEAVYIBOOK7:( (three HBook2) ( mastered john))-> (three Book2)( mastered john). cbv. intros. firstorder.                                                 Qed.
Axiom HB: HBook1.(B)->Book1.(B). 

Theorem HEAVYIBOOK8: (three HBook1)((picked_up john ))->    three Book1 (Heavy).
 decompose record HBook1.  cbv.
decompose record heavybook. intros. 
firstorder. decompose record H0. decompose record x.

decompose record x. exists l5. split. assumption.  decompose record x0. exists l6. split. assumption. decompose record x1. 
exists l7. split. assumption. firstorder.  Abort all. End BOOK.

 
Definition Three_d:=fun A:CN=> fun c: A.(B)->PHYINFO.(B)=>fun P:PHYINFO.(B)->Prop=>exists x y z: A.(B), not((PHY.(B2))(c(x))(c(y)))/\not((PHY.(B2))(c(y))(c(z))) /\not((PHY.(B2))(c(x))(c(z)))/\not((INFO.(B2))(c(x))(c(y)))/\not((INFO.(B2))(c(y))(c(z))) /\not((INFO.(B2))(c(x))(c(z)))/\P (c(x))/\ P(c(y))/\P(c(z)).

Theorem masteredheavy: (Three_d HBook1 bf)(mastered john)-> exists x y z: heavybook, not((PHY.(B2))((x))((y)))/\not((PHY.(B2))((y))((z))) /\not((PHY.(B2))((x))((z))). cbv. firstorder. Qed.


Theorem masteredheavy1: (Three_d HBook1 bf)(mastered john)-> (three Book1) Heavy. cbv.  firstorder. exists x. split. 
apply (x.(L)). 
exists x0. split.  apply (x0.(L)).    exists x1. split. apply (x1.(L)). firstorder.  Qed.                                                                               