(** Some Neo-davidsonian Semantics*)
Require Import Bvector.
Require Import Coq.Lists.List.
Require Import Omega.
Load LibTactics.
Ltac AUTO:= cbv delta;intuition;try repeat congruence;  jauto;intuition.
Parameter Event Ind LOcation Instrument:Set.
Parameter Agent
          Theme: Ind->Event->Prop.
Parameter Caesar Brutus:Ind.
Parameter IN: LOcation->Event->Prop.
Parameter WITH: Instrument->Event->Prop.  Definition In:= fun
x:LOcation=>fun E: Event->Prop=> fun e1:Event=> exists e:Event, E e1/\
IN x e1.  Definition With:= fun x:Instrument=>fun E: Event->Prop=> fun
                                                  e1:Event=> exists e:Event, E e1/\ WITH x e1.
Parameter stab: Ind->Ind->Event->Prop.
Parameter e1:Event. 
Definition stabs:= fun
x:Ind=> fun y:Ind=>fun e1:Event=> exists e:Event, stab x y e /\
Theme(x)(e)/\Agent(y)(e)/\ e=e1.  Parameter a_knife: Instrument.
Parameter Rome Verona Athens: LOcation.  Theorem BRUTUS: (stabs Caesar
Brutus e1)-> Agent(Brutus)(e1). (**AUTO automates the proof*)  cbv. intro.  destruct H. destruct
H. destruct H0. destruct H1. firstorder. congruence. Qed.  Theorem
BRUTUS1:(In Rome) ((With a_knife) (stabs Caesar Brutus)) e1-> WITH
a_knife e1. AUTO. Qed.  Theorem BRUTUS2:(In Rome) ((With a_knife)
(stabs Caesar Brutus)) e1-> ((With a_knife) (stabs Caesar Brutus))
                              e1. AUTO. Qed.
Theorem BRUTUS3:(In Rome) ((With a_knife) (stabs
                                             Caesar Brutus)) e1-> ((In Rome) (stabs Caesar Brutus)) e1. AUTO. Qed.

Theorem BRUTUS4:(In Rome) ((With a_knife) (stabs Caesar Brutus)) e1->
((stabs Caesar Brutus)) e1. AUTO. Qed.



