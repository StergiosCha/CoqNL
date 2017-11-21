Variable P:Prop.
Require Import Classical. 
Theorem goclassical:  forall P:Prop, not (not P)-> P.
tauto. 


  
Theorem noIllstayintuitionistic: P -> not (not P). (** :) **)
  tauto.



  