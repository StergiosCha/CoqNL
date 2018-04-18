Load LibTactics.

(**Basic record example "a man owns a donkey" from Cooper 2014"**)
Definition Ind:=Set.
Parameter man: Ind->Prop.
Parameter donkey: Ind->Prop.
Parameter own: Ind->Ind->Prop.

Record amanownsadonkey : Type := mkamanownsadonkey{
 x : Ind;
 c1 : man x;
 y : Ind;
 c2 : donkey y;
 c3 : own x y }.
Check mkamanownsadonkey.

Theorem RECORD:amanownsadonkey-> exists x, man x/\exists y, donkey y /\ own x y. intro.  decompose record X. exists x0. split. assumption.  exists y0. split. assumption.   assumption.  Qed.

(**Defining Ind as a record with one Ind field**)
Record IND: Type := mkIND{ x1 :> Ind;}.
Parameter run:Ind->Prop.
(**Defining Run as a record which takes a record IND as argument**)
CoInductive  Run(X:IND):={ e: run X.(x1) ;}.
Check Run.
(**Defining John and Mary as being of type IND**)
Parameter John Mary:IND. 
Check Run John.
Check John. 
Theorem RUN: Run John -> exists x: Ind, run x. cbv. intro.
                                                decompose record John. decompose record H. exists x2. Undo.   exists (x1 John). apply e0. Qed.


Record Run1 (X:IND):Type:= mkRun1{e2: run X.(x1);}.


Theorem RUN1: Run1 John -> exists x: Ind, run x.  cbv. intro.
                                                  decompose record John. decompose record H. exists x2. Undo.   exists (x1 John). apply e3. Qed.                                                    Check man. 
Record Man (X:IND):Type:= mkman{e3: man  X.(x1);}.

Check Man.
Parameter black:(Ind->Prop). 
Record Black (Y:IND->Prop) (X:IND):Type:= mkBlack{e4: man  X.(x1);e5:black X.(x1) }.
Theorem BLACK: Black Man John-> exists x:Ind, black x. cbv.   intros.  decompose record H. decompose record e6. exists (x1 John). assumption. Qed.
Check Black.
Require Import Omega. 
(**John fainted example**)
Parameter Faint: Ind->Prop.
Record faint (X:IND):Type:= mkfainted{f: Faint  X.(x1);}.
Record Johnfainted : Type := mkjf{
j : IND;
eq: j = John;
F : faint j}.

(**some reasoning**)
Theorem FAINT: Johnfainted -> faint John. cbv. intro.  firstorder. decompose record IND.  replace John with j0. assumption. Qed.
Theorem FAINT2: Johnfainted -> exists x: IND, faint x. intro. destruct X. exists j0. assumption. Qed.

(**Chorlton example**)
Parameter doctor: Ind->Prop.
Record Doctor (X:IND):Type:= mkdoctor{d: doctor  X.(x1);}.
Parameter fitz: Ind-> Prop.
Record Fitz (X:IND):Type:= mkfitz{f1: fitz  X.(x1);}.
Definition e_s:=Type.
Parameter examine: e_s.
Parameter subj: e_s -> Ind -> Prop.
Parameter obj: e_s -> Ind -> Prop.
Parameter spkr: Ind. 
Record r :Type:= mkr{
x2:> Ind;
P:  doctor x2;
P1:  fitz x2 ;
}.

Record chorlton :Type:= mkcholtr{
R: r;
x3: Ind;
eq1: x3 = R.(x2);
ev: e_s;
eq2: ev = examine;
x4: Ind;
eq3: x4=spkr;
p3:  subj ev x3;
p4 : obj ev x4  }.


(**Some reasoning**)
Theorem CHORLTON: chorlton -> exists x: Ind, doctor x /\ fitz x /\ subj examine x. firstorder. destruct X.  destruct R0. elim  eq4. exists x7. firstorder. destruct eq6. firstorder.  replace x7 with x5. replace examine with ev0.     assumption. Qed.                                                                                                                                                                                      