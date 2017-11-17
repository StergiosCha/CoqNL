Load LibTactics.

(**Basic record example "a man owns a donkey" from Cooper 2014"**)
Definition Ind:=Set.
Parameter man: Ind->Prop.
Parameter donkey: Ind->Prop.
Parameter own: Ind->Ind->Prop.
Record amanownsadonkey : Type := mkamanownsadonkey{ x : Ind;  c1 : man x;  y : Ind;  c2 : donkey y; c3 : own x y }.

Theorem RECORD:amanownsadonkey-> exists x, man x/\exists y, donkey y. intro.  decompose record X. exists x0. split. assumption. exists y0. assumption.                                              Qed.

(**Defining IND as a record with one Ind field**)
Record IND: Type := mkIND{ x1 :> Ind;}.
Parameter run:Ind->Prop.
(**Defining Run as a record which takes a record IND as argument**)
CoInductive  Run(X:IND):={ e: run X.(x1) ;}.
Check Run.
(**Defining John and Mary as being of type IND**)
Parameter John Mary:IND. 
Check Run John.
Theorem RUN: Run John -> exists x: Ind, run x. cbv. intro.
                                                decompose record John. decompose record H. exists x2. Undo.   exists (x1 John). apply e0. Qed.


Record Run1 (X:IND):Type:= mkRun1{e2: run X.(x1);}.


Theorem RUN1: Run1 John -> exists x: Ind, run x.  cbv. intro.
                                                  decompose record John. decompose record H. exists x2. Undo.   exists (x1 John). apply e3. Qed.                                                    Check man. 
Record Man (X:IND):Type:= mkman{e3: man  X.(x1);}.

Check Man.
Parameter black:(Ind->Prop). 
Record Black (Y:IND->Prop) (X:IND):Type:= mkBlack{e4: man  X.(x1);e5:black X.(x1) }.
Theorem BLACK: Black Man John-> exists x:Ind, black x. cbv. decompose record John. decompose record Black. intros. decompose record Black. decompose record Man. decompose record H. decompose record e6. exists (x1 John). assumption. Qed.
Check Black. 