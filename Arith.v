Require Import ZArith.
Require Import List.

(* Arithmetic expressions with variables *)

Definition aArg := nat.

Definition mkAArg n : aArg := n.
Definition aArgName (a : aArg) := a.

Inductive aBop : Set :=
| AAdd : aBop
| ASub : aBop
| AMul : aBop.

Inductive aExp : Set :=
| ArgExp : aArg -> aExp
| ABinop : aBop -> aExp -> aExp -> aExp.

Definition aMap := aArg -> Z.

Open Scope Z_scope.

Fixpoint aExpEval (e : aExp) (m : aMap) : Z :=
  match e with
    | ArgExp a => m a
    | ABinop AAdd l r =>
      (aExpEval l m) + (aExpEval r m)
    | ABinop ASub l r =>
      (aExpEval l m) - (aExpEval r m)
    | ABinop AMul l r =>
      (aExpEval l m) * (aExpEval r m)
  end.

(* Stack machine definition *)

Inductive stkReg : Set :=
| StkArg : nat -> stkReg
| StkTemp : nat -> stkReg.

Definition beq_stkReg (l r : stkReg) : bool :=
  match l, r with
    | StkArg ln, StkArg rn => beq_nat ln rn
    | StkTemp ln, StkTemp rn => beq_nat ln rn
    | _, _ => false
  end.

Inductive sBop : Set :=
| SAdd : sBop
| SSub : sBop
| SMul : sBop.

Inductive stkInstr : Set :=
| Push : stkReg -> stkInstr
| Pop : stkReg -> stkInstr
| SBinop : sBop -> stkReg -> stkReg -> stkInstr.

Inductive isPush : stkInstr -> Prop :=
| IsPush : forall r : stkReg, isPush (Push r).

Inductive isPop : stkInstr -> Prop :=
| IsPop : forall r : stkReg, isPop (Pop r).

Inductive isSBinop : stkInstr -> Prop :=
| IsSBinop :
    forall (b : sBop) (r0 r1 : stkReg), isSBinop (SBinop b r0 r1).

Record stackMachine :=
  {
    smRegMap : stkReg -> Z;
    smStk : list Z
  }.

Definition smStackSize (sm : stackMachine) : nat :=
  length (smStk sm).

(* Stack program evaluation *)

Definition smSetStkRegVal (r : stkReg) (v : Z) (sm : stackMachine) :=
  Build_stackMachine
    (fun x => if beq_stkReg x r then v else (smRegMap sm) x)
    (smStk sm).

Definition smPush (r : stkReg) (sm : stackMachine) : stackMachine :=
  Build_stackMachine (smRegMap sm) ((smRegMap sm) r :: smStk sm).

Definition smPop (r : stkReg) (sm : stackMachine) : option stackMachine :=
  match smStk sm with
    | nil => None
    | v :: s' =>
      Some (Build_stackMachine
              (fun x => if beq_stkReg x r then v else (smRegMap sm) x)
              s')
  end.

Definition smBinop (b : sBop) (r0 r1 : stkReg) (sm : stackMachine) : stackMachine :=
  match b with
    | SAdd =>
      smSetStkRegVal r1 (((smRegMap sm) r1) + ((smRegMap sm) r0)) sm
    | SSub =>
      smSetStkRegVal r1 (((smRegMap sm) r1) - ((smRegMap sm) r0)) sm
    | SMul =>
      smSetStkRegVal r1 (((smRegMap sm) r1) * ((smRegMap sm) r0)) sm
  end.

Definition stackProgram := list stkInstr.

Fixpoint stkInstrEval (i : stkInstr) (sm : stackMachine) : option stackMachine :=
  match i with
    | Push r => Some (smPush r sm)
    | Pop r => smPop r sm
    | SBinop b r0 r1 => Some (smBinop b r0 r1 sm)
  end.

Fixpoint stkProgEval (p : stackProgram) (sm : stackMachine) : option stackMachine :=
  match p with
    | i :: p' =>
      match stkInstrEval i sm with
        | Some sm' => stkProgEval p' sm'
        | _ => None
      end
    | nil => Some sm
  end.

(* Stack program meaning as a relation  *)

Inductive sBopEvalR : sBop -> Z -> Z -> Z -> Prop :=
| SBopEvalR_smul :
    forall m n p, m * n = p -> sBopEvalR SMul n m p
| SBopEvalR_sadd :
    forall m n p, m + n = p -> sBopEvalR SAdd n m p
| SBopEvalR_ssub :
    forall m n p, m - n = p -> sBopEvalR SSub n m p.

Inductive stkInstrEvalR : stackMachine -> stkInstr -> stackMachine -> Prop :=
| StkInstrEvalR_push :
    forall srv stk r v, srv r = v ->
                        stkInstrEvalR
                          (Build_stackMachine srv stk)
                          (Push r)
                          (Build_stackMachine srv (v :: stk))
| StkInstrEvalR_pop :
    forall srv stk r v, stkInstrEvalR
                          (Build_stackMachine srv (v :: stk))
                          (Pop r)
                          (Build_stackMachine
                             (fun x => if beq_stkReg x r then v else srv x)
                             stk)
| StkInstrEvalR_sBinop :
    forall srv stk r0 r1 b n, sBopEvalR b (srv r0) (srv r1) n ->
                                stkInstrEvalR
                                  (Build_stackMachine srv stk)
                                  (SBinop b r0 r1)
                                  (Build_stackMachine
                                     (fun x => if beq_stkReg x r1
                                               then n
                                               else srv x)
                                     stk).                             

Inductive stkProgEvalR : stackMachine -> stackProgram -> stackMachine -> Prop :=
| StkProgEvalR_empty : forall sm1, stkProgEvalR sm1 nil sm1
| StkProgEvalR_i :
    forall sm1 sm1' sm2 i p, stkInstrEvalR sm1 i sm1' ->
                             stkProgEvalR sm1' p sm2 ->
                             stkProgEvalR sm1 (i :: p) sm2.

(* Equivalence of computational and relational definitions *)

Theorem stkInstrEvalR_imp_stackInstrEval :
  forall (i : stkInstr) (sm1 sm2 : stackMachine),
    stkInstrEvalR sm1 i sm2 -> stkInstrEval i sm1 = Some sm2.
Proof.
  intros; destruct i.

  destruct H. simpl stkInstrEval. unfold smPush. unfold smRegMap.
  rewrite -> H. unfold smStk. reflexivity.

  simpl stkInstrEval. unfold smPop. unfold smStk. unfold smRegMap.
  reflexivity.

  inversion H; simpl stkInstrEval; unfold smSetStkRegVal; unfold smRegMap;
  unfold smStk; rewrite -> H0; reflexivity.

  inversion H; simpl stkInstrEval. unfold smPop. unfold smStk.
  unfold smRegMap. reflexivity.

  inversion H. simpl stkInstrEval. unfold smBinop.

  destruct s; unfold smRegMap; unfold smSetStkRegVal; unfold smStk;
  unfold smRegMap; inversion H5; rewrite -> H6; reflexivity.
Qed.

Lemma some_eq :
  forall sm1 sm2 : stackMachine, Some sm1 = Some sm2 -> sm1 = sm2.
Proof.                                   
  intros; injection H; trivial.
Qed.
                                                                  
Theorem stackInstrEval_imp_stkInstrEvalR :
  forall (i : stkInstr) (sm1 sm2 : stackMachine),
    stkInstrEval i sm1 = Some sm2 -> stkInstrEvalR sm1 i sm2.
Proof.
  intros. destruct i. simpl stkInstrEval in H. unfold smPush in H.
  destruct sm1. unfold smRegMap in H. unfold smStk in H.
  pose proof some_eq.
  specialize (H0 (Build_stackMachine smRegMap0 ((smRegMap0 s) :: smStk0)) sm2).
  apply H0 in H. rewrite <- H.
  apply (StkInstrEvalR_push smRegMap0 smStk0 s (smRegMap0 s)); reflexivity.

  simpl stkInstrEval in H.
  destruct sm1. unfold smPop in H.
  unfold smStk in H. destruct smStk0.

  discriminate.

  unfold smRegMap in H.
  pose proof some_eq.
  specialize (H0 (Build_stackMachine
                    (fun x  =>
                       if beq_stkReg x s then z else smRegMap0 x)
                    smStk0)
                 sm2).
  apply H0 in H. rewrite <- H.
  apply (StkInstrEvalR_pop smRegMap0 smStk0 s z).

  simpl stkInstrEval in H. unfold smBinop in H.
  destruct s; destruct sm1; unfold smRegMap in H;
  unfold smSetStkRegVal in H; unfold smRegMap in H;
  unfold smStk in H; pose proof some_eq.

  specialize (H0 (Build_stackMachine
                    (fun x =>
                       if beq_stkReg x s1 then smRegMap0 s1 + smRegMap0 s0 else smRegMap0 x)
                    smStk0)
                 sm2).
  apply H0 in H. rewrite <- H.
  apply (StkInstrEvalR_sBinop smRegMap0 smStk0 s0 s1 SAdd (smRegMap0 s1 + smRegMap0 s0)).
  apply (SBopEvalR_sadd (smRegMap0 s1) (smRegMap0 s0) (smRegMap0 s1 + smRegMap0 s0)).
  reflexivity.

  specialize (H0 (Build_stackMachine
                    (fun x =>
                       if beq_stkReg x s1 then smRegMap0 s1 - smRegMap0 s0 else smRegMap0 x)
                    smStk0)
                 sm2).
  apply H0 in H. rewrite <- H.
  apply (StkInstrEvalR_sBinop smRegMap0 smStk0 s0 s1 SSub (smRegMap0 s1 - smRegMap0 s0)).
  apply (SBopEvalR_ssub (smRegMap0 s1) (smRegMap0 s0) (smRegMap0 s1 - smRegMap0 s0)).
  reflexivity.

  specialize (H0 (Build_stackMachine
                    (fun x =>
                       if beq_stkReg x s1 then smRegMap0 s1 * smRegMap0 s0 else smRegMap0 x)
                    smStk0)
                 sm2).
  apply H0 in H. rewrite <- H.
  apply (StkInstrEvalR_sBinop smRegMap0 smStk0 s0 s1 SMul (smRegMap0 s1 * smRegMap0 s0)).
  apply (SBopEvalR_smul (smRegMap0 s1) (smRegMap0 s0) (smRegMap0 s1 * smRegMap0 s0)).
  reflexivity.
Qed.

Theorem stackInstrEval_stkInstrEvalR_equiv :
  forall (i : stkInstr) (sm1 sm2 : stackMachine),
    stkInstrEvalR sm1 i sm2 <-> stkInstrEval i sm1 = Some sm2.
Proof.
  split; [pose proof stkInstrEvalR_imp_stackInstrEval;
           specialize (H i sm1 sm2); apply H |
          pose proof stackInstrEval_imp_stkInstrEvalR;
            specialize (H i sm1 sm2); apply H].
Qed.

Lemma stkInstrEval_res :
  forall i sm1,
    stkInstrEval i sm1 = None \/
    exists sm1', stkInstrEval i sm1 = Some sm1'.
Proof.
  intros. destruct (stkInstrEval i sm1).

  right. eapply ex_intro. reflexivity.

  left. reflexivity.
Qed.

Lemma stkProgEval_imp_stkInstrEval :
  forall i p sm1 sm2,
    stkProgEval (i :: p) sm1 = Some sm2 ->
    exists sm1', stkInstrEval i sm1 = Some sm1'.
Proof.
  intros. unfold stkProgEval in H.
  pose proof stkInstrEval_res.
  specialize (H0 i sm1).
  inversion H0.

  (* None case *)
  rewrite -> H1 in H.
  discriminate.

  (* Some sm1' case *)
  inversion H1. clear H0.
  eapply ex_intro. apply H2.
Qed.

Lemma stkProg_cons :
  forall i p sm1 sm2 sm1',
    stkProgEval (i :: p) sm1 = Some sm2 ->
    stkInstrEval i sm1 = Some sm1' ->
    stkProgEval p sm1' = Some sm2.
Proof.
  intros.
  simpl stkProgEval in H.
  rewrite -> H0 in H. assumption.
Qed.

Theorem stkProgEvalR_stackProgEval_equiv :
  forall (p : stackProgram) (sm1 sm2 : stackMachine),
    stkProgEvalR sm1 p sm2 <-> stkProgEval p sm1 = Some sm2.
Proof.
  induction p.

  split.

  unfold stkProgEval. inversion 1. reflexivity.

  unfold stkProgEval. inversion 1. apply StkProgEvalR_empty.

  split.

  inversion 1. simpl stkProgEval.
  inversion H.
  pose proof stkInstrEvalR_imp_stackInstrEval.
  specialize (H12 a sm1 sm1'0).
  apply H12 in H9. rewrite -> H9.
  specialize (IHp sm1'0 sm2).
  destruct IHp.
  apply H13 in H11. rewrite -> H11. reflexivity.
  
  (* stkProgEval (a :: p) sm1 = Some sm2 -> stkProgEvalR sm1 (a :: p) sm2 *)
  intro.
  pose proof stkProgEval_imp_stkInstrEval.
  specialize (H0 a p sm1 sm2).
  assert (H' := H).
  apply H0 in H. inversion H.
  apply (StkProgEvalR_i sm1 x sm2 a p).
  
  (* stkInstrEvalR sm1 a x *)
  pose proof stackInstrEval_imp_stkInstrEvalR.
  specialize (H2 a sm1 x).
  apply H2 in H1. assumption.

  (* stkProgEvalR x p sm2 *)
  pose proof stkProg_cons.
  specialize (H2 a p sm1 sm2 x).
  apply H2 in H'.
  specialize (IHp x sm2).
  inversion IHp. clear H3. apply H4 in H'.
  assumption.

  (* stkInstrEval a sm1 = Some x *)
  assumption.
Qed.
  
(* Compilation of aExps to stackPrograms *)

Definition aBopToSBop (b : aBop) : sBop :=
  match b with
    | AAdd => SAdd
    | ASub => SSub
    | AMul => SMul
  end.

Definition r0 := StkTemp 0.
Definition r1 := StkTemp 1.

Fixpoint aExpToStackProgram (a : aExp) : stackProgram :=
  match a with
    | ArgExp arg => Push (StkArg (aArgName arg)) :: nil
    | ABinop b l r =>
      (aExpToStackProgram l) ++ (aExpToStackProgram r) ++ (Pop r0 :: Pop r1 :: SBinop (aBopToSBop b) r0 r1 :: Push r1 :: nil)
  end.

Eval compute in aExpToStackProgram (ArgExp (mkAArg 23%nat)).
Eval compute in
    aExpToStackProgram (ABinop AAdd (ArgExp (mkAArg 23%nat)) (ArgExp (mkAArg 76%nat))).

(* Compiler properties *)

Theorem aExpToStackProgram_safe :
  forall (a : aExp) (sm : stackMachine),
    exists sm', stkProgEval (aExpToStackProgram a) sm = Some sm'.
Proof.
  intros; induction a.

  simpl. unfold aArgName. unfold smPush. eapply ex_intro.
  reflexivity.

  