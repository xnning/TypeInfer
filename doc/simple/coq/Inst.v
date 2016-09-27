Require Import LibLN.
Require Import DeclDef.
Require Import AlgoDef.
Require Import DeclInfra.
Require Import AlgoInfra.
Require Import CtxExtension.
Require Import UtilityEnv.
Require Import Subst.
Require Import Exists.
Require Import UtilityMore.


(*
********************************************
Basic Properties
********************************************
*)

Lemma ainst_awf: forall G s t H,
    AWf G ->
    AInst G s t H ->
    AWf H.
Proof.
  introv wf inst. induction inst.
  assumption.
  apply IHinst.
  apply~ AWf_Ctx_Unsolved_EVar.
Qed.

Lemma ainst_destruct: forall G s t H,
    AWf G ->
    AInst G s t H ->
    exists I, Softness I /\ H = G & I.
Proof.
  introv wf inst. induction inst.
  exists~ (empty:ACtx). split. apply Softness_Empty. rewrite~ concat_empty_r.

  assert (AWf (G & a ~ AC_Unsolved_EVar)).
  apply~ AWf_Ctx_Unsolved_EVar.
  lets: IHinst H1.
  destruct H2 as (I1 & [si h2]).
  exists~ (a ~ AC_Unsolved_EVar & I1).
  split. apply~ soft_append.
  apply~ soft_single_unsolved.
  assert (AWf H). apply* ainst_awf.
  rewrite h2 in H2. rewrite <- concat_assoc in H2. apply awf_is_ok in H2.
  apply* ok_concat_inv_r.

  rewrite~ concat_assoc.
Qed.

Lemma ainst_extension: forall G s t H,
    AWf G ->
    AInst G s t H ->
    ExtCtx G H.
Proof.
  introv wf inst.
  destruct (ainst_destruct G s t H wf inst) as (I & [sf hh]).
  subst.
  apply~ right_softness.
  apply~ extension_reflexivity.
  apply ainst_awf with G s t; auto.
Qed.


Lemma awftyp_change': forall G y s a n I3,
    AWf (G & y ~ AC_Unsolved_EVar & I3) ->
    AWf (G & a ~ AC_Unsolved_EVar & I3) ->
    y \notin ATFv s ->
    AWfTyp (G & y ~ AC_Unsolved_EVar & I3) (AOpenTypRec n (AE_EVar y) s) ->
    AWfTyp (G & a ~ AC_Unsolved_EVar & I3) (AOpenTypRec n (AE_EVar a) s).
Proof.
  introv wfy wfa notin wt.
  gen_eq s2: (AOpenTypRec n (AE_EVar y) s).
  gen_eq H: (G & y ~ AC_Unsolved_EVar & I3).
  gen s n I3. induction wt; introv notin wfa hg exp.

  (* Unsolved *)
  destruct s. inversion exp.
  simpls. inversion exp. subst. clear exp.

  destruct a0; unfold AOpenRec in H1; simpls; try(solve[inversion H1]).
  case_nat~.
  apply AWf_Unsolve_EVar.
  apply binds_middle_eq.
  apply awf_is_ok in wfa. apply* ok_middle_inv.

  inversion H1; subst.
  apply notin_singleton in notin.
  apply binds_subst in H; auto.
  apply AWf_Unsolve_EVar.
  apply~ binds_weaken.

  (* Solved *)
  destruct s0. inversion exp.
  simpls. inversion exp. subst. clear exp.

  destruct a0; unfold AOpenRec in H1; simpls; try(solve[inversion H1]).
  case_nat~.
  apply AWf_Unsolve_EVar.
  apply binds_middle_eq.
  apply awf_is_ok in wfa. apply* ok_middle_inv.

  inversion H1; subst.
  apply notin_singleton in notin.
  apply binds_subst in H; auto.
  apply AWf_Solved_EVar with s.
  apply~ binds_weaken.

  (* Pi *)
  destruct s. inversion exp.
  simpls. inversion exp. subst. clear exp.

  destruct a0; simpls; try(solve[inversion H2]).
  case_nat~.
  inversion H2. subst. clear H2.
  apply AWf_Pi with (L \u dom G \u dom I3 \u \{a} \u \{y}).
  lets: IHwt wfy (AT_Expr a0_1).
  simpls.
  apply~ H1.

  admit.

  (* Forall *)
  destruct s0; try (solve[inversion exp]).
  simpls. inversion exp. subst. clear exp.
  apply AWf_Poly with (L \u dom G \u \{y} \u dom I3 \u \{a}).
  intros z notin_z.
  assert (AWfTyp (G & a ~ AC_Unsolved_EVar & (I3 & z ~ AC_Unsolved_EVar)) (AOpenTypRec (S n) (AE_EVar a) (s0 @@' AE_EVar z))).
  apply H0 with (x:=z); auto.
  apply~ notin_opent_inv. simpls. auto_star.
  rewrite concat_assoc. apply~ AWf_Ctx_Unsolved_EVar.
  rewrite~ concat_assoc.
  unfold AOpenT. rewrite~ opent_reorder.
  rewrite concat_assoc in H1. unfold AOpenT in H1. rewrite opent_reorder in H1; auto.

  (* Expr *)
  destruct s; try (solve[inversion exp]).
  simpls. inversion exp. subst. clear exp.
Admitted.


Lemma awftyp_change: forall G y s a,
    AWf (G & y ~ AC_Unsolved_EVar) ->
    AWf (G & a ~ AC_Unsolved_EVar) ->
    y \notin ATFv s ->
    AWfTyp (G & y ~ AC_Unsolved_EVar) (s @@' (AE_EVar y)) ->
    AWfTyp (G & a ~ AC_Unsolved_EVar) (s @@' (AE_EVar a)).
Proof.
  intros.
  assert(AWfTyp (G & a ~ AC_Unsolved_EVar & empty) (s @@' AE_EVar a)).
  apply awftyp_change' with y; try(rewrite~ concat_empty_r); auto.
  rewrite concat_empty_r in H3.
  auto.
Qed.

(*
*********************************************************************************
to Solve one subgoal
*********************************************************************************
*)


Definition CommonCtx (ctx: ACtx) :=
  forall x v, binds x v ctx -> v = AC_Var \/ exists t, v = AC_Typ t.

Lemma common_empty: CommonCtx empty.
Proof.
  unfold CommonCtx. introv bd.
  false bd.
  apply get_some_inv in e. simpl_dom. false in_empty_elim e.
Qed.

Lemma common_add: forall G x,
    CommonCtx G ->
    CommonCtx (G & x ~ AC_Var).
Proof.
  unfold CommonCtx.
  introv cm.
  intros y v bd.
  apply binds_concat_inv in bd.
  destruct bd as [bd1 | [_ bd2]].
  destruct (binds_single_inv bd1). subst.
  left. auto.
  apply* cm.
Qed.

Lemma common_add_typ: forall G x t,
    CommonCtx G ->
    CommonCtx (G & x ~ AC_Typ t).
Proof.
  unfold CommonCtx.
  introv cm.
  intros y v bd.
  apply binds_concat_inv in bd.
  destruct bd as [bd1 | [_ bd2]].
  destruct (binds_single_inv bd1). subst.
  right. exists* t.
  apply* cm.
Qed.

Lemma common_contains_solved: forall G x t,
    CommonCtx G ->
    binds x (AC_Solved_EVar t) G -> False.
Proof.
  introv g bd.
  unfold CommonCtx in g.
  lets: g bd. inversion H. false H0.
  inversion H0. false H1.
Qed.


Lemma cpltctxsubst_replace': forall I1 I2 I3 a it ia y s s2 n t,
   CompleteCtx (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) ->
   AWf (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) ->
   AWTerm (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) (AOpenRec n (AE_FVar y) s) ->
   CommonCtx I3 ->
   y \notin AFv s ->
   y \notin DFv s2 ->
   ACpltCtxSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) (AOpenRec n (AE_FVar y) s) (DOpenRec n (DE_FVar y) s2) ->
   ACpltCtxSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) (AE_EVar a) ia ->
   ACpltCtxSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) (AOpenRec n (AE_EVar a) s) (DOpenRec n ia s2).
Proof.
  introv comp wf wt cm notin_t notin_d sub_s sub_a.
  gen_eq I:(I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3).
  gen_eq tss: (AOpenRec n (AE_FVar y) s).
  gen_eq dss: (DOpenRec n (DE_FVar y) s2).

  gen I3 s s2 n. induction sub_s;
  introv cm notin_t notin_d dsinfo tsinfo iinfo; simpls.

  (* Var *)
  destruct s; try(solve[inversion tsinfo]).
  unfold AOpen in tsinfo. simpls.
  case_nat~. inversion tsinfo. subst. unfold AOpen. simpls.
  destruct s2; try(solve[inversion dsinfo]).
  unfold DOpen in dsinfo. simpls.
  case_nat~. subst. unfold DOpen. simpls.
  unfold DOpen in dsinfo. simpls.
  inversion dsinfo. subst.  false notin_same notin_d.

  unfold AOpen in tsinfo. simpls.
  inversion tsinfo. subst.
  unfold AOpen. simpls.
  destruct s2; try(solve[inversion dsinfo]).
  unfold DOpen in dsinfo. simpls.
  case_nat~. inversion dsinfo; subst. false notin_same notin_t.
  unfold DOpen in dsinfo. simpls. inversion dsinfo; subst.
  unfold DOpen. simpls. apply~ ACpltCtxSubst_Var.

  (* TyVar *)
  destruct s; try(solve[inversion tsinfo]).
  unfold AOpen in tsinfo. simpls.
  case_nat~. inversion tsinfo. subst. unfold AOpen. simpls.
  destruct s2; try(solve[inversion dsinfo]).
  unfold DOpen in dsinfo. simpls.
  case_nat~. subst. unfold DOpen. simpls.
  unfold DOpen in dsinfo. simpls.
  inversion dsinfo. subst.  false notin_same notin_d.

  unfold AOpen in tsinfo. simpls.
  inversion tsinfo. subst.
  unfold AOpen. simpls.
  destruct s2; try(solve[inversion dsinfo]).
  unfold DOpen in dsinfo. simpls.
  case_nat~. inversion dsinfo; subst. false notin_same notin_t.
  unfold DOpen in dsinfo. simpls. inversion dsinfo; subst.
  unfold DOpen. simpls. apply* ACpltCtxSubst_TyVar.

  (* BndVar *)
  destruct s; try(solve[inversion tsinfo]).
  unfold AOpen in tsinfo. simpls.
  case_nat~. inversion tsinfo. subst. unfold AOpen. simpls.
  destruct s2; try(solve[inversion dsinfo]).
  unfold DOpen in dsinfo. simpls.
  case_nat~. subst. unfold DOpen. simpls.
  unfold DOpen in dsinfo. simpls.
  inversion dsinfo. subst.  false notin_same notin_d.

  unfold AOpen in tsinfo. simpls.
  inversion tsinfo. subst.
  unfold AOpen. simpls.
  destruct s2; try(solve[inversion dsinfo]).
  unfold DOpen in dsinfo. simpls.
  case_nat~. inversion dsinfo; subst. false notin_same notin_t.
  unfold DOpen in dsinfo. simpls. inversion dsinfo; subst.
  unfold DOpen. simpls. apply* ACpltCtxSubst_BndVar.

  (* EVar *)
  destruct s; try(solve[inversion tsinfo]).
  unfold AOpen in tsinfo. simpls.
  case_nat~. inversion tsinfo. simpls.
  subst.
  apply~ ACpltCtxSubst_EVar.

  assert (binds y (AC_Typ t) (G1 & v ~ AC_Solved_EVar t0 & G2)). rewrite iinfo. apply binds_middle_eq. rewrite iinfo in wf. apply awf_is_ok in wf. apply ok_middle_inv in wf. destruct wf. auto.
  assert (y # G1).
    destruct (binds_middle_inv H2) as [bd1 | [bd2 | bd3]].
    destruct (split_bind_context bd1) as (X1 & X2 & X). subst.
    repeat rewrite concat_assoc in wf. apply awf_is_ok in wf.
    apply ok_middle_inv_l in wf. auto_star.
    destruct bd2 as [_ [to_inv _]]. apply notin_singleton in notin_t. false notin_t to_inv.
    destruct bd3 as [_ [_ bd3]].
    destruct (split_bind_context bd3) as (X1 & X2 & X). subst.
    assert(X1 & y ~ AC_Typ t & (X2 & v ~ AC_Solved_EVar t0 & G2) = I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) by repeat rewrite~ concat_assoc.
    apply ok_middle_eq2 in H3. destruct H3 as[_ [_ H3]].
    assert (binds v (AC_Solved_EVar t0) I3). rewrite <- H3. apply binds_middle_eq. apply ok_middle_inv in H1. inversion~ H1.
    false common_contains_solved cm H4.
    repeat rewrite~ concat_assoc.
    rewrite <- H3. repeat rewrite~ concat_assoc.

  lets: cpltctxsubst_notin sub_s H3.
  lets: cpltctxsubst_dterm sub_s.
  lets: dopen_fv H5 H4.
  rewrite <- dopen_rec_term in sub_s; auto.
  rewrite~ <- dopen_rec_term.

  (* Star *)
  destruct s; try(solve[inversion tsinfo]).
  unfold AOpen in tsinfo. simpls.
  case_nat~. inversion tsinfo. simpls.
  subst.
  destruct s2; try(solve[inversion dsinfo]).
  unfold DOpen in dsinfo. simpls.
  case_nat~. subst. simpls.
  apply ACpltCtxSubst_Star.

  (* App *)
  destruct s; try(solve[inversion tsinfo]).
  unfold AOpen in tsinfo. simpls.
  case_nat~. inversion tsinfo. simpls.
  subst.
  destruct s2; try(solve[inversion dsinfo]).
  unfold DOpen in dsinfo. simpls.
  case_nat~. subst. simpls. inversion dsinfo; subst.

  inversion wt; subst.
  apply ACpltCtxSubst_App.
  apply~ IHsub_s1. auto. apply~ IHsub_s2. auto.

  (* Lam *)
  destruct s; try(solve[inversion tsinfo]).
  unfold AOpen in tsinfo. simpls.
  case_nat~. inversion tsinfo. simpls.
  subst.
  destruct s2; try(solve[inversion dsinfo]).
  unfold DOpen in dsinfo. simpls.
  case_nat~. subst. simpls. inversion dsinfo; subst.

  inversion wt; subst.
  apply ACpltCtxSubst_Lam with (L \u L0 \u dom(I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) \u \{y}).
  intros z notin_z. simpls.
  assert(ACpltCtxSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3 & z ~ AC_Var)
     (AOpenRec (S n) (AE_EVar a) (s @ z)) (DOpenRec (S n) ia (s2 ^ z))).
  apply H0 with (x:=z) (I4:= (I3 & z ~ AC_Var)); auto.
  apply ~ complete_add.
  inversion sub_a; subst. rewrite <- concat_assoc. apply~ ACpltCtxSubst_EVar. apply~ complete_add. rewrite concat_assoc. apply ok_push. assumption. rewrite~ H1. apply* common_add.
  apply~ notin_open_inv. simpls. auto_star.
  apply~ notin_dopen_inv. simpls. auto_star.
  apply~ dopen_reorder.
  apply~ open_reorder.
  rewrite~ concat_assoc.
  unfold AOpen. rewrite open_reorder.
  unfold DOpen. rewrite~ dopen_reorder.
  apply* cpltctxsubst_dterm.
  apply~ ATerm_Var.
  apply~ ATerm_EVar.
  auto.

  (* Pi *)
  destruct s; try(solve[inversion tsinfo]).
  unfold AOpen in tsinfo. simpls.
  case_nat~. inversion tsinfo. simpls.
  subst.
  destruct s2; try(solve[inversion dsinfo]).
  unfold DOpen in dsinfo. simpls.
  case_nat~. subst. simpls. inversion dsinfo; subst.

  inversion wt; subst.
  apply ACpltCtxSubst_Pi with (L \u L0 \u dom(I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) \u \{y}).
  apply~ IHsub_s. auto.
  intros z notin_z. simpls.
  assert(ACpltCtxSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3 & z ~ AC_Var)
     (AOpenRec (S n) (AE_EVar a) (s3 @ z)) (DOpenRec (S n) ia (s2_2 ^ z))).
  apply H0 with (x:=z) (I4:= (I3 & z ~ AC_Var)); auto.
  apply ~ complete_add.
  inversion sub_a; subst. rewrite <- concat_assoc. apply~ ACpltCtxSubst_EVar. apply~ complete_add. rewrite concat_assoc. apply ok_push. assumption. rewrite~ H1. apply* common_add.
  apply~ notin_open_inv. simpls. auto_star.
  apply~ notin_dopen_inv. simpls. auto_star.
  apply~ dopen_reorder.
  apply~ open_reorder.
  rewrite~ concat_assoc.
  unfold AOpen. rewrite open_reorder.
  unfold DOpen. rewrite~ dopen_reorder.
  apply* cpltctxsubst_dterm.
  apply~ ATerm_Var.
  apply~ ATerm_EVar.
  auto.

  (* Let *)
  destruct s; try(solve[inversion tsinfo]).
  unfold AOpen in tsinfo. simpls.
  case_nat~. inversion tsinfo. simpls.
  subst.
  destruct s2; try(solve[inversion dsinfo]).
  unfold DOpen in dsinfo. simpls.
  case_nat~. subst. simpls. inversion dsinfo; subst.

  inversion wt; subst.
  apply ACpltCtxSubst_Let with (L \u L0 \u dom(I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) \u \{y}).
  apply~ IHsub_s. auto.
  intros z notin_z. simpls.
  assert(ACpltCtxSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3 & z ~ AC_Var)
     (AOpenRec (S n) (AE_EVar a) (s3 @ z)) (DOpenRec (S n) ia (s2_2 ^ z))).
  apply H0 with (x:=z) (I4:= (I3 & z ~ AC_Var)); auto.
  apply ~ complete_add.
  inversion sub_a; subst. rewrite <- concat_assoc. apply~ ACpltCtxSubst_EVar. apply~ complete_add. rewrite concat_assoc. apply ok_push. assumption. rewrite~ H1. apply* common_add.
  apply~ notin_open_inv. simpls. auto_star.
  apply~ notin_dopen_inv. simpls. auto_star.
  apply~ dopen_reorder.
  apply~ open_reorder.
  rewrite~ concat_assoc.
  unfold AOpen. rewrite open_reorder.
  unfold DOpen. rewrite~ dopen_reorder.
  apply* cpltctxsubst_dterm.
  apply~ ATerm_Var.
  apply~ ATerm_EVar.
  auto.

  (* CastUp *)
  destruct s; try(solve[inversion tsinfo]).
  unfold AOpen in tsinfo. simpls.
  case_nat~. inversion tsinfo. simpls.
  subst.
  destruct s2; try(solve[inversion dsinfo]).
  unfold DOpen in dsinfo. simpls.
  case_nat~. subst. simpls. inversion dsinfo; subst.

  inversion wt; subst.
  apply ACpltCtxSubst_CastUp.
  apply~ IHsub_s. auto.

  (* CastDn *)
  destruct s; try(solve[inversion tsinfo]).
  unfold AOpen in tsinfo. simpls.
  case_nat~. inversion tsinfo. simpls.
  subst.
  destruct s2; try(solve[inversion dsinfo]).
  unfold DOpen in dsinfo. simpls.
  case_nat~. subst. simpls. inversion dsinfo; subst.

  inversion wt; subst.
  apply ACpltCtxSubst_CastDn.
  apply~ IHsub_s. auto.

  (* Ann *)
  destruct s; try(solve[inversion tsinfo]).
  unfold AOpen in tsinfo. simpls.
  case_nat~. inversion tsinfo. simpls.
  subst.
  destruct s2; try(solve[inversion dsinfo]).
  unfold DOpen in dsinfo. simpls.
  case_nat~. subst. simpls. inversion dsinfo; subst.

  inversion wt; subst.
  apply ACpltCtxSubst_Ann.
  apply~ IHsub_s1. auto. apply~ IHsub_s2. auto.
Qed.

Lemma cpltctxsubst_replace: forall I1 I2 a it ia y s s2 t,
   CompleteCtx (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) ->
   AWf (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) ->
   AWTerm (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) (s @ y) ->
   y \notin AFv s ->
   y \notin DFv s2 ->
   ACpltCtxSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) (s @ y) (s2 ^ y) ->
   ACpltCtxSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) (AE_EVar a) ia ->
   ACpltCtxSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) (s @@ AE_EVar a) (s2 ^^ ia).
Proof.
intros.
  assert(ACpltCtxSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & empty) (s @@ AE_EVar a) (s2 ^^ ia)).
  apply~ cpltctxsubst_replace'; try(rewrite concat_empty_r); auto.
  apply common_empty.
  rewrite concat_empty_r in H6. auto.
Qed.

Lemma cpltctxtsubst_replace': forall I1 I2 I3 a it ia y s s2 t,
   CompleteCtx (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) ->
   AWf (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) ->
   AWTermT (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) (s @' y) ->
   CommonCtx I3 ->
   y \notin ATFv s ->
   y \notin DTFv s2 ->
   ACpltCtxTSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) (s @' y) (s2 ^' y) ->
   ACpltCtxSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) (AE_EVar a) ia ->
   ACpltCtxTSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) (s @@' AE_EVar a) (s2 ^^' ia).
Proof.
  introv comp wf wt cm notin_t notin_d sub_s sub_a.
  gen_eq I:(I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3).
  gen_eq tss: (s @' y).
  gen_eq dss: (s2 ^' y).

  unfold AOpenT.
  unfold DOpenT.
  gen I3 s s2. generalize 0. induction sub_s;
  introv cm  notin_t notin_d dsinfo tsinfo iinfo; simpls.

  (* Forall *)
  destruct s; try(solve[inversion tsinfo]). inversion tsinfo; subst.
  destruct s0; try(solve[inversion dsinfo]). inversion dsinfo; subst.
  simpls.

  inversion wt; subst.
  apply ACpltCtxTSubst_Poly with (L \u L0 \u dom(I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3) \u \{y}).
  intros z notin_z. simpls.
  assert(ACpltCtxTSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & I3 & z ~ AC_Typ AE_Star)
     (AOpenTypRec (S n) (AE_EVar a) (s @' z)) (DOpenTypRec (S n) ia (s0 ^' z))).
  apply H0 with (x:=z) (I4:= (I3 & z ~ AC_Typ AE_Star)); auto.
  apply ~ complete_add_typ.
  apply~ AWf_TyVar. apply~ awftyp_star.
  inversion sub_a; subst. rewrite <- concat_assoc. apply~ ACpltCtxSubst_EVar. apply~ complete_add_typ. rewrite concat_assoc. apply ok_push. assumption. rewrite~ H1.
  apply* common_add_typ.
  apply~ notin_opent_inv. simpls. auto_star.
  apply~ notin_dopent_inv. simpls. auto_star.
  apply~ dopent_reorder.
  apply~ opent_reorder.
  rewrite~ concat_assoc.
  unfold AOpenT. rewrite opent_reorder.
  unfold DOpenT. rewrite~ dopent_reorder.
  apply* cpltctxsubst_dterm.
  apply~ ATerm_Var.
  apply~ ATerm_EVar.
  auto.

  (* Expr *)
  destruct s; try(solve[inversion tsinfo]). inversion tsinfo; subst.
  destruct s2; try(solve[inversion dsinfo]). inversion dsinfo; subst.
  simpls.

  inversion wt.
  apply ACpltCtxTSubst_Expr.
  apply~ cpltctxsubst_replace'.
Qed.

Lemma cpltctxtsubst_replace: forall I1 I2 a it ia y s s2 t,
   CompleteCtx (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) ->
   AWf (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) ->
   AWTermT (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) (s @' y) ->
   y \notin ATFv s ->
   y \notin DTFv s2 ->
   ACpltCtxTSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) (s @' y) (s2 ^' y) ->
   ACpltCtxSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) (AE_EVar a) ia ->
   ACpltCtxTSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) (s @@' AE_EVar a) (s2 ^^' ia).
Proof.
  intros.
  assert(ACpltCtxTSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & empty) (s @@' AE_EVar a) (s2 ^^' ia)).
  apply~ cpltctxtsubst_replace'; try(rewrite concat_empty_r); auto.
  apply common_empty.
  rewrite concat_empty_r in H6. auto.
Qed.

Lemma cpltctxtsubst_replace_removey: forall I1 I2 a it ia y s s2 t,
   CompleteCtx (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) ->
   AWf (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) ->
   AWTermT (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) (s @' y) ->
   y \notin ATFv s ->
   y \notin DTFv s2 ->
   ACpltCtxTSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) (s @' y) (s2 ^' y) ->
   ACpltCtxSubst (I1 & a ~ AC_Solved_EVar it & I2) (AE_EVar a) ia ->
   ACpltCtxTSubst (I1 & a ~ AC_Solved_EVar it & I2) (s @@' AE_EVar a) (s2 ^^' ia).
Proof.
  intros.
  assert(ACpltCtxSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) (AE_EVar a) ia).
  rewrite <- concat_assoc. apply~ ACpltCtxSubst_EVar.
  repeat rewrite <- concat_assoc in H. apply complete_part_left with ((a ~ AC_Solved_EVar it & (I2 & y ~ AC_Typ t))); auto.
  repeat rewrite concat_assoc. apply* awf_is_ok.
  rewrite <- concat_assoc in H. apply complete_part_right with ((I1 & a ~ AC_Solved_EVar it)); auto.
  repeat rewrite concat_assoc. apply* awf_is_ok.
  inversion H5; subst.
  apply ok_middle_eq2 in H6; auto.
  destruct H6 as [eqg [eqv eqi]]. inversion eqv. subst.
  assumption.
  rewrite~ <- H6.

  assert(ACpltCtxTSubst (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t) (s @@' AE_EVar a) (s2 ^^' ia)).
  apply~ cpltctxtsubst_replace.

  apply cpltctxtsubst_weaken_append with (y~AC_Typ t); auto.
  apply cpltctxtsubst_awtermt in H7; auto.
  assert (y \notin \{a}). apply awf_is_ok in H0.
  assert(ok (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & empty)) by rewrite~ concat_empty_r.
  apply ok_non_eq in H8. rewrite notin_singleton. auto.
  assert (y \notin ATFv (s @@' AE_EVar a)).
  apply~ notin_opent_inv.
  assert(AWTermT (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ t & empty) (s @@' AE_EVar a)) by rewrite~ concat_empty_r.
  apply awtermt_remove in H10; auto.
  rewrite concat_empty_r in H10.
  assumption.
Qed.


Ltac gather_vars_strong :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : AExpr => AFv x) in
  let D := gather_vars_with (fun x : AType => ATFv x) in
  let E := gather_vars_with (fun x : ACtx => dom x) in
  let F := gather_vars_with (fun x : DExpr => DFv x) in
  let G := gather_vars_with (fun x : DType => DTFv x) in
  let H := gather_vars_with (fun x : DCtx => dom x) in
  constr:(A \u B \u C \u D \u E \u F \u G \u H).

Ltac pick_fresh_strong X :=
  let L := gather_vars_strong in (pick_fresh_gen L X).

Theorem Soundness_Instantiation_proof: forall G H I s t G' s' t',
    AWf G ->
    AInst G s t H ->
    AWfTyp G s ->
    ExtCtx H I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I G G' ->
    ACpltCtxTSubst I s s' ->
    ACpltCtxSubst I t t' ->
    DInst G' s' t'.
Proof.
  introv wf inst wt_s ex comp sub_h sub_s sub_t.
  gen I G' s' t'.
  induction inst; introv ex comp sub_h sub_s sub_t.

  inversion sub_s; subst; clear sub_s.
  assert (eq:= cplt_ctxsubst_eq sub_t H1). subst. clear H1.
  apply DInst_Expr.

  admit.

  inversion sub_s; subst; clear sub_s.
  assert (wfi: AWf I). apply* awf_preservation.

  assert (exists ta, ACpltCtxSubst I (AE_EVar a) ta).
  apply~ cpltctxsubst_exists.
  apply extension_weakening_awterm with H; auto.
  apply extension_weakening_awterm with (G & a ~ AC_Unsolved_EVar); auto. apply* ainst_extension.

  destruct H1 as (ia & sub_ia).
  apply DInst_Poly with ia.
  admit.

  apply IHinst with I; auto.

  (* AWfTyp (G & a ~ AC_Unsolved_EVar) (s @@' AE_EVar a) *)
  inversion wt_s; subst.
  pick_fresh y.
  assert (y \notin L0) by auto_star.
  lets: H4 y H1.
  apply awftyp_change with y; auto.

  (* ACpltCtxSubstCtx I (G & a ~ AC_Unsolved_EVar) G' *)
  apply ainst_destruct in inst.
  destruct inst as (H2 & [soft_h2 hh2]). subst.
  lets: softness_cpltctxsubstctx soft_h2 ex comp sub_h.
  destruct H as (I1 & I2 & it & [hi [hi1 soft_i2]]).
  subst.
  apply~ cpltctxsubstctx_append_soft.
  apply~ ACpltCtxSubstCtx_Solved_Unsolved_EVar.
  do 2 apply complete_part_left in comp. assumption.
  apply awf_is_ok in wfi.
  apply* ok_concat_inv_l.
  apply* awf_is_ok.
  apply* awf_is_ok.
  apply~ AWf_Ctx_Unsolved_EVar.

  (* ACpltCtxTSubst I (s @@' AE_EVar a) (s2 ^^' ia) *)
  inversion wt_s; subst.
  pick_fresh_strong y.
  assert (notinl: y \notin L) by auto_star.
  assert (notinl0: y \notin L0) by auto_star.
  lets: H3 y notinl.
  lets: H4 y notinl0.
  apply ainst_destruct in inst.
  destruct inst as (HT & [soft_h2 hh2]). subst.
  lets: softness_cpltctxsubstctx soft_h2 ex comp sub_h.
  destruct H as (I1 & I2 & it & [hi [hi1 soft_i2]]).
  subst.
  clear H4 H3 IHinst.
  apply cpltctxtsubst_replace_removey with y (AE_Star); auto.
  apply~ complete_add_typ.
  apply~ AWf_TyVar. apply~ awftyp_star.
  apply cpltctxtsubst_awtermt in H1.
  assert(AWTermT (I1 & a ~ AC_Solved_EVar it & I2 & y ~ AC_Typ AE_Star & empty) (s @' y)) by rewrite~ concat_empty_r.
  apply awtermt_replace in H.
  rewrite concat_empty_r in H.
  assumption.
  apply~ AWf_TyVar. apply~ awftyp_star.
  apply~ AWf_Ctx_Unsolved_EVar.
Qed.