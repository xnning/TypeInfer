Require Import CtxExtension.
Require Import LibLN.
Require Import AlgoDef.
Require Import UtilityEnv.
Require Import DeclDef.
Require Import AlgoInfra.
Require Import DeclInfra.
Require Import Subst.
Require Import Theorems.
Require Import Exists.
Require Import UtilityMore.
Require Import WeakExtension.
Require Import UtilityAlgo.

Set Implicit Arguments.

Lemma cpltctxsubst_over_subst: forall I1 I2 a t e d,
    AWf (I1 & a ~ AC_Solved_EVar t & I2) ->
    CompleteCtx (I1 & a ~ AC_Solved_EVar t & I2) ->
    AWTermT (I1 & a ~ AC_Solved_EVar t & I2) e ->
    ACpltCtxSubst (I1 & a ~ AC_Solved_EVar t & I2) e d ->
    ACpltCtxSubst (I1 & a ~ AC_Solved_EVar t & I2) (ATSubstT a t e) d.
Proof.
  introv wf comp wt sub.
  lets: cpltctxsubst_wftyp wf sub.
  gen_eq S: (I1 & a ~ AC_Solved_EVar t & I2). gen I2 d.

  induction H; introv sub sinfo; f_equal *.

  (* APP *)
  rewrite atsubstt_expr.
  inversion sub; subst. simpls.
  apply ACpltCtxSubst_App.
  apply IHAWTermT1 with I2; auto.
  apply IHAWTermT2 with I2; auto.

  (* LAM *)
  rewrite atsubstt_expr.
  inversion sub; subst. simpls.
  apply ACpltCtxSubst_Lam with (L \u L0 \u dom (I1 & a ~ AC_Solved_EVar t & I2)). intros y notin.
  assert (y \notin L) by auto.
  assert (y \notin L0) by auto.
  lets: H3 H2.
  forwards: H0 H1 H4. apply~ AWf_Var.
  apply~ complete_add. auto_star.
  assert(I1 & a ~ AC_Solved_EVar t & I2 & y ~ AC_Var =
         I1 & a ~ AC_Solved_EVar t &(I2 & y ~ AC_Var)) by rewrite~ concat_assoc.
  exact H5.
  unfold AOpen in H5. rewrite asubstt_openrec in H5.
  simpl in H5. exact H5.
  apply AWf_left in wf. apply awterm_solved_evar in wf. apply* awtermt_is_atermty.

  (* PI *)
  inversion wt; subst.
  rewrite atsubstt_expr.
  inversion sub; subst. simpls.
  apply ACpltCtxSubst_Pi with (L \u L0 \u L1 \u dom (I1 & a ~ AC_Solved_EVar t & I2)).
  apply IHAWTermT with I2; auto.
  intros y notin.
  assert (y \notin L) by auto.
  assert (y \notin L0) by auto.
  assert (y \notin L1) by auto. lets: H6 H3.
  lets: H9 H4.
  forwards: H1 H2 H10. apply~ AWf_Var.
  apply~ complete_add. auto.
  assert(I1 & a ~ AC_Solved_EVar t & I2 & y ~ AC_Var =
         I1 & a ~ AC_Solved_EVar t &(I2 & y ~ AC_Var)) by rewrite~ concat_assoc.
  exact H11.
  unfold AOpenT in H11. rewrite atsubstt_opentyprec in H11.
  simpl in H11. exact H11.
  apply AWf_left in wf. apply awterm_solved_evar in wf. apply* awtermt_is_atermty.

  (* CASTUP *)
  rewrite atsubstt_expr.
  inversion sub; subst. simpls.
  apply ACpltCtxSubst_CastUp.
  apply IHAWTermT with I2; auto.

  (* CASTDN *)
  rewrite atsubstt_expr.
  inversion sub; subst. simpls.
  apply ACpltCtxSubst_CastDn.
  apply IHAWTermT with I2; auto.

  (* ANN *)
  rewrite atsubstt_expr.
  inversion sub; subst. simpls.
  apply ACpltCtxSubst_Ann.
  apply IHAWTermT1 with I2; auto.
  apply IHAWTermT2 with I2; auto.

  (* LAM *)
  rewrite atsubstt_expr.
  inversion sub; subst. simpls.
  apply ACpltCtxSubst_Forall with (L \u L0 \u dom (I1 & a ~ AC_Solved_EVar t & I2)). intros y notin.
  assert (y \notin L) by auto.
  assert (y \notin L0) by auto.
  lets: H3 H2.
  forwards: H0 H1 H4. apply~ AWf_TVar.
  apply~ complete_add_tvar.
  lets: H H1. auto.
  assert(I1 & a ~ AC_Solved_EVar t & I2 & y ~ AC_TVar =
         I1 & a ~ AC_Solved_EVar t &(I2 & y ~ AC_TVar)) by rewrite~ concat_assoc.
  exact H5.
  unfold ATOpenT in H5. rewrite atsubstt_topentyprec in H5.
  assert (y <> a). simpl_dom. auto.
  simpl in H5. case_if in H5. exact H5.
  apply AWf_left in wf. apply awterm_solved_evar in wf. apply* awtermt_is_atermty.

  (*TFVar*)
  simpls. case_var~.
  subst. apply binds_middle_eq_inv in H. false H.
  apply* awf_is_ok.

  (*UNSOLVED EVar*)
  simpls. case_var~.
  subst. apply binds_middle_eq_inv in H. false H.
  apply* awf_is_ok.

  (*EVar*)
  simpls. case_var~.
  subst.
  inversion sub; subst.
  apply ok_middle_eq2 in H0; auto.
  destruct H0 as [? [? ?]]. inversion H1. subst.
  apply~ a2d_cpltctxsubst. apply awterm_evar_binds with a; auto. apply binds_middle_eq. apply ok_middle_inv_r in H4; auto.
  apply AWf_left in wf. lets: awterm_solved_evar wf.
  rewrite <- concat_assoc. rewrite~ actxtsubst_append.
  apply acpltctxsubst_ctxsubst_a2d in H5; auto. apply AWf_left in wf; auto.
  rewrite~ concat_assoc.
Qed.

Theorem resolve_evar_invariance: forall G a e t H,
    AWf G ->
    AResolveEVar G a e t H ->
    AWTermT G e ->
    ACtxTSubst H e = ACtxTSubst H t.
Proof.
  introv wf res wt.
  induction res; auto.
  rewrite actxtsubst_evar.
  symmetry.
  rewrite~ <- concat_assoc.
  rewrite~ actxtsubst_append.
  do 2 rewrite <- concat_assoc.
  apply ok_insert; auto.
  repeat rewrite concat_assoc.
  apply* ok_middle_change.
  do 3 rewrite~ <- concat_assoc.
  apply ok_insert; auto.
  repeat rewrite concat_assoc.
  apply* ok_middle_change.

  (* PI *)
  repeat rewrite actxtsubst_expr. f_equal.
  repeat rewrite actxsubst_pi.
  inversion wt; subst. clear wt.
  lets: IHres wf H6. clear IHres.
  f_equal.
  pick_fresh y.
  assert (y \notin L) by auto.
  lets: H0 H4.
  lets: resolve_evar_awf_preservation res wf.
  assert(AWf (H1 & y ~ AC_Var)) by apply* AWf_Var.
  lets: resolve_evar_extension H5 H9.
  apply extctx_remove_var in H10.
  rewrite (substitution_extension_invariance_left2) with (G:=H1); auto.
  rewrite (substitution_extension_invariance_left2) with (G:=H1) (t:=t3); auto.
  rewrite~ H3.

  pick_fresh y.
  assert (y \notin L) by auto.
  lets: resolve_evar_awf_preservation res wf.
  assert(AWf (H1 & y ~ AC_Var)) by apply* AWf_Var.
  assert(AWTermT (H1 & y ~ AC_Var) (ACtxTSubst H1 (t2 @@' AE_FVar y))).
  rewrite <- tsubst_add_var with (x:=y).
  apply* ctxsubst_awterm.
  assert (y \notin L0) by auto.
  lets: H7 H9. clear H7.
  assert(ExtCtx (G & y ~ AC_Var) (H1 & y ~ AC_Var)). apply ExtCtx_Var; auto.
  lets: resolve_evar_extension res wf; auto.
  lets: extension_weakening_awtermt H10 H7; auto.

  lets: H2 H4 H8 H9.
  repeat rewrite tsubst_add_var in H10.
  lets: H0 H4. clear H0.
  lets: resolve_evar_extension H11 H8.
  apply extctx_remove_var in H0.
  rewrite <- substitution_extension_invariance_left2 in H10; auto.
  lets: resolve_evar_awf_preservation H11 H8.
  apply AWf_left in H12.
  do 2 rewrite actxtsubst_open in H10; auto.
  rewrite actxsubst_fvar in H10.
  apply atopen_var_inj in H10; auto.

  apply* notin_actxtsubst.
  apply* notin_actxtsubst.

  (* APP *)
  repeat rewrite actxtsubst_expr. f_equal.
  repeat rewrite actxsubst_app.
  inversion wt; subst. clear wt.
  f_equal.
  lets: IHres1 wf H4.
  repeat rewrite actxtsubst_expr in H0. inversion H0; subst.
  lets: resolve_evar_awf_preservation res1 wf.
  lets: resolve_evar_extension res2 H2.
  rewrite (substitution_extension_invariance_left) with (G:=H1); auto.
  rewrite (substitution_extension_invariance_left) with (G:=H1) (t:=d1); auto.
  rewrite~ H3.

  lets: resolve_evar_awf_preservation res1 wf.
  assert (AWTermT H1 (ACtxTSubst H1 (AT_Expr t2))).
  apply* ctxsubst_awterm.
  lets: resolve_evar_extension res1 wf; auto.
  lets: extension_weakening_awtermt H5 H2; auto.
  lets: IHres2 H0 H2.
  lets: resolve_evar_extension res2 H0.
  rewrite <- substitution_extension_invariance_left2 in H3; auto.
  repeat rewrite actxtsubst_expr in H3. inversion~ H3.

  (* LAM *)
  repeat rewrite actxtsubst_expr. f_equal.
  repeat rewrite actxsubst_lam. f_equal.
  inversion wt; subst. clear wt.
  pick_fresh y.
  assert (notinl: y \notin L) by auto.
  assert (notinl0: y \notin L0) by auto.
  lets: H0 notinl; clear H0.
  lets: H1 notinl; clear H1.
  lets: H4 notinl0; clear H4.
  repeat rewrite tsubst_add_var in H0.
  assert (AWf (G & y ~ AC_Var)) by apply* AWf_Var.
  lets: H0 H3 H1. clear H0.

  do 2 rewrite actxtsubst_expr in H4. inversion~ H4. clear H4.
  lets: resolve_evar_awf_preservation H2 H3.
  apply AWf_left in H0.
  do 2 rewrite actxsubst_open in H5; auto.
  rewrite actxsubst_fvar in H5.
  apply aopen_var_inj in H5; auto.

  apply* notin_actxsubst.
  apply* notin_actxsubst.

  (* CASTUP *)
  repeat rewrite actxtsubst_expr. f_equal.
  repeat rewrite actxsubst_castup. f_equal.
  inversion wt; subst.
  lets: IHres wf H2.
  repeat rewrite actxtsubst_expr in H0. inversion H0. auto.

  (* CASTDN *)
  repeat rewrite actxtsubst_expr. f_equal.
  repeat rewrite actxsubst_castdn. f_equal.
  inversion wt; subst.
  lets: IHres wf H2.
  repeat rewrite actxtsubst_expr in H0. inversion H0. auto.

  (* ANN *)
  repeat rewrite actxtsubst_expr. f_equal.
  repeat rewrite actxsubst_ann.
  inversion wt; subst. clear wt.
  f_equal.
  lets: IHres1 wf H4.
  repeat rewrite actxtsubst_expr in H0. inversion H0; subst.
  lets: resolve_evar_awf_preservation res1 wf.
  lets: resolve_evar_extension res2 H2.
  rewrite (substitution_extension_invariance_left) with (G:=H1); auto.
  rewrite (substitution_extension_invariance_left) with (G:=H1) (t:=d1); auto.
  rewrite~ H3.

  lets: resolve_evar_awf_preservation res1 wf.
  assert (AWTermT H1 (ACtxTSubst H1 t2)).
  apply* ctxsubst_awterm.
  lets: resolve_evar_extension res1 wf; auto.
  lets: extension_weakening_awtermt H5 H2; auto.
  lets: IHres2 H0 H2.
  lets: resolve_evar_extension res2 H0.
  rewrite <- substitution_extension_invariance_left2 in H3; auto.
Qed.

Theorem unif_soundness_same : forall G H I t1 t2 H' t1' t2',
    AUnify G t1 t2 H ->
    t1 = ACtxTSubst G t1 ->
    t2 = ACtxTSubst G t2 ->
    ExtCtx H I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I H H' ->
    ACpltCtxSubst I t1 t1' ->
    ACpltCtxSubst I t2 t2' ->
    AWf G -> AWTermT G t1 -> AWTermT G t2 ->
    t1' = t2'.
Proof.
  intros. gen t1'. gen t2'. gen I. gen H'. inductions H0; intros.

  apply* cplt_ctxsubst_eq.
  apply* cplt_ctxsubst_eq.
  apply* cplt_ctxsubst_eq.
  apply* cplt_ctxsubst_eq.

  (* STAR *)
  inversions H6. inversions H7.
  auto.

  (* APP *)
  lets: unify_extension H0_ H8.
  destruct H11 as [? ?].
  lets: unify_extension H0_0 H11.
  destruct H13 as [? ?].
  lets: extension_transitivity H14 H3.
  inversions H6. inversions H7. inversion H9; subst. inversion H10; subst.
  forwards * : IHAUnify1 H18 H19.
  rewrite actxtsubst_expr. f_equal.
  rewrite actxtsubst_expr in H0. inversion~ H0.
  rewrite actxsubst_app in H7. inversion H7. rewrite <- H16. auto.
  rewrite actxtsubst_expr. f_equal.
  rewrite actxtsubst_expr in H2. inversion~ H2.
  rewrite actxsubst_app in H7. inversion H7. rewrite <- H16. auto.
  lets: confluence_cplt3 H3 H15 H4 H5. exact H6.
  inversion~ H6. subst. clear H6.

  clear IHAUnify1 H18 H19 H0_.
  assert(AT_Expr (ACtxSubst H1 t3) = ACtxTSubst H1 (AT_Expr (ACtxSubst H1 t3))).
  rewrite actxtsubst_expr. f_equal. rewrite~ ctxsubst_twice.
  assert(AT_Expr (ACtxSubst H1 t4) = ACtxTSubst H1 (AT_Expr (ACtxSubst H1 t4))).
  rewrite actxtsubst_expr. f_equal. rewrite~ ctxsubst_twice.
  lets: IHAUnify2 H6 H7 H11. clear IHAUnify2 H6 H7.
  clear H9 H17 H23 H10.
  assert(AWTermT H1 (AT_Expr (ACtxSubst H1 t3))).
  rewrite <- actxtsubst_expr. apply~ ctxsubst_awterm.
  lets: extension_weakening_awtermt H20 H12; auto.
  assert(AWTermT H1 (AT_Expr (ACtxSubst H1 t4))).
  rewrite <- actxtsubst_expr. apply~ ctxsubst_awterm.
  lets: extension_weakening_awtermt H24 H12; auto.
  lets: H16 H6 H7 H3 H4 H5. clear H20 H24.
  assert (ACpltCtxSubst I (AT_Expr (ACtxSubst H1 t4)) (DT_Expr d3)).
  apply complete_eq with (AT_Expr t4); auto.
  apply awf_preservation in H3; auto.
  apply* extension_weakening_awtermt.
  rewrite <- actxtsubst_expr.
  apply substitution_extension_invariance2; auto.
  assert (ACpltCtxSubst I (AT_Expr (ACtxSubst H1 t3)) (DT_Expr d2)).
  apply complete_eq with (AT_Expr t3); auto.
  apply awf_preservation in H3; auto.
  apply* extension_weakening_awtermt.
  rewrite <- actxtsubst_expr.
  apply substitution_extension_invariance2; auto.
  lets: H9 H10 H17. inversion~ H18.

  (* LAM *)
  inversions H11. inversions H7.
  inversion H9; subst. inversion H10; subst.
  pick_fresh y.
  assert (notinl: y \notin L) by auto.
  assert (notinl0: y \notin L0) by auto.
  assert (notinl1: y \notin L1) by auto.
  assert (notinl2: y \notin L2) by auto.
  assert (notinl3: y \notin L3) by auto.
  lets: H0 notinl. clear H0.
  assert (wf: AWf(G & y ~ AC_Var)) by apply~ AWf_Var.
  lets: unify_extension H7 wf.
  destruct H0 as [? ?].
  lets: H13 notinl1.  clear H13.
  lets: H14 notinl0. clear H14.
  lets: H12 notinl2. clear H12.
  lets: H15 notinl3. clear H15.
  assert(AT_Expr (t1 @@ AE_FVar y) = ACtxTSubst (G & y ~ AC_Var) (AT_Expr (t1 @@ AE_FVar y))).
  rewrite actxtsubst_expr in *. f_equal.
  inversion H2; subst. clear H2.
  rewrite actxsubst_lam in H17. inversion H17.  clear H17.
  rewrite <- H15. rewrite subst_add_var. rewrite~ actxsubst_open.
  rewrite actxsubst_fvar. rewrite <- H15. auto.
  assert(AT_Expr (t2 @@ AE_FVar y) = ACtxTSubst (G & y ~ AC_Var) (AT_Expr (t2 @@ AE_FVar y))).
  rewrite actxtsubst_expr in *. f_equal.
  inversion H3; subst. clear H3.
  rewrite actxsubst_lam in H18. inversion H18.  clear H18.
  rewrite <- H17. rewrite subst_add_var. rewrite~ actxsubst_open.
  rewrite actxsubst_fvar. rewrite <- H17. auto.

  lets: H1 notinl H15 H17 wf.
  clear H1 H15 H17 H2 H3.
  lets: H18 H14 H12. clear H18 H14 H12.
  lets: awf_preservation H4.
  assert (AWf (I & y ~ AC_Var)) by apply~ AWf_Var.
  assert(ExtCtx (H & y ~ AC_Var) (I & y ~ AC_Var)) by apply~ ExtCtx_Var.
  assert (CompleteCtx (I & y ~ AC_Var)) by apply~ complete_add.
  assert (ACpltCtxSubstCtx (I & y ~ AC_Var) (H & y ~ AC_Var) H') by apply~ ACpltCtxSubstCtx_Var.
  lets: H1 H12 H14 H15 H16 H13. clear H1.
  inversion H17. clear H17.
  apply dopen_var_inj in H18; auto.
  rewrite~ H18.

  (* CASTUP *)
  inversions H6. inversions H7. inversion H9; subst. inversion H10; subst.
  forwards * : IHAUnify H11 H14.
  rewrite actxtsubst_expr. f_equal.
  rewrite actxtsubst_expr in H1. inversion~ H1.
  rewrite actxsubst_castup in H7. inversion H7. rewrite <- H15. auto.
  rewrite actxtsubst_expr. f_equal.
  rewrite actxtsubst_expr in H2. inversion~ H2.
  rewrite actxsubst_castup in H7. inversion H7. rewrite <- H15. auto.
  inversion~ H6.

  (* CASTDN *)
  inversions H6. inversions H7. inversion H9; subst. inversion H10; subst.
  forwards * : IHAUnify H11 H14.
  rewrite actxtsubst_expr. f_equal.
  rewrite actxtsubst_expr in H1. inversion~ H1.
  rewrite actxsubst_castdn in H7. inversion H7. rewrite <- H15. auto.
  rewrite actxtsubst_expr. f_equal.
  rewrite actxtsubst_expr in H2. inversion~ H2.
  rewrite actxsubst_castdn in H7. inversion H7. rewrite <- H15. auto.
  inversion~ H6.

  (* PI *)
  inversions H12. inversions H13. inversion H9; subst. inversion H10; subst.
  clear H9 H10.
  pick_fresh y.
  assert(notinl: y \notin L) by auto.
  assert(notinl0: y \notin L0) by auto.
  assert(notinl1: y \notin L1) by auto.
  assert(notinl2: y \notin L2) by auto.
  assert(notinl3: y \notin L3) by auto.
  lets: unify_extension H0 H8.
  destruct H9 as [? ?].
  lets: H2 notinl. clear H2.
  lets: H19 notinl0. clear H19.
  lets: H20 notinl1. clear H20.
  lets: H18 notinl2. clear H18.
  lets: H22 notinl3. clear H22.
  assert(AWf (H1 & y ~ AC_Var)) by apply~ AWf_Var.
  lets: unify_extension H12 H19.
  destruct H20 as [? ?].
  apply extctx_remove_var in H22.
  lets: extension_transitivity H22 H6.
  inversions H4. inversions H5.
  forwards * : IHAUnify H23.
  rewrite actxtsubst_expr in H25. inversion~ H25.
  rewrite actxsubst_pi in H5. inversion H5. rewrite <- H26. auto.
  rewrite actxtsubst_expr in H24. inversion~ H24.
  rewrite actxsubst_pi in H5. inversion H5. repeat rewrite <- H26. auto.
  lets: confluence_cplt3 H6 H23 H7 H11. exact H4.
  inversion~ H4. subst. clear H5.

  clear IHAUnify H15 H21 H16 H17.
  assert (ACtxTSubst H1 (t2 @@' AE_FVar y) =
          ACtxTSubst (H1 & y ~ AC_Var) (ACtxTSubst H1 (t2 @@' AE_FVar y))).
  rewrite actxtsubst_expr in *.
  inversion H25; subst. clear H25.
  rewrite actxsubst_pi in H5. inversion H5. clear H15. repeat rewrite <- H16.
  rewrite tsubst_add_var. rewrite ctxtsubst_twice; auto.
  assert(ACtxTSubst H1 (t4 @@' AE_FVar y) =
         ACtxTSubst (H1 & y ~ AC_Var) (ACtxTSubst H1 (t4 @@' AE_FVar y))).
  rewrite actxtsubst_expr in *.
  inversion H24; subst. clear H24.
  rewrite actxsubst_pi in H15. inversion H15. clear H16. repeat rewrite <- H17.
  rewrite tsubst_add_var. rewrite ctxtsubst_twice; auto.

  lets: H3 notinl H4 H5.
  clear H3 H4 H5 H24 H25.
  assert (ExtCtx (H & y ~ AC_Var) (I & y ~ AC_Var)). apply~ ExtCtx_Var. apply~ AWf_Var. lets: awf_preservation H23; auto.
  assert (CompleteCtx (I & y ~ AC_Var)) by apply~ complete_add.
  assert (ACpltCtxSubstCtx (I & y ~ AC_Var) (H & y ~ AC_Var) H') by apply~ ACpltCtxSubstCtx_Var.
  lets: H15 H19 H3 H4 H5.
  rewrite <- tsubst_add_var with (x:=y). apply~ ctxsubst_awterm.
  assert (ExtCtx (G & y ~ AC_Var) (H1 & y ~ AC_Var)). apply~ ExtCtx_Var.
  lets: extension_weakening_awtermt H14 H16; auto.
  rewrite <- tsubst_add_var with (x:=y). apply~ ctxsubst_awterm.
  assert (ExtCtx (G & y ~ AC_Var) (H1 & y ~ AC_Var)). apply~ ExtCtx_Var.
  lets: extension_weakening_awtermt H18 H16; auto.
  clear H15.

  assert(ACpltCtxSubst (I & y ~ AC_Var) (ACtxTSubst H1 (t4 @@' AE_FVar y)) (d2 ^^' DE_FVar y)).
  rewrite <- tsubst_add_var with (x:=y).
  apply~ acpltctxsubst_subst_invariance.
  apply~ ExtCtx_Var.
  lets: awf_preservation H23; auto.
  apply extension_weakening_awtermt with (G & y ~ AC_Var); auto.
  assert(ACpltCtxSubst (I & y ~ AC_Var) (ACtxTSubst H1 (t2 @@' AE_FVar y)) (d3 ^^' DE_FVar y)).
  rewrite <- tsubst_add_var with (x:=y).
  apply~ acpltctxsubst_subst_invariance.
  apply~ ExtCtx_Var.
  lets: awf_preservation H23; auto.
  apply extension_weakening_awtermt with (G & y ~ AC_Var); auto.
  lets: H16 H15 H17. clear H16 H15 H17.
  apply dopent_var_inj in H21; auto.
  rewrite~ H21.

  (* FORALL *)
  inversions H11. inversions H7.
  inversion H9; subst. inversion H10; subst.
  pick_fresh y.
  assert (notinl: y \notin L) by auto.
  assert (notinl0: y \notin L0) by auto.
  assert (notinl1: y \notin L1) by auto.
  assert (notinl2: y \notin L2) by auto.
  assert (notinl3: y \notin L3) by auto.
  lets: H0 notinl. clear H0.
  assert (wf: AWf(G & y ~ AC_TVar)) by apply~ AWf_TVar.
  lets: unify_extension H7 wf.
  destruct H0 as [? ?].
  lets: H13 notinl1.  clear H13.
  lets: H14 notinl0. clear H14.
  lets: H12 notinl2. clear H12.
  lets: H15 notinl3. clear H15.
  assert((t1 @@#' AT_TFVar y) = ACtxTSubst (G & y ~ AC_TVar) (t1 @@#' AT_TFVar y)).
  rewrite actxtsubst_expr in *.
  inversion H2; subst. clear H2.
  rewrite actxsubst_forall in H17. inversion H17.  clear H17.
  rewrite <- H15. rewrite tsubst_add_tvar. rewrite~ actxtsubst_topen.
  rewrite~ actxtsubst_tfvar_notin. rewrite <- H15. auto.
  assert(t2 @@#' AT_TFVar y = ACtxTSubst (G & y ~ AC_TVar) (t2 @@#' AT_TFVar y)).
  rewrite actxtsubst_expr in *.
  inversion H3; subst. clear H3.
  rewrite actxsubst_forall in H18. inversion H18.  clear H18.
  rewrite <- H17. rewrite tsubst_add_tvar. rewrite~ actxtsubst_topen.
  rewrite~ actxtsubst_tfvar_notin. rewrite <- H17. auto.

  lets: H1 notinl H15 H17 wf.
  clear H1 H15 H17 H2 H3.
  lets: H18 H14 H12. clear H18 H14 H12.
  lets: awf_preservation H4.
  assert (AWf (I & y ~ AC_TVar)) by apply~ AWf_TVar.
  assert(ExtCtx (H & y ~ AC_TVar) (I & y ~ AC_TVar)) by apply~ ExtCtx_TVar.
  assert (CompleteCtx (I & y ~ AC_TVar)) by apply~ complete_add_tvar.
  assert (ACpltCtxSubstCtx (I & y ~ AC_TVar) (H & y ~ AC_TVar) (H' & y ~ DC_TVar)) by apply~ ACpltCtxSubstCtx_TVar.
  lets: H1 H12 H14 H15 H16 H13. clear H1.
  inversion H17. clear H17.
  apply dtopent_var_inj in H18; auto.
  rewrite~ H18.

  (* ANN *)
  lets: unify_extension H0_ H8.
  destruct H11 as [? ?].
  lets: unify_extension H0_0 H11.
  destruct H13 as [? ?].
  lets: extension_transitivity H14 H3.
  inversions H6. inversions H7. inversion H9; subst. inversion H10; subst.
  forwards * : IHAUnify1 H18 H19.
  rewrite actxtsubst_expr. f_equal.
  rewrite actxtsubst_expr in H0. inversion~ H0.
  rewrite actxsubst_ann in H7. inversion H7. rewrite <- H16. auto.
  rewrite actxtsubst_expr. f_equal.
  rewrite actxtsubst_expr in H2. inversion~ H2.
  rewrite actxsubst_ann in H7. inversion H7. rewrite <- H16. auto.
  lets: confluence_cplt3 H3 H15 H4 H5. exact H6.
  inversion~ H6. subst. clear H6.

  clear IHAUnify1 H18 H19 H17 H23 H9 H10.
  assert(ACtxTSubst H1 t3 = ACtxTSubst H1 (ACtxTSubst H1 t3)).
  rewrite~ ctxtsubst_twice.
  assert(ACtxTSubst H1 t4 = ACtxTSubst H1 (ACtxTSubst H1 t4)).
  rewrite~ ctxtsubst_twice.
  lets: IHAUnify2 H6 H7 H11. clear IHAUnify2 H6 H7.
  assert(AWTermT H1 (ACtxTSubst H1 t3)).
  apply~ ctxsubst_awterm.
  lets: extension_weakening_awtermt H20 H12; auto.
  assert(AWTermT H1 (ACtxTSubst H1 t4)).
  apply~ ctxsubst_awterm.
  lets: extension_weakening_awtermt H24 H12; auto.
  lets: H9 H6 H7 H3 H4 H5. clear H9.
  assert (ACpltCtxSubst I (ACtxTSubst H1 t4) d3).
  apply complete_eq with t4; auto.
  apply awf_preservation in H3; auto.
  apply* extension_weakening_awtermt.
  apply substitution_extension_invariance2; auto.
  assert (ACpltCtxSubst I (ACtxTSubst H1 t3) d2).
  apply complete_eq with t3; auto.
  apply awf_preservation in H3; auto.
  apply* extension_weakening_awtermt.
  apply substitution_extension_invariance2; auto.
  lets: H10 H9 H16. inversion~ H17.

  (* EVarTy *)
  lets: awf_preservation H6; auto.
  lets: awf_context H6.
  assert (ACpltCtxSubst I t2 t1').
  apply complete_eq with (AT_EVar a); auto.
  assert (binds a (AC_Solved_EVar t2) (H1 & a ~ AC_Solved_EVar t2 & H2)). apply binds_middle_eq.
  apply awf_is_ok in H14. apply* ok_middle_inv_r.
  lets: awterm_evar_binds H15 H16.
  lets: extension_weakening_awtermt H17 H6; auto.
  rewrite substitution_extension_invariance_left2 with (G:= H1 & a ~ AC_Solved_EVar t2 & H2); auto.
  rewrite substitution_extension_invariance_left2 with (t:=t2) (G:= H1 & a ~ AC_Solved_EVar t2 & H2); auto.
  f_equal.

  rewrite~ actxtsubst_evar.
  rewrite <- concat_assoc.
  rewrite~ actxtsubst_append.
  rewrite concat_assoc. apply awf_is_ok in H14; auto.

  assert (ACpltCtxSubst I t2 t2').
  apply complete_eq with t1; auto.
  assert (binds a (AC_Solved_EVar t2) (H1 & a ~ AC_Solved_EVar t2 & H2)). apply binds_middle_eq.
  apply awf_is_ok in H14. apply* ok_middle_inv_r.
  lets: awterm_evar_binds H15 H17.
  lets: extension_weakening_awtermt H18 H6; auto.
  assert (AWf H1). rewrite <- concat_assoc in H15. apply AWf_left in H15; auto.
  assert (ExtCtx (H1 & a ~ AC_Unsolved_EVar & H2) (H1 & a ~ AC_Solved_EVar t2 & H2)).
  apply~ extension_append. apply~ ExtCtx_Solve.
  apply~ extension_reflexivity.
  apply* AWf_Ctx_Unsolved_EVar.
  apply AWf_left in H15; auto.
  lets: resolve_evar_awf_preservation H0; auto.
  lets: extension_transitivity H18 H6.
  rewrite substitution_extension_invariance_left2 with (G:= H1 & a ~ AC_Unsolved_EVar & H2); auto.
  rewrite substitution_extension_invariance_left2 with (t:=t2) (G:= H1 & a ~ AC_Unsolved_EVar & H2); auto.
  f_equal.
  lets: resolve_evar_invariance H8 H0 H10; auto.

  lets: cplt_ctxsubst_eq H16 H17; auto.

  (* TyEVar *)
  clear H.
  lets: awf_preservation H7; auto.
  lets: awf_context H7.
  assert (ACpltCtxSubst I t2 t2').
  apply complete_eq with (AT_EVar a); auto.
  assert (binds a (AC_Solved_EVar t2) (H1 & a ~ AC_Solved_EVar t2 & H2)). apply binds_middle_eq.
  apply awf_is_ok in H15. apply* ok_middle_inv_r.
  lets: awterm_evar_binds H15 H16.
  lets: extension_weakening_awtermt H17 H7; auto.
  rewrite substitution_extension_invariance_left2 with (G:= H1 & a ~ AC_Solved_EVar t2 & H2); auto.
  rewrite substitution_extension_invariance_left2 with (t:=t2) (G:= H1 & a ~ AC_Solved_EVar t2 & H2); auto.
  f_equal.

  rewrite~ actxtsubst_evar.
  rewrite <- concat_assoc.
  rewrite~ actxtsubst_append.
  rewrite concat_assoc. apply awf_is_ok in H15; auto.

  assert (ACpltCtxSubst I t2 t1').
  apply complete_eq with t1; auto.
  assert (binds a (AC_Solved_EVar t2) (H1 & a ~ AC_Solved_EVar t2 & H2)). apply binds_middle_eq.
  apply awf_is_ok in H15. apply* ok_middle_inv_r.
  lets: awterm_evar_binds H15 H17.
  lets: extension_weakening_awtermt H18 H7; auto.

  assert (AWf H1). rewrite <- concat_assoc in H15. apply AWf_left in H15; auto.
  assert (ExtCtx (H1 & a ~ AC_Unsolved_EVar & H2) (H1 & a ~ AC_Solved_EVar t2 & H2)).
  apply~ extension_append. apply~ ExtCtx_Solve.
  apply~ extension_reflexivity.
  apply* AWf_Ctx_Unsolved_EVar.
  apply AWf_left in H15; auto.
  lets: resolve_evar_awf_preservation H3; auto.
  lets: extension_transitivity H18 H7.
  rewrite substitution_extension_invariance_left2 with (G:= H1 & a ~ AC_Unsolved_EVar & H2); auto.
  rewrite substitution_extension_invariance_left2 with (t:=t2) (G:= H1 & a ~ AC_Unsolved_EVar & H2); auto.
  f_equal.
  lets: resolve_evar_invariance H8 H3 H9. auto.

  lets: cplt_ctxsubst_eq H16 H17; auto.
Qed.
