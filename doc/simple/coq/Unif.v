Require Import CtxExtension.
Require Import LibLN.
Require Import AlgoDef.
Require Import UtilityEnv.
Require Import DeclDef.
Require Import AlgoInfra.
Require Import DeclInfra.
Require Import Subst.
Require Import Exists.
Require Import UtilityMore.
Require Import WeakExtension.
Require Import UtilityAlgo.
Require Import UnifEq.
Require Import AWt.
Require Import SoftExtension.

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

Theorem resolve_evar_invariance_awt: forall G a e t H,
    AWt G ->
    AResolveEVar G a e t H ->
    ACtxTSubst H e = ACtxTSubst H t.
Proof.
  introv wf res.
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
  lets: IHres wf. clear IHres.
  f_equal.
  pick_fresh y.
  assert (y \notin L) by auto.
  lets: H0 H4.
  lets: resolve_evar_awt_preservation res wf.
  assert(AWt (H1 & y ~ AC_Var)) by apply* AWt_Var.
  lets: resolve_evar_sextctx H5 H7.
  apply soft_extension_remove_var in H8.
  rewrite (soft_substitution_extension_invariance_left2) with (G:=H1); auto.
  rewrite (soft_substitution_extension_invariance_left2) with (G:=H1) (t:=t3); auto.
  rewrite~ H3.

  pick_fresh y.
  assert (y \notin L) by auto.
  lets: resolve_evar_awt_preservation res wf.
  assert(AWt (H1 & y ~ AC_Var)) by apply* AWt_Var.

  lets: H2 H4 H6.
  repeat rewrite tsubst_add_var in H7.
  lets: H0 H4. clear H0.
  lets: resolve_evar_sextctx H8 H6.
  apply soft_extension_remove_var in H0.
  rewrite <- soft_substitution_extension_invariance_left2 in H7; auto.
  lets: resolve_evar_awt_preservation H8 H6.
  apply awt_left in H9.
  do 2 rewrite actxtsubst_open_awt in H7; auto.
  rewrite actxsubst_fvar in H7.
  apply atopen_var_inj in H7; auto.

  apply* notin_actxtsubst_awt.
  apply* notin_actxtsubst_awt.

  (* APP *)
  repeat rewrite actxtsubst_expr. f_equal.
  repeat rewrite actxsubst_app.
  f_equal.
  lets: IHres1 wf.
  repeat rewrite actxtsubst_expr in H0. inversion H0; subst.
  lets: resolve_evar_awt_preservation res1 wf.
  lets: resolve_evar_sextctx res2 H2.
  rewrite (soft_substitution_extension_invariance_left) with (G:=H1); auto.
  rewrite (soft_substitution_extension_invariance_left) with (G:=H1) (t:=d1); auto.
  rewrite~ H3.

  lets: resolve_evar_awt_preservation res1 wf.
  lets: IHres2 H0.
  lets: resolve_evar_sextctx res2 H0.
  rewrite <- soft_substitution_extension_invariance_left2 in H2; auto.
  repeat rewrite actxtsubst_expr in H2. inversion~ H2.

  (* LAM *)
  repeat rewrite actxtsubst_expr. f_equal.
  repeat rewrite actxsubst_lam. f_equal.
  pick_fresh y.
  assert (notinl: y \notin L) by auto.
  lets: H0 notinl; clear H0.
  lets: H1 notinl; clear H1.
  repeat rewrite tsubst_add_var in H0.
  assert (AWt (G & y ~ AC_Var)) by apply* AWt_Var.
  lets: H0 H1. clear H0.

  do 2 rewrite actxtsubst_expr in H3. inversion~ H3. clear H3.
  lets: resolve_evar_awt_preservation H2 H1.
  apply awt_left in H0.
  do 2 rewrite actxsubst_open_awt in H4; auto.
  rewrite actxsubst_fvar in H4.
  apply aopen_var_inj in H4; auto.

  apply* notin_actxsubst_awt.
  apply* notin_actxsubst_awt.

  (* CASTUP *)
  repeat rewrite actxtsubst_expr. f_equal.
  repeat rewrite actxsubst_castup. f_equal.
  lets: IHres wf.
  repeat rewrite actxtsubst_expr in H0. inversion H0. auto.

  (* CASTDN *)
  repeat rewrite actxtsubst_expr. f_equal.
  repeat rewrite actxsubst_castdn. f_equal.
  lets: IHres wf.
  repeat rewrite actxtsubst_expr in H0. inversion H0. auto.

  (* ANN *)
  repeat rewrite actxtsubst_expr. f_equal.
  repeat rewrite actxsubst_ann.
  f_equal.
  lets: IHres1 wf.
  repeat rewrite actxtsubst_expr in H0. inversion H0; subst.
  lets: resolve_evar_awt_preservation res1 wf.
  lets: resolve_evar_sextctx res2 H2.
  rewrite (soft_substitution_extension_invariance_left) with (G:=H1); auto.
  rewrite (soft_substitution_extension_invariance_left) with (G:=H1) (t:=d1); auto.
  rewrite~ H3.

  lets: resolve_evar_awt_preservation res1 wf.
  lets: resolve_evar_sextctx res1 wf; auto.
  lets: IHres2 H0.
  lets: resolve_evar_sextctx res2 H0.
  rewrite <- soft_substitution_extension_invariance_left2 in H3; auto.
Qed.

Theorem resolve_evar_invariance: forall G a e t H,
    AWf G ->
    AResolveEVar G a e t H ->
    ACtxTSubst H e = ACtxTSubst H t.
Proof.
  intros.
  lets: awf_is_awt H0.
  apply* resolve_evar_invariance_awt.
Qed.

Theorem unify_invariance: forall G e t H,
    AWt G ->
    AUnify G e t H ->
    ACtxTSubst G e = e ->
    ACtxTSubst G t = t ->
    ACtxTSubst H e = ACtxTSubst H t.
Proof.
  introv wt uni sub1 sub2.
  induction uni; auto.

  (* APP *)
  repeat rewrite actxtsubst_expr in *. f_equal.
  repeat rewrite actxsubst_app in *. f_equal.
  forwards * : IHuni1 wt. f_equal~.
  inversion~ sub1. repeat rewrite~  H2.
  inversion~ sub2. repeat rewrite~  H2. inversion H0.
  assert (SExtCtx H1 H).
  lets: unify_awt_preservation uni1 wt.
  lets: unify_sextctx uni2 H2. auto.
  rewrite soft_substitution_extension_invariance_left with (G:= H1); auto. rewrite H3.
  rewrite <- soft_substitution_extension_invariance_left with (G:= H1); auto.

  lets: unify_awt_preservation uni1 wt.
  lets: unify_sextctx uni2 H0.
  forwards * : IHuni2 H0.
  rewrite~ ctxsubst_twice_awt.
  rewrite~ ctxsubst_twice_awt.
  inversion~ H3.
  rewrite <- soft_substitution_extension_invariance_left with (G:= H1) in H5; auto.
  rewrite <- soft_substitution_extension_invariance_left with (G:= H1) in H5; auto.

  (* LAM *)
  pick_fresh y.
  assert (y \notin L). auto.
  assert (AWt (G & y ~ AC_Var)) by constructor~.
  forwards * :  H1 H2 H3.
  rewrite actxtsubst_expr in *. rewrite actxsubst_lam in sub1. inversion sub1. f_equal.
  rewrite subst_add_var.
  rewrite~ actxsubst_open_awt.
  rewrite~ actxsubst_fvar.
  rewrite~ ctxsubst_twice_awt.
  rewrite actxtsubst_expr in *. rewrite actxsubst_lam in sub2. inversion sub2. f_equal.
  rewrite subst_add_var.
  rewrite~ actxsubst_open_awt.
  rewrite~ actxsubst_fvar.
  rewrite~ ctxsubst_twice_awt.

  repeat rewrite tsubst_add_var in H4.
  repeat rewrite actxtsubst_expr in *. f_equal.
  inversion H4.
  lets: H0 H2. clear H0.
  lets: unify_awt_preservation H5 H3.
  lets: awt_left H0.
  do 2 rewrite actxsubst_open_awt in H6; auto.
  rewrite actxsubst_fvar in H6.
  do 2 rewrite actxsubst_lam.  f_equal.
  apply aopen_var_inj in H6; auto.
  apply* notin_actxsubst_awt.
  apply* notin_actxsubst_awt.

  (* CASTUP *)
  repeat rewrite actxtsubst_expr in *.
  repeat rewrite actxsubst_castup in *. f_equal. f_equal.
  forwards * : IHuni wt.
  f_equal. inversion~ sub1. rewrite~ H1.
  f_equal. inversion~ sub2. rewrite~ H1.
  inversion~ H0.

  (* CASTDN *)
  repeat rewrite actxtsubst_expr in *.
  repeat rewrite actxsubst_castdn in *. f_equal. f_equal.
  forwards * : IHuni wt.
  f_equal. inversion~ sub1. rewrite~ H1.
  f_equal. inversion~ sub2. rewrite~ H1.
  inversion~ H0.

  (* PI *)
  pick_fresh y.
  assert (y \notin L) by auto.
  lets: H0 H3. clear H0.
  lets: unify_awt_preservation uni wt.
  assert (AWt (H1 & y ~ AC_Var)) by constructor~.
  forwards * :  H2 H3 H5.
  rewrite tsubst_add_var.
  rewrite~ ctxtsubst_twice_awt.
  rewrite tsubst_add_var.
  rewrite~ ctxtsubst_twice_awt.
  clear H2.
  forwards * :  IHuni wt.
  rewrite actxtsubst_expr in sub1.
  rewrite actxsubst_pi in sub1.
  inversion sub1. rewrite~ H7.
  rewrite actxtsubst_expr in sub2.
  rewrite actxsubst_pi in sub2.
  inversion sub2. rewrite~ H7.
  clear IHuni.

  lets: unify_sextctx H4 H5.
  lets: soft_extension_remove_var H7.
  repeat rewrite actxtsubst_expr in *.
  repeat rewrite actxsubst_pi. f_equal. f_equal.
  rewrite soft_substitution_extension_invariance_left2 with (G:= H1); auto. rewrite H2.
  rewrite <- soft_substitution_extension_invariance_left2 with (G:= H1); auto.

  repeat rewrite tsubst_add_var in H6.
  rewrite <- soft_substitution_extension_invariance_left2 with (G:= H1) in H6; auto.
  rewrite <- soft_substitution_extension_invariance_left2 with (G:= H1) in H6; auto.
  lets: unify_awt_preservation H4 H5.
  lets: awt_left H9.
  do 2 rewrite actxtsubst_open_awt in H6; auto.
  rewrite actxsubst_fvar in H6.
  apply atopen_var_inj in H6; auto.
  apply* notin_actxtsubst_awt.
  apply* notin_actxtsubst_awt.

  (* FORALL *)
  pick_fresh y.
  assert (y \notin L). auto.
  assert (AWt (G & y ~ AC_TVar)) by constructor~.
  forwards * : H1 H2 H3.
  rewrite tsubst_add_tvar.
  rewrite actxtsubst_expr in sub1.
  rewrite actxsubst_forall in sub1.
  inversion~ sub1. rewrite H5.
  rewrite~ actxtsubst_topen_awt.
  rewrite~ actxtsubst_tfvar_notin.
  rewrite~ H5.
  rewrite tsubst_add_tvar.
  rewrite actxtsubst_expr in sub2.
  rewrite actxsubst_forall in sub2.
  inversion~ sub2. rewrite H5.
  rewrite~ actxtsubst_topen_awt.
  rewrite~ actxtsubst_tfvar_notin.
  rewrite~ H5.

  repeat rewrite tsubst_add_tvar in H4.
  repeat rewrite actxtsubst_expr in *. f_equal.
  lets: H0 H2. clear H0.
  lets: unify_awt_preservation H5 H3.
  lets: awt_left H0.
  do 2 rewrite actxtsubst_topen_awt in H4; auto.
  rewrite actxtsubst_tfvar_notin in H4; auto.
  do 2 rewrite actxsubst_forall.  f_equal.
  apply atopen_tvar_inj in H4; auto.
  apply* notin_actxtsubst_awt.
  apply* notin_actxtsubst_awt.

  (* ANN *)
  repeat rewrite actxtsubst_expr. f_equal.
  repeat rewrite actxsubst_ann. f_equal.
  forwards * : IHuni1 wt.
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_ann in sub1.
  inversion sub1. f_equal.
  rewrite~ H2.

  rewrite actxtsubst_expr in *.
  rewrite actxsubst_ann in sub2.
  inversion sub2. f_equal.
  rewrite~ H2.

  repeat rewrite actxtsubst_expr in H0. inversion~ H0.
  assert (SExtCtx H1 H).
  lets: unify_awt_preservation uni1 wt.
  lets: unify_sextctx uni2 H2. auto.
  rewrite soft_substitution_extension_invariance_left with (G:= H1); auto. rewrite H3.
  rewrite <- soft_substitution_extension_invariance_left with (G:= H1); auto.

  lets: unify_awt_preservation uni1 wt.
  lets: unify_sextctx uni2 H0.
  forwards * : IHuni2 H0.
  rewrite~ ctxtsubst_twice_awt.
  rewrite~ ctxtsubst_twice_awt.
  rewrite <- soft_substitution_extension_invariance_left2 with (G:= H1) in H3; auto.
  rewrite <- soft_substitution_extension_invariance_left2 with (G:= H1) in H3; auto.

  (* RESOLVE EVAR L *)
  lets: resolve_evar_invariance_awt wt H0.
  lets: resolve_evar_awt_preservation H0 wt.
  lets: awt_is_ok wt.
  lets: awt_is_ok H5.

  rewrite~ actxtsubst_evar.
  rewrite <- actxtsubst_append with (H:=a ~ AC_Solved_EVar t2 & H2); auto.
  rewrite concat_assoc.
  rewrite tsubst_add_ctx. rewrite tsubst_add_solved_evar.
  rewrite tsubst_add_ctx. rewrite tsubst_add_solved_evar.
  rewrite~ distributivity_ctxtsubst_tsubstt_awt.
  rewrite~ distributivity_ctxtsubst_tsubstt_awt.

  rewrite tsubst_add_ctx in H4; auto.
  rewrite tsubst_add_evar in H4.
  rewrite tsubst_add_ctx in H4; auto.
  rewrite tsubst_add_evar in H4.
  rewrite~ H4.
  do 2 apply awt_left in H5. auto.
  destruct (ok_middle_inv H7). auto.
  do 2 apply awt_left in H5. auto.
  destruct (ok_middle_inv H7). auto.
  rewrite~ concat_assoc.
  apply* ok_middle_change.
  apply* ok_middle_change.

  (* RESOLVE EVAR R *)
  lets: resolve_evar_invariance_awt wt H3.
  lets: resolve_evar_awt_preservation H3 wt.
  lets: awt_is_ok wt.
  lets: awt_is_ok H6.

  rewrite~ actxtsubst_evar.
  pattern (ACtxTSubst H1 t2) at 1 ; rewrite <- actxtsubst_append with (H:=a ~ AC_Solved_EVar t2 & H2); auto.
  rewrite concat_assoc.
  rewrite tsubst_add_ctx. rewrite tsubst_add_solved_evar.
  rewrite tsubst_add_ctx. rewrite tsubst_add_solved_evar.
  rewrite~ distributivity_ctxtsubst_tsubstt_awt.
  rewrite~ distributivity_ctxtsubst_tsubstt_awt.

  rewrite tsubst_add_ctx in H5; auto.
  rewrite tsubst_add_evar in H5.
  rewrite tsubst_add_ctx in H5; auto.
  rewrite tsubst_add_evar in H5.
  rewrite~ H5.
  do 2 apply awt_left in H6. auto.
  destruct (ok_middle_inv H8). auto.
  do 2 apply awt_left in H6. auto.
  destruct (ok_middle_inv H8). auto.
  rewrite~ concat_assoc.
  apply* ok_middle_change.
  apply* ok_middle_change.
Qed.

Inductive SubTTerm: AType -> AType -> Prop :=
| STT_App1: forall t e1 e2,
    SubTTerm t (AT_Expr e1) -> SubTTerm t (AT_Expr (AE_App e1 e2))
| STT_App2: forall t e1 e2,
    SubTTerm t (AT_Expr e2) -> SubTTerm t (AT_Expr (AE_App e1 e2))
| STT_Lam: forall t L e,
    (forall x, x \notin L -> SubTTerm  (t @' x) (AT_Expr (e @ x))) ->
    SubTTerm t (AT_Expr (AE_Lam e))
| STT_Pi1: forall t e1 e2,
    SubTTerm t e1 -> SubTTerm t (AT_Expr (AE_Pi e1 e2))
| STT_Pi2: forall t e1 e2 L,
    (forall x, x \notin L -> SubTTerm (t @' x) (e2 @' x)) ->
    SubTTerm t (AT_Expr (AE_Pi e1 e2)).

Lemma atunify_awf: forall G H1 H2 I t d e,
    AWfTyp G e ->
    SubTTerm t e ->
    ExtCtx G H1 ->
    AWf (H1 & I) ->
    AUnify (H1 & I) t d (H2 & I) ->
    t = ACtxTSubst G t ->
    d = ACtxTSubst G d ->
    AWf (H1 & I) /\ ExtCtx (H1 & I) (H2 & I).
Proof.
  introv wt sub ex wf uni sub_t sub_d.
  gen_eq M1: (H1 & I).
  gen_eq M2: (H2 & I). gen H1 H2 I.
  induction uni; introv ex m2info m1info; try(subst).
   admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
   admit.
  gen_eq M1: (H1 & I).

with atunify_awf_expr: forall G t d H,
    ATUnify UExpr G t d H ->
    AWf G ->
    t = ACtxTSubst G t ->
    d = ACtxTSubst G d ->
    AWf H /\ ExtCtx G H.

Theorem unify_extension: forall G s t H,
    AUnify G s t H ->
    AWf G ->
    t = ACtxTSubst G t ->
    s = ACtxTSubst G s ->
    AWfTyp G t -> AWfTyp G s ->
    AWf H /\ ExtCtx G H.
Proof.
Admitted.

Theorem unify_extension_expr: forall G s t H,
    AUnify G (AT_Expr s) (AT_Expr t) H ->
    AWf G ->
    t = ACtxSubst G t ->
    s = ACtxSubst G s ->
    AWfTyping G (AT_Expr t) -> AWfTyping G (AT_Expr s) ->
    AWf H /\ ExtCtx G H.
Proof.
  intros.
  lets: aunify_is_atunify H0.
  lets: awf_is_ok H1. auto.
  inversion H6.
  apply* atunify_awf_expr.
  rewrite actxtsubst_expr. f_equal ~.
  rewrite actxtsubst_expr. f_equal ~.
Qed.

Theorem unif_soundness_same' : forall G H I t1 t2 H' t1' t2',
    AUnify2 G t1 t2 H ->
    t1 = ACtxTSubst G t1 ->
    t2 = ACtxTSubst G t2 ->
    ExtCtx H I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I H H' ->
    ACpltCtxSubst I t1 t1' ->
    ACpltCtxSubst I t2 t2' ->
    AWf G -> AWTermT G t1 -> AWTermT G t2 ->
    AWfTyping G t1 ->
    AWfTyping G t2 ->
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
  inversion H11. clear H13 H14 H15.
  inversion H12. clear H13 H14 H15.
  assert (H0_':AUnify G (AT_Expr t1) (AT_Expr t2) H1). apply* aunify2_is_aunify.
  lets: unify_extension_expr H0_' H8 H18 H16.
  rewrite actxtsubst_expr in H2. rewrite actxsubst_app in H2. inversion~ H2. rewrite~ <- H14.
  rewrite actxtsubst_expr in H0. rewrite actxsubst_app in H0. inversion~ H0. rewrite~ <- H14.
  destruct H13 as [? ?].
  assert (H0_0': AUnify H1 (AT_Expr (ACtxSubst H1 t3)) (AT_Expr (ACtxSubst H1 t4)) H). apply* aunify2_is_aunify.

  lets: unify_extension_expr H0_0' H13.
  destruct H15 as [? ?].
  rewrite~ ctxsubst_twice. rewrite~ ctxsubst_twice.
  rewrite <- actxtsubst_expr. apply~ awftyping_subst.
  lets: extension_weakening_awftyping H19 H14. auto.
  rewrite <- actxtsubst_expr. apply~ awftyping_subst.
  lets: extension_weakening_awftyping H17 H14. auto.

  lets: extension_transitivity H20 H3.
  inversions H6. inversions H7. inversion H9; subst. inversion H10; subst.
  forwards * : IHAUnify2_1 H23 H29 H4.
  rewrite actxtsubst_expr. f_equal.
  rewrite actxtsubst_expr in H0. rewrite actxsubst_app in H0. inversion H0. rewrite <- H7. auto.
  rewrite actxtsubst_expr in H2. rewrite actxsubst_app in H2. inversion H2. rewrite <- H7. rewrite actxtsubst_expr. f_equal~.

  lets: confluence_cplt3 H3 H21 H4 H5. exact H6.
  inversion~ H6. subst. clear H6.

  clear IHAUnify2_1 H16 H18 H23 H29 H0_ H0_' H24 H25.
  assert(AT_Expr (ACtxSubst H1 t3) = ACtxTSubst H1 (AT_Expr (ACtxSubst H1 t3))).
  rewrite actxtsubst_expr. f_equal. rewrite~ ctxsubst_twice.
  assert(AT_Expr (ACtxSubst H1 t4) = ACtxTSubst H1 (AT_Expr (ACtxSubst H1 t4))).
  rewrite actxtsubst_expr. f_equal. rewrite~ ctxsubst_twice.
  lets: IHAUnify2_2 H6 H7 H13. clear IHAUnify2_2 H6 H7.
  assert(AWTermT H1 (AT_Expr (ACtxSubst H1 t3))).
  rewrite <- actxtsubst_expr. apply~ ctxsubst_awterm.
  lets: extension_weakening_awtermt H26 H14; auto.
  assert(AWTermT H1 (AT_Expr (ACtxSubst H1 t4))).
  rewrite <- actxtsubst_expr. apply~ ctxsubst_awterm.
  lets: extension_weakening_awtermt H30 H14; auto.
  lets: H16 H6 H7 H3 H4 H5.
  rewrite <- actxtsubst_expr. apply~ awftyping_subst.
  lets: extension_weakening_awftyping H17 H14. auto.
  rewrite <- actxtsubst_expr. apply~ awftyping_subst.
  lets: extension_weakening_awftyping H19 H14. auto.

  clear H16.
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
  lets: H18 H16 H22. inversion~ H23.

  (* LAM *)
  inversion H7. clear H14 H15 H17.
  inversion H13. clear H14 H15 H18.
  inversion H11. clear H14 H15.
  inversion H12. clear H14 H15.
  inversion H9; subst. inversion H10; subst.
  pick_fresh y.
  assert (notinl: y \notin L) by auto.
  assert (notinl0: y \notin L0) by auto.
  assert (notinl1: y \notin L1) by auto.
  assert (notinl2: y \notin L2) by auto.
  assert (notinl3: y \notin L3) by auto.
  assert (notinl4: y \notin L4) by auto.
  assert (notinl5: y \notin L5) by auto.
  lets: H0 notinl. clear H0.
  assert (wf: AWf(G & y ~ AC_Var)) by apply~ AWf_Var.
  lets: H16 notinl0. clear H16.
  lets: H17 notinl1.  clear H17.
  lets: H18 notinl2. clear H18.
  lets: H19 notinl3. clear H19.
  lets: H20 notinl4. clear H20.
  lets: H21 notinl5. clear H21.

  assert(AT_Expr (t1 @@ AE_FVar y) = ACtxTSubst (G & y ~ AC_Var) (AT_Expr (t1 @@ AE_FVar y))).
  rewrite actxtsubst_expr in *. f_equal.
  inversion H2; subst. clear H2.
  rewrite actxsubst_lam in H21. inversion H21.  clear H21.
  rewrite <- H20. rewrite subst_add_var. rewrite~ actxsubst_open.
  rewrite actxsubst_fvar. rewrite <- H20. auto.
  assert(AT_Expr (t2 @@ AE_FVar y) = ACtxTSubst (G & y ~ AC_Var) (AT_Expr (t2 @@ AE_FVar y))).
  rewrite actxtsubst_expr in *. f_equal.
  inversion H3; subst. clear H3.
  rewrite actxsubst_lam in H22. inversion H22.  clear H22.
  rewrite <- H21. rewrite subst_add_var. rewrite~ actxsubst_open.
  rewrite actxsubst_fvar. rewrite <- H21. auto.

  assert (H14':AUnify (G & y ~ AC_Var) (AT_Expr (t1 @@ AE_FVar y))
                      (AT_Expr (t2 @@ AE_FVar y)) (H & y ~ AC_Var)).
  apply* aunify2_is_aunify.
  lets: unify_extension_expr H14' wf H17 H16.
  rewrite actxtsubst_expr in H21. inversion~ H21.
  rewrite actxtsubst_expr in H20. inversion~ H20.

  destruct H22 as [? ?].

  lets: H1 notinl H20 H21 wf.
  clear H1 H20 H21 H2 H3.
  lets: H24 H18 H19 H16 H17. clear H24 H16 H17 H18 H19.
  lets: awf_preservation H4.
  assert (AWf (I & y ~ AC_Var)) by apply~ AWf_Var.
  assert(ExtCtx (H & y ~ AC_Var) (I & y ~ AC_Var)) by apply~ ExtCtx_Var.
  assert (CompleteCtx (I & y ~ AC_Var)) by apply~ complete_add.
  assert (ACpltCtxSubstCtx (I & y ~ AC_Var) (H & y ~ AC_Var) H') by apply~ ACpltCtxSubstCtx_Var.
  lets: H1 H16 H17 H18 H0 H15; auto.
  clear H1.
  inversion H19. clear H19.
  apply dopen_var_inj in H20; auto.
  rewrite~ H20.

  (* CASTUP *)
  inversions H6. inversions H7. inversion H9; subst. inversion H10; subst.
  forwards * : IHAUnify2 H13 H16.
  rewrite actxtsubst_expr. f_equal.
  rewrite actxtsubst_expr in H1. inversion~ H1.
  rewrite actxsubst_castup in H7. inversion H7. rewrite <- H17. auto.
  rewrite actxtsubst_expr. f_equal.
  rewrite actxtsubst_expr in H2. inversion~ H2.
  rewrite actxsubst_castup in H7. inversion H7. rewrite <- H17. auto.
  inversion H11; auto.
  inversion H12; auto.
  inversion~ H6.

  (* CASTDN *)
  inversions H6. inversions H7. inversion H9; subst. inversion H10; subst.
  forwards * : IHAUnify2 H13 H16.
  rewrite actxtsubst_expr. f_equal.
  rewrite actxtsubst_expr in H1. inversion~ H1.
  rewrite actxsubst_castdn in H7. inversion H7. rewrite <- H17. auto.
  rewrite actxtsubst_expr. f_equal.
  rewrite actxtsubst_expr in H2. inversion~ H2.
  rewrite actxsubst_castdn in H7. inversion H7. rewrite <- H17. auto.
  inversion H11; auto.
  inversion H12; auto.
  inversion~ H6.

  (* PI *)
  inversions H14. inversions H15. inversion H9; subst. inversion H10; subst.
  clear H9 H10. inversion H11; subst. inversion H12; subst.
  pick_fresh y.
  assert(notinl: y \notin L) by auto.
  assert(notinl0: y \notin L0) by auto.
  assert(notinl1: y \notin L1) by auto.
  assert(notinl2: y \notin L2) by auto.
  assert(notinl3: y \notin L3) by auto.
  assert(notinl4: y \notin L4) by auto.
  assert(notinl5: y \notin L5) by auto.
  assert (H0' : AUnify G t1 t3 H1). apply* aunify2_is_aunify.
  lets: unify_extension H0' H8 H25 H15.
  rewrite actxtsubst_expr in H5. rewrite actxsubst_pi in H5. inversion H5. rewrite <- H10. auto.
  rewrite actxtsubst_expr in H4. rewrite actxsubst_pi in H4. inversion H4. rewrite <- H10. auto.
  destruct H9 as [? ?].
  lets: H2 notinl. clear H2.
  lets: H21 notinl0. clear H21.
  lets: H22 notinl1. clear H22.
  lets: H20 notinl2. clear H20.
  lets: H24 notinl3. clear H24.
  lets: H16 notinl4. clear H16.
  lets: H26 notinl5. clear H26.
  assert(AWf (H1 & y ~ AC_Typ t1)). apply~ AWf_TyVar.
  lets: extension_weakening_awftyp H15 H10. auto.
  assert (H14' : AUnify (H1 & y ~ AC_Typ t1) (ACtxTSubst H1 (t2 @@' AE_FVar y))
                         (ACtxTSubst H1 (t4 @@' AE_FVar y)) (H & y ~ AC_Typ t1)).
  apply* aunify2_is_aunify.
  lets: unify_extension H14' H26.
  destruct H27 as [? ?].
  rewrite tsubst_add_typvar. rewrite~ ctxtsubst_twice.
  rewrite tsubst_add_typvar. rewrite~ ctxtsubst_twice.
  rewrite <- tsubst_add_typvar with (x:=y) (t:=t1).
  apply -> awftyp_subst.
  pattern(H1 & y ~ AC_Typ t1) at 1; rewrite <- concat_empty_r.
  apply awftyp_middle_change_typvar with t3.
  rewrite concat_empty_r.
  assert (ExtCtx (G & y ~ AC_Typ t3) (H1 & y ~ AC_Typ t3)).
  apply~ ExtCtx_TypVar.
  apply~ AWf_TyVar.
  lets: extension_weakening_awftyp H25 H10. auto.
  lets: extension_weakening_awftyp H16 H27. auto.
  symmetry.
  apply unify_invariance with G; auto. apply* awf_is_awt.
  rewrite actxtsubst_expr in H4. rewrite actxsubst_pi in H4. inversion H4. rewrite~ <- H28.
  rewrite actxtsubst_expr in H5. rewrite actxsubst_pi in H5. inversion H5. rewrite~ <- H28.

  rewrite <- tsubst_add_typvar with (x:=y) (t:=t1).
  apply -> awftyp_subst.
  pattern(H1 & y ~ AC_Typ t1) at 1; rewrite <- concat_empty_r.
  rewrite concat_empty_r.
  assert (ExtCtx (G & y ~ AC_Typ t1) (H1 & y ~ AC_Typ t1)).
  apply~ ExtCtx_TypVar.
  lets: extension_weakening_awftyp H24 H27. auto.

  apply extctx_remove_typvar in H28.
  lets: extension_transitivity H28 H6.
  inversions H4. inversions H5.
  forwards * : IHAUnify2 H23.
  rewrite actxtsubst_expr in H31. inversion~ H31.
  rewrite actxsubst_pi in H5. inversion H5. rewrite <- H32. auto.
  rewrite actxtsubst_expr in H30. inversion~ H30.
  rewrite actxsubst_pi in H5. inversion H5. repeat rewrite <- H32. auto.
  lets: awftyp_is_awftyping H15. auto.
  lets: awftyp_is_awftyping H25. auto.

  lets: confluence_cplt3 H6 H29 H7 H13. exact H4.
  inversion~ H4. subst. clear H5.

  clear IHAUnify2.
  assert (ACtxTSubst H1 (t2 @@' AE_FVar y) =
          ACtxTSubst (H1 & y ~ AC_Typ t1) (ACtxTSubst H1 (t2 @@' AE_FVar y))).
  rewrite actxtsubst_expr in *.
  inversion H31; subst. clear H31.
  rewrite actxsubst_pi in H5. inversion H5. repeat rewrite <- H32.
  rewrite tsubst_add_typvar. rewrite ctxtsubst_twice; auto.
  assert(ACtxTSubst H1 (t4 @@' AE_FVar y) =
         ACtxTSubst (H1 & y ~ AC_Typ t1) (ACtxTSubst H1 (t4 @@' AE_FVar y))).
  rewrite actxtsubst_expr in *.
  inversion H30; subst.
  rewrite actxsubst_pi in H32. inversion H32. repeat rewrite <- H33.
  rewrite tsubst_add_typvar. rewrite ctxtsubst_twice; auto.

  lets: H3 notinl H4 H5.
  clear H3 H4 H5.
  assert (ExtCtx (H & y ~ AC_Typ t1) (I & y ~ AC_Typ t1)). apply~ ExtCtx_TypVar. apply~ AWf_TyVar. lets: awf_preservation H29; auto.
  lets: extension_transitivity H10 H29.
  lets: extension_weakening_awftyp H15 H3. auto.
  assert (CompleteCtx (I & y ~ AC_Typ t1)) by apply~ complete_add_typ.
  assert (exists t1', ACpltCtxSubst I t1 t1'). apply* cpltctxsubst_exists.
  lets: awf_preservation H29; auto.
  lets: extension_transitivity H10 H29.
  lets: extension_weakening_awftyp H15 H5. apply* awtermt_awftyp.
  destruct H5 as (t1' & cpltsubst).
  assert (ACpltCtxSubstCtx (I & y ~ AC_Typ t1) (H & y ~ AC_Typ t1) (H' & y ~ DC_Typ t1')). apply~ ACpltCtxSubstCtx_TypVar.
  lets: H32 H26 H3 H4 H5.
  rewrite <- tsubst_add_typvar with (x:=y) (t:=t1). apply~ ctxsubst_awterm.
  assert (ExtCtx (G & y ~ AC_Typ t1) (H1 & y ~ AC_Typ t1)). apply~ ExtCtx_TypVar.
  lets: awtermt_awftyp H24.
  lets: extension_weakening_awtermt H34 H33; auto.
  rewrite <- tsubst_add_typvar with (x:=y) (t:=t1). apply~ ctxsubst_awterm.
  pattern (H1 & y ~ AC_Typ t1) at 1; rewrite <- concat_empty_r.
  apply~ awtermt_replace2.
  rewrite~ concat_empty_r.
  assert (ExtCtx (G & y ~ AC_Var) (H1 & y ~ AC_Var)). apply~ ExtCtx_Var.
  lets: extension_weakening_awtermt H20 H33. auto.
  rewrite <- tsubst_add_typvar with (x:=y) (t:=t1).
  apply~ awftyping_subst.
  apply awftyp_is_awftyping.
  assert (ExtCtx (G & y ~ AC_Typ t1) (H1 & y ~ AC_Typ t1)). apply~ ExtCtx_TypVar.
  lets: extension_weakening_awftyp H24 H33. auto.
  rewrite <- tsubst_add_typvar with (x:=y) (t:=t1).
  apply~ awftyping_subst.
  apply awftyp_is_awftyping.
  pattern(H1 & y ~ AC_Typ t1) at 1; rewrite <- concat_empty_r.
  apply awftyp_middle_change_typvar with t3.
  rewrite concat_empty_r.
  assert (ExtCtx (G & y ~ AC_Typ t3) (H1 & y ~ AC_Typ t3)).
  apply~ ExtCtx_TypVar.
  apply~ AWf_TyVar.
  lets: extension_weakening_awftyp H25 H10. auto.
  lets: extension_weakening_awftyp H16 H33. auto.
  symmetry.
  apply unify_invariance with G; auto. apply* awf_is_awt.
  rewrite actxtsubst_expr in H31. rewrite actxsubst_pi in H31. inversion H31. rewrite~ <- H34.
  rewrite actxtsubst_expr in H30. rewrite actxsubst_pi in H30. inversion H30. rewrite~ <- H34.

  assert(ACpltCtxSubst (I & y ~ AC_Typ t1) (ACtxTSubst H1 (t4 @@' AE_FVar y)) (d2 ^^' DE_FVar y)).
  rewrite <- tsubst_add_typvar with (x:=y) (t:=t1).
  apply~ acpltctxsubst_subst_invariance.
  apply~ ExtCtx_TypVar.
  lets: awf_preservation H3; auto.
  apply extension_weakening_awtermt with (G & y ~ AC_Typ t1); auto.
  pattern (G & y ~ AC_Typ t1) at 1; rewrite <- concat_empty_r.
  apply awtermt_replace2.
  rewrite~ concat_empty_r.
  lets: cplt_ctxsubst_replace' H2; auto. apply~ ok_push.
  lets: ok_preservation H29. auto.
  exact H34.
  assert(ACpltCtxSubst (I & y ~ AC_Typ t1) (ACtxTSubst H1 (t2 @@' AE_FVar y)) (d3 ^^' DE_FVar y)).
  rewrite <- tsubst_add_typvar with (x:=y) (t:=t1).
  apply~ acpltctxsubst_subst_invariance.
  apply~ ExtCtx_TypVar.
  lets: awf_preservation H3; auto.
  apply extension_weakening_awtermt with (G & y ~ AC_Typ t1); auto.
  pattern (G & y ~ AC_Typ t1) at 1; rewrite <- concat_empty_r.
  apply awtermt_replace2.
  rewrite~ concat_empty_r.
  lets: cplt_ctxsubst_replace' H21; auto. apply~ ok_push.
  lets: ok_preservation H29. auto.
  exact H35.
  lets: H33 H34 H35.
  apply dopent_var_inj in H36; auto.
  rewrite~ H36.

  (* FORALL *)
  inversions H11. inversions H12.
  inversion H9; subst. inversion H10; subst.
  inversion H7; subst.
  inversion H13; subst.
  pick_fresh y.
  assert (notinl: y \notin L) by auto.
  assert (notinl0: y \notin L0) by auto.
  assert (notinl1: y \notin L1) by auto.
  assert (notinl2: y \notin L2) by auto.
  assert (notinl3: y \notin L3) by auto.
  assert (notinl4: y \notin L4) by auto.
  assert (notinl5: y \notin L5) by auto.
  lets: H0 notinl. clear H0.
  assert (wf: AWf(G & y ~ AC_TVar)) by apply~ AWf_TVar.
  assert (H11' : AUnify (G & y ~ AC_TVar) (t1 @@#' AT_TFVar y) (t2 @@#' AT_TFVar y)
          (H & y ~ AC_TVar)). apply* aunify2_is_aunify.
  lets: unify_extension H11' wf.
  lets: H16 notinl0.  clear H16.
  lets: H15 notinl1.  clear H15.
  lets: H14 notinl2. clear H14.
  lets: H17 notinl3. clear H17.
  lets: H18 notinl4. clear H18.
  lets: H19 notinl5. clear H19.

  assert((t1 @@#' AT_TFVar y) = ACtxTSubst (G & y ~ AC_TVar) (t1 @@#' AT_TFVar y)).
  rewrite actxtsubst_expr in *.
  inversion H2; subst. clear H2.
  rewrite actxsubst_forall in H20. inversion H20.  clear H20.
  rewrite <- H19. rewrite tsubst_add_tvar. rewrite~ actxtsubst_topen.
  rewrite~ actxtsubst_tfvar_notin. rewrite <- H19. auto.
  assert(t2 @@#' AT_TFVar y = ACtxTSubst (G & y ~ AC_TVar) (t2 @@#' AT_TFVar y)).
  rewrite actxtsubst_expr in *.
  inversion H3; subst. clear H3.
  rewrite actxsubst_forall in H21. inversion H21.  clear H21.
  rewrite <- H20. rewrite tsubst_add_tvar. rewrite~ actxtsubst_topen.
  rewrite~ actxtsubst_tfvar_notin. rewrite <- H20. auto.
  destruct H0 as [? ?]; auto.

  lets: H1 notinl H19 H20 wf.
  clear H1.
  lets: awftyp_is_awftyping H12.
  lets: awftyp_is_awftyping H16.
  lets: H22 H15 H14 H1 H23. clear H22.
  lets: awf_preservation H4.
  assert (AWf (I & y ~ AC_TVar)) by apply~ AWf_TVar.
  assert(ExtCtx (H & y ~ AC_TVar) (I & y ~ AC_TVar)) by apply~ ExtCtx_TVar.
  assert (CompleteCtx (I & y ~ AC_TVar)) by apply~ complete_add_tvar.
  assert (ACpltCtxSubstCtx (I & y ~ AC_TVar) (H & y ~ AC_TVar) (H' & y ~ DC_TVar)) by apply~ ACpltCtxSubstCtx_TVar.
  lets: H24 H26 H27 H28 H17 H18.
  apply dtopent_var_inj in H29; auto.
  rewrite~ H29.

  (* ANN *)
  assert (H0_':  AUnify G (AT_Expr t1) (AT_Expr t2) H1). apply* aunify2_is_aunify.
  assert (AT_Expr t2 = ACtxTSubst G (AT_Expr t2)).
  rewrite actxtsubst_expr. f_equal.
  rewrite actxtsubst_expr in H2. inversion~ H2.
  rewrite actxsubst_ann in H14. inversion H14. rewrite <- H15. auto.
  assert (AT_Expr t1 = ACtxTSubst G (AT_Expr t1)).
  rewrite actxtsubst_expr. f_equal.
  rewrite actxtsubst_expr in H0. inversion~ H0.
  rewrite actxsubst_ann in H15. inversion H15. rewrite <- H16. auto.

  inversion H11. subst. inversion H12. subst.
  lets: unify_extension_expr H0_' H8 H20 H18.
  rewrite actxtsubst_expr in H13.  inversion H13. rewrite~ <- H16.
  rewrite actxtsubst_expr in H14.  inversion H14. rewrite~ <- H16.
  destruct H15 as [? ?].

  assert (H0_0' : AUnify H1 (ACtxTSubst H1 t3) (ACtxTSubst H1 t4) H). apply* aunify2_is_aunify.
  assert (ACtxTSubst H1 t4 = ACtxTSubst H1 (ACtxTSubst H1 t4)). rewrite~ ctxtsubst_twice.
  assert (ACtxTSubst H1 t3 = ACtxTSubst H1 (ACtxTSubst H1 t3)). rewrite~ ctxtsubst_twice.
  lets: unify_extension H0_0' H15 H17 H22.
  assert (AWfTyp H1 (ACtxTSubst H1 t4)).
  apply -> awftyp_subst.
  lets: extension_weakening_awftyp H21 H16. auto.
  assert (AWfTyp H1 (ACtxTSubst H1 t3)).
  apply -> awftyp_subst.
  lets: extension_weakening_awftyp H19 H16. auto.
  destruct H23 as [? ?]; auto.

  lets: extension_transitivity H26 H3.
  inversions H6. inversions H7. inversion H9; subst. inversion H10; subst.
  forwards * : IHAUnify2_1 H27.
  lets: confluence_cplt3 H3 H27 H4 H5. exact H6.
  inversion~ H6. subst. clear H6.

  clear IHAUnify2_1.
  lets: awtermt_awftyp H24.
  lets: awtermt_awftyp H25.
  lets: IHAUnify2_2 H22 H17 H15 H7 H6.
  lets: awftyp_is_awftyping H25.
  lets: awftyp_is_awftyping H24.
  forwards ~ : H28 H37 H38 H3 H5.
  assert (ACpltCtxSubst I (ACtxTSubst H1 t4) d3).
  apply complete_eq with t4; auto.
  apply awf_preservation in H3; auto.
  apply* extension_weakening_awtermt.
  apply substitution_extension_invariance2; auto. exact H39.
  assert (ACpltCtxSubst I (ACtxTSubst H1 t3) d2).
  apply complete_eq with t3; auto.
  apply awf_preservation in H3; auto.
  apply* extension_weakening_awtermt.
  apply substitution_extension_invariance2; auto. exact H39.
  rewrite~ H39.

  (* EVarTy *)
  lets: awf_preservation H6; auto.
  lets: awf_context H6.
  assert (ACpltCtxSubst I t2 t1').
  apply complete_eq with (AT_EVar a); auto.
  assert (binds a (AC_Solved_EVar t2) (H1 & a ~ AC_Solved_EVar t2 & H2)). apply binds_middle_eq.
  apply awf_is_ok in H17. apply* ok_middle_inv_r.
  lets: awterm_evar_binds H17 H18.
  lets: extension_weakening_awtermt H19 H6; auto.
  rewrite substitution_extension_invariance_left2 with (G:= H1 & a ~ AC_Solved_EVar t2 & H2); auto.
  rewrite substitution_extension_invariance_left2 with (t:=t2) (G:= H1 & a ~ AC_Solved_EVar t2 & H2); auto.
  f_equal.

  rewrite~ actxtsubst_evar.
  rewrite <- concat_assoc.
  rewrite~ actxtsubst_append.
  rewrite concat_assoc. apply awf_is_ok in H17; auto.

  assert (ACpltCtxSubst I t2 t2').
  apply complete_eq with t1; auto.
  assert (binds a (AC_Solved_EVar t2) (H1 & a ~ AC_Solved_EVar t2 & H2)). apply binds_middle_eq.
  apply awf_is_ok in H17. apply* ok_middle_inv_r.
  lets: awterm_evar_binds H17 H19.
  lets: extension_weakening_awtermt H20 H6; auto.
  assert (AWf H1). rewrite <- concat_assoc in H17. apply AWf_left in H17; auto.
  assert (ExtCtx (H1 & a ~ AC_Unsolved_EVar & H2) (H1 & a ~ AC_Solved_EVar t2 & H2)).
  apply~ extension_append. apply~ ExtCtx_Solve.
  apply~ extension_reflexivity.
  apply* AWf_Ctx_Unsolved_EVar.
  apply AWf_left in H17; auto.
  lets: resolve_evar_awf_preservation H0; auto.
  lets: extension_transitivity H20 H6.
  rewrite substitution_extension_invariance_left2 with (G:= H1 & a ~ AC_Unsolved_EVar & H2); auto.
  rewrite substitution_extension_invariance_left2 with (t:=t2) (G:= H1 & a ~ AC_Unsolved_EVar & H2); auto.
  f_equal.
  lets: resolve_evar_invariance H8 H0; auto.

  lets: cplt_ctxsubst_eq H18 H19; auto.

  (* TyEVar *)
  clear H.
  lets: awf_preservation H7; auto.
  lets: awf_context H7.
  assert (ACpltCtxSubst I t2 t2').
  apply complete_eq with (AT_EVar a); auto.
  assert (binds a (AC_Solved_EVar t2) (H1 & a ~ AC_Solved_EVar t2 & H2)). apply binds_middle_eq.
  apply awf_is_ok in H17. apply* ok_middle_inv_r.
  lets: awterm_evar_binds H17 H18.
  lets: extension_weakening_awtermt H19 H7; auto.
  rewrite substitution_extension_invariance_left2 with (G:= H1 & a ~ AC_Solved_EVar t2 & H2); auto.
  rewrite substitution_extension_invariance_left2 with (t:=t2) (G:= H1 & a ~ AC_Solved_EVar t2 & H2); auto.
  f_equal.

  rewrite~ actxtsubst_evar.
  rewrite <- concat_assoc.
  rewrite~ actxtsubst_append.
  rewrite concat_assoc. apply awf_is_ok in H17; auto.

  assert (ACpltCtxSubst I t2 t1').
  apply complete_eq with t1; auto.
  assert (binds a (AC_Solved_EVar t2) (H1 & a ~ AC_Solved_EVar t2 & H2)). apply binds_middle_eq.
  apply awf_is_ok in H17. apply* ok_middle_inv_r.
  lets: awterm_evar_binds H17 H19.
  lets: extension_weakening_awtermt H20 H7; auto.

  assert (AWf H1). rewrite <- concat_assoc in H17. apply AWf_left in H17; auto.
  assert (ExtCtx (H1 & a ~ AC_Unsolved_EVar & H2) (H1 & a ~ AC_Solved_EVar t2 & H2)).
  apply~ extension_append. apply~ ExtCtx_Solve.
  apply~ extension_reflexivity.
  apply* AWf_Ctx_Unsolved_EVar.
  apply AWf_left in H17; auto.
  lets: resolve_evar_awf_preservation H3; auto.
  lets: extension_transitivity H20 H7.
  rewrite substitution_extension_invariance_left2 with (G:= H1 & a ~ AC_Unsolved_EVar & H2); auto.
  rewrite substitution_extension_invariance_left2 with (t:=t2) (G:= H1 & a ~ AC_Unsolved_EVar & H2); auto.
  f_equal.
  lets: resolve_evar_invariance H8 H3. auto.

  lets: cplt_ctxsubst_eq H18 H19; auto.
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
    AWf G ->
    AWfTyp G t1 ->
    AWfTyp G t2 ->
    t1' = t2'.
Proof.
  intros.
  lets: aunify_is_aunify2 H0. apply* awf_is_ok.
  lets: awftyp_is_awftyping H9.
  lets: awftyp_is_awftyping H10.
  lets: awtermt_awftyp H9.
  lets: awtermt_awftyp H10.
  forwards * : unif_soundness_same' H11 H1 H2 H3 H4.
Qed.