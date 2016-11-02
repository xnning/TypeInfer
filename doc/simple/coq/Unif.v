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

Theorem weak_extension_invariance: forall G H e,
    WExtCtx G H ->
    AWTermT G e ->
    ACtxTSubst H (ACtxTSubst G e) = ACtxTSubst H e.
Proof.
  introv ex wt. gen H.
  induction wt; introv ex; subst; auto.

  (* VAR *)
  repeat rewrite actxtsubst_expr.
  rewrite~ actxsubst_fvar.

  (* TYP VAR *)
  repeat rewrite actxtsubst_expr.
  rewrite~ actxsubst_fvar.

  (* STAR *)
  repeat rewrite~ tsubst_star.

  (* APP *)
  repeat rewrite actxtsubst_expr in *. f_equal.
  repeat rewrite~ actxsubst_app. f_equal.
  lets: IHwt1 ex.
  repeat rewrite actxtsubst_expr in *. inversion~ H0.
  lets: IHwt2 ex.
  repeat rewrite actxtsubst_expr in *. inversion~ H0.

  (* LAM *)
  repeat rewrite actxtsubst_expr in *. f_equal.
  repeat rewrite~ actxsubst_lam. f_equal.
  pick_fresh y.
  assert (y \notin L) by auto.
  assert (WExtCtx (G & y ~ AC_Var) (H1 & y ~ AC_Var)).
  apply~ WExtCtx_Var.
  lets: H0 H2 H3.
  repeat rewrite tsubst_add_var in H4.
  repeat rewrite actxtsubst_expr in *. inversion~ H4.
Admitted.


Theorem unify_invariance: forall G e t H,
    AWf G ->
    AUnify G e t H ->
    AWTermT G e ->
    ACtxTSubst H e = ACtxTSubst H t.
Proof.
  introv uni wt.
  induction uni; subst; auto.

  (* APP *)
  repeat rewrite actxtsubst_expr.
  admit.
Admitted.

(***********************)
(* AWfTyping *)
(***********************)

Inductive AWfTyping : ACtx -> AType -> Prop :=
| AWfTyping_Star: forall G,
    AWf G ->
    AWfTyping G (AT_Expr (AE_Star))
| AWfTyping_Var: forall G x,
    AWf G ->
    binds x AC_Var G ->
    AWfTyping G (AT_Expr (AE_FVar x))
| AWfTyping_TypVar: forall G x t,
    AWf G ->
    binds x (AC_Typ t) G ->
    AWfTyping G (AT_Expr (AE_FVar x))
| AWfTyping_EVar: forall G x,
    AWf G ->
    binds x AC_Unsolved_EVar G ->
    AWfTyping G (AT_EVar x)
| AWfTyping_Solved_EVar: forall G x t,
    AWf G ->
    binds x (AC_Solved_EVar t) G ->
    AWfTyping G (AT_EVar x)
| AWfTyping_TVar: forall G x,
    AWf G ->
    binds x AC_TVar G ->
    AWfTyping G (AT_TFVar x)
| AWfTyping_Ann: forall G e1 e2,
    AWfTyping G (AT_Expr e1) ->
    AWfTyp G e2 ->
    AWfTyping G (AT_Expr (AE_Ann e1 e2))
| AWfTyping_Pi: forall G e1 e2 L,
    AWfTyp G e1 ->
    (forall x, x \notin L ->
          AWfTyp (G & x ~ AC_Typ e1) (e2 @' x)) ->
    AWfTyping G (AT_Expr (AE_Pi e1 e2))
| AWfTyping_Lam: forall G e L,
    (forall x, x \notin L ->
          AWfTyping (G & x ~ AC_Var) (AT_Expr (e @ x))) ->
    AWfTyping G (AT_Expr (AE_Lam e))
| AWfTyping_App: forall G e1 e2,
    AWfTyping G (AT_Expr e1) ->
    AWfTyping G (AT_Expr e2) ->
    AWfTyping G (AT_Expr (AE_App e1 e2))
| AWfTyping_CastDn: forall G e,
    AWfTyping G (AT_Expr e) ->
    AWfTyping G (AT_Expr (AE_CastDn e))
| AWfTyping_CastUp: forall G e,
    AWfTyping G (AT_Expr e) ->
    AWfTyping G (AT_Expr (AE_CastUp e))
| AWfTyping_Forall: forall G e L,
    (forall a, a \notin L ->
          AWfTyp (G & a ~ AC_TVar) (e @#' a)) ->
    AWfTyping G (AT_Expr (AE_Forall e)).

Lemma extension_weakening_awftyping: forall G H t,
    AWfTyping G t ->
    ExtCtx G H ->
    AWfTyping H t.
Proof.
  introv wf ex. gen H.
  induction wf; introv ex; auto; try(solve[constructor~]).

  (* STAR *)
  apply AWfTyping_Star.
  lets: awf_preservation ex. auto.

  (* VAR *)
  apply~ AWfTyping_Var.
  lets: awf_preservation ex. auto.
  apply split_bind_context in H0.
  destruct H0 as (G1 & G2 & ginfo); subst.
  lets: awf_preservation ex.
  apply extension_order_var in ex.
  destruct ex as (H2 & H3 & [hinfo _]). subst.
  apply binds_middle_eq.
  apply awf_is_ok in H0.
  lets: ok_middle_inv_r H0.  auto.

  (* TYP VAR *)
  apply split_bind_context in H0.
  destruct H0 as (G1 & G2 & ginfo); subst.
  lets: awf_preservation ex.
  apply extension_order_typvar in ex.
  destruct ex as (H2 & H3 & t1 & [hinfo _]). subst.
  apply AWfTyping_TypVar with t1. auto.
  apply binds_middle_eq.
  apply awf_is_ok in H0.
  lets: ok_middle_inv_r H0.  auto.

  (* EVAR *)
  apply split_bind_context in H0.
  destruct H0 as (G1 & G2 & ginfo); subst.
  lets: awf_preservation ex.
  apply extension_order_unsolved_evar in ex.
  destruct ex as (H2 & H3 & [[hinfo1 | (t1 & hinfo2)] _]); subst.
  apply AWfTyping_EVar. auto.
  apply binds_middle_eq.
  apply awf_is_ok in H0.
  lets: ok_middle_inv_r H0.  auto.
  apply AWfTyping_Solved_EVar with t1. auto.
  apply binds_middle_eq.
  apply awf_is_ok in H0.
  lets: ok_middle_inv_r H0.  auto.

  (* SOLVED EVAR *)
  apply split_bind_context in H0.
  destruct H0 as (G1 & G2 & ginfo); subst.
  lets: awf_preservation ex.
  apply extension_order_solved_evar in ex.
  destruct ex as (H2 & H3 & t2 &  [hinfo _]); subst.
  apply AWfTyping_Solved_EVar with t2. auto.
  apply binds_middle_eq.
  apply awf_is_ok in H0.
  lets: ok_middle_inv_r H0.  auto.

  (* TVAR *)
  apply split_bind_context in H0.
  destruct H0 as (G1 & G2 & ginfo); subst.
  lets: awf_preservation ex.
  apply extension_order_tvar in ex.
  destruct ex as (H2 & H3 & [hinfo _]); subst.
  apply AWfTyping_TVar. auto.
  apply binds_middle_eq.
  apply awf_is_ok in H0.
  lets: ok_middle_inv_r H0.  auto.

  (* ANN *)
  apply AWfTyping_Ann.
  lets: IHwf ex; auto.
  lets: extension_weakening_awftyp H ex. auto.

  (* PI *)
  apply AWfTyping_Pi with (L \u dom G \u dom H1).
  lets: extension_weakening_awftyp H ex. auto.
  intros y notin.
  assert (y \notin L) by auto.
  lets: H0 H2. clear H0.
  assert (ExtCtx (G & y ~ AC_Typ e1) (H1 & y ~ AC_Typ e1)).
  apply~ ExtCtx_TypVar.
  apply~ AWf_TyVar.
  lets: awf_context ex; auto.
  apply~ AWf_TyVar.
  lets: awf_preservation ex; auto.
  lets: extension_weakening_awftyp H ex; auto.
  lets: extension_weakening_awftyp H3 H0. auto.

  (* LAM *)
  apply AWfTyping_Lam with (L \u dom G \u dom H1).
  intros y notin.
  assert (y \notin L) by auto.
  assert (ExtCtx (G & y ~ AC_Var) (H1 & y ~ AC_Var)).
  apply~ ExtCtx_Var. apply~ AWf_Var.
  lets: awf_context ex; auto.
  apply~ AWf_Var.
  lets: awf_preservation ex; auto.
  lets: H0 H2 H3. auto.

  (* FORALL *)
  apply AWfTyping_Forall with (L \u dom G \u dom H0).
  intros y notin.
  assert (y \notin L) by auto.
  assert (ExtCtx (G & y ~ AC_TVar) (H0 & y ~ AC_TVar)).
  apply~ ExtCtx_TVar. apply~ AWf_TVar.
  lets: awf_context ex; auto.
  apply~ AWf_TVar.
  lets: awf_preservation ex; auto.
  lets: H H1.
  lets: extension_weakening_awftyp H3 H2. auto.
Qed.

Lemma awftyping_awf: forall G e,
    AWfTyping G e ->
    AWf G.
Proof.
  introv wf. induction wf; auto.

  pick_fresh y. assert (y \notin L) by auto.
  lets: H0 H1.
  lets: awftyp_awf H2.
  lets: AWf_left H3. auto.

  pick_fresh y. assert (y \notin L) by auto.
  lets: H0 H1.
  lets: AWf_left H2. auto.

  pick_fresh y. assert (y \notin L) by auto.
  lets: H H0.
  lets: awftyp_awf H1.
  lets: AWf_left H2. auto.
Qed.

Lemma awftyping_middle_remove: forall G H I e,
    AWfTyping (G & H & I) e ->
    AWf (G & I) ->
    AWTermT (G & I) e ->
    AWfTyping (G & I) e.
Proof.
  introv ty wf wt.
  gen_eq S: (G & H & I). gen I.
  induction ty; introv wf wt sinfo; subst.
  apply~ AWfTyping_Star.
  (* VAR *)
  apply~ AWfTyping_Var.
  inversion wt; subst; auto.
  lets: awf_is_ok H0.
  lets: binds_weaken H4 H2.
  false binds_func H1 H3.

  (* TYPVAR *)
  inversion wt; subst; auto.
  lets: awf_is_ok H0.
  lets: binds_weaken H4 H2.
  false binds_func H1 H3.
  apply AWfTyping_TypVar with t0; auto.

  (* EVAR *)
  apply~ AWfTyping_EVar.
  inversion wt; subst; auto.
  lets: awf_is_ok H0.
  lets: binds_weaken H4 H2.
  false binds_func H1 H3.

  (* SOLVED EVAR *)
  inversion wt; subst; auto.
  lets: awf_is_ok H0.
  lets: binds_weaken H4 H2.
  false binds_func H1 H3.
  apply AWfTyping_Solved_EVar with t0; auto.

  (* TVAR *)
  apply~ AWfTyping_TVar.
  inversion wt; subst; auto.

  (* ANN *)
  inversion wt; subst.
  forwards * : IHty H4.
  lets: awftyp_middle_remove H0 H5; auto.
  apply~ AWfTyping_Ann.

  (* PI *)
  inversion wt; subst.
  apply AWfTyping_Pi with (L \u L0 \u dom G \u dom I).
  lets: awftyp_middle_remove H0 H5; auto.
  intros y notin.
  assert (y \notin L0) by auto.
  lets: H6 H2. clear H6.
  assert (AWTermT (G & I & y ~ AC_Var & empty) (e2 @@' AE_FVar y)) by rewrite~ concat_empty_r.
  lets: awtermt_replace2 e1 H4.
  rewrite concat_empty_r in H6.

  assert (y \notin L) by auto.
  lets: H1 H7.
  rewrite <- concat_assoc in H8.
  rewrite <- concat_assoc in H6.
  lets: awftyp_middle_remove H8 H6.
  rewrite concat_assoc in *.
  apply~ AWf_TyVar.

  lets: awftyp_awf H8.
  lets: awftyp_middle_remove H0 wf H5. auto.

  rewrite concat_assoc in H9. auto.

  (* LAM *)
  inversion wt; subst.
  apply AWfTyping_Lam with (L \u L0 \u dom G \u dom I).
  intros y notin.
  assert (y \notin L0) by auto.
  lets: H4 H2. clear H4.
  rewrite <- concat_assoc.
  apply~ H1.
  rewrite concat_assoc. apply~ AWf_Var.
  rewrite~ concat_assoc.
  rewrite~ concat_assoc.

  (* APP *)
  inversion wt; subst.
  forwards * : IHty1 H3.
  forwards * : IHty2 H4.
  apply~ AWfTyping_App.

  (* CASTDN *)
  inversion wt; subst.
  forwards * : IHty H2.
  apply~ AWfTyping_CastDn.

  (* CASTUP *)
  inversion wt; subst.
  forwards * : IHty H2.
  apply~ AWfTyping_CastUp.

  (* FORALL *)
  inversion wt; subst.
  apply AWfTyping_Forall with (L \u L0 \u dom G \u dom I).
  intros y notin.
  assert (y \notin L0) by auto.
  lets: H3 H1. clear H3.
  assert (y \notin L) by auto.
  lets: H0 H3. clear H0.
  rewrite <- concat_assoc in H2.
  rewrite <- concat_assoc in H4.
  lets: awftyp_middle_remove H4 H2.
  rewrite concat_assoc. apply~ AWf_TVar.
  rewrite~ concat_assoc in H0.
Qed.


Lemma awftyping_remove: forall G H e,
    AWfTyping (G & H) e ->
    AWTermT G e ->
    AWfTyping G e.
Proof.
  introv wf wt.
  assert (wf2 := wf).
  assert (I1: AWfTyping (G & H & empty) e) by rewrite~ concat_empty_r.
  assert (I2: AWf (G & empty)). rewrite~ concat_empty_r. lets: awftyping_awf wf. apply AWf_left in H0. auto.
  assert (I3: AWTermT (G & empty) e). rewrite~ concat_empty_r.
  lets: awftyping_middle_remove I1 I2 I3.
  rewrite concat_empty_r in H0. auto.
Qed.

Lemma awftyp_is_awftyping: forall G e,
    AWfTyp G e ->
    AWfTyping G e.
Admitted.

Lemma awftyping_subst: forall G t,
    AWfTyping G t ->
    AWfTyping G (ACtxTSubst G t).
Proof.
  introv wf. induction wf; simpls~.
  rewrite tsubst_star. apply~ AWfTyping_Star.
  rewrite actxtsubst_expr. rewrite actxsubst_fvar. apply~ AWfTyping_Var.
  rewrite actxtsubst_expr. rewrite actxsubst_fvar. apply* AWfTyping_TypVar.
  apply split_bind_context in H0.
  admit.
  admit.
  admit.

  (* ANN *)
  rewrite actxtsubst_expr.
  rewrite actxsubst_ann.
  apply~ AWfTyping_Ann.
  rewrite actxtsubst_expr in IHwf; auto.
  apply -> awftyp_subst. auto.

  (* PI *)
  rewrite actxtsubst_expr.
  rewrite actxsubst_pi.
  apply AWfTyping_Pi with L.
  apply -> awftyp_subst. auto.
Admitted.

Lemma extension_remove_tvar : forall G H y,
    ExtCtx (G & y ~ AC_TVar) (H & y ~ AC_TVar) ->
    ExtCtx G H.
Proof.
  introv D.
  rewrite <- concat_empty_r in D at 1.
  rewrite <- concat_empty_r in D.
  destruct (extension_order_tvar D) as [X [Y (K1 & K2 & _)]].
  lets C: awf_preservation D.
  pose (Ok2 := awf_is_ok C).
  lets Ok3: Ok2.
  rewrite K1 in Ok3.
  destruct~ (ok_middle_eq Ok2 eq_refl Ok3 eq_refl K1) as (Eq1 & Eq2 & Eq3).
  subst*.
Qed.

Lemma atunify_awf: forall G t d H,
    ATUnify UType G t d H ->
    AWf G ->
    AWfTyp G t -> AWfTyp G d ->
    AWf H /\ ExtCtx G H
with atunify_awf_expr: forall G t d H,
    ATUnify UExpr G t d H ->
    AWf G ->
    AWfTyping G t ->
    AWfTyping G d ->
    AWf H /\ ExtCtx G H.
Proof.
  introv uni wf awf1 awf2.
  inversion uni; subst; auto.
  split; auto. apply~ extension_reflexivity.
  split; auto. apply~ extension_reflexivity.

  (* *)
  lets: resolve_evar_awf_preservation H3 wf.
  assert (AWfTyp H1 t2).
  lets: resolve_evar_extension H3 wf.
  lets: extension_weakening_awftyp awf2 H5.
  apply awftyp_subst in H6.
  lets: awtermt_awftyp awf2.
  lets: resolve_evar_invariance wf H3 H7.
  rewrite H8 in H6.
  apply awftyp_subst in H6.
  rewrite <- concat_assoc in H6.
  lets: awftyp_remove H6 H4. auto.

  assert (AWf (H1 & a ~ AC_Solved_EVar t2 & H2)).
  apply awf_solve_middle with (t:=t2) in H; auto.
  lets: resolve_evar_atmono_preservation H3; auto.

  split; auto.

  lets: resolve_evar_extension H3 wf.
  assert (ExtCtx (H1 & a ~ AC_Unsolved_EVar & H2) (H1 & a ~ AC_Solved_EVar t2 & H2)).
  apply~ extension_append.
  apply ExtCtx_Solve. apply extension_reflexivity.
  repeat apply AWf_left in H. auto.
  apply AWf_left in H. auto.
  apply AWf_left in H6. auto.
  lets: extension_transitivity H7 H8. auto.

  (* *)
  lets: resolve_evar_awf_preservation H4 wf.
  assert (AWfTyp H1 t2).
  lets: resolve_evar_extension H4 wf.
  lets: extension_weakening_awftyp awf1 H6.
  apply awftyp_subst in H7.
  lets: awtermt_awftyp awf1.
  lets: resolve_evar_invariance wf H4 H8.
  rewrite H9 in H7.
  apply awftyp_subst in H7.
  rewrite <- concat_assoc in H7.
  lets: awftyp_remove H7 H5. auto.

  assert (AWf (H1 & a ~ AC_Solved_EVar t2 & H2)).
  apply awf_solve_middle with (t:=t2) in H; auto.
  lets: resolve_evar_atmono_preservation H4; auto.

  split; auto.

  lets: resolve_evar_extension H4 wf.
  assert (ExtCtx (H1 & a ~ AC_Unsolved_EVar & H2) (H1 & a ~ AC_Solved_EVar t2 & H2)).
  apply~ extension_append.
  apply ExtCtx_Solve. apply extension_reflexivity.
  repeat apply AWf_left in H. auto.
  apply AWf_left in H. auto.
  apply AWf_left in H7. auto.
  lets: extension_transitivity H8 H9. auto.

  lets: awftyp_is_awftyping awf1.
  lets: awftyp_is_awftyping awf2.
  lets: atunify_awf_expr H1 wf H0 H2. auto.
Proof.
  clear atunify_awf_expr.
  introv uni wf awf1 awf2.
  gen_eq M: UExpr.
  induction uni; introv minfo; subst; auto;
    try(solve[inversion minfo]);
    try(solve[split; [auto | apply~ extension_reflexivity]]).

  (* APP *)
  inversion awf1; subst.
  inversion awf2; subst.
  lets: IHuni1 wf H4 H6 minfo. clear IHuni1.
  destruct H0 as [wfh1 exgh1].
  lets: extension_weakening_awftyping H5 exgh1.
  apply awftyping_subst in H0.
  rewrite actxtsubst_expr in H0.
  lets: extension_weakening_awftyping H7 exgh1.
  apply awftyping_subst in H2.
  rewrite actxtsubst_expr in H2.
  lets: IHuni2 wfh1 H0 H2 minfo.
  destruct H3.
  lets: extension_transitivity exgh1 H8. split; auto.

  (* LAM *)
  inversion awf1; subst.
  inversion awf2; subst.
  pick_fresh y.
  assert (notinl : y \notin L) by auto.
  assert (notinl0 : y \notin L0) by auto.
  assert (notinl1 : y \notin L1) by auto.
  assert (AWf (G & y ~ AC_Var)) by apply~ AWf_Var.
  lets: H4 notinl0.
  lets: H5 notinl1.
  lets: H1 notinl H2 H3 H6 minfo.
  destruct H7 as [wfh exgh].
  split.
  apply AWf_left in wfh; auto.
  apply extctx_remove_var in exgh. auto.

  (* CASTUP *)
  inversion awf1; subst.
  inversion awf2; subst.
  lets: IHuni wf H2 H3 minfo. auto.

  (* CASTDOWN *)
  inversion awf1; subst.
  inversion awf2; subst.
  lets: IHuni wf H2 H3 minfo. auto.

  (* PI *)
  inversion awf1; subst.
  inversion awf2; subst.
  clear H2 IHuni.

  lets: atunify_awf uni wf H6 H8.
  destruct H2.
  pick_fresh y.
  assert (y \notin L0) by auto.
  assert (y \notin L1) by auto.
  lets: H7 H4. clear H7.
  lets: H9 H5. clear H9.
  assert (ExtCtx (G & y ~ AC_Typ t1) (H1 & y ~ AC_Typ t1)).
  apply~ ExtCtx_TypVar.
  apply~ AWf_TyVar.
  lets: extension_weakening_awftyp H6 H3. auto.
  assert (ExtCtx (G & y ~ AC_Typ t3) (H1 & y ~ AC_Typ t3)).
  apply~ ExtCtx_TypVar.
  apply~ AWf_TyVar.
  lets: extension_weakening_awftyp H8 H3. auto.
  lets: extension_weakening_awftyp H10 H9.
  lets: extension_weakening_awftyp H7 H11.
  lets: awtermt_awftyp H6.
  lets: atunify_is_aunify uni.
  lets: awf_is_ok wf. auto.
  lets: unify_invariance wf H15 H14.
  assert (AWfTyp (H1 & y ~ AC_Typ t3 & empty) (t4 @@' AE_FVar y)) by rewrite~ concat_empty_r.
  symmetry in H16.
  lets: awftyp_middle_change_typvar H17 H16.
  rewrite concat_empty_r in H18.

  assert (y \notin L) by auto.
  lets: H0 H19. clear H0.
  apply awftyp_subst in H12.
  rewrite tsubst_add_typvar in H12.
  apply awftyp_subst in H18.
  rewrite tsubst_add_typvar in H18.
  lets: atunify_awf H20 H12 H18.
  apply~ AWf_TyVar.
  lets: extension_weakening_awftyp H6 H3. auto.

  destruct H0.
  split.
  lets: AWf_left H0. auto.
  lets: extension_remove_tyvar H21.
  lets: extension_transitivity H3 H22. auto.

  (* FORALL *)
  clear H1.
  inversion awf1; subst.
  inversion awf2; subst.
  pick_fresh y.
  assert (y \notin L) by auto.
  lets: H0 H1. clear H0.
  assert (y \notin L0) by auto.
  lets: H3 H0. clear H3.
  assert (y \notin L1) by auto.
  lets: H4 H3. clear H4.
  lets: atunify_awf H2 H5 H6.
  apply~ AWf_TVar.
  destruct H4.
  split.
  lets: AWf_left H4. auto.
  lets: extension_remove_tvar H7. auto.

  (* ANN *)
  clear IHuni2.
  inversion awf1; subst.
  inversion awf2; subst.
  lets: IHuni1 wf H4 H6 minfo. clear IHuni1 uni1.
  destruct H0.
  lets: extension_weakening_awftyp H5 H2.
  apply awftyp_subst in H3.
  lets: extension_weakening_awftyp H7 H2.
  apply awftyp_subst in H8.
  lets: atunify_awf uni2 H0 H3 H8.
  destruct H9.
  lets: extension_transitivity H2 H10.
  split; auto.
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
