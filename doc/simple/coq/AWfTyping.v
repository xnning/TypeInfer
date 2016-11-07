Require Import LibLN.
Require Import AlgoDef.
Require Import DeclDef.
Require Import AlgoInfra.
Require Import DeclInfra.
Require Import CtxExtension.
Require Import UtilityEnv.
Require Import UtilityMore.
Require Import UtilityAlgo.
Require Import Subst.

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

(***********************)
(* Admits *)
(***********************)

Lemma awftyp_is_awftyping: forall G e,
    AWfTyp G e ->
    AWfTyping G e.
Admitted.

(***********************)
(* Lemmas *)
(***********************)

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

Lemma awftyping_subst: forall G t,
    AWf G ->
    AWfTyping G t ->
    AWfTyping G (ACtxTSubst G t).
Proof.
  introv wfg wf. induction wf; simpls~.
  rewrite tsubst_star. apply~ AWfTyping_Star.
  rewrite actxtsubst_expr. rewrite actxsubst_fvar. apply~ AWfTyping_Var.
  rewrite actxtsubst_expr. rewrite actxsubst_fvar. apply* AWfTyping_TypVar.
  rewrite ctxsubst_evar_eq; auto. apply~ AWfTyping_EVar.

  (* SOLVED EVAR *)
  apply split_bind_context in H0.
  destruct H0 as (I1 & I2 & ginfo). subst.
  rewrite~ actxtsubst_evar.
  lets: AWf_left wfg.
  lets: awterm_solved_evar H0.
  rewrite <- actxtsubst_append with (H:=x~ AC_Solved_EVar t & I2); auto.
  rewrite concat_assoc.
  apply awftyp_is_awftyping.
  apply -> awftyp_subst.
  lets: awftyp_solved_evar H0.
  rewrite <- concat_assoc.
  apply~ awftyp_weakening.
  rewrite~ concat_assoc.
  rewrite~ concat_assoc.

  (* TFVar *)
  rewrite~ actxtsubst_tfvar. apply* AWfTyping_TVar.

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
  intros y notin.
  lets: H0 notin.
  assert (AWfTyp (G & y ~ AC_Typ e1 & empty) (e2 @@' AE_FVar y)). rewrite~ concat_empty_r.
  assert (ACtxTSubst G e1 = ACtxTSubst G (ACtxTSubst G e1)). rewrite~ ctxtsubst_twice.
  lets: awftyp_middle_change_typvar H2 H3.
  rewrite concat_empty_r in H4.
  rewrite awftyp_subst in H4.
  rewrite tsubst_add_typvar in H4.
  rewrite actxtsubst_open in H4; auto.
  rewrite actxsubst_fvar in H4. auto.

  (* LAM *)
  rewrite actxtsubst_expr.
  rewrite actxsubst_lam.
  apply AWfTyping_Lam with (L \u dom G).
  intros y notin. assert (y \notin L) by auto.
  lets: H0 H1. clear H0.
  assert (AWf (G & y ~ AC_Var)) by apply~ AWf_Var.
  lets: H2 H0. clear H2.
  rewrite actxtsubst_expr in H3.
  rewrite subst_add_var in H3.
  rewrite actxsubst_open in H3; auto.
  rewrite actxsubst_fvar in H3. auto.

  (* APP *)
  lets: IHwf1 wfg.
  lets: IHwf2 wfg.
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_app.
  apply~ AWfTyping_App.

  (* CASTDN *)
  lets: IHwf wfg.
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_castdn.
  apply~ AWfTyping_CastDn.

  (* CASTUP *)
  lets: IHwf wfg.
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_castup.
  apply~ AWfTyping_CastUp.

  (* FORALL *)
  rewrite actxtsubst_expr.
  rewrite actxsubst_forall.
  apply AWfTyping_Forall with (L \u dom G).
  intros y notin. assert (y \notin L) by auto.
  lets: H H0. clear H.
  apply -> awftyp_subst in H1.
  rewrite tsubst_add_tvar in H1; auto.
  rewrite actxtsubst_topen in H1; auto.
  rewrite actxtsubst_tfvar_notin in H1; auto.
Qed.
