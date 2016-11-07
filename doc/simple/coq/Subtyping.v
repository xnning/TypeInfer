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
Require Import Unif.

Lemma awftyp_forall: forall G e x,
    AWfTyp G (AT_Expr (AE_Forall e)) ->
    x # G ->
    AWfTyp (G & x ~ AC_TVar) (e @#' x).
Admitted.

Lemma awftyp_pi1: forall G e1 e2,
    AWfTyp G (AT_Expr (AE_Pi e1 e2)) ->
    AWfTyp G e1.
Admitted.

Lemma awftyp_pi2: forall G e1 e2 x,
    AWfTyp G (AT_Expr (AE_Pi e1 e2)) ->
    x # G ->
    AWfTyp (G & x ~ AC_Typ e1) e2.
Admitted.

Lemma awftyp_forall_evar: forall G e x,
    AWfTyp G (AT_Expr (AE_Forall e)) ->
    x # G ->
    AWfTyp (G & x ~ AC_Unsolved_EVar) (e @@#' (AT_EVar x)).
Admitted.

Lemma acpltctxsubst_add_tvar: forall I s t x,
    ACpltCtxSubst I s t ->
    x # I ->
    ACpltCtxSubst (I & x ~ AC_TVar) s t.
Proof.
Admitted.

Theorem subtype_soundness: forall G H I t1 t2 H' t1' t2',
    ASubtyping G t1 t2 H ->
    t1 = ACtxTSubst G t1 ->
    t2 = ACtxTSubst G t2 ->
    ExtCtx H I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I H H' ->
    ACpltCtxSubst I t1 t1' ->
    ACpltCtxSubst I t2 t2' ->
    AWf G -> AWfTyp G t1 -> AWfTyp G t2 ->
    DSubtyping H' t1' t2'.
Proof.
  intros. gen t1' t2' I H'. inductions H0; intros.

  (* POLYR *)
  inversion H7. rewrite <- H15 in *.
  clear H12 H13 H15.
  apply DSub_PolyR with (dom I).

  intros n notin.
  assert (I1: s1 = ACtxTSubst (G & v ~ AC_TVar) s1).
  rewrite~ tsubst_add_tvar.
  assert (I2: s2 @@#' AT_TFVar v =
              ACtxTSubst (G & v ~ AC_TVar) (s2 @@#' AT_TFVar v)).
  rewrite tsubst_add_tvar.
  rewrite actxtsubst_expr in H3.
  inversion H3.
  rewrite actxsubst_forall in H13.
  inversion H13.
  rewrite <- H15.
  rewrite~ actxtsubst_topen.
  rewrite~ actxtsubst_tfvar_notin.
  rewrite~ <- H15.

  assert (I3 : AWf (G & v ~ AC_TVar)).
  apply~ AWf_TVar.
  assert (I4: AWfTyp (G & v ~ AC_TVar) s1).
  apply~ awftyp_weakening.
  assert (I5: AWfTyp (G & v ~ AC_TVar) (s2 @@#' AT_TFVar v)).
  lets: awftyp_forall H10 H0. auto.
  assert (I6: ExtCtx (H & v ~ AC_TVar) (I & v ~ AC_TVar)).
  apply~ ExtCtx_TVar.
  apply~ AWf_TVar.
  lets: awf_context H4. auto.
  lets: promise_fresh v (dom H). auto.
  apply~ AWf_TVar.
  lets: awf_preservation H4. auto.
  lets: promise_fresh v (dom I). auto.
  assert (I7: CompleteCtx (I & v ~ AC_TVar)).
  apply~ complete_add_tvar.
  assert (I8: ACpltCtxSubst (I & v ~ AC_TVar) s1 t1').
  apply~ acpltctxsubst_add_tvar.
  lets: promise_fresh v (dom I). auto.
  assert(I9: ACpltCtxSubst (I & v ~ AC_TVar) (s2 @@#' AT_TFVar v) (s3 ^^%' DT_TFVar v)).
  lets: promise_fresh v L.
  lets: H14 H12. auto.
  assert (I10: ACpltCtxSubstCtx (I & v ~ AC_TVar) (H & v ~ AC_TVar) (H' & v ~ DC_TVar)).
  apply~ ACpltCtxSubstCtx_TVar.
  lets: IHASubtyping I1 I2 I3 I4 I5. clear IHASubtyping.
  lets: H12 I6 I7 I8 I9 I10. clear H12.

  admit. (* renaming *)

  (* POLYL *)
  inversion H11. rewrite <- H17 in *. clear H14 H15 H17.
  assert (I1: s1 @@#' AT_EVar a = ACtxTSubst (G & b ~ AC_Marker & a ~ AC_Unsolved_EVar) (s1 @@#' AT_EVar a)).
  rewrite tsubst_add_evar.
  rewrite tsubst_add_marker.
  rewrite~ actxtsubst_topen.
  rewrite~ actxtsubst_evar_notin.
  rewrite actxtsubst_expr in H4.
  inversion H4.
  rewrite actxsubst_forall in H15.
  inversion H15.
  repeat rewrite~ <- H17.

  assert (I2: s2 = ACtxTSubst (G & b ~ AC_Marker & a ~ AC_Unsolved_EVar) s2).
  rewrite tsubst_add_evar.
  rewrite~ tsubst_add_marker.

  assert (I3: AWf (G & b ~ AC_Marker & a ~ AC_Unsolved_EVar)).
  apply~ AWf_Ctx_Unsolved_EVar.

  assert (I4: AWfTyp (G & b ~ AC_Marker & a ~ AC_Unsolved_EVar) (s1 @@#' AT_EVar a)).
  lets: awftyp_forall_evar a H9 H0.
  apply* awftyp_weakening_middle.

  assert (I5: AWfTyp (G & b ~ AC_Marker & a ~ AC_Unsolved_EVar) s2).
  apply* awftyp_weakening.
  apply* awftyp_weakening.

  admit.

  (* PI *)
  inversion H6; subst.
  inversion H7; subst.
  apply DSub_Pi with (L \u L0).
  clear IHASubtyping2.
  rewrite actxtsubst_expr in H2. rewrite actxsubst_pi in H2. inversion H2.
  rewrite actxtsubst_expr in H3. rewrite actxsubst_pi in H3. inversion H3.
  lets: awftyp_pi1 H9.
  lets: awftyp_pi1 H10.
  lets: IHASubtyping1 H18 H13 H8 H21 H12. clear IHASubtyping1 H14 H20 H17 H19.
  admit.

  (* EVARL *)
  admit.

  (* EVARR *)
  admit.

  (* UNIFY *)
  lets: unif_soundness_same H0 H1 H2 H3 H4.
  lets: H11 H5 H6 H7 H8. clear H11.
  lets: awtermt_awftyp H9.
  lets: awtermt_awftyp H10.
  lets: H12 H11 H13.
  rewrite H14. apply DSub_AEq.