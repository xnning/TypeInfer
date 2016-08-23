Require Import CtxExtension.
Require Import LibLN.
Require Import AlgoDef.
Require Import UtilityEnv.
Require Import DeclDef.

Set Implicit Arguments.

Lemma ctxsubst_inv_empty : forall I,
    ACpltCtxSubstCtx empty empty I ->
    I = empty.
Proof.
  intros. inversions H; auto.
  false. apply* empty_push_inv.
  false. apply* empty_push_inv.
  false. apply* empty_push_inv.
  false. apply* empty_push_inv.
  false. apply* empty_push_inv.
  false. apply* empty_push_inv.
Qed.

Lemma ctxsubst_inv_var : forall H G I x,
    ACpltCtxSubstCtx (H & x ~ AC_Var) (G & x ~ AC_Var) I ->
    CompleteCtx H /\
    ACpltCtxSubstCtx H G I.
Proof.
  intros. inversions H0.
  false. apply* empty_push_inv.
  destruct (eq_push_inv H2) as [? [? ?]]; subst.
  destruct (eq_push_inv H3) as [? [? ?]]; subst.
  auto.
  destruct (eq_push_inv H2) as [? [? ?]].
  false.
  destruct (eq_push_inv H2) as [? [? ?]].
  false.
  destruct (eq_push_inv H2) as [? [? ?]].
  false.
  destruct (eq_push_inv H2) as [? [? ?]].
  false.
  destruct (eq_push_inv H2) as [? [? ?]].
  false.
Qed.

Lemma ctxsubst_inv_typvar : forall H G I' x t1 t2,
    ACpltCtxSubstCtx (H & x ~ AC_Typ t1) (G & x ~ AC_Typ t2) I' ->
    exists I t1', (I' = I & x ~ DC_Typ t1' /\
    CompleteCtx H /\ ACpltCtxSubstCtx H G I /\ ACtxSubst H t1 = ACtxSubst H t2 /\
    ACpltCtxSubst H t1 t1').
Proof.
  intros. inversions H0.
  false. apply* empty_push_inv.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  exists I t1'.
  destruct (eq_push_inv H2) as [? [? ?]]; subst.
  destruct (eq_push_inv H3) as [? [? ?]]; subst.
  inversions H8; inversions H1.
  auto.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
Qed.

Lemma ctxsubst_inv_bndvar : forall H G I' x s1 s2 t1 t2,
    ACpltCtxSubstCtx (H & x ~ AC_Bnd s1 t1) (G & x ~ AC_Bnd s2 t2) I' ->
    exists I s1' t1', (I' = I & x ~ DC_Bnd s1' t1' /\
      CompleteCtx H /\ ACpltCtxSubstCtx H G I /\
      ACtxSubst H t1 = ACtxSubst H t2 /\
      ACtxTSubst H s1 = ACtxTSubst H s2 /\
      ACpltCtxSubst H t1 t1' /\
      ACpltCtxTSubst H s1 s1').
Proof.
  intros. inversions H0.
  false. apply* empty_push_inv.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  exists I s1' t1'.
  destruct (eq_push_inv H2) as [? [? ?]]; subst.
  destruct (eq_push_inv H3) as [? [? ?]]; subst.
  inversions H10; inversions H1.
  split*.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
Qed.

Lemma ctxsubst_inv_suevar : forall H G I a t,
    ACpltCtxSubstCtx (H & a ~ AC_Solved_EVar t) (G & a ~ AC_Unsolved_EVar) I ->
    CompleteCtx H /\
    ACpltCtxSubstCtx H G I.
Proof.
  intros. inversions H0.
  false. apply* empty_push_inv.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]].
  false.
  destruct (eq_push_inv H2) as [? [? ?]].
  false.
  destruct (eq_push_inv H2) as [? [? ?]]; subst.
  destruct (eq_push_inv H3) as [? [? ?]]; subst.
  auto.
  destruct (eq_push_inv H3) as [? [? ?]].
  false.
  destruct (eq_push_inv H2) as [? [? ?]]; subst.
  auto.
  false.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_tail.
  apply binds_fresh_inv with (A := ACtxT) (x := a) (v := AC_Unsolved_EVar) (E := G & a ~ AC_Unsolved_EVar).
  auto. auto.
Qed.

Lemma ctxsubst_inv_ssevar : forall H G I t1 t2 a,
    ACpltCtxSubstCtx (H & a ~ AC_Solved_EVar t1) (G & a ~ AC_Solved_EVar t2) I ->
    CompleteCtx H /\
    ACpltCtxSubstCtx H G I /\
    ACtxSubst H t1 = ACtxSubst H t2.
Proof.
  intros. inversions H0.
  false. apply* empty_push_inv.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]].
  false.
  destruct (eq_push_inv H2) as [? [? ?]].
  false.
  destruct (eq_push_inv H3) as [? [? ?]]; false.
  destruct (eq_push_inv H2) as [? [? ?]]; subst.
  destruct (eq_push_inv H3) as [? [? ?]]; subst.
  inversions H1; inversions H7.
  auto.
  destruct (eq_push_inv H2) as [? [? ?]]; subst.
  auto.
  false.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_tail.
  apply binds_fresh_inv with (A := ACtxT) (x := a) (v := AC_Unsolved_EVar) (E := G & a ~ AC_Unsolved_EVar).
  auto. auto.
Qed.

Lemma ctxsubst_inv_sevar : forall H G I t a,
    ACpltCtxSubstCtx (H & a ~ AC_Solved_EVar t) G I ->
    a # G ->
    CompleteCtx H /\
    ACpltCtxSubstCtx H G I.
Proof.
  intros. inversions H0.
  false. apply* empty_push_inv.
  destruct (eq_push_inv H3) as [? [? ?]]. false.
  destruct (eq_push_inv H3) as [? [? ?]]. false.
  destruct (eq_push_inv H3) as [? [? ?]]. false.
  
  destruct (eq_push_inv H3) as [? [? ?]]; subst.
  assert (binds a AC_Unsolved_EVar (G0 & a ~ AC_Unsolved_EVar)).
  apply* binds_tail.
  false.
  apply binds_fresh_inv with (A := ACtxT) (x := a) (v := AC_Unsolved_EVar) (E := G0 & a ~ AC_Unsolved_EVar).
  auto. auto.

  destruct (eq_push_inv H3) as [? [? ?]]; subst.
  assert (binds a AC_Unsolved_EVar (G0 & a ~ AC_Unsolved_EVar)).
  apply* binds_tail.
  false.
  apply binds_fresh_inv with (A := ACtxT) (x := a) (v := AC_Unsolved_EVar) (E := G0 & a ~ AC_Unsolved_EVar).
  auto. auto.

  destruct (eq_push_inv H3) as [? [? ?]]; subst.
  auto.
Qed.

Lemma ctxsubst_inv_uuevar : forall H G I a,
    ACpltCtxSubstCtx (H & a ~ AC_Unsolved_EVar) (G & a ~ AC_Unsolved_EVar) I -> False.
Proof.
  intros. inversions H0.
  false. apply* empty_push_inv.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
Qed.

Lemma cplt_ctxsubst_eq : forall G t1 t2 t2',
    ACpltCtxSubst G t1 t2 ->
    ACpltCtxSubst G t1 t2' ->
    t2 = t2'.
Proof.
  introv Hyp1. gen t2'. inductions Hyp1; introv Hyp2; inversions Hyp2; auto.
  (* FIXME!!! *)
  admit. 
  rewrite -> (IHHyp1_1 d0 H2).
  rewrite -> (IHHyp1_2 d3 H4).
  auto.
  rewrite -> (IHHyp1 d0 H1).
  auto.
  rewrite -> (IHHyp1_1 d0 H2).
  rewrite -> (IHHyp1_2 d3 H4).
  auto.
  rewrite -> (IHHyp1_1 d0 H2).
  rewrite -> (IHHyp1_2 d3 H4).
  auto.
  rewrite -> (IHHyp1 d0 H1).
  auto.
  rewrite -> (IHHyp1 d0 H1).
  auto.
  rewrite -> (IHHyp1_1 d0 H2).
  rewrite -> (IHHyp1_2 d3 H4).
  auto.
Qed.

Lemma cplt_ctxtsubst_eq : forall G t1 t2 t2',
    ACpltCtxTSubst G t1 t2 ->
    ACpltCtxTSubst G t1 t2' ->
    t2 = t2'.
Proof.
  introv Hyp1. gen t2'. inductions Hyp1; introv Hyp2; inversions Hyp2; auto.
  pose (IHHyp1 s3 H1).
  rewrite* e.
  assert (t2 = t3).
  apply* cplt_ctxsubst_eq.
  rewrite* H0.
Qed.

Lemma stable_cplt_env : forall G H I J,
    ExtCtx G H ->
    ACpltCtxSubstCtx H G I ->
    ACpltCtxSubstCtx H H J ->
    I = J.
Proof.
  intros. gen I J. inductions H0; intros.
  pose (ctxsubst_inv_empty H1).
  pose (ctxsubst_inv_empty H2).
  rewrite e. rewrite e0. auto.
  destruct (ctxsubst_inv_var H3) as [_ ?].
  destruct (ctxsubst_inv_var H4) as [_ ?].
  apply* IHExtCtx.
  destruct (ctxsubst_inv_typvar H4) as [I1' [t1' [? [? [? [? ?]]]]]].
  destruct (ctxsubst_inv_typvar H5) as [I2' [t2' [? [? [? [? ?]]]]]].
  pose (cplt_ctxsubst_eq H10 H15).
  pose (IHExtCtx I1' H8 I2' H13).
  rewrite H6.
  rewrite H11.
  rewrite e.
  rewrite e0.
  auto.
  destruct (ctxsubst_inv_bndvar H5) as [I1' [s1' [t1' [? [? [? [? [? [? ?]]]]]]]]].
  destruct (ctxsubst_inv_bndvar H6) as [I2' [s2' [t2' [? [? [? [? [? [? ?]]]]]]]]].
  pose (IHExtCtx I1' H9 I2' H16).
  pose (cplt_ctxsubst_eq H12 H19).
  pose (cplt_ctxtsubst_eq H13 H20).
  rewrite H7. rewrite H14. rewrite e; rewrite e0; rewrite e1. auto.
  false. pose (ctxsubst_inv_uuevar H3). auto.
  destruct (ctxsubst_inv_ssevar H4) as [? [? ?]].
  destruct (ctxsubst_inv_ssevar H5) as [? [? ?]].
  apply* IHExtCtx.
  destruct (ctxsubst_inv_suevar H3) as [? ?].
  destruct (ctxsubst_inv_ssevar H4) as [? [? ?]].
  apply* IHExtCtx.
  false. pose (ctxsubst_inv_uuevar H3). auto.
  (* FIXME!!! *)
  assert (a # G). admit.
  destruct (ctxsubst_inv_sevar H2 H4) as [? ?].
  destruct (ctxsubst_inv_ssevar H3) as [? [? ?]].
  apply* IHExtCtx.
Qed.

