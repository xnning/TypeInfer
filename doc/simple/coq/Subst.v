Require Import CtxExtension.
Require Import LibLN.
Require Import AlgoDef.
Require Import UtilityEnv.
Require Import DeclDef.

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

Lemma stable_cplt_env : forall G H I J,
    ExtCtx G H ->
    ACpltCtxSubstCtx H G I ->
    ACpltCtxSubstCtx H H J ->
    I = J.
Proof.
  intros. inductions H0.
  pose (ctxsubst_inv_empty I H1).
  pose (ctxsubst_inv_empty J H2).
  rewrite e. rewrite e0. auto.
  destruct (ctxsubst_inv_var H G I x H3) as [_ ?].
  destruct (ctxsubst_inv_var H H J x H4) as [_ ?].
  apply* IHExtCtx.
  destruct (ctxsubst_inv_typvar H G I x t2 t1 H4) as [I1' [t1' [? [_ [? ?]]]]].
Admitted.
  