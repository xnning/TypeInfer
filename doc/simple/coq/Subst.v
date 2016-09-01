Require Import CtxExtension.
Require Import LibLN.
Require Import AlgoDef.
Require Import UtilityEnv.
Require Import DeclDef.
Require Import AlgoInfra.
Require Import LibReflect.

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
  destruct (ok_middle_eq H6 eq_refl H1 eq_refl H2) as [? [? ?]].
  inversions H8; subst.
  apply* IHHyp1.
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

Lemma stable_cplt_env_eq : forall G H I J,
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
  assert (a # G). 
  assert (a # H).
  assert (ok (H & a ~ AC_Solved_EVar t)).
  apply* awf_is_ok.
  destruct~ (ok_push_inv H4) as [_ ?].
  apply* declaration_preservation_inv.
  destruct (ctxsubst_inv_sevar H2 H4) as [? ?].
  destruct (ctxsubst_inv_ssevar H3) as [? [? ?]].
  apply* IHExtCtx.
Qed.

Hint Constructors ACpltCtxSubst.

Lemma complete_contains_unsolved: forall G a,
    CompleteCtx G ->
    binds a AC_Unsolved_EVar G ->
    False.
Proof.
  intros. unfold CompleteCtx in H. apply H in H0. apply* H0.
Qed.

Lemma complete_empty: CompleteCtx empty.
Proof.
  unfold CompleteCtx. intros.
  false (binds_empty_inv H).
Qed.

Lemma complete_part_right: forall G1 G2,
    CompleteCtx (G1 & G2) ->
    CompleteCtx G2.
Proof.
  unfold CompleteCtx.
  introv cm bd.
  assert (binds x v (G1 & G2)) by apply* binds_concat_right.
  unfold not. intros.
  false (cm x v H H0).
Qed.

Lemma complete_part_left: forall G1 G2,
    ok (G1 & G2) ->
    CompleteCtx (G1 & G2) ->
    CompleteCtx G1.
Proof.
  unfold CompleteCtx.
  introv ok cm bd.
  assert (binds x v (G1 & G2)). apply* binds_concat_left_ok.
  unfold not. intros.
  false (cm x v H H0).
Qed.


Lemma eq_aexpr_dec : forall (T T' : AExpr),
  sumbool (T = T') (T <> T').
Proof.
  decide equality.
  decide equality.
  apply* eq_var_dec.
  apply* eq_var_dec.
Qed.

Lemma eq_atype_dec : forall (T T' : AType),
  sumbool (T = T') (T <> T').
Proof.
  decide equality.
  apply* eq_aexpr_dec.
Qed.

Lemma eq_actx_dec : forall (T T' : ACtxT),
  sumbool (T = T') (T <> T').
Proof.
  decide equality.
  apply* eq_aexpr_dec.
  apply* eq_aexpr_dec.
  apply* eq_atype_dec.
  apply* eq_aexpr_dec.
Qed.
  
Lemma cplt_ctx_weaken : forall G x v,
    CompleteCtx (G & x ~ v) ->
    x # G ->
    CompleteCtx G.
Proof.
  unfold CompleteCtx.
  intros.
  apply (H x0 v0).
  destruct (eq_var_dec x x0); subst.
  false. apply (binds_fresh_inv H1 H0).
  apply* binds_concat_left.
Qed.
  
Lemma confluence_cplt : forall G1 G2 H I J K,
    ExtCtx G1 H -> ExtCtx G2 H ->
    ACpltCtxSubstCtx H G1 I ->
    ACpltCtxSubstCtx H G2 J ->
    ACpltCtxSubstCtx H H K ->
    I = J.
Proof.
  intros.
  assert (I = K).
  intros. apply stable_cplt_env_eq with (G := G1) (H := H).
  auto. auto. auto.
  assert (J = K).
  intros. apply stable_cplt_env_eq with (G := G2) (H := H).
  auto. auto. auto.
  subst. auto.
Qed.   




Lemma ctxsubst_fvar_eq : forall G x v,
    ok G ->
    (forall a1 a2, v <> AC_Bnd a1 a2) ->
    (forall a, v <> AC_Solved_EVar a) ->
    (binds x v G \/ x # G) ->
    ACtxSubst G (AE_FVar x) = AE_FVar x.
Proof.
  introv H NBnd NEvar H1. inductions H.
  rewrite* subst_empty_env.
  inductions v0.
  rewrite~ subst_add_var.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ subst_add_typvar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ subst_add_bndvar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  false. simpl. case_var~.
  rewrite dom_single in NIn.
  false. apply* notin_same.
  simpl. case_var~.
  false. rewrite dom_push in Frh.
  apply* notin_same.

  rewrite~ subst_add_evar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ subst_add_solved_evar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  false. simpl. case_var~.
  rewrite dom_single in NIn.
  false. apply* notin_same.
  simpl. case_var~.
  false. rewrite dom_push in Frh.
  apply* notin_same.
Qed.

Lemma ctxsubst_evar_eq : forall G x,
    ok G ->
    (binds x AC_Unsolved_EVar G \/ x # G) ->
    ACtxSubst G (AE_EVar x) = AE_EVar x.
Proof.
  introv H H1. inductions H.
  rewrite* subst_empty_env.
  inductions v.
  rewrite~ subst_add_var.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ subst_add_typvar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ subst_add_bndvar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  false. simpl. case_var~.
  rewrite dom_single in NIn.
  false. apply* notin_same.
  simpl. case_var~.
  false. rewrite dom_push in Frh.
  apply* notin_same.

  rewrite~ subst_add_evar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ subst_add_solved_evar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  false. simpl. case_var~.
  rewrite dom_single in NIn.
  false. apply* notin_same.
  simpl. case_var~.
  false. rewrite dom_push in Frh.
  apply* notin_same.
Qed.

Lemma ctxsubst_awterm : forall G t,
    ok G ->
    AWTerm G t ->
    AWTerm G (ACtxSubst G t).
Proof.
  introv Ok Hyp. 
  inductions Hyp.
  assert (ACtxSubst G (AE_FVar x) = AE_FVar x).
  apply* ctxsubst_fvar_eq. 
  unfold not; intros. inversions H0.
  unfold not; intros. inversions H0.
  rewrite H0.
  apply* AWTerm_Var.
  
  assert (ACtxSubst G (AE_FVar x) = AE_FVar x).
  apply* ctxsubst_fvar_eq.
  unfold not; intros. inversions H0.
  unfold not; intros. inversions H0.
  rewrite H0.
  apply* AWTerm_TypVar.
  
  inductions Ok.
  false. apply* binds_empty_inv.
  inductions v.
  rewrite~ subst_add_var.
  destruct (binds_concat_inv H0) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  false. apply* awterm_weaken.
  rewrite~ subst_add_typvar.
  destruct (binds_concat_inv H0) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  false. apply* awterm_weaken.
  rewrite~ subst_add_bndvar.
  destruct (binds_concat_inv H0) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  inversions Eq2.
  simpl. case_var~.
  apply* awterm_weaken.
  (* FIXME: AWTerm E (ACtxSubst E a0) *) admit.
  simpl. case_var~.
  rewrite dom_single in NIn.
  false. apply* notin_same.
  apply* awterm_weaken.
  rewrite~ subst_add_evar.
  destruct (binds_concat_inv H0) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  false. apply* awterm_weaken.
  rewrite~ subst_add_solved_evar.
  destruct (binds_concat_inv H0) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  false. simpl. case_var~. false.
  rewrite dom_single in NIn.
  false. apply* notin_same.
  apply* awterm_weaken.

  assert (ACtxSubst G (AE_EVar a) = AE_EVar a).
  apply* ctxsubst_evar_eq.
  unfold not; intros.
  rewrite H0.
  apply* AWTerm_EVar.

  inductions Ok.
  false. apply* binds_empty_inv.
  inductions v.
  rewrite~ subst_add_var.
  destruct (binds_concat_inv H0) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  false. apply* awterm_weaken.
  rewrite~ subst_add_typvar.
  destruct (binds_concat_inv H0) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  false. apply* awterm_weaken.
  rewrite~ subst_add_bndvar.
  destruct (binds_concat_inv H0) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  false. simpl. case_var~. false.
  rewrite dom_single in NIn.
  false. apply* notin_same.
  apply* awterm_weaken.
  rewrite~ subst_add_evar.
  destruct (binds_concat_inv H0) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  false. apply* awterm_weaken.
  rewrite~ subst_add_solved_evar.
  destruct (binds_concat_inv H0) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  inversions Eq2.
  simpl. case_var~.
  apply* awterm_weaken.
  (* FIXME: AWTerm E (ACtxSubst E a) *) admit.
  simpl. case_var~.
  rewrite dom_single in NIn.
  false. apply* notin_same.
  apply* awterm_weaken.

  rewrite~ subst_star.
Admitted.

Lemma finishing_types : forall G G' t,
    AWTerm G t ->
    ExtCtx G G' ->
    ACtxSubst G t = ACtxSubst G' t.
Proof.
Admitted.


(* another form of awterm, which does not care about bound variables *)

Inductive AWTermA : ACtx -> AExpr -> Prop :=
  | AWTermA_Var : forall G x, binds x AC_Var G -> AWTermA G (AE_FVar x)
  | AWTermA_BVar : forall G x, AWTermA G (AE_BVar x)
  | AWTermA_TypVar : forall G x t, binds x (AC_Typ t) G -> AWTermA G (AE_FVar x)
  | AWTermA_LetVar : forall G x t e, binds x (AC_Bnd t e) G -> AWTermA G (AE_FVar x)
  | AWTermA_EVar : forall G a, binds a AC_Unsolved_EVar G -> AWTermA G (AE_EVar a)
  | AWTermA_Solved_EVar : forall G a t, binds a (AC_Solved_EVar t) G -> AWTermA G (AE_EVar a)
  | AWTermA_Star: forall G, AWTermA G AE_Star
  | AWTermA_App: forall e1 e2 G, AWTermA G e1 -> AWTermA G e2 -> AWTermA G (AE_App e1 e2)
  | AWTermA_Lam: forall e G , AWTermA G e  -> AWTermA G (AE_Lam e)
  | AWTermA_Pi: forall t1 t2 G, AWTermA G t1 -> AWTermA G t2 -> AWTermA G (AE_Pi t1 t2)
  | AWTermA_Let: forall e1 e2 G, AWTermA G e1 -> AWTermA G e2 -> AWTermA G (AE_Let e1 e2)
  | AWTermA_CastUp : forall e G, AWTermA G e -> AWTermA G (AE_CastUp e)
  | AWTermA_CastDn : forall e G, AWTermA G e -> AWTermA G (AE_CastDn e)
  | AWTermA_Ann: forall e1 e2 G, AWTermA G e1 -> AWTermA G e2 -> AWTermA G (AE_Ann e1 e2)
.

(* helper lemmas *)
Hint Constructors AWTermA ACpltCtxSubst.
Lemma awterma_open: forall G k u e,
    AWTermA G (AOpenRec k u e) ->
    AWTermA G e.
Proof.
  introv wt. gen k u. induction e; intros; simpls; auto_star;
  try(inversion wt; subst; auto_star).
Qed.

Lemma awterma_remove: forall G H e y v,
    AWTermA (G & y ~ v & H) e ->
    y \notin AFv e ->
    AWTermA (G & H) e.
Proof.
  introv wt notin. gen_eq I: (G & y ~ v & H).
  gen H. induction wt; introv hh; auto_star.
  simpl in notin. rewrite hh in H. apply AWTermA_Var. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTermA_TypVar. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTermA_LetVar. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTermA_EVar. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTermA_Solved_EVar. apply* binds_subst.

  simpl in notin. apply AWTermA_App. apply* IHwt1. apply* IHwt2.

  simpl in notin. apply AWTermA_Pi. apply* IHwt1. apply* IHwt2.
  simpl in notin. apply AWTermA_Let. apply* IHwt1. apply* IHwt2.
  simpl in notin. apply AWTermA_Ann. apply* IHwt1. apply* IHwt2.
Qed.

Lemma awterma_remove_empty: forall G e y v,
    AWTermA (G & y ~ v) e ->
    y \notin AFv e ->
    AWTermA G e.
Proof.
  intros. assert (AWTermA (G & y ~ v & empty) e). rewrite* concat_empty_r.
  assert (AWTermA (G & empty) e). apply* awterma_remove.
  rewrite concat_empty_r in H2. auto.
Qed.

Lemma cpltctxsubst_append: forall G1 G2 t e,
    AWf (G1 & G2) ->
    CompleteCtx (G1 & G2) ->
    AWTermA G1 t ->
    ACpltCtxSubst G1 t e ->
    ACpltCtxSubst (G1 & G2) t e.
Proof.
  introv wf comp wt sub.
  gen e. induction t; introv sub; inversion sub; subst; auto.
  auto.
  apply* ACpltCtxSubst_FVar. apply* binds_concat_left_ok. apply* awf_is_ok.
  rewrite <- concat_assoc. apply* ACpltCtxSubst_EVar. rewrite <- concat_assoc in comp. apply* complete_part_right. rewrite concat_assoc. apply* awf_is_ok.

  inversion wt; subst. apply* ACpltCtxSubst_App.
  inversion wt; subst. apply* ACpltCtxSubst_Lam.
  inversion wt; subst. apply* ACpltCtxSubst_Pi.
  inversion wt; subst. apply* ACpltCtxSubst_Let.
  inversion wt; subst. apply* ACpltCtxSubst_CastUp.
  inversion wt; subst. apply* ACpltCtxSubst_CastDn.
  inversion wt; subst. apply* ACpltCtxSubst_Ann.
Qed.

Lemma cpltctxsubst_solved_weaken: forall G1 G2 t e,
    AWf (G1 & G2) ->
    CompleteCtx (G1 & G2) ->
    AWTermA G1 t ->
    ACpltCtxSubst (G1 & G2) t e ->
    ACpltCtxSubst G1 t e.
Proof.
  introv wf comp wt sub.
  gen e. induction t; introv sub; inversion sub; subst; auto.
  apply ACpltCtxSubst_BVar. apply* complete_part_left. apply* awf_is_ok.
  inversion wt; subst;
  apply* ACpltCtxSubst_FVar; apply* complete_part_left; apply* awf_is_ok.

  inversion wt; subst.
  assert (CompleteCtx G1). apply* complete_part_left. apply* awf_is_ok.
  false complete_contains_unsolved H0 H6.
  destruct (split_bind_context H6) as (G11 & G12 & HG).
  subst.
  assert (G0 & v ~ AC_Solved_EVar t & G3 = G11 & v ~ AC_Solved_EVar t0 & (G12 & G2)). rewrite* concat_assoc.
  apply ok_middle_eq with  (I1:=G0) (I2:=G3) (G1:=G11) (G4:=(G12&G2)) (x:=v) (v1:=AC_Solved_EVar t) (v2:=AC_Solved_EVar t0) in H0; auto.
  destruct H0 as [eqg [eqv eqg2]]. inversion eqv. subst.
  apply ACpltCtxSubst_EVar; auto. apply* complete_part_left.
  apply* awf_is_ok. apply* AWf_left.
  rewrite H0 in H3.  auto.

  inversion wt; subst. apply* ACpltCtxSubst_App.
  inversion wt; subst. apply* ACpltCtxSubst_Lam.
  inversion wt; subst. apply* ACpltCtxSubst_Pi.
  inversion wt; subst. apply* ACpltCtxSubst_Let.
  inversion wt; subst. apply* ACpltCtxSubst_CastUp.
  inversion wt; subst. apply* ACpltCtxSubst_CastDn.
  inversion wt; subst. apply* ACpltCtxSubst_Ann.
Qed.

(* one important one, changes from awterm to awterma *)

Theorem awterm_is_awterma: forall G e,
    AWTerm G e ->
    AWTermA G e.
Proof.
  introv wt. induction wt; auto_star.
  pick_fresh y. assert (AWTermA (G & y ~ AC_Var) (e @ y)).
  apply H0. auto_star. apply awterma_open in H1. apply awterma_remove_empty in H1. constructor*. auto_star.
  constructor*. pick_fresh y. assert (AWTermA (G & y ~ AC_Var) (t2 @ y)).
  apply H0. auto_star. apply awterma_open in H1. apply awterma_remove_empty in H1. auto_star. auto_star.
  constructor*. pick_fresh y. assert (AWTermA (G & y ~ AC_Var) (e2 @ y)).
  apply H0. auto_star. apply awterma_open in H1. apply awterma_remove_empty in H1. auto_star. auto_star.
Qed.


(* a definition about length of a expression.
( in order to make all the expression has length,
( there are many meaningless definition,
( which ends with `I` *)

Inductive ALen : ACtx -> AExpr -> nat -> Prop :=
| ALen_BVar: forall G i, ALen G (AE_BVar i) 1
| ALen_Var: forall G x, binds x AC_Var G -> ALen G (AE_FVar x) 1
| ALen_TypVar: forall G x t, binds x (AC_Typ t) G -> ALen G (AE_FVar x) 1
| ALen_LetVar : forall G x t e i, binds x (AC_Bnd t e) G -> ALen G e i -> ALen G (AE_FVar x) (i + 1)
| ALen_Var_I1 : forall G x, binds x AC_Unsolved_EVar G -> ALen G (AE_FVar x) 1
| ALen_Var_I2 : forall G x t, binds x (AC_Solved_EVar t) G -> ALen G (AE_FVar x) 1
| ALen_Var_I : forall G x, x # G -> ALen G (AE_FVar x) 1
| ALen_EVar : forall G a, binds a AC_Unsolved_EVar G -> ALen G (AE_EVar a) 1
| ALen_EVar_I1: forall G x, binds x AC_Var G -> ALen G (AE_EVar x) 1
| ALen_EVar_I2: forall G x t, binds x (AC_Typ t) G -> ALen G (AE_EVar x) 1
| ALen_EVar_I3: forall G x t e, binds x (AC_Bnd t e) G -> ALen G (AE_EVar x) 1
| ALen_Solved_EVar: forall G a t i, binds a (AC_Solved_EVar t) G -> ALen G t i -> ALen G (AE_EVar a) (i + 1)
| ALen_EVar_I : forall G a, a # G -> ALen G (AE_EVar a) 1
| ALen_Star: forall G, ALen G (AE_Star) 1
| ALen_App: forall e1 e2 G i1 i2, ALen G e1 i1 -> ALen G e2 i2 -> ALen G (AE_App e1 e2) (i1 + i2 + 1)
| ALen_Lam: forall e G i, ALen G e i -> ALen G (AE_Lam e) (i + 1)
| ALen_Pi: forall e1 e2 G i1 i2, ALen G e1 i1 -> ALen G e2 i2 -> ALen G (AE_Pi e1 e2) (i1 + i2 + 1)
| ALen_Let: forall e1 e2 G i1 i2, ALen G e1 i1 -> ALen G e2 i2 -> ALen G (AE_Let e1 e2) (i1 + i2 + 1)
| ALen_CastUp:  forall e G i, ALen G e i -> ALen G (AE_CastUp e) (i + 1)
| ALen_CastDn:  forall e G i, ALen G e i -> ALen G (AE_CastDn e) (i + 1)
| ALen_Ann: forall e1 e2 G i1 i2, ALen G e1 i1 -> ALen G e2 i2 -> ALen G (AE_Ann e1 e2) (i1 + i2 + 1).

Hint Constructors ALen.

(* some lemmas about alen *)

Lemma alen_awterm_append: forall G H e n,
    AWf (G & H) ->
    AWTermA G e ->
    ALen G e n ->
    ALen (G & H) e n.
Proof.
  introv wf wt len.
  induction len.
  auto.
  apply ALen_Var. apply* binds_concat_left_ok. apply* awf_is_ok.
  apply ALen_TypVar with t. apply* binds_concat_left_ok. apply* awf_is_ok.
  apply* ALen_LetVar. apply* binds_concat_left_ok. apply* awf_is_ok. apply* IHlen. destruct (split_bind_context H0) as (G1 & G2 & Hg). rewrite Hg in wf.
  assert (AWTerm G1 e).
  rewrite <- concat_assoc in wf. apply AWf_left in wf. apply* awterm_bnd.
  rewrite Hg. rewrite <- concat_assoc. apply* awterm_is_awterma. apply* awterm_weaken_ctx.
  rewrite concat_assoc. apply AWf_left in wf. apply* awf_is_ok.

  apply* ALen_Var_I1. apply* binds_concat_left_ok. apply* awf_is_ok.
  apply* ALen_Var_I2. apply* binds_concat_left_ok. apply* awf_is_ok.
  inversion wt; subst; try(solve[false binds_fresh_inv H3 H0]).

  apply* ALen_EVar. apply* binds_concat_left_ok. apply* awf_is_ok.
  apply* ALen_EVar_I1. apply* binds_concat_left_ok. apply* awf_is_ok.
  apply* ALen_EVar_I2. apply* binds_concat_left_ok. apply* awf_is_ok.
  apply* ALen_EVar_I3. apply* binds_concat_left_ok. apply* awf_is_ok.

  apply* ALen_Solved_EVar. apply* binds_concat_left_ok. apply* awf_is_ok. apply* IHlen. destruct (split_bind_context H0) as (G1 & G2 & Hg). rewrite Hg in wf.
  assert (AWTerm G1 t).
  rewrite <- concat_assoc in wf. apply AWf_left in wf. apply* awterm_solved_evar.
  rewrite Hg. rewrite <- concat_assoc. apply* awterm_is_awterma. apply* awterm_weaken_ctx.
  rewrite concat_assoc. apply AWf_left in wf. apply* awf_is_ok.

  inversion wt; subst; try(solve[false binds_fresh_inv H3 H0]).

  apply* ALen_Star.
  inversion wt; subst.
  apply* ALen_App.
  inversion wt; subst. apply* ALen_Lam.
  inversion wt; subst. apply* ALen_Pi.
  inversion wt; subst. apply* ALen_Let.
  inversion wt; subst. apply* ALen_CastUp.
  inversion wt; subst. apply* ALen_CastDn.
  inversion wt; subst. apply* ALen_Ann.
Qed.


Lemma alen_exists': forall n G e,
    AWf G ->
    LibList.length G < n ->
    exists m, ALen G e m.
Proof.
  intro n. induction n as [|n']; introv okg len.
  false. inversion len.
  induction e.
  exists* 1.
  assert ({v \in dom G}+{v \notin dom G}). apply* decidable_sumbool. apply indom_decidable.
  destruct H as [hin | hnotin].
  (* in *)
  assert (exists vx, binds v vx G) by apply* get_some.
  destruct H as (vx & H). destruct vx; auto_star.
  destruct (split_bind_context H) as (G1 & G2 & IG).
  assert (exists n, ALen G1 a0 n). apply~ IHn'.

  rewrite IG in okg. rewrite <- concat_assoc in okg. apply* AWf_left.

  rewrite IG in len.
  rewrite concat_def in len. repeat(rewrite LibList.length_app in len).
  assert(LibList.length (v~ AC_Bnd a a0) = 1). rewrite single_def. rewrite LibList.length_cons. rewrite LibList.length_nil. Omega.omega.
  Omega.omega.

  destruct H0 as (n & H0). exists* (n + 1). apply ALen_LetVar with a a0; auto.

  rewrite <- concat_assoc in IG. rewrite IG. apply* alen_awterm_append. rewrite* <- IG. apply awterm_is_awterma. rewrite IG in okg. rewrite concat_assoc in okg. apply AWf_left in okg. apply* awterm_bnd.

  (* notin *)
  exists* 1.

  assert ({v \in dom G}+{v \notin dom G}). apply* decidable_sumbool. apply indom_decidable.
  destruct H as [hin | hnotin].
  (* in *)
  assert (exists vx, binds v vx G) by apply* get_some.
  destruct H as (vx & H). destruct vx; auto_star.
  destruct (split_bind_context H) as (G1 & G2 & IG).
  assert (exists n, ALen G1 a n). apply~ IHn'.
  rewrite IG in okg. rewrite <- concat_assoc in okg. apply* AWf_left.

  rewrite IG in len.
  rewrite concat_def in len. repeat(rewrite LibList.length_app in len).
  assert(LibList.length (v~ AC_Solved_EVar a) = 1). rewrite single_def. rewrite LibList.length_cons. rewrite LibList.length_nil. Omega.omega.
  Omega.omega.
  destruct H0 as (ne & H0). exists (ne + 1). apply ALen_Solved_EVar with a; auto.

  rewrite <- concat_assoc in IG. rewrite IG. apply* alen_awterm_append. rewrite* <- IG. apply awterm_is_awterma. rewrite IG in okg. rewrite concat_assoc in okg. apply AWf_left in okg. apply* awterm_solved_evar.

  (* notin *)
  exists* 1.

  exists* 1.

  destruct IHe1 as (n1 & IHe1). destruct IHe2 as (n2 & IHe2). exists* (n1 + n2 + 1).
  destruct IHe as (n & IHe1). exists* (n + 1).
  destruct IHe1 as (n1 & IHe1). destruct IHe2 as (n2 & IHe2). exists* (n1 + n2 + 1).
  destruct IHe1 as (n1 & IHe1). destruct IHe2 as (n2 & IHe2). exists* (n1 + n2 + 1).
  destruct IHe as (n & IHe1). exists* (n + 1).
  destruct IHe as (n & IHe1). exists* (n + 1).
  destruct IHe1 as (n1 & IHe1). destruct IHe2 as (n2 & IHe2). exists* (n1 + n2 + 1).
Qed.

Lemma alen_exists: forall G e,
    AWf G ->
    exists n, ALen G e n.
Proof.
  introv wf.
  apply* alen_exists'.
Qed.

Lemma alen_eq: forall G e i1 i2,
    ALen G e i1 ->
    ALen G e i2 ->
    i1 = i2.
Proof.
  introv hy1. gen i2. induction hy1; introv hy2; inversion hy2; subst; auto;
  try(solve[apply (binds_func H) in H1; inversion H1]);
  try(solve[apply (binds_func H) in H2; inversion H2]).
  lets: binds_func H H1. inversion H0; subst. lets: IHhy1 i0 H3. subst*.
  false binds_fresh_inv H H2.
  false binds_fresh_inv H1 H.
  lets: binds_func H H1. inversion H0; subst. lets: IHhy1 i0 H3. subst*.
  false binds_fresh_inv H H2.
  false binds_fresh_inv H1 H.
Qed.

Lemma alen_evar: forall G a t m n,
    AWf G ->
    binds a (AC_Solved_EVar t) G ->
    ALen G (AE_EVar a) n ->
    ALen G t m ->
    n = m + 1.
Proof.
  introv wf bd lenn lenm.
  inversion lenn; subst.
  apply (binds_func H1) in bd; inversion bd.
  apply (binds_func H1) in bd; inversion bd.
  apply (binds_func H1) in bd; inversion bd.
  apply (binds_func H1) in bd; inversion bd.
  apply (binds_func bd) in H0; inversion H0; subst.
  lets: alen_eq H2 lenm. subst*.
  false binds_fresh_inv bd H1.
Qed.

(* begin the main proofs *)

Theorem cpltctxsubst_exists': forall G e n m,
    AWf G ->
    n < m ->
    ALen G e n ->
    AWTermA G e ->
    CompleteCtx G ->
    exists t, ACpltCtxSubst G e t
.
Proof.
  intros. gen G e n. induction m; introv wt comp wf less len .
  inversion less.
  induction wf; simpls; auto_star.
  false (complete_contains_unsolved comp H).
  assert (exists e, ACpltCtxSubst G t e).
     destruct(@alen_exists G t) as (nt & ex). auto.
     apply IHm with nt; auto. apply awterm_is_awterma.
     apply* awterm_evar_binds.
     lets: alen_evar wt H len ex. rewrite H0 in less. Omega.omega.

  destruct H0 as (et & H0).
  exists et. destruct (split_bind_context H) as (G1 & G2 & HG). rewrite HG.
  apply ACpltCtxSubst_EVar.
  rewrite HG in comp. rewrite <- concat_assoc in comp. apply* complete_part_left. rewrite concat_assoc. rewrite HG in wt. apply* awf_is_ok.
  rewrite HG in comp. apply* complete_part_right. rewrite HG in wt. apply* awf_is_ok.

  apply* cpltctxsubst_solved_weaken. rewrite HG in wt. rewrite <- concat_assoc in wt. exact wt.
  rewrite HG in comp. rewrite <- concat_assoc in comp. exact comp.
  apply* awterm_is_awterma.
  apply* awterm_solved_evar. rewrite HG in wt. apply AWf_left in wt. exact wt. rewrite concat_assoc. rewrite HG in H0. assumption.

  destruct(@alen_exists G e1) as (ne1 & ex1). auto. assert (exists t1, ACpltCtxSubst G e1 t1). apply* IHm.
  inversion len; subst. lets: alen_eq H2 ex1. Omega.omega.
  destruct H as (t1 & Ht1).
  destruct(@alen_exists G e2) as (ne2 & ex2). auto.
  assert (exists t2, ACpltCtxSubst G e2 t2). apply* IHm.
  inversion len; subst. lets: alen_eq H4 ex2. Omega.omega.
  destruct H as (t2 & Ht2).
  exists* (DE_App t1 t2).

  assert (exists t, ACpltCtxSubst G e t).
    destruct(@alen_exists G e) as (ne & ex). auto. apply IHm with ne; auto.
  inversion len; subst. lets: alen_eq H1 ex. Omega.omega.
  destruct H as (et & H).
  exists* (DE_Lam et).

  destruct(@alen_exists G t1) as (nt1 & ex1). auto.
  assert (exists e1, ACpltCtxSubst G t1 e1). apply* IHm.
  inversion len; subst. lets: alen_eq H2 ex1. Omega.omega.
  destruct H as (e1 & Ht1).
  destruct(@alen_exists G t2) as (ne2 & ex2). auto.
  assert (exists e2, ACpltCtxSubst G t2 e2). apply* IHm.
  inversion len; subst. lets: alen_eq H4 ex2. Omega.omega.
  destruct H as (e2 & Ht2).
  exists* (DE_Pi e1 e2).

  destruct(@alen_exists G e1) as (ne1 & ex1). auto. assert (exists t1, ACpltCtxSubst G e1 t1). apply* IHm.
  inversion len; subst. lets: alen_eq H2 ex1. Omega.omega.
  destruct H as (t1 & Ht1).
  destruct(@alen_exists G e2) as (ne2 & ex2). auto.
  assert (exists t2, ACpltCtxSubst G e2 t2). apply* IHm.
  inversion len; subst. lets: alen_eq H4 ex2. Omega.omega.
  destruct H as (t2 & Ht2).
  exists* (DE_Let t1 t2).

  assert (exists t, ACpltCtxSubst G e t).
    destruct(@alen_exists G e) as (ne & ex). auto. apply IHm with ne; auto.
  inversion len; subst. lets: alen_eq H1 ex. Omega.omega.
  destruct H as (et & H).
  exists* (DE_CastUp et).

  assert (exists t, ACpltCtxSubst G e t).
    destruct(@alen_exists G e) as (ne & ex). auto. apply IHm with ne; auto.
  inversion len; subst. lets: alen_eq H1 ex. Omega.omega.
  destruct H as (et & H).
  exists* (DE_CastDn et).

  destruct(@alen_exists G e1) as (ne1 & ex1). auto. assert (exists t1, ACpltCtxSubst G e1 t1). apply* IHm.
  inversion len; subst. lets: alen_eq H2 ex1. Omega.omega.
  destruct H as (t1 & Ht1).
  destruct(@alen_exists G e2) as (ne2 & ex2). auto.
  assert (exists t2, ACpltCtxSubst G e2 t2). apply* IHm.
  inversion len; subst. lets: alen_eq H4 ex2. Omega.omega.
  destruct H as (t2 & Ht2).
  exists* (DE_Ann t1 t2).
Qed.

Theorem cpltctxsubst_exists: forall G e,
    AWf G ->
    AWTerm G e ->
    CompleteCtx G ->
    exists t, ACpltCtxSubst G e t
.
Proof.
  intros. destruct(@alen_exists G e) as (n & ex). auto. apply* cpltctxsubst_exists'.
  apply* awterm_is_awterma.
Qed.