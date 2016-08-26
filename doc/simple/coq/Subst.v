Require Import CtxExtension.
Require Import LibLN.
Require Import AlgoDef.
Require Import UtilityEnv.
Require Import DeclDef.
Require Import AlgoInfra.

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

Lemma binds_push_fresh : forall A x v (G : env A) x' v',
    binds x v G -> x' # G ->
    binds x v (G & x' ~ v').
Proof.
  intros. apply* binds_push_neq.
  unfold not; intros. rewrite <- H1 in H0.
  apply binds_fresh_inv with (x := x) (v := v) (E := G).
  auto. auto.
Qed.

Lemma binds_swap : forall A (G1 G2 : env A) x v x1 v1 x2 v2,
    x1 <> x2 ->
    binds x v (G1 & x1 ~ v1 & x2 ~ v2 & G2) ->
    binds x v (G1 & x2 ~ v2 & x1 ~ v1 & G2).
Proof.
  intros.
  destruct (binds_concat_inv H0) as [Bnd1 | [Frsh Bnd2]].
  apply* binds_concat_right.
  destruct (binds_push_inv Bnd2) as [[Eq1 Eq2] | [NEeq Bnd]]; subst.
  apply* binds_concat_left.
  destruct (binds_push_inv Bnd) as [[Eq1' Eq2'] | [NEeq' Bnd']]; subst.
  apply* binds_concat_left.
  apply* binds_concat_left.
Qed.

Lemma awterm_reorder : forall G1 G2 x1 x2 v e,
    x1 <> x2 ->
    AWTerm (G1 & x2 ~ AC_Var & x1 ~ v & G2) e ->
    AWTerm (G1 & x1 ~ v & x2 ~ AC_Var & G2) e.
Proof.
  intros. inductions H0.
  apply* AWTerm_Var. apply* binds_swap.
  apply* AWTerm_TypVar. apply* binds_swap.
  apply* AWTerm_LetVar. apply* binds_swap.
  apply* AWTerm_EVar. apply* binds_swap.
  apply* AWTerm_Solved_EVar. apply* binds_swap.
  apply* AWTerm_Star.
  apply* AWTerm_App.

  apply AWTerm_Lam with (L := L); intros.
  assert (JMeq.JMeq (G1 & x2 ~ AC_Var & x1 ~ v & G2 & x ~ AC_Var)
                    (G1 & x2 ~ AC_Var & x1 ~ v & (G2 & x ~ AC_Var))).
  rewrite -> concat_assoc. auto.
  pose (Re := H0 x H2 v x2 x1 H (G2 & x ~ AC_Var) G1 H3).
  rewrite -> concat_assoc in Re.
  auto.

  apply AWTerm_Pi with (L := L). auto. intros.
  assert (JMeq.JMeq (G1 & x2 ~ AC_Var & x1 ~ v & G2 & x ~ AC_Var)
                    (G1 & x2 ~ AC_Var & x1 ~ v & (G2 & x ~ AC_Var))).
  rewrite -> concat_assoc. auto.
  pose (Re := H1 x H3 v x2 x1 H (G2 & x ~ AC_Var) G1 H4).
  rewrite -> concat_assoc in Re.
  auto.

  apply AWTerm_Let with (L := L). auto. intros.
  assert (JMeq.JMeq (G1 & x2 ~ AC_Var & x1 ~ v & G2 & x ~ AC_Var)
                    (G1 & x2 ~ AC_Var & x1 ~ v & (G2 & x ~ AC_Var))).
  rewrite -> concat_assoc. auto.
  pose (Re := H1 x H3 v x2 x1 H (G2 & x ~ AC_Var) G1 H4).
  rewrite -> concat_assoc in Re.
  auto.

  apply* AWTerm_CastUp.
  apply* AWTerm_CastDn.
  apply* AWTerm_Ann.
Qed.

Lemma awterm_reorder_simp : forall G1 x1 x2 v e,
    x1 <> x2 ->
    AWTerm (G1 & x2 ~ AC_Var & x1 ~ v) e ->
    AWTerm (G1 & x1 ~ v & x2 ~ AC_Var) e.
Proof.
  intros.
  assert (G1 & x2 ~ AC_Var & x1 ~ v = G1 & x2 ~ AC_Var & x1 ~ v & empty).
  rewrite* concat_empty_r.
  assert (G1 & x1 ~ v & x2 ~ AC_Var = G1 & x1 ~ v & x2 ~ AC_Var & empty).
  rewrite* concat_empty_r.
  rewrite H1 in H0.
  rewrite H2.
  apply* awterm_reorder.
Qed.

Lemma awterm_weaken : forall G x v e,
    AWTerm G e ->
    x # G ->
    AWTerm (G & x ~ v) e.
Proof.
  intros. inductions H.
  apply* AWTerm_Var. apply* binds_push_fresh.
  apply* AWTerm_TypVar. apply* binds_push_fresh.
  apply* AWTerm_LetVar. apply* binds_push_fresh.
  apply* AWTerm_EVar. apply* binds_push_fresh.
  apply* AWTerm_Solved_EVar. apply* binds_push_fresh.
  apply* AWTerm_Star.
  apply* AWTerm_App.
  apply AWTerm_Lam with (L := L \u \{x}); intros. apply* awterm_reorder_simp.
  apply AWTerm_Pi with (L := L \u \{x}); intros. apply* IHAWTerm. apply* awterm_reorder_simp.
  apply AWTerm_Let with (L := L \u \{x}); intros. apply* IHAWTerm. apply* awterm_reorder_simp.
  apply* AWTerm_CastUp.
  apply* AWTerm_CastDn.
  apply* AWTerm_Ann.
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

