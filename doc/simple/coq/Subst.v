Require Import CtxExtension.
Require Import LibLN.
Require Import AlgoDef.
Require Import UtilityEnv.
Require Import DeclDef.
Require Import DeclInfra.
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
  false. apply* empty_push_inv.
Qed.

Lemma not_in_cpltctx : forall x G H I,
    ACpltCtxSubstCtx G H I ->
    x # G ->
    x # I.
Proof.
  intros. inductions H0.
  auto. apply* IHACpltCtxSubstCtx.

  rewrite dom_push. notin_simpl.
  rewrite dom_push in H4.
  auto. apply* IHACpltCtxSubstCtx.

  rewrite dom_push. notin_simpl.
  rewrite dom_push in H2.
  auto. apply* IHACpltCtxSubstCtx.

  apply* IHACpltCtxSubstCtx.
  apply* IHACpltCtxSubstCtx.
  apply* IHACpltCtxSubstCtx.
  apply* IHACpltCtxSubstCtx.
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
  destruct (eq_push_inv H2) as [? [? ?]].
  false.
Qed.

Lemma ctxsubst_inv_typvar : forall H G I' x t1 t2,
    ACpltCtxSubstCtx (H & x ~ AC_Typ t1) (G & x ~ AC_Typ t2) I' ->
    exists I t1', (I' = I & x ~ DC_Typ t1' /\
    CompleteCtx H /\ ACpltCtxSubstCtx H G I /\ ACtxTSubst H t1 = ACtxTSubst H t2 /\
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
  destruct (eq_push_inv H2) as [? [? ?]]. false.
Qed.

Lemma ctxsubst_inv_tvar : forall H G I' x,
    ACpltCtxSubstCtx (H & x ~ AC_TVar) (G & x ~ AC_TVar) I' ->
    exists I, (I' = I & x ~ DC_TVar /\
      CompleteCtx H /\ ACpltCtxSubstCtx H G I).
Proof.
  intros. inversions H0.
  false. apply* empty_push_inv.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  exists I.
  destruct (eq_push_inv H2) as [? [? ?]]; subst.
  destruct (eq_push_inv H3) as [? [? ?]]; subst.
  inversions H8; inversions H1.
  destruct (eq_push_inv H2) as [? [? ?]]; subst.
  destruct (eq_push_inv H3) as [? [? ?]]; subst.
  exists I.
  auto.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
Qed.

Lemma ctxsubst_declaration_preservation_inv: forall H G I x v,
    ACpltCtxSubstCtx H G I ->
    binds x v G ->
    exists v2, binds x v2 H.
Proof.
  introv sub bd.
  induction sub.
  false binds_empty_inv bd.

  destruct (eq_var_dec x x0).
  subst. exists~ AC_Var.
  lets: binds_push_neq_inv bd n.
  lets: IHsub H1.
  destruct H2 as (v2 & bd2). exists~ v2.

  destruct (eq_var_dec x x0).
  subst. exists~ (AC_Typ t1).
  lets: binds_push_neq_inv bd n.
  lets: IHsub H3.
  destruct H4 as (v2 & bd2). exists~ v2.

  destruct (eq_var_dec x a).
  subst. exists~ AC_TVar.
  lets: binds_push_neq_inv bd n.
  lets: IHsub H1.
  destruct H2 as (v2 & bd2). exists~ v2.

  destruct (eq_var_dec x a).
  subst. exists~ AC_Marker.
  lets: binds_push_neq_inv bd n.
  lets: IHsub H1.
  destruct H2 as (v2 & bd2). exists~ v2.

  destruct (eq_var_dec x a).
  subst. exists~ (AC_Solved_EVar t).
  lets: binds_push_neq_inv bd n.
  lets: IHsub H1.
  destruct H2 as (v2 & bd2). exists~ v2.

  destruct (eq_var_dec x a).
  subst. exists~ (AC_Solved_EVar t1).
  lets: binds_push_neq_inv bd n.
  lets: IHsub H2.
  destruct H3 as (v2 & bd2). exists~ v2.

  destruct (eq_var_dec x a).
  subst. exists~ (AC_Solved_EVar t).
  lets: IHsub bd.
  destruct H2 as (v2 & bd2). exists~ v2.
Qed.

Lemma ctxsubst_inv_marker : forall H G I x,
    ACpltCtxSubstCtx (H & x ~ AC_Marker) (G & x ~ AC_Marker) I ->
    CompleteCtx H /\ ACpltCtxSubstCtx H G I.
Proof.
  intros. inversions H0.
  false. apply* empty_push_inv.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]]; subst.
  destruct (eq_push_inv H3) as [? [? ?]]; subst.
  auto.
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
  destruct (eq_push_inv H2) as [? [? ?]].
  false.
  destruct (eq_push_inv H2) as [? [? ?]]; subst.
  destruct (eq_push_inv H3) as [? [? ?]]; subst.
  auto.
  destruct (eq_push_inv H3) as [? [? ?]].
  false.
  destruct (eq_push_inv H2) as [? [? ?]]; subst.
  split; auto.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_tail.
  lets: ctxsubst_declaration_preservation_inv H4 H0.
  destruct H1 as (v2 & bd).
  false binds_fresh_inv bd H5.
Qed.

Lemma ctxsubst_inv_ssevar : forall H G I t1 t2 a,
    ACpltCtxSubstCtx (H & a ~ AC_Solved_EVar t1) (G & a ~ AC_Solved_EVar t2) I ->
    CompleteCtx H /\
    ACpltCtxSubstCtx H G I /\
    ACtxTSubst H t1 = ACtxTSubst H t2.
Proof.
  intros. inversions H0.
  false. apply* empty_push_inv.
  destruct (eq_push_inv H2) as [? [? ?]]. false.
  destruct (eq_push_inv H2) as [? [? ?]].
  false.
  destruct (eq_push_inv H2) as [? [? ?]].
  false.
  destruct (eq_push_inv H3) as [? [? ?]]; false.
  destruct (eq_push_inv H3) as [? [? ?]]; false.
  destruct (eq_push_inv H2) as [? [? ?]]; subst.
  destruct (eq_push_inv H3) as [? [? ?]]; subst.
  inversions H1; inversions H7.
  auto.
  destruct (eq_push_inv H2) as [? [? ?]]; subst.
  split; auto.
  false.
  assert (binds a (AC_Solved_EVar t2) (G & a ~ AC_Solved_EVar t2)).
  apply* binds_tail.
  lets: ctxsubst_declaration_preservation_inv H4 H0.
  destruct H1 as (v2 & H1).
  false binds_fresh_inv H1 H5.
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
  f_equal *. lets: (IHHyp1_1 (DT_Expr d0) H2). inversion~ H.
  lets: (IHHyp1_2 (DT_Expr d3) H4). inversion~ H0.

  DeclInfra.pick_fresh y.
  assert (DT_Expr (d ^ y) = DT_Expr (d0 ^ y)). apply* H0. inversion~ H1.
  apply dopen_var_inj in H4; auto.
  subst*.

  rewrite -> (IHHyp1 d0 H4).
  DeclInfra.pick_fresh y.
  assert (d2 ^' y = d3 ^' y). apply* H0.
  apply dopent_var_inj in H1; auto.
  subst*.

  lets: (IHHyp1 (DT_Expr d0) H1). inversion~ H.
  lets: (IHHyp1 (DT_Expr d0) H1). inversion~ H.
  lets: (IHHyp1_1 (DT_Expr d0) H2). inversion~ H.
  rewrite -> (IHHyp1_2 d3 H4).
  auto.

  DeclInfra.pick_fresh y.
  assert (s2 ^%' y = s3 ^%' y). apply* H0.
  apply dtopent_var_inj in H1; auto.
  subst*.
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
  destruct (ctxsubst_inv_tvar H3) as [I1' [? [? ?]]].
  destruct (ctxsubst_inv_tvar H4) as [I2' [? [? ?]]].
  pose (IHExtCtx I1' H7 I2' H10).
  rewrite H5. rewrite H8. rewrite e. auto.
  destruct (ctxsubst_inv_marker H3) as [? ?].
  destruct (ctxsubst_inv_marker H4) as [? ?].
  apply* IHExtCtx.
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

Lemma complete_add: forall G x,
    CompleteCtx G ->
    CompleteCtx (G & x ~ AC_Var).
Proof.
  introv comp.
  unfold CompleteCtx.
  intros z zv bd eqzv. subst.
  apply binds_push_inv in bd. destruct bd as [[_ neq] | [_ neq]].
  false neq.
  false complete_contains_unsolved comp neq.
Qed.

Lemma complete_add_typ: forall G x t,
    CompleteCtx G ->
    CompleteCtx (G & x ~ AC_Typ t).
Proof.
  introv comp.
  unfold CompleteCtx.
  intros z zv bd eqzv. subst.
  apply binds_push_inv in bd. destruct bd as [[_ neq] | [_ neq]].
  false neq.
  false complete_contains_unsolved comp neq.
Qed.

Lemma complete_add_tvar: forall G x,
    CompleteCtx G ->
    CompleteCtx (G & x ~ AC_TVar).
Proof.
  introv comp.
  unfold CompleteCtx.
  intros z zv bd eqzv. subst.
  apply binds_push_inv in bd. destruct bd as [[_ neq] | [_ neq]].
  false neq.
  false complete_contains_unsolved comp neq.
Qed.

Lemma complete_add_marker: forall G x,
    CompleteCtx G ->
    CompleteCtx (G & x ~ AC_Marker).
Proof.
  introv comp.
  unfold CompleteCtx.
  intros z zv bd eqzv. subst.
  apply binds_push_inv in bd. destruct bd as [[_ neq] | [_ neq]].
  false neq.
  false complete_contains_unsolved comp neq.
Qed.

Lemma complete_add_solved: forall G x e,
    CompleteCtx G ->
    CompleteCtx (G & x ~ AC_Solved_EVar e).
Proof.
  introv comp.
  unfold CompleteCtx.
  intros z zv bd eqzv. subst.
  apply binds_push_inv in bd. destruct bd as [[_ neq] | [_ neq]].
  false neq.
  false complete_contains_unsolved comp neq.
Qed.

Lemma complete_append: forall G H,
    CompleteCtx G ->
    CompleteCtx H ->
    ok (G & H) ->
    CompleteCtx (G & H).
Proof.
  introv comp_g comp_h okgh.
  induction H using env_ind.
  rewrite~ concat_empty_r.

  induction v.
  rewrite concat_assoc.
  apply~ complete_add.
  apply~ IHenv.
  apply complete_part_left in comp_h. auto. apply* ok_concat_inv_r.
  rewrite concat_assoc in okgh. apply* ok_concat_inv_l.

  rewrite concat_assoc.
  apply~ complete_add_typ.
  apply~ IHenv.
  apply complete_part_left in comp_h. auto. apply* ok_concat_inv_r.
  rewrite concat_assoc in okgh. apply* ok_concat_inv_l.

  rewrite concat_assoc.
  apply~ complete_add_tvar.
  apply~ IHenv.
  apply complete_part_left in comp_h. auto. apply* ok_concat_inv_r.
  rewrite concat_assoc in okgh. apply* ok_concat_inv_l.

  assert (binds x AC_Unsolved_EVar (H & x ~ AC_Unsolved_EVar)). apply binds_tail.
  false complete_contains_unsolved comp_h H0.

  rewrite concat_assoc.
  apply~ complete_add_solved.
  apply~ IHenv.
  apply complete_part_left in comp_h. auto. apply* ok_concat_inv_r.
  rewrite concat_assoc in okgh. apply* ok_concat_inv_l.

  rewrite concat_assoc.
  apply~ complete_add_marker.
  apply~ IHenv.
  apply complete_part_left in comp_h. auto. apply* ok_concat_inv_r.
  rewrite concat_assoc in okgh. apply* ok_concat_inv_l.
Qed.

Lemma complete_replace: forall G1 G2 x t,
  ok (G1 & x ~ AC_Var & G2) ->
  CompleteCtx (G1 & x ~ AC_Var & G2) ->
  CompleteCtx (G1 & x ~ AC_Typ t & G2).
Proof.
  introv okg compl.
  apply complete_append.
  apply complete_add_typ.
  do 2 apply complete_part_left in compl; auto.
  apply complete_part_right in compl; auto.
  apply* ok_middle_change.
Qed.

Lemma complete_replace': forall G1 x t,
  ok (G1 & x ~ AC_Var) ->
  CompleteCtx (G1 & x ~ AC_Var) ->
  CompleteCtx (G1 & x ~ AC_Typ t).
Proof.
  introv okg compl.
  assert (ok (G1 & x ~ AC_Var & empty)). rewrite~ concat_empty_r.
  assert (CompleteCtx (G1 & x ~ AC_Var & empty)).  rewrite~ concat_empty_r.
  lets: complete_replace H H0.
  rewrite concat_empty_r in H1. exact H1.
Qed.

Lemma eq_aexpr_dec : forall (T T' : AExpr),
  sumbool (T = T') (T <> T')
with eq_atype_dec : forall (T T' : AType),
  sumbool (T = T') (T <> T').
Proof.
  decide equality.
  decide equality.
  apply* eq_var_dec.
Proof.
  decide equality.
  decide equality.
  apply* eq_var_dec.
  apply* eq_var_dec.
Qed.

Lemma eq_actx_dec : forall (T T' : ACtxT),
  sumbool (T = T') (T <> T').
Proof.
  decide equality.
  apply* eq_atype_dec.
  apply* eq_atype_dec.
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

Hint Constructors ACpltCtxSubst.
Hint Resolve complete_replace complete_replace'.
Lemma cplt_ctxsubst_replace : forall G1 t G2 t1 t2 x,
    ok (G1 & x ~ AC_Var & G2) ->
    ACpltCtxSubst (G1 & x ~ AC_Var & G2) t1 t2 ->
    ACpltCtxSubst (G1 & x ~ AC_Typ t & G2) t1 t2.
Proof.
  introv okg sub.
  gen_eq M: (G1 & x ~ AC_Var & G2). gen G2.
  induction sub;
  introv hinfo; subst; auto.
  apply binds_middle_inv in H0.
  destruct H0 as [bdg2 | [bdm | bdg1]].
  apply~ ACpltCtxSubst_Var.
  destruct bdm as [? [? _]]. subst.
  apply ACpltCtxSubst_TyVar with t; auto.
  destruct bdg1 as [? [? ?]].
  apply ACpltCtxSubst_Var; auto.

  (* TYP VAR *)
  apply binds_middle_inv in H0.
  destruct H0 as [bdg2 | [bdm | bdg1]].
  apply ACpltCtxSubst_TyVar with t0; auto.
  destruct bdm as [? [? inv]]. false inv.
  destruct bdg1 as [? [? ?]].
  apply ACpltCtxSubst_TyVar with t0; auto.

  (* TVAR *)
  apply binds_middle_inv in H0.
  destruct H0 as [bdg2 | [bdm | bdg1]].
  apply~ ACpltCtxSubst_TVar.
  destruct bdm as [? [? inv]]. false inv.
  destruct bdg1 as [? [? ?]].
  apply ACpltCtxSubst_TVar; auto.

  (* EVAR *)
  assert (binds x AC_Var (G0 & a ~ AC_Solved_EVar t0 & G2)).
  rewrite hinfo.
  apply binds_middle_eq.
  rewrite hinfo in H1. destruct (ok_middle_inv H1) as [? ?]. auto.

  apply binds_middle_inv in H2.
  destruct H2 as [bdg2 | [bda | bdg0]].
  apply split_bind_context in bdg2.
  destruct bdg2 as (I1 & I2 & g2info). subst.
  repeat rewrite concat_assoc in hinfo.
  apply ok_middle_eq2 in hinfo; auto.

  destruct hinfo as [g1info [_ i2g3]]. subst.
  assert (ACpltCtxSubst
            (G0 & a ~ AC_Solved_EVar t0 & (I1 & x ~ AC_Typ t & G3))
            (AT_EVar a) d).
  apply~ ACpltCtxSubst_EVar.
  repeat rewrite~ concat_assoc.
  repeat rewrite concat_assoc in H1. apply* ok_middle_change.
  repeat rewrite~ concat_assoc in H2.
  repeat rewrite concat_assoc in H1. auto.
  rewrite <- hinfo.
  repeat rewrite concat_assoc in H1. auto.

  destruct bda as [_ [_ inv]]. false inv.
  destruct bdg0 as [noting2 [neq bdg0]].
  apply split_bind_context in bdg0.
  destruct bdg0 as (I1 & I2 & g0info). subst.
  assert (I1 & x ~ AC_Var & (I2 & a ~ AC_Solved_EVar t0 & G2) =
                            G1 & x ~ AC_Var & G3).
  repeat rewrite~ concat_assoc.
  apply ok_middle_eq2 in H2.
  destruct H2 as [? [_ ?]]. subst.
  forwards * : IHsub. do 2 apply ok_concat_inv_l in okg. auto.
  repeat rewrite~ concat_assoc.
  apply~ ACpltCtxSubst_EVar. apply* complete_replace.
  do 2 apply ok_concat_inv_l in okg. auto.
  assert (ok (G1 & x ~ AC_Var & (I2 & a ~ AC_Solved_EVar t0 & G2))).
  repeat rewrite~ concat_assoc.
  assert (ok (G1 & x ~ AC_Typ t & (I2 & a ~ AC_Solved_EVar t0 & G2))).
  apply* ok_middle_change.
  repeat rewrite concat_assoc in H4. auto.
  repeat rewrite~ concat_assoc.
  rewrite <- H2.
  repeat rewrite~ concat_assoc.

  (* LAM *)
  apply ACpltCtxSubst_Lam with (L \u dom (G1 & x ~ AC_Var & G2)).
  intros y notin. assert (notinl: y \notin L) by auto.
  assert (G1 & x ~ AC_Var & G2 & y ~ AC_Var =
          G1 & x ~ AC_Var & (G2 & y ~ AC_Var)).
  repeat rewrite~ concat_assoc.
  lets: H0 notinl H1.
  rewrite H1. repeat rewrite concat_assoc. apply~ ok_push.
  repeat rewrite concat_assoc in H2. auto.

  (* PI *)
  apply ACpltCtxSubst_Pi with (L \u dom (G1 & x ~ AC_Var & G2)).
  apply~ IHsub.
  intros y notin. assert (notinl: y \notin L) by auto.
  assert (G1 & x ~ AC_Var & G2 & y ~ AC_Var =
          G1 & x ~ AC_Var & (G2 & y ~ AC_Var)).
  repeat rewrite~ concat_assoc.
  lets: H0 notinl H1.
  apply~ ok_push.
  repeat rewrite concat_assoc in H2. auto.

  (* FORALL *)
  apply ACpltCtxSubst_Forall with (L \u dom (G1 & x ~ AC_Var & G2)).
  intros y notin. assert (notinl: y \notin L) by auto.
  assert (G1 & x ~ AC_Var & G2 & y ~ AC_TVar =
          G1 & x ~ AC_Var & (G2 & y ~ AC_TVar)).
  repeat rewrite~ concat_assoc.
  lets: H0 notinl H1.
  apply~ ok_push.
  repeat rewrite concat_assoc in H2. auto.
Qed.

Lemma cplt_ctxsubst_replace' : forall G1 t t1 t2 x,
    ok (G1 & x ~ AC_Var) ->
    ACpltCtxSubst (G1 & x ~ AC_Var) t1 t2 ->
    ACpltCtxSubst (G1 & x ~ AC_Typ t) t1 t2.
Proof.
  introv okg sub.
  assert (ok (G1 & x ~ AC_Var & empty)) by rewrite~ concat_empty_r.
  assert (ACpltCtxSubst (G1 & x ~ AC_Var & empty) t1 t2) by rewrite~ concat_empty_r.
  lets: cplt_ctxsubst_replace H H0.
  rewrite concat_empty_r in H1.
  exact H1.
Qed.

Lemma ctxsubst_fvar_eq : forall G x,
    ok G ->
    ACtxSubst G (AE_FVar x) = AE_FVar x.
Proof.
  introv H. induction G using env_ind.
  rewrite* subst_empty_env.

  induction v.
  rewrite~ subst_add_var.
  rewrite~ subst_add_typvar.
  rewrite~ subst_add_tvar.
  rewrite~ subst_add_evar.
  rewrite~ subst_add_solved_evar.
  rewrite~ subst_add_marker.
Qed.

Lemma ctxsubst_evar_eq : forall G x,
    ok G ->
    (binds x AC_Unsolved_EVar G \/ x # G) ->
    ACtxTSubst G (AT_EVar x) = AT_EVar x.
Proof.
  introv H H1. inductions H.
  rewrite* tsubst_empty_env.
  inductions v.
  rewrite~ tsubst_add_var.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ tsubst_add_typvar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ tsubst_add_tvar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ tsubst_add_evar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ tsubst_add_solved_evar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  false. simpl. case_var~.
  rewrite dom_single in NIn.
  false. apply* notin_same.
  simpl. case_var~.
  false. rewrite dom_push in Frh.
  apply* notin_same.

  rewrite~ tsubst_add_marker.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

Qed.

Lemma ctxsubst_tvar_eq : forall G x,
    ok G ->
    (binds x AC_TVar G \/ x # G) ->
    ACtxTSubst G (AT_TFVar x) = AT_TFVar x.
Proof.
  introv H H1. inductions H.
  rewrite* tsubst_empty_env.
  inductions v.
  rewrite~ tsubst_add_var.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ tsubst_add_typvar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ tsubst_add_tvar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ tsubst_add_evar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ tsubst_add_solved_evar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  false. simpl. case_var~.
  rewrite dom_single in NIn.
  false. apply* notin_same.
  simpl. case_var~.
  false. rewrite dom_push in Frh.
  apply* notin_same.

  rewrite~ tsubst_add_marker.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

Qed.

Lemma actxsubst_open: forall G e u,
    AWf G ->
    ACtxSubst G (e @@ u) = (ACtxSubst G e) @@ (ACtxSubst G u).
Proof.
  introv wf. gen e u.
  induction G using env_ind; introv.
  repeat rewrite~ subst_empty_env.
  assert (AWf G) by apply* AWf_left.
  induction v.
  repeat rewrite~ subst_add_var.
  repeat rewrite~ subst_add_typvar.
  repeat rewrite~ subst_add_tvar.
  repeat rewrite~ subst_add_evar.
  repeat rewrite~ subst_add_solved_evar.
  rewrite~ <- IHG. f_equal ~.
  unfold AOpen. rewrite~ asubstt_openrec.
  apply awtermt_is_awtermty with G.
  apply* awterm_solved_evar.
  repeat rewrite~ subst_add_marker.
Qed.

Lemma actxtsubst_open: forall G e u,
    AWf G ->
    ACtxTSubst G (e @@' u) = (ACtxTSubst G e) @@' (ACtxSubst G u).
Proof.
  introv wf. gen e u.
  induction G using env_ind; introv.
  repeat rewrite~ subst_empty_env.
  repeat rewrite~ tsubst_empty_env.
  assert (AWf G) by apply* AWf_left.
  induction v.
  repeat rewrite~ subst_add_var. repeat rewrite~ tsubst_add_var.
  repeat rewrite~ subst_add_typvar. repeat rewrite~ tsubst_add_typvar.
  repeat rewrite~ subst_add_tvar. repeat rewrite~ tsubst_add_tvar.
  repeat rewrite~ subst_add_evar. repeat rewrite~ tsubst_add_evar.
  repeat rewrite~ subst_add_solved_evar. repeat rewrite~ tsubst_add_solved_evar.
  rewrite~ <- IHG. f_equal ~.
  unfold AOpenT. rewrite~ atsubstt_opentyprec.
  apply awtermt_is_awtermty with G.
  apply* awterm_solved_evar.
  repeat rewrite~ subst_add_marker. repeat rewrite~ tsubst_add_marker.
Qed.

Lemma actxtsubst_topen: forall G e u,
    AWf G ->
    ACtxTSubst G (e @@#' u) = (ACtxTSubst G e) @@#' (ACtxTSubst G u).
Proof.
  introv wf. gen e u.
  induction G using env_ind; introv.
  repeat rewrite~ tsubst_empty_env.
  assert (AWf G) by apply* AWf_left.
  induction v.
  repeat rewrite~ tsubst_add_var.
  repeat rewrite~ tsubst_add_typvar.
  repeat rewrite~ tsubst_add_tvar.
  repeat rewrite~ tsubst_add_evar.
  repeat rewrite~ tsubst_add_solved_evar.
  rewrite~ <- IHG. f_equal ~.
  unfold ATOpenT. rewrite~ atsubstt_topentyprec.
  apply awtermt_is_awtermty with G.
  apply* awterm_solved_evar.
  repeat rewrite~ subst_add_marker. repeat rewrite~ tsubst_add_marker.
Qed.
