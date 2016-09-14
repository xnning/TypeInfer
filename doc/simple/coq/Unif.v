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

Set Implicit Arguments.

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
  rewrite dom_push in H6.
  auto. apply* IHACpltCtxSubstCtx.

  apply* IHACpltCtxSubstCtx.
  apply* IHACpltCtxSubstCtx.
  apply* IHACpltCtxSubstCtx.
Qed.

Lemma ctxsubst_comm_app : forall G e1 e2,
    ACtxSubst G (AE_App e1 e2) = AE_App (ACtxSubst G e1) (ACtxSubst G e2).
Proof.
  intros. gen e1 e2. induction G using env_ind; intros.
  rewrite subst_empty_env.
  rewrite subst_empty_env.
  rewrite subst_empty_env.
  auto.
  inductions v.
  rewrite subst_add_var.
  rewrite subst_add_var.
  rewrite subst_add_var.
  auto.
  rewrite subst_add_typvar.
  rewrite subst_add_typvar.
  rewrite subst_add_typvar.
  auto.
  rewrite subst_add_bndvar.
  rewrite subst_add_bndvar.
  rewrite subst_add_bndvar.
  apply* IHG.
  rewrite subst_add_evar.
  rewrite subst_add_evar.
  rewrite subst_add_evar.
  auto.
  rewrite subst_add_solved_evar.
  rewrite subst_add_solved_evar.
  rewrite subst_add_solved_evar.
  apply* IHG.
Qed.

Lemma ctxsubst_id_app: forall G e1 e2,
    AE_App e1 e2 = ACtxSubst G (AE_App e1 e2) ->
    e1 = ACtxSubst G e1.
Proof.
  intros. induction G using env_ind.
  rewrite subst_empty_env. auto.
  inductions v.
  rewrite subst_add_var in H.
  rewrite subst_add_var. apply* IHG.
  rewrite subst_add_typvar in H.
  rewrite subst_add_typvar. apply* IHG.
  rewrite subst_add_bndvar in H.
  simpl in H.
  rewrite subst_add_bndvar.
  rewrite ctxsubst_comm_app in H.
  injection H; intros. auto.
  rewrite subst_add_evar.
  rewrite subst_add_evar in H.
  apply* IHG.
  rewrite subst_add_solved_evar in H.
  simpl in H.
  rewrite ctxsubst_comm_app in H.
  injection H; intros.
  rewrite subst_add_solved_evar.
  auto.
Qed.

Lemma ctxsubst_comm_ann : forall G e1 e2,
    ACtxSubst G (AE_Ann e1 e2) = AE_Ann (ACtxSubst G e1) (ACtxSubst G e2).
Proof.
  intros. gen e1 e2. induction G using env_ind; intros.
  rewrite subst_empty_env.
  rewrite subst_empty_env.
  rewrite subst_empty_env.
  auto.
  inductions v.
  rewrite subst_add_var.
  rewrite subst_add_var.
  rewrite subst_add_var.
  auto.
  rewrite subst_add_typvar.
  rewrite subst_add_typvar.
  rewrite subst_add_typvar.
  auto.
  rewrite subst_add_bndvar.
  rewrite subst_add_bndvar.
  rewrite subst_add_bndvar.
  apply* IHG.
  rewrite subst_add_evar.
  rewrite subst_add_evar.
  rewrite subst_add_evar.
  auto.
  rewrite subst_add_solved_evar.
  rewrite subst_add_solved_evar.
  rewrite subst_add_solved_evar.
  apply* IHG.
Qed.

Lemma ctxsubst_id_ann: forall G e1 e2,
    AE_Ann e1 e2 = ACtxSubst G (AE_Ann e1 e2) ->
    e1 = ACtxSubst G e1.
Proof.
  intros. induction G using env_ind.
  rewrite subst_empty_env. auto.
  inductions v.
  rewrite subst_add_var in H.
  rewrite subst_add_var. apply* IHG.
  rewrite subst_add_typvar in H.
  rewrite subst_add_typvar. apply* IHG.
  rewrite subst_add_bndvar in H.
  simpl in H.
  rewrite subst_add_bndvar.
  rewrite ctxsubst_comm_ann in H.
  injection H; intros. auto.
  rewrite subst_add_evar.
  rewrite subst_add_evar in H.
  apply* IHG.
  rewrite subst_add_solved_evar in H.
  simpl in H.
  rewrite ctxsubst_comm_ann in H.
  injection H; intros.
  rewrite subst_add_solved_evar.
  auto.
Qed.

Lemma ctxsubst_comm_castup : forall G e1,
    ACtxSubst G (AE_CastUp e1) = AE_CastUp (ACtxSubst G e1).
Proof.
  intros. gen e1. induction G using env_ind; intros.
  rewrite subst_empty_env.
  rewrite subst_empty_env.
  auto.
  inductions v.
  rewrite subst_add_var.
  rewrite subst_add_var.
  auto.
  rewrite subst_add_typvar.
  rewrite subst_add_typvar.
  auto.
  rewrite subst_add_bndvar.
  rewrite subst_add_bndvar.
  apply* IHG.
  rewrite subst_add_evar.
  rewrite subst_add_evar.
  auto.
  rewrite subst_add_solved_evar.
  rewrite subst_add_solved_evar.
  apply* IHG.
Qed.

Lemma ctxsubst_id_castup: forall G e1,
    AE_CastUp e1 = ACtxSubst G (AE_CastUp e1) ->
    e1 = ACtxSubst G e1.
Proof.
  intros. induction G using env_ind.
  rewrite subst_empty_env. auto.
  inductions v.
  rewrite subst_add_var in H.
  rewrite subst_add_var. apply* IHG.
  rewrite subst_add_typvar in H.
  rewrite subst_add_typvar. apply* IHG.
  rewrite subst_add_bndvar in H.
  simpl in H.
  rewrite subst_add_bndvar.
  rewrite ctxsubst_comm_castup in H.
  injection H; intros. auto.
  rewrite subst_add_evar.
  rewrite subst_add_evar in H.
  apply* IHG.
  rewrite subst_add_solved_evar in H.
  simpl in H.
  rewrite ctxsubst_comm_castup in H.
  injection H; intros.
  rewrite subst_add_solved_evar.
  auto.
Qed.

Lemma ctxsubst_comm_castdn : forall G e1,
    ACtxSubst G (AE_CastDn e1) = AE_CastDn (ACtxSubst G e1).
Proof.
  intros. gen e1. induction G using env_ind; intros.
  rewrite subst_empty_env.
  rewrite subst_empty_env.
  auto.
  inductions v.
  rewrite subst_add_var.
  rewrite subst_add_var.
  auto.
  rewrite subst_add_typvar.
  rewrite subst_add_typvar.
  auto.
  rewrite subst_add_bndvar.
  rewrite subst_add_bndvar.
  apply* IHG.
  rewrite subst_add_evar.
  rewrite subst_add_evar.
  auto.
  rewrite subst_add_solved_evar.
  rewrite subst_add_solved_evar.
  apply* IHG.
Qed.

Lemma ctxsubst_id_castdn: forall G e1,
    AE_CastDn e1 = ACtxSubst G (AE_CastDn e1) ->
    e1 = ACtxSubst G e1.
Proof.
  intros. induction G using env_ind.
  rewrite subst_empty_env. auto.
  inductions v.
  rewrite subst_add_var in H.
  rewrite subst_add_var. apply* IHG.
  rewrite subst_add_typvar in H.
  rewrite subst_add_typvar. apply* IHG.
  rewrite subst_add_bndvar in H.
  simpl in H.
  rewrite subst_add_bndvar.
  rewrite ctxsubst_comm_castdn in H.
  injection H; intros. auto.
  rewrite subst_add_evar.
  rewrite subst_add_evar in H.
  apply* IHG.
  rewrite subst_add_solved_evar in H.
  simpl in H.
  rewrite ctxsubst_comm_castdn in H.
  injection H; intros.
  rewrite subst_add_solved_evar.
  auto.
Qed.

Lemma awtyp_expr_wf: forall G a,
    AWfTyp G (AT_Expr a) ->
    AWTerm G a.
Proof.
  intros. inductions H; intros.
  apply* AWTerm_EVar.
  apply* AWTerm_Solved_EVar.
  apply AWTerm_Pi with (L:=L). auto.
  intros. rewrite <- (concat_empty_r (G & x ~ AC_Var)).
  apply awterm_replace with (t := t1).
  rewrite -> (concat_empty_r (G & x ~ AC_Typ t1)).
  apply* H1.
  apply* atyping_awterm.
Qed.

Lemma awterm_typ: forall G x a,
    AWf (G & x ~ AC_Typ a) ->
    AWTerm G a.
Proof.
  intros. inductions H.
  false. apply* empty_push_inv.
  destruct (eq_push_inv x) as [? [? ?]]. inversions H2.
  destruct (eq_push_inv x) as [? [? ?]]. inversions H3.
  inversions H1. apply* AWTerm_EVar. apply* AWTerm_Solved_EVar.
  apply AWTerm_Pi with (L:=L). apply* awtyp_expr_wf.
  intros. rewrite <- (concat_empty_r (G & x0 ~ AC_Var)).
  apply awterm_replace with (t := t1).
  rewrite -> (concat_empty_r (G & x0 ~ AC_Typ t1)).
  pose (H5 x0 H1).
  apply* awtyp_expr_wf.
  apply* atyping_awterm.
  destruct (eq_push_inv x) as [? [? ?]]. inversions H5.
  destruct (eq_push_inv x) as [? [? ?]]. inversions H5.
  destruct (eq_push_inv x) as [? [? ?]]. inversions H2.
  destruct (eq_push_inv x) as [? [? ?]]. inversions H3.
Qed.

Lemma awtermt_bnd: forall G x s t,
    AWf (G & x ~ AC_Bnd s t) ->
    AWTermT G s.
Proof.
  introv wf. gen_eq H : (G & x ~ AC_Bnd s t).
  gen G s. induction wf; introv hi; try(
  solve[apply eq_push_inv in hi; destruct hi as [eqx [eqv eqg]]; inversion eqv]); subst; auto.
  apply empty_push_inv in hi. inversion hi.
  apply eq_push_inv in hi; destruct hi as [eqx [eqv eqg]]; inversion eqv. subst. apply* AWTermT_Expr. apply* awtyp_expr_wf.

  apply eq_push_inv in hi; destruct hi as [eqx [eqv eqg]]. inversion eqv. subst.
  apply AWTermT_Forall with (L := L). intros.
  apply (H2 x0 H3). auto.
Qed.

Theorem cpltctxsubstctx_exists: forall G,
    AWf G ->
    CompleteCtx G ->
    exists H, ACpltCtxSubstCtx G G H.
Proof.
  intros.
  induction G using env_ind.
  exists* (empty : DCtx). apply* ACpltCtxSubstCtx_Empty.
  assert (WfG : AWf G) by (apply* AWf_left).
  assert (CCtxG : CompleteCtx G) by (apply* complete_part_left; apply* awf_is_ok).
  induction v.

  destruct (IHG WfG CCtxG) as [H1 IHSubst].
  exists H1. apply* ACpltCtxSubstCtx_Var.

  assert (TrmA: AWTerm G a) by (apply* awterm_typ).
  destruct (cpltctxsubst_exists G a WfG TrmA CCtxG) as [t1' S].
  destruct (IHG WfG CCtxG) as [H1 S'].
  exists (H1 & x ~ DC_Typ t1'). apply* ACpltCtxSubstCtx_TypVar.

  assert (TrmA: AWTerm G a0) by (apply* awterm_bnd).
  destruct (cpltctxsubst_exists G a0 WfG TrmA CCtxG) as [t1' S].
  destruct (IHG WfG CCtxG) as [H1 S'].
  assert (TrmAT: AWTermT G a) by (apply* awtermt_bnd).
  destruct (cpltctxtsubst_exists G a WfG TrmAT CCtxG) as [t2' S2].
  exists (H1 & x ~ DC_Bnd t2' t1'). apply* ACpltCtxSubstCtx_BndVar.

  false. unfold CompleteCtx in H0.
  destruct (H0 x AC_Unsolved_EVar).
  apply* binds_tail. auto.

  destruct (IHG WfG CCtxG) as [H1 IHSubst].
  exists H1. apply* ACpltCtxSubstCtx_Solved_Solved_EVar.
Qed.

Lemma confluence_cplt2 : forall G1 G2 H I J,
    ExtCtx G1 H -> ExtCtx G2 H ->
    CompleteCtx H ->
    ACpltCtxSubstCtx H G1 I ->
    ACpltCtxSubstCtx H G2 J ->
    I = J.
Proof.
  intros.
  assert (Wf: AWf H) by (apply* awf_preservation).
  destruct (cpltctxsubstctx_exists Wf H2) as [K P].
  assert (I = K).
  intros. apply stable_cplt_env_eq with (G := G1) (H := H).
  auto. auto. auto.
  assert (J = K).
  intros. apply stable_cplt_env_eq with (G := G2) (H := H).
  auto. auto. auto.
  subst. auto.
Qed.

Lemma extctx_remove_var : forall G H y,
    ExtCtx (G & y ~ AC_Var) (H & y ~ AC_Var) ->
    ExtCtx G H.
Proof.
  introv D.
  rewrite <- concat_empty_r in D at 1.
  rewrite <- concat_empty_r in D.
  destruct (extension_order_var D) as [X [Y (K1 & K2 & _)]].
  lets C: awf_preservation D.
  pose (Ok2 := awf_is_ok C).
  lets Ok3: Ok2.
  rewrite K1 in Ok3.
  destruct~ (ok_middle_eq Ok2 eq_refl Ok3 eq_refl K1) as (Eq1 & Eq2 & Eq3).
  subst*.
Qed.

Lemma extctx_remove_typvar : forall G H y t1 t2,
    ExtCtx (G & y ~ AC_Typ t1) (H & y ~ AC_Typ t2) ->
    ExtCtx G H.
Proof.
  introv D.
  rewrite <- concat_empty_r in D at 1.
  rewrite <- concat_empty_r in D.
  destruct (extension_order_typvar D) as [X [Y [Z (K1 & K2 & _)]]].
  lets C: awf_preservation D.
  pose (Ok2 := awf_is_ok C).
  lets Ok3: Ok2.
  rewrite K1 in Ok3.
  destruct~ (ok_middle_eq Ok2 eq_refl Ok3 eq_refl K1) as (Eq1 & Eq2 & Eq3).
  subst*.
Qed.

Lemma extctx_remove_exists : forall G I y v,
    ExtCtx G (I & y ~ v) ->
    exists G', G = G' & y ~ v /\ ExtCtx G' I.
Admitted.

Lemma extctx_to_empty_inv : forall G,
    ExtCtx G empty -> G = empty.
Proof.
  intros.
  inversions H; auto; false; apply* empty_push_inv.
Qed.

Theorem cpltctxsubstctx_exists_ext: forall G I,
    ExtCtx I G ->
    CompleteCtx G ->
    exists H, ACpltCtxSubstCtx G I H.
Proof.
  intros. gen I.
  induction G using env_ind; intros.
  assert (I = empty) by (apply* extctx_to_empty_inv).
  subst.
  exists* (empty : DCtx). apply* ACpltCtxSubstCtx_Empty.
  lets:  awf_preservation H.
  destruct (extctx_remove_exists H) as [I' [Eq Ext']].
  assert (WfG : AWf G) by (apply* AWf_left).
  assert (CCtxG : CompleteCtx G) by (apply* complete_part_left; apply* awf_is_ok).
  induction v.
  
  destruct (IHG CCtxG I' Ext') as [H1' IHSubst].
  exists H1'. rewrite Eq. apply* ACpltCtxSubstCtx_Var.

  assert (TrmA: AWTerm G a) by (apply* awterm_typ).
  destruct (cpltctxsubst_exists G a WfG TrmA CCtxG) as [t1' S].
  destruct (IHG CCtxG I' Ext') as [H1' S'].
  exists (H1' & x ~ DC_Typ t1'). rewrite Eq. apply* ACpltCtxSubstCtx_TypVar.

  assert (TrmA: AWTerm G a0) by (apply* awterm_bnd).
  destruct (cpltctxsubst_exists G a0 WfG TrmA CCtxG) as [t1' S].
  destruct (IHG CCtxG I' Ext') as [H1' S'].
  assert (TrmAT: AWTermT G a) by (apply* awtermt_bnd).
  destruct (cpltctxtsubst_exists G a WfG TrmAT CCtxG) as [t2' S2].
  exists (H1' & x ~ DC_Bnd t2' t1'). rewrite Eq. apply* ACpltCtxSubstCtx_BndVar.

  false. unfold CompleteCtx in H0.
  destruct (H0 x AC_Unsolved_EVar).
  apply* binds_tail. auto.

  destruct (IHG CCtxG I' Ext') as [H1' IHSubst].
  exists H1'. rewrite Eq. apply* ACpltCtxSubstCtx_Solved_Solved_EVar.
Qed.

Lemma confluence_cplt3 : forall G1 G2 H I,
    ExtCtx G1 H -> ExtCtx G2 H ->
    CompleteCtx H ->
    ACpltCtxSubstCtx H G1 I ->
    ACpltCtxSubstCtx H G2 I.
Proof.
  intros.
  destruct (cpltctxsubstctx_exists_ext H1 H2) as [J ?].
  assert (I = J).
  apply (confluence_cplt2 H0 H1 H2 H3 H4).
  subst. auto.
Qed.

Lemma unif_to_extctx : forall G H t1 t2,
    AWf G ->
    AUnify G t1 t2 H ->
    AWf H /\ ExtCtx G H.
Proof.
  intros. inductions H1; try solve [split*; apply* extension_reflexivity].

  destruct (IHAUnify1 H0) as [A B].
  destruct (IHAUnify2 A) as [A1 B1].
  split*. apply* extension_transitivity.

  destruct (IHAUnify H0) as [A B].
  pick_fresh_gen (L \u dom H1) y.
  assert (y \notin L) by auto.
  destruct (H4 y H5) as [C D].
  apply AWf_Var. auto. auto.
  split. apply* AWf_left. apply* extension_transitivity.
  apply* extctx_remove_var.

  pick_fresh_gen (L \u dom G) y.
  assert (y \notin L) by auto.
  destruct (H2 y H3) as [C D].
  apply AWf_Var. auto. auto.
  split. apply* AWf_left. 
  apply* extctx_remove_var.

  destruct (IHAUnify H0) as [A B].
  pick_fresh_gen (L \u dom H1) y.
  assert (y \notin L) by auto.
  destruct (H4 y H5) as [C D].
  apply AWf_TyVar. auto. auto. admit.
  split. apply* AWf_left. apply* extension_transitivity.
  apply* extctx_remove_typvar.
  
  destruct (IHAUnify1 H0) as [A B].
  destruct (IHAUnify2 A) as [A1 B1].
  split*. apply* extension_transitivity.

  admit. admit.
Qed.

Theorem unif_soundness : forall G H I t1 t2 H' t1' t2',
    AUnify G t1 t2 H ->
    t1 = ACtxSubst G t1 ->
    t2 = ACtxSubst G t2 ->
    ExtCtx H I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I H H' ->
    ACpltCtxSubst I t1 t1' ->
    ACpltCtxSubst I t2 t2' ->
    AWf G ->
    t1' = t2'.
Proof.
  intros. gen t1'. gen t2'. inductions H0; intros.

  apply* cplt_ctxsubst_eq.
  apply* cplt_ctxsubst_eq.
  apply* cplt_ctxsubst_eq.
  apply* cplt_ctxsubst_eq.
  
  inversions H6. inversions H7.
  auto.

  inversions H6. inversions H7.
  destruct (unif_to_extctx H8 H0_) as [Wf _].
  destruct (unif_to_extctx Wf H0_0) as [_ Ext].
  pose (ctxsubst_id_app G H0).
  pose (ctxsubst_id_app G H2).
  assert (d1 = d0).
  apply* IHAUnify1. 
  apply* extension_transitivity.
  apply* confluence_cplt3.
  apply* extension_transitivity.
  assert (d2 = d3).
  apply* cplt_ctxsubst_eq.
  rewrite H6. rewrite H7. auto.

  inversions H11. inversions H10. admit.

  inversions H7. inversions H9. admit.

  inversions H6. inversions H7.
  destruct (unif_to_extctx H8 H0) as [Wf Ext].
  pose (ctxsubst_id_castup G H1).
  pose (ctxsubst_id_castup G H2).
  assert (d = d0).
  apply* IHAUnify. 
  rewrite H6. auto.

  inversions H6. inversions H7.
  destruct (unif_to_extctx H8 H0) as [Wf Ext].
  pose (ctxsubst_id_castdn G H1).
  pose (ctxsubst_id_castdn G H2).
  assert (d = d0).
  apply* IHAUnify. 
  rewrite H6. auto.

  inversions H10. inversions H11. admit.

  inversions H6. inversions H7.
  destruct (unif_to_extctx H8 H0_) as [Wf _].
  destruct (unif_to_extctx Wf H0_0) as [_ Ext].
  pose (ctxsubst_id_ann G H0).
  pose (ctxsubst_id_ann G H2).
  assert (d1 = d0).
  apply* IHAUnify1. 
  apply* extension_transitivity.
  apply* confluence_cplt3.
  apply* extension_transitivity.
  assert (d2 = d3).
  apply* cplt_ctxsubst_eq.
  rewrite H6. rewrite H7. auto.

  admit.

  admit.
Qed.

