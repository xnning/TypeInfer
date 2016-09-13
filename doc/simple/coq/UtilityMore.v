Require Import LibLN.
Require Import DeclDef.
Require Import AlgoDef.
Require Import AlgoInfra.
Require Import CtxExtension.
Require Import UtilityEnv.
Require Import Subst.
Require Import Exists.

(* properties about extension *)

Lemma extension_remove_evar: forall G H a,
    ExtCtx (G & a ~ AC_Unsolved_EVar) H ->
    ExtCtx G H.
Proof.
  introv ex.
  destruct (evar_input ex) as (H1 & H2 & H3 & [ih [ih1 [ih2 ih3]]]).
  subst. apply~ right_softness.
  destruct ih2 as [ih21 | (t & ih22)].
  subst. apply~ ExtCtx_Add. eapply AWf_left. apply* awf_preservation.
  subst. apply~ ExtCtx_AddSolved. eapply AWf_left. apply* awf_preservation.
  apply* awf_preservation.
Qed.

Lemma extension_remove_evar_both: forall G H a,
    ExtCtx (G & a ~ AC_Unsolved_EVar) (H & a ~ AC_Unsolved_EVar) ->
    ExtCtx G H.
Proof.
  introv ex.
  destruct (evar_input ex) as (H1 & H2 & H3 & [ih [ih1 [ih2 ih3]]]).
  destruct ih2 as [ih21 | (t & ih22)].
  subst. assert (H & a ~ AC_Unsolved_EVar & empty = H1 & a ~ AC_Unsolved_EVar & H3) by rewrite* concat_empty_r.
  apply ok_middle_eq2 in H0; auto. destruct H0 as [eqh _]. subst~.
  rewrite~ concat_empty_r. apply* ok_preservation.
  rewrite <- H0. rewrite~ concat_empty_r. apply* ok_preservation.

  subst. assert (H & a ~ AC_Unsolved_EVar & empty = H1 & a ~ AC_Solved_EVar t & H3) by rewrite* concat_empty_r.
  apply ok_middle_eq2 in H0; auto. destruct H0 as [_ [eqv _]]. inversion eqv.
  rewrite~ concat_empty_r. apply* ok_preservation.
  rewrite <- H0. rewrite~ concat_empty_r. apply* ok_preservation.
Qed.

Lemma extension_remove_tyvar: forall G H a t,
    ExtCtx (G & a ~ AC_Typ t) (H & a ~ AC_Typ t) ->
    ExtCtx G H.
Proof.
  introv ex.
  assert(ExtCtx (G & a ~ AC_Typ t & empty) (H & a ~ AC_Typ t)). rewrite* concat_empty_r.
  destruct (extension_order_typvar H0) as (H1 & H2 & t2 & [ih [ih1 [ih2 ih3]]]).
  assert (H & a ~ AC_Typ t & empty = H1 & a ~ AC_Typ t2 & H2) by rewrite* concat_empty_r.
  apply ok_middle_eq2 in H3; auto.
  destruct H3 as [hh _]. subst. auto.

  rewrite concat_empty_r. apply* ok_preservation.
  rewrite <- ih.  apply* ok_preservation.
Qed.

(* properties about cpltctxsubst *)

Lemma cpltctxsubst_wftyp: forall G s t,
    AWf G ->
    ACpltCtxSubst G s t ->
    AWTerm G s.
Proof.
  introv wf sub.
  induction sub.
  constructor~.
  apply* AWTerm_TypVar.
  apply* AWTerm_LetVar.
  apply AWTerm_Solved_EVar with t. apply binds_concat_left_ok. apply~ awf_is_ok. apply binds_push_eq.
  apply~ AWTerm_Star.
  apply~ AWTerm_App.
  apply AWTerm_Lam with (L \u dom G). intros y notin. apply~ H0.
  apply AWTerm_Pi with (L \u dom G). apply~ IHsub. intros y notin. apply~ H0.
  apply AWTerm_Let with (L \u dom G). apply~ IHsub. intros y notin. apply~ H0.
  apply AWTerm_CastUp. apply~ IHsub.
  apply AWTerm_CastDn. apply~ IHsub.
  apply AWTerm_Ann; f_equal~.
Qed.

Lemma cpltctxsubstctx_remove_soft: forall G H I G',
    ExtCtx G H ->
    Softness I ->
    AWf (H & I) ->
    CompleteCtx (H & I) ->
    ACpltCtxSubstCtx (H & I) G G' ->
    ACpltCtxSubstCtx H G G'.
Proof.
  introv ex soft wf comp sub.

  gen_eq HI: (H & I).
  gen I. induction sub; introv soft hi.

  apply empty_concat_inv in hi. destruct hi as [hi1 hi2]. subst. apply ACpltCtxSubstCtx_Empty.

  assert (binds x AC_Var (G & x ~ AC_Var)). apply binds_push_eq.
  destruct (declaration_preservation ex H2) as (v2 & bd).
  apply split_bind_context in bd. destruct bd as (HH1 & HH2 & hh). subst.
  rewrite <- concat_assoc in hi.
  symmetry in hi. apply tail_empty_eq2 in hi. destruct hi as [eqh [eqv eqh2]].
  symmetry in eqh2. destruct (empty_concat_inv eqh2) as [em1 em2]. subst. rewrite concat_empty_r in *.
  apply~ ACpltCtxSubstCtx_Var. rewrite hi. apply* awf_is_ok.
  apply* awf_is_ok.

  assert (binds x (AC_Typ t2) (G & x ~ AC_Typ t2)). apply binds_push_eq.
  destruct (declaration_preservation ex H4) as (v2 & bd).
  apply split_bind_context in bd. destruct bd as (HH1 & HH2 & hh). subst.
  rewrite <- concat_assoc in hi.
  symmetry in hi. apply tail_empty_eq2 in hi. destruct hi as [eqh [eqv eqh2]].
  symmetry in eqh2. destruct (empty_concat_inv eqh2) as [em1 em2]. subst. rewrite concat_empty_r in *.
  apply~ ACpltCtxSubstCtx_TypVar. rewrite hi. apply* awf_is_ok.
  apply* awf_is_ok.

  assert (binds x (AC_Bnd s2 t2) (G & x ~ AC_Bnd s2 t2)). apply binds_push_eq.
  destruct (declaration_preservation ex H6) as (v2 & bd).
  apply split_bind_context in bd. destruct bd as (HH1 & HH2 & hh). subst.
  rewrite <- concat_assoc in hi.
  symmetry in hi. apply tail_empty_eq2 in hi. destruct hi as [eqh [eqv eqh2]].
  symmetry in eqh2. destruct (empty_concat_inv eqh2) as [em1 em2]. subst. rewrite concat_empty_r in *.
  apply~ ACpltCtxSubstCtx_BndVar. rewrite hi. apply* awf_is_ok.
  apply* awf_is_ok.

  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)). apply binds_push_eq.
  destruct (declaration_preservation ex H2) as (v2 & bd).
  apply split_bind_context in bd. destruct bd as (HH1 & HH2 & hh). subst.
  rewrite <- concat_assoc in hi.
  symmetry in hi. apply tail_empty_eq2 in hi. destruct hi as [eqh [eqv eqh2]].
  symmetry in eqh2. destruct (empty_concat_inv eqh2) as [em1 em2]. subst. rewrite concat_empty_r in *.
  apply~ ACpltCtxSubstCtx_Solved_Unsolved_EVar. rewrite hi. apply* awf_is_ok.
  apply* awf_is_ok.

  assert (binds a (AC_Solved_EVar t2) (G & a ~ AC_Solved_EVar t2)). apply binds_push_eq.
  destruct (declaration_preservation ex H3) as (v2 & bd).
  apply split_bind_context in bd. destruct bd as (HH1 & HH2 & hh). subst.
  rewrite <- concat_assoc in hi.
  symmetry in hi. apply tail_empty_eq2 in hi. destruct hi as [eqh [eqv eqh2]].
  symmetry in eqh2. destruct (empty_concat_inv eqh2) as [em1 em2]. subst. rewrite concat_empty_r in *.
  apply~ ACpltCtxSubstCtx_Solved_Solved_EVar. rewrite hi. apply* awf_is_ok.
  apply* awf_is_ok.

  induction I0 using env_ind.
  rewrite concat_empty_r in hi.
  rewrite <- hi.
  apply~ ACpltCtxSubstCtx_Solved_EVar.
  apply IHsub with (I0:=I0); auto.
  apply* AWf_left.
  apply* soft_left.
  rewrite concat_assoc in hi.
  apply eq_push_inv in hi.
  destruct hi as [_ [_ eqh]]. auto.
Qed.

Lemma softness_cpltctxsubstctx: forall G G' H I a,
    Softness H ->
    ExtCtx (G & a ~ AC_Unsolved_EVar & H) I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I G G' ->
    exists I1 I2 t, I = I1 & a ~ (AC_Solved_EVar t) & I2 /\
         ACpltCtxSubstCtx I1 G G' /\ Softness I2.
Proof.
  introv soft ext comp sub.

  destruct (extension_order_unsolved_evar ext) as (I1 & I2 & [[hhi1 | (t & hhi2)] [hh1 hh2]]).
  assert (binds a AC_Unsolved_EVar I).
  rewrite hhi1. apply binds_middle_eq. apply ok_preservation in ext. rewrite hhi1 in ext. apply* ok_middle_inv_r.
  false complete_contains_unsolved comp H0.

  gen I1 I2 H. induction sub; intros I1 exti1 I2 hh HH soft ext softi2.

  false (empty_middle_inv hh).
  assert (xin: x \in dom I1). apply declaration_preservation_dom with (G & x ~ AC_Var); auto. simpl_dom. apply union_left. apply in_singleton_self.
  destruct (split_context xin) as (I11 & I12 & v & hinfo).
  rewrite hinfo in hh.
  assert (inv: H & x ~ AC_Var & empty = I11 & x ~ v & (I12 & a ~ AC_Solved_EVar t & I2)). rewrite~ concat_empty_r. do 2 rewrite~ concat_assoc.
  apply ok_middle_eq2 in inv; auto.
  destruct inv as [_ [_ inv]].
  false empty_middle_inv inv.
  rewrite~ concat_empty_r. apply* ok_preservation.
  rewrite <- inv. rewrite~ concat_empty_r. apply* ok_preservation.

  assert (xin: x \in dom I1). apply declaration_preservation_dom with (G & x ~ AC_Typ t2); auto. simpl_dom. apply union_left. apply in_singleton_self.
  destruct (split_context xin) as (I11 & I12 & v & hinfo).
  rewrite hinfo in hh.
  assert (inv: H & x ~ AC_Typ t1 & empty = I11 & x ~ v & (I12 & a ~ AC_Solved_EVar t & I2)). rewrite~ concat_empty_r. do 2 rewrite~ concat_assoc.
  apply ok_middle_eq2 in inv; auto.
  destruct inv as [_ [_ inv]].
  false empty_middle_inv inv.
  rewrite~ concat_empty_r. apply* ok_preservation.
  rewrite <- inv. rewrite~ concat_empty_r. apply* ok_preservation.

  assert (xin: x \in dom I1). apply declaration_preservation_dom with (G & x ~ AC_Bnd s2 t2); auto. simpl_dom. apply union_left. apply in_singleton_self.
  destruct (split_context xin) as (I11 & I12 & v & hinfo).
  rewrite hinfo in hh.
  assert (inv: H & x ~ AC_Bnd s1 t1 & empty = I11 & x ~ v & (I12 & a ~ AC_Solved_EVar t & I2)). rewrite~ concat_empty_r. do 2 rewrite~ concat_assoc.
  apply ok_middle_eq2 in inv; auto.
  destruct inv as [_ [_ inv]].
  false empty_middle_inv inv.
  rewrite~ concat_empty_r. apply* ok_preservation.
  rewrite <- inv. rewrite~ concat_empty_r. apply* ok_preservation.

  assert (xin: a0 \in dom I1). apply declaration_preservation_dom with (G & a0 ~ AC_Unsolved_EVar); auto. simpl_dom. apply union_left. apply in_singleton_self.
  destruct (split_context xin) as (I11 & I12 & v & hinfo).
  rewrite hinfo in hh.
  assert (inv: H & a0 ~ AC_Solved_EVar t0 & empty = I11 & a0 ~ v & (I12 & a ~ AC_Solved_EVar t & I2)). rewrite~ concat_empty_r. do 2 rewrite~ concat_assoc.
  apply ok_middle_eq2 in inv; auto.
  destruct inv as [_ [_ inv]].
  false empty_middle_inv inv.
  rewrite~ concat_empty_r. apply* ok_preservation.
  rewrite <- inv. rewrite~ concat_empty_r. apply* ok_preservation.

  assert (xin: a0 \in dom I1). apply declaration_preservation_dom with (G & a0 ~ AC_Solved_EVar t2); auto. simpl_dom. apply union_left. apply in_singleton_self.
  destruct (split_context xin) as (I11 & I12 & v & hinfo).
  rewrite hinfo in hh.
  assert (inv: H & a0 ~ AC_Solved_EVar t1 & empty = I11 & a0 ~ v & (I12 & a ~ AC_Solved_EVar t & I2)). rewrite~ concat_empty_r. do 2 rewrite~ concat_assoc.
  apply ok_middle_eq2 in inv; auto.
  destruct inv as [_ [_ inv]].
  false empty_middle_inv inv.
  rewrite~ concat_empty_r. apply* ok_preservation.
  rewrite <- inv. rewrite~ concat_empty_r. apply* ok_preservation.

  destruct (eq_var_dec a a0).
  subst.
  assert (inv: H & a0 ~ AC_Solved_EVar t0 & empty = I1 & a0 ~ AC_Solved_EVar t & I2). rewrite~ concat_empty_r.
  apply ok_middle_eq2 in inv; auto.
  destruct inv as [eqh [eqv eqi]]. inversion eqv. subst.
  exists~ I1 (empty:ACtx) t.
  rewrite concat_empty_r. apply* ok_preservation.
  rewrite <- inv. rewrite concat_empty_r. apply* ok_preservation.

  assert (a0 <> a) by auto.
  destruct (tail_exists_eq H2 hh) as (I3 & hi2).
  subst.
  exists I1 (I3 & a0 ~ AC_Solved_EVar t0) t.
  split; auto.
  rewrite concat_assoc in hh.
  apply eq_push_inv in hh.
  destruct hh as [_ [eqv eqh]]. subst.
  split; auto. clear eqv n.

  rewrite <- concat_assoc in sub.
  apply cpltctxsubstctx_remove_soft in sub; auto.
  apply~ soft_append. apply~ soft_single_solved. lets: softi2 soft.
  apply* soft_left.
  apply ok_preservation in ext. destruct (ok_concat_inv ext) as [okx _]. rewrite <- concat_assoc in okx. apply* ok_concat_inv.
  apply awf_preservation in ext. rewrite~ concat_assoc. apply* AWf_left.
  rewrite~ concat_assoc.
Qed.

Lemma cpltctxsubstctx_append_soft: forall I G G' H,
    AWf (I & H) ->
    CompleteCtx (I & H) ->
    Softness H ->
    ACpltCtxSubstCtx I G G' ->
    ACpltCtxSubstCtx (I & H) G G'.
Proof.
  introv wf comp soft sub.
  induction H using env_ind.
  rewrite~ concat_empty_r.
  rewrite concat_assoc in *.
  inversion soft.
  false empty_push_inv H1.
  destruct (eq_push_inv H0) as [eqx [eqv eqg]]. subst.
  assert (binds x AC_Unsolved_EVar (I & H & x ~ AC_Unsolved_EVar)). apply~ binds_push_eq.
  false complete_contains_unsolved comp H3.

  destruct (eq_push_inv H0) as [eqx [eqv eqg]]. subst.
  apply ACpltCtxSubstCtx_Solved_EVar.
  apply* complete_part_left.
  apply~ IHenv. apply* AWf_left.
  apply* complete_part_left.
  apply awf_is_ok in wf.
  apply ok_push_inv in wf.
  inversion~ wf.
Qed.

Lemma cpltctxtsubst_remove': forall m n I1 I2 t d x v,
   AWf (I1 & x ~ v & I2) ->
   AWf (I1 & I2) ->
   CompleteCtx (I1 & x ~ v & I2) ->
   ACpltCtxSubst (I1 & x ~ v & I2) t d ->
   x \notin AFv t ->
   ALen (I1 & x ~ v & I2) t n ->
   n < m ->
   ACpltCtxSubst (I1 & I2) t d.
Proof.
  intro m.
  induction m.
  introv wfx wf comp sub notin len less. inversion less.
  introv wfx wf comp sub notin len less.

  gen_eq I : (I1 & x ~ v & I2).
  gen I2 n. induction sub; introv wf len less hg.

  subst. simpls.
  apply notin_singleton in notin.
  assert (x0 <> x) by auto.
  lets: binds_subst H0 H1. apply~ ACpltCtxSubst_Var.
  apply complete_append.
  rewrite <- concat_assoc in comp. apply complete_part_left in comp. assumption. rewrite concat_assoc. apply* awf_is_ok.
  apply complete_part_right in comp. assumption. apply* awf_is_ok.

  subst. simpls.
  apply notin_singleton in notin.
  assert (x0 <> x) by auto.
  lets: binds_subst H0 H1. apply ACpltCtxSubst_TyVar with t; auto.
  apply complete_append.
  rewrite <- concat_assoc in comp. apply complete_part_left in comp. assumption. rewrite concat_assoc. apply* awf_is_ok.
  apply complete_part_right in comp. assumption. apply* awf_is_ok.

  subst. simpls.
  apply notin_singleton in notin.
  assert (x0 <> x) by auto.
  lets: binds_subst H0 H1. apply ACpltCtxSubst_BndVar with t e; auto.
  apply complete_append.
  rewrite <- concat_assoc in comp. apply complete_part_left in comp. assumption. rewrite concat_assoc. apply* awf_is_ok.
  apply complete_part_right in comp. assumption. apply* awf_is_ok.

  subst. simpls.
  apply notin_singleton in notin.

  assert(binds a (AC_Solved_EVar t) (I1 & x ~ v & I2)).
  rewrite <- hg.
  apply binds_concat_left_ok. apply* awf_is_ok.
  apply binds_push_eq.
  assert (a <> x) by auto.
  lets: (binds_subst H2 H3).
  apply binds_concat_inv in H4.
  destruct H4 as [bd | bd].
  apply split_bind_context in bd.
  destruct bd as (I11 & I12 & iinfo). subst.
  repeat(rewrite concat_assoc).
  apply~ ACpltCtxSubst_EVar.
  apply complete_append. rewrite hg in comp. rewrite <- concat_assoc in comp. apply complete_part_left in comp. assumption.
  rewrite concat_assoc. rewrite <- hg. assumption.
  rewrite hg in comp. apply complete_part_right in comp. rewrite <- concat_assoc in comp. apply complete_part_left in comp. assumption.
  rewrite hg in wfx. rewrite concat_assoc. apply awf_is_ok in wfx. apply ok_concat_inv_r in wfx. assumption.
  rewrite hg in wfx. do 2 rewrite concat_assoc in wfx. apply awf_is_ok in wfx. do 2 apply ok_concat_inv_l in wfx. apply ok_remove in wfx. assumption.
  repeat (rewrite concat_assoc in hg). rewrite hg in comp. apply complete_part_right in comp. assumption.
  rewrite hg in wfx. apply awf_is_ok in wfx.  apply ok_remove in wfx. do 2 rewrite concat_assoc in wfx. assumption.
  repeat(rewrite concat_assoc in hg). apply ok_middle_eq2 in hg; auto.
  destruct hg as [okg [okt okg2]]. subst. clear okt.
  assert (exists m, ALen (I1 & x ~ v & I11) t m).
  apply alen_exists.
  rewrite <- concat_assoc in wfx. apply AWf_left in wfx. auto.
  destruct H4 as (mt & alen_t).
  apply IHm with mt x v; auto.
  rewrite <- concat_assoc in wfx. apply AWf_left in wfx. auto.
  repeat (rewrite concat_assoc in wf).
  rewrite <- concat_assoc in wf. apply AWf_left in wf. auto.
  assert (x # (I1 & I11)). rewrite <- concat_assoc in H1. apply ok_concat_inv_l in H1. apply ok_middle_inv in H1. simpl_dom. auto_star.
  assert (AWTerm (I1 & I11) t). do 2 rewrite concat_assoc in wf. apply AWf_left in wf. apply awterm_solved_evar in wf. assumption.
  lets: notin_awterm H5 H4. auto.
  assert (n = mt + 1). apply alen_evar with (I1 & x ~ v & I11) (I12) a t; auto.
  Omega.omega.
  rewrite~ <- hg.

  destruct bd as [notina bd].
  apply split_bind_context in bd.
  destruct bd as (I11 & I12 & iinfo). subst.
  rewrite <- concat_assoc. apply~ ACpltCtxSubst_EVar.
  rewrite hg in comp.
  do 3 rewrite <- concat_assoc in comp. apply complete_part_left in comp. assumption. do 3 rewrite concat_assoc.  rewrite hg in wfx. apply* awf_is_ok.
  rewrite hg in comp.
  apply complete_append.
  rewrite <- concat_assoc in comp. apply complete_part_left in comp. apply complete_part_right in comp. assumption. rewrite concat_assoc.  rewrite hg in wfx. apply* awf_is_ok.
  apply complete_part_right in comp. assumption.
  rewrite hg in wfx. apply awf_is_ok in wfx.
  assert(ok (I11 & a ~ AC_Solved_EVar t & (I12 & x ~ v & I2))). repeat(rewrite concat_assoc). assumption.
  apply ok_concat_inv_r in H4. apply ok_remove in H4. assumption.
  rewrite hg in wfx.
  rewrite concat_assoc. apply awf_is_ok in wfx.
  apply ok_remove in wfx. assumption.

  assert (hg2: G1 & a ~ AC_Solved_EVar t & G2 = I11 & a ~ AC_Solved_EVar t & (I12 & x ~ v & I2)). repeat(rewrite~ concat_assoc).
  apply ok_middle_eq2 in hg2; auto.
  destruct hg2 as [eqgi [eqt eqgi2]]. inversion eqt. subst. assumption.
  rewrite hg2 in H1. assumption.

  apply ACpltCtxSubst_Star.
  simpls. inversion len; subst. apply ACpltCtxSubst_App. apply IHsub1 with i1; auto. Omega.omega.
  apply IHsub2 with i2; auto. Omega.omega.

  apply ACpltCtxSubst_Lam with (L \u dom G \u AFv t \u \{x}).
  intros y notiny.
  subst.
  inversion len; subst.
  assert (IH1: y \notin L) by auto_star.
  assert (IH2: AWf (I1 & x ~ v & I2 & y ~ AC_Var)) by apply~ AWf_Var.
  assert (IH3: CompleteCtx (I1 & x ~ v & I2 & y ~AC_Var)) by apply~ complete_add.
  assert (IH4: x\notin AFv (t @ y)). apply~ notin_open_inv. simpls. apply notin_singleton. auto_star.
  assert (IH5: AWf (I1 & (I2 & y ~ AC_Var))). rewrite concat_assoc. apply~ AWf_Var.
  assert (IH6: ALen (I1 & x ~ v & I2 & y ~ AC_Var) (t @ y) i). apply alen_add_var with (y:=y) in H3; auto. apply alen_open with (y:=y) in H3; auto.
  assert (IH7: i < S m) by Omega.omega.
  assert (IH8: I1 & x ~ v & I2 & y ~ AC_Var = I1 & x ~ v & (I2 & y ~ AC_Var)) by rewrite~ concat_assoc.
  lets: H0 y IH1 IH2 IH3 IH4.
  lets: H1 (I2 & y ~ AC_Var) IH5 i IH6. clear H1.
  lets: H2 IH7 IH8. clear H2.
  rewrite concat_assoc in H1. assumption.

  simpls. inversion len; subst.
  apply ACpltCtxSubst_Pi with (L \u dom I1 \u dom I2 \u AFv t1 \u AFv t2 \u \{x}).
  apply IHsub with i1; auto. Omega.omega.
  intros y notiny.
  subst.
  assert (IH1: y \notin L) by auto_star.
  assert (IH2: AWf (I1 & x ~ v & I2 & y ~ AC_Var)) by apply~ AWf_Var.
  assert (IH3: CompleteCtx (I1 & x ~ v & I2 & y ~AC_Var)) by apply~ complete_add.
  assert (IH4: x\notin AFv (t2 @ y)). apply~ notin_open_inv. simpls. apply notin_singleton. auto_star.
  assert (IH5: AWf (I1 & (I2 & y ~ AC_Var))). rewrite concat_assoc. apply~ AWf_Var.
  assert (IH6: ALen (I1 & x ~ v & I2 & y ~ AC_Var) (t2 @ y) i2). apply alen_add_var with (y:=y) in H6; auto. apply alen_open with (y:=y) in H6; auto.
  assert (IH7: i2 < S m) by Omega.omega.
  assert (IH8: I1 & x ~ v & I2 & y ~ AC_Var = I1 & x ~ v & (I2 & y ~ AC_Var)) by rewrite~ concat_assoc.
  lets: H0 y IH1 IH2 IH3 IH4.
  lets: H1 (I2 & y ~ AC_Var) IH5 i2 IH6. clear H1.
  lets: H2 IH7 IH8. clear H2.
  rewrite concat_assoc in H1. assumption.

  simpls. inversion len; subst.
  apply ACpltCtxSubst_Let with (L \u dom I1 \u dom I2 \u AFv t1 \u AFv t2 \u \{x}).
  apply IHsub with i1; auto. Omega.omega.
  intros y notiny.
  subst.
  assert (IH1: y \notin L) by auto_star.
  assert (IH2: AWf (I1 & x ~ v & I2 & y ~ AC_Var)) by apply~ AWf_Var.
  assert (IH3: CompleteCtx (I1 & x ~ v & I2 & y ~AC_Var)) by apply~ complete_add.
  assert (IH4: x\notin AFv (t2 @ y)). apply~ notin_open_inv. simpls. apply notin_singleton. auto_star.
  assert (IH5: AWf (I1 & (I2 & y ~ AC_Var))). rewrite concat_assoc. apply~ AWf_Var.
  assert (IH6: ALen (I1 & x ~ v & I2 & y ~ AC_Var) (t2 @ y) i2). apply alen_add_var with (y:=y) in H6; auto. apply alen_open with (y:=y) in H6; auto.
  assert (IH7: i2 < S m) by Omega.omega.
  assert (IH8: I1 & x ~ v & I2 & y ~ AC_Var = I1 & x ~ v & (I2 & y ~ AC_Var)) by rewrite~ concat_assoc.
  lets: H0 y IH1 IH2 IH3 IH4.
  lets: H1 (I2 & y ~ AC_Var) IH5 i2 IH6. clear H1.
  lets: H2 IH7 IH8. clear H2.
  rewrite concat_assoc in H1. assumption.

  simpls. inversion len; subst.
  apply ACpltCtxSubst_CastUp; auto.
  apply IHsub with i; auto. Omega.omega.

  simpls. inversion len; subst.
  apply ACpltCtxSubst_CastDn; auto.
  apply IHsub with i; auto. Omega.omega.

  simpls. inversion len; subst. apply ACpltCtxSubst_Ann. apply IHsub1 with i1; auto. Omega.omega.
  apply IHsub2 with i2; auto. Omega.omega.
Qed.

Lemma cpltctxtsubst_remove: forall I1 I2 t d x v,
   AWf (I1 & x ~ v & I2) ->
   AWf (I1 & I2) ->
   CompleteCtx (I1 & x ~ v & I2) ->
   ACpltCtxSubst (I1 & x ~ v & I2) t d ->
   x \notin AFv t ->
   ACpltCtxSubst (I1 & I2) t d.
Proof.
  introv. intros.
  destruct(@alen_exists (I1 & x ~ v & I2) t) as (n & ex). auto.
  apply* cpltctxtsubst_remove'.
Qed.

Lemma cpltctxsubst_weaken: forall I1 t d x v,
   AWf (I1 & x ~ v) ->
   CompleteCtx (I1 & x ~ v) ->
   ACpltCtxSubst (I1 & x ~ v) t d ->
   x \notin AFv t ->
   ACpltCtxSubst I1 t d.
Proof.
  intros.
  assert (ACpltCtxSubst (I1 & empty) t d).
  apply cpltctxtsubst_remove with (I2:=empty) (x:=x) (v:=v); repeat(rewrite concat_empty_r); auto.
  apply* AWf_left.
  rewrite concat_empty_r in H3. auto.
Qed.

Lemma cpltctxtsubst_weaken_append: forall I1 I2 t d,
   AWf (I1 & I2) ->
   CompleteCtx (I1 & I2) ->
   ACpltCtxSubst (I1 & I2) t d ->
   AWTerm I1 t ->
   ACpltCtxSubst I1 t d.
Proof.
  introv wf comp sub wt.
  induction I2 using env_ind.
  rewrite concat_empty_r in sub. auto.
  assert (x # I1). rewrite concat_assoc in wf. apply awf_is_ok in wf. destruct (ok_push_inv wf) as [_ notin]. auto_star.
  lets: notin_awterm wt H.
  rewrite concat_assoc in *.
  lets: cpltctxsubst_weaken (I1 & I2) t d x.
  lets: H1 wf comp sub H0.
  apply~ IHI2.
  apply* AWf_left.
  apply* complete_part_left.
Qed.
