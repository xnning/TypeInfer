Require Import LibLN.
Require Import DeclDef.
Require Import DeclInfra.
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

Lemma extension_append: forall G H I,
    ExtCtx G H ->
    AWf (G & I) ->
    AWf (H & I) ->
    ExtCtx (G & I) (H & I).
Proof.
  introv ex wfgi wfhi.
  induction I using env_ind.
  repeat rewrite concat_empty_r in *. auto.
  repeat rewrite concat_assoc in *. auto.
  induction v; auto.
  apply~ ExtCtx_Var. apply~ IHI. apply* AWf_left. apply* AWf_left.
  apply~ ExtCtx_TypVar. apply~ IHI. apply* AWf_left. apply* AWf_left.
  apply~ ExtCtx_TVar. apply~ IHI. apply* AWf_left. apply* AWf_left.
  apply~ ExtCtx_EVar. apply~ IHI. apply* AWf_left. apply* AWf_left.
  apply~ ExtCtx_SolvedEVar. apply~ IHI. apply* AWf_left. apply* AWf_left.
Qed.

(* properties about cpltctxsubst *)

Lemma cpltctxsubst_wftyp: forall G s t,
    AWf G ->
    ACpltCtxSubst G s t ->
    AWTermT G s.
Proof.
  introv wf sub.
  induction sub.
  constructor~.
  apply* AWTermT_TypVar.
  apply* AWTermT_TFVar.
  apply AWTermT_Solved_EVar with t. apply binds_concat_left_ok. apply~ awf_is_ok. apply binds_push_eq.
  apply~ AWTermT_Star.
  apply~ AWTermT_App.
  apply AWTermT_Lam with (L \u dom G). intros y notin. apply~ H0.
  apply AWTermT_Pi with (L \u dom G). apply~ IHsub. intros y notin. apply~ H0.
  apply AWTermT_CastUp. apply~ IHsub.
  apply AWTermT_CastDn. apply~ IHsub.
  apply AWTermT_Ann; f_equal~.
  apply AWTermT_Forall with (L \u dom G). intros y notin. apply~ H0.
Qed.

Lemma cpltctxsubst_awterm: forall G t d,
      ACpltCtxSubst G t d ->
      AWTermT G t.
Proof.
  introv sub.
  induction sub; simpls; f_equal ~.
  apply AWTermT_TypVar with t; auto.
  apply AWTermT_Solved_EVar with t; auto. apply binds_middle_eq. apply* ok_middle_inv.
  apply AWTermT_Lam with L. intros y notin. apply (H0 y notin).
  apply AWTermT_Pi with L. auto. intros y notin. apply (H0 y notin).
  apply AWTermT_Forall with L. auto.
Qed.

Lemma cpltctxsubst_notin: forall G t d y,
    ACpltCtxSubst G t d ->
    y # G ->
    y \notin DTFv d.
Proof.
  introv sub notin.
  induction sub; simpls; try(solve[f_equal *]).
  apply notin_singleton. introv xyeq. subst. false binds_fresh_inv H0 notin0.
  apply notin_singleton. introv xyeq. subst. false binds_fresh_inv H0 notin0.
  apply notin_singleton. introv xyeq. subst. false binds_fresh_inv H0 notin0.

  pick_fresh z.
  assert (z \notin L) by auto_star.
  assert (y # G & z ~ AC_Var). simpl_dom. auto_star.
  lets: H0 H1 H2.
  apply notin_dopen_fv in H3. auto.

  pick_fresh z.
  assert (z \notin L) by auto_star.
  assert (y # G & z ~ AC_Var). simpl_dom. auto_star.
  lets: IHsub notin.
  lets: H0 H1 H2. apply notin_dopent_fv in H4.
  auto.

  pick_fresh z.
  assert (z \notin L) by auto_star.
  assert (y # G & z ~ AC_TVar). simpl_dom. auto_star.
  lets: H0 H1 H2. apply notin_dtopent_fv in H3.
  auto.
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

  assert (binds a AC_TVar (G & a ~ AC_TVar)). apply binds_push_eq.
  destruct (declaration_preservation ex H2) as (v2 & bd).
  apply split_bind_context in bd. destruct bd as (HH1 & HH2 & hh). subst.
  rewrite <- concat_assoc in hi.
  symmetry in hi. apply tail_empty_eq2 in hi. destruct hi as [eqh [eqv eqh2]].
  symmetry in eqh2. destruct (empty_concat_inv eqh2) as [em1 em2]. subst. rewrite concat_empty_r in *.
  apply~ ACpltCtxSubstCtx_TVar. rewrite hi. apply* awf_is_ok.
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

  assert (xin: a0 \in dom I1). apply declaration_preservation_dom with (G & a0 ~ AC_TVar); auto. simpl_dom. apply union_left. apply in_singleton_self.
  destruct (split_context xin) as (I11 & I12 & v & hinfo).
  rewrite hinfo in hh.
  assert (inv: H & a0 ~ AC_TVar & empty = I11 & a0 ~ v & (I12 & a ~ AC_Solved_EVar t & I2)). rewrite~ concat_empty_r. do 2 rewrite~ concat_assoc.
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

Lemma cpltctxsubst_remove': forall m n I1 I2 t d x v,
   AWf (I1 & x ~ v & I2) ->
   AWf (I1 & I2) ->
   CompleteCtx (I1 & x ~ v & I2) ->
   ACpltCtxSubst (I1 & x ~ v & I2) t d ->
   x \notin ATFv t ->
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
  lets: binds_subst H0 H1. apply ACpltCtxSubst_TVar; auto.
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
  apply AWf_left in wfx. apply awterm_solved_evar in wfx. auto.
  destruct H4 as (mt & alen_t).
  apply IHm with mt x v; auto.
  rewrite <- concat_assoc in wfx. apply AWf_left in wfx. auto.
  repeat (rewrite concat_assoc in wf).
  rewrite <- concat_assoc in wf. apply AWf_left in wf. auto.
  assert (x # (I1 & I11)). rewrite <- concat_assoc in H1. apply ok_concat_inv_l in H1. apply ok_middle_inv in H1. simpl_dom. auto_star.
  assert (AWTermT (I1 & I11) t). do 2 rewrite concat_assoc in wf. apply AWf_left in wf. apply awterm_solved_evar in wf. assumption.
  lets: notin_awtermt H5 H4. auto.
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
  assert (IH4: x\notin ATFv (AT_Expr (t @ y))). apply~ notin_open_inv. simpls. apply notin_singleton. auto_star.
  assert (IH5: AWf (I1 & (I2 & y ~ AC_Var))). rewrite concat_assoc. apply~ AWf_Var.
  assert (IH6: ALen (I1 & x ~ v & I2 & y ~ AC_Var) (AT_Expr (t @ y)) i). apply alen_add_var with (y:=y) in H3; auto. apply alen_open with (y:=y) (n:=0) in H3; auto.
  assert (IH7: i < S m) by Omega.omega.
  assert (IH8: I1 & x ~ v & I2 & y ~ AC_Var = I1 & x ~ v & (I2 & y ~ AC_Var)) by rewrite~ concat_assoc.
  lets: H0 y IH1 IH2 IH3 IH4.
  lets: H1 (I2 & y ~ AC_Var) IH5 i IH6. clear H1.
  lets: H2 IH7 IH8. clear H2.
  rewrite concat_assoc in H1. assumption.

  simpls. inversion len; subst.
  apply ACpltCtxSubst_Pi with (L \u dom I1 \u dom I2 \u ATFv t1 \u ATFv t2 \u \{x}).
  apply IHsub with i1; auto. Omega.omega.
  intros y notiny.
  subst.
  assert (IH1: y \notin L) by auto_star.
  assert (IH2: AWf (I1 & x ~ v & I2 & y ~ AC_Var)) by apply~ AWf_Var.
  assert (IH3: CompleteCtx (I1 & x ~ v & I2 & y ~AC_Var)) by apply~ complete_add.
  assert (IH4: x\notin ATFv (t2 @' y)). apply~ notin_opent_inv. simpls. apply notin_singleton. auto_star.
  assert (IH5: AWf (I1 & (I2 & y ~ AC_Var))). rewrite concat_assoc. apply~ AWf_Var.
  assert (IH6: ALen (I1 & x ~ v & I2 & y ~ AC_Var) (t2 @' y) i2). apply alen_add_var with (y:=y) in H6; auto. apply alen_open with (y:=y) (n:=0) in H6; auto.
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

  apply ACpltCtxSubst_Forall with (L \u dom G \u ATFv s1 \u \{x}).
  intros y notiny.
  subst.
  inversion len; subst.
  assert (IH1: y \notin L) by auto_star.
  assert (IH2: AWf (I1 & x ~ v & I2 & y ~ AC_TVar)) by apply~ AWf_TVar.
  assert (IH3: CompleteCtx (I1 & x ~ v & I2 & y ~AC_TVar)) by apply~ complete_add_tvar.
  assert (IH4: x\notin ATFv (s1 @#' y)). apply~ notin_topent_inv. simpls. apply notin_singleton. auto_star.
  assert (IH5: AWf (I1 & (I2 & y ~ AC_TVar))). rewrite concat_assoc. apply~ AWf_TVar.
  assert (IH6: ALen (I1 & x ~ v & I2 & y ~ AC_TVar) (s1 @#' y) i). apply alen_add_tvar with (y:=y) in H3; auto. apply alen_topen with (y:=y) (n:=0) in H3; auto.
  assert (IH7: i < S m) by Omega.omega.
  assert (IH8: I1 & x ~ v & I2 & y ~ AC_TVar = I1 & x ~ v & (I2 & y ~ AC_TVar)) by rewrite~ concat_assoc.
  lets: H0 y IH1 IH2 IH3 IH4.
  lets: H1 (I2 & y ~ AC_TVar) IH5 i IH6. clear H1.
  lets: H2 IH7 IH8. clear H2.
  rewrite concat_assoc in H1. assumption.
Qed.

Lemma cpltctxsubst_remove: forall I1 I2 t d x v,
   AWf (I1 & x ~ v & I2) ->
   AWf (I1 & I2) ->
   CompleteCtx (I1 & x ~ v & I2) ->
   ACpltCtxSubst (I1 & x ~ v & I2) t d ->
   x \notin ATFv t ->
   ACpltCtxSubst (I1 & I2) t d.
Proof.
  introv. intros.
  destruct(@alen_exists (I1 & x ~ v & I2) t) as (n & ex). auto.
  apply awterm_is_awterma.
  apply* cpltctxsubst_wftyp.
  apply* cpltctxsubst_remove'.
Qed.

Lemma cpltctxsubst_weaken: forall I1 t d x v,
   AWf (I1 & x ~ v) ->
   CompleteCtx (I1 & x ~ v) ->
   ACpltCtxSubst (I1 & x ~ v) t d ->
   x \notin ATFv t ->
   ACpltCtxSubst I1 t d.
Proof.
  intros.
  assert (ACpltCtxSubst (I1 & empty) t d).
  apply cpltctxsubst_remove with (I2:=empty) (x:=x) (v:=v); repeat(rewrite concat_empty_r); auto.
  apply* AWf_left.
  rewrite concat_empty_r in H3. auto.
Qed.

Lemma cpltctxsubst_weaken_append: forall I1 I2 t d,
   AWf (I1 & I2) ->
   CompleteCtx (I1 & I2) ->
   ACpltCtxSubst (I1 & I2) t d ->
   AWTermT I1 t ->
   ACpltCtxSubst I1 t d.
Proof.
  introv wf comp sub wt.
  induction I2 using env_ind.
  rewrite concat_empty_r in sub. auto.
  assert (x # I1). rewrite concat_assoc in wf. apply awf_is_ok in wf. destruct (ok_push_inv wf) as [_ notin]. auto_star.
  lets: notin_awtermt wt H.
  rewrite concat_assoc in *.
  lets: cpltctxsubst_weaken (I1 & I2) t d x.
  lets: H1 wf comp sub H0.
  apply~ IHI2.
  apply* AWf_left.
  apply* complete_part_left.
Qed.

Hint Resolve awf_is_ok.

Lemma actxtsubst_append: forall G H t,
    ok (G & H) ->
    AWTermT G t ->
    ACtxTSubst (G & H) t = ACtxTSubst G t.
Proof.
  introv okg wt.
  induction H using env_ind.
  rewrite~ concat_empty_r.
  rewrite concat_assoc.
  rewrite tsubst_add_ctx.

  assert (ACtxTSubst (x ~ v) t = t).
  rewrite single_def. unfold ACtxTSubst. rewrite LibList.fold_left_cons. rewrite LibList.fold_left_nil.
  destruct v; simpls; auto.
  apply atsubstt_fresh.
  apply notin_tfv_tftv.
  apply notin_awtermt with G; auto.
  rewrite concat_assoc in okg.
  destruct (ok_push_inv okg) as [_ okg2]. auto_star.
  rewrite H0. apply* IHenv.
  rewrite concat_assoc in okg.
  destruct (ok_push_inv okg) as [okg1 _]. auto_star.
Qed.

Lemma ctxsubst_awterm' : forall G t n m,
    AWf G ->
    AWTermT G t ->
    n < m ->
    ALen G t n ->
    AWTermT G (ACtxTSubst G t).
Proof.
  intros. gen G t n. induction m; introv wf wt less len.
  inversion less.


  gen n. induction wt; introv less len; simpls; auto.

  (* AE_FVar *)
  assert (ACtxTSubst G (AT_Expr (AE_FVar x)) = AT_Expr (AE_FVar x)).
  rewrite actxtsubst_expr. f_equal.
  apply ctxsubst_fvar_eq; auto.
  rewrite H0.
  apply* AWTermT_Var.

  (* AE_FVar *)
  assert (ACtxTSubst G (AT_Expr (AE_FVar x)) = AT_Expr (AE_FVar x)).
  rewrite* actxtsubst_expr. f_equal ~.
  apply* ctxsubst_fvar_eq.
  rewrite H0.
  apply* AWTermT_TypVar.

  (* Star *)
  rewrite tsubst_star.
  apply AWTermT_Star.

  (* APP *)
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_app.
  inversion len; subst.
  apply* AWTermT_App.
  apply IHwt1 with i1; auto. Omega.omega.
  apply IHwt2 with i2; auto. Omega.omega.

  (* Lam *)
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_lam.
  apply AWTermT_Lam with (L \u dom G).
  intros y notiny.
  assert (AWf (G & y ~ AC_Var)). apply* AWf_Var.
  assert (y \notin L) by auto_star.
  lets: H0 H2 H1.
  rewrite actxtsubst_expr in H3.
  rewrite subst_add_var in H3.
  inversion len; subst.
  apply alen_open_expr with (n:=0) (y:=y) in H6; auto.
  apply alen_add_var_expr with (y:=y) in H6; auto.
  lets: H3 H6. Omega.omega.

  rewrite actxsubst_open in H4; auto.
  rewrite ctxsubst_fvar_eq in H4; auto.

  (* Pi *)
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_pi.
  inversion len; subst.
  apply AWTermT_Pi with (L \u dom G).
  apply IHwt with (n:=i1); auto. Omega.omega.
  intros y notiny.
  assert (AWf (G & y ~ AC_Var)). apply* AWf_Var.
  assert (y \notin L) by auto_star.
  lets: H0 H2 H1.
  rewrite tsubst_add_var in H3.
  apply alen_open with (n:=0) (y:=y) in H6; auto.
  apply alen_add_var with (y:=y) in H6; auto.
  lets: H3 H6. Omega.omega.

  rewrite actxtsubst_open in H5; auto.
  rewrite ctxsubst_fvar_eq in H5; auto.

  (* CASTUP *)
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_castup.
  apply AWTermT_CastUp.
  inversion len; subst.
  apply IHwt with i; auto. Omega.omega.

  (* CASTDOWN *)
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_castdn.
  apply AWTermT_CastDn.
  inversion len; subst.
  apply IHwt with i; auto. Omega.omega.

  (* ANN *)
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_ann.
  inversion len; subst.
  apply AWTermT_Ann.
  apply IHwt1 with i1; auto. Omega.omega.
  apply IHwt2 with i2; auto. Omega.omega.

  (* FORALL *)
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_forall.
  inversion len; subst.
  apply AWTermT_Forall with (L \u dom G).
  intros y notiny.
  assert (AWf (G & y ~ AC_TVar)). apply* AWf_TVar.
  assert (y \notin L) by auto_star.
  lets: H0 H2 H1.
  rewrite tsubst_add_tvar in H4.
  apply alen_topen with (n:=0) (y:=y) in H3; auto.
  apply alen_add_tvar with (y:=y) in H3; auto.
  lets: H4 H3. Omega.omega.

  rewrite actxtsubst_topen in H5.
  rewrite ctxsubst_tvar_eq in H5; auto.
  apply AWf_left in H1; auto.

  (* TVar *)
  rewrite* ctxsubst_tvar_eq.
  (* Unsolved EVAR *)
  rewrite* ctxsubst_evar_eq.

  (* Solved EVar*)
  destruct (split_bind_context H) as (G1 & G2 & hg).
  assert (AWTermT G t) by apply* awterm_evar_binds.
  assert (exists n1, ALen G1 t n1). apply* alen_exists. rewrite hg in wf. do 2 apply AWf_left in wf. auto.
  rewrite hg in wf. apply AWf_left in wf. apply awterm_solved_evar in wf. apply* awterm_is_awterma.
  destruct H1 as (n1 & len_t).
  assert (n1 < m). rewrite hg in len. apply alen_evar with (G2:=G2) (a:=i) (n:=n) in len_t; auto. Omega.omega. rewrite <- hg. apply* awf_is_ok.
  lets: IHm wf H0 n1 H1.

  assert (ALen (G1 & (i ~ AC_Solved_EVar t & G2)) t n1).
  apply* alen_awterm_append.
  rewrite concat_assoc. rewrite <- hg. auto.
  apply awterm_is_awterma. rewrite hg in wf. apply AWf_left in wf. apply awterm_solved_evar in wf. auto.
  rewrite concat_assoc in H3. rewrite <- hg in H3.
  lets: H2 H3.

  rewrite hg.
  rewrite tsubst_add_ctx.
  assert (i # G2). rewrite hg in wf. apply awf_is_ok in wf. apply* ok_middle_inv_r.
  rewrite* ctxsubst_evar_eq.
  simpls.
  rewrite tsubst_add_ctx.
  assert (ACtxTSubst (i ~ AC_Solved_EVar t) (AT_EVar i) = t). unfold ACtxTSubst.
  rewrite single_def.
  rewrite LibList.fold_left_cons.
  rewrite LibList.fold_left_nil.
  simpls. case_if*.

  rewrite H6. clear H6.
  rewrite <- actxtsubst_append with (H:=i ~ AC_Solved_EVar t & G2); auto.
  rewrite concat_assoc. rewrite <- hg. auto.

  rewrite concat_assoc. rewrite~ <- hg.
  rewrite hg in wf. apply AWf_left in wf. apply awterm_solved_evar in wf; auto.
  rewrite hg in wf.
  apply* ok_concat_inv_r.
Qed.

Lemma ctxsubst_awterm : forall G t,
    AWf G ->
    AWTermT G t ->
    AWTermT G (ACtxTSubst G t).
Proof.
  intros.
  assert (exists n, ALen G t n). apply~ alen_exists.
  destruct H1 as (n & len).
  apply* ctxsubst_awterm'.
Qed.
