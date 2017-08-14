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
    AWfTyp (G & x ~ AC_Typ e1) (e2 @' x).
Admitted.

Lemma awftyp_forall_evar: forall G e x,
    AWfTyp G (AT_Expr (AE_Forall e)) ->
    x # G ->
    AWfTyp (G & x ~ AC_Unsolved_EVar) (e @@#' (AT_EVar x)).
Admitted.

Lemma promise_fresh: forall (x:var) L,
    x \notin L.
Admitted.

Lemma acpltctxsubst_complete: forall I s t,
    ok I ->
    ACpltCtxSubst I s t ->
    CompleteCtx I.
Proof.
  introv oki sub.
  induction sub; auto.
  apply~ complete_append. apply~ complete_add_solved.
  pick_fresh y. assert (y \notin L) by auto.
  assert (ok (G & y ~ AC_Var)). apply~ ok_push.
  lets: H0 H1 H2.
  apply complete_part_left in H3; auto.

  pick_fresh y. assert (y \notin L) by auto.
  assert (ok (G & y ~ AC_TVar)). apply~ ok_push.
  lets: H0 H1 H2.
  apply complete_part_left in H3; auto.
Qed.

Lemma acpltctxsubst_add_tvar: forall I s t x,
    AWf I ->
    ACpltCtxSubst I s t ->
    x # I ->
    ACpltCtxSubst (I & x ~ AC_TVar) s t.
Proof.
  introv wf sub notin.
  apply~ a2d_cpltctxsubst.
  lets: cpltctxsubst_wftyp wf sub.
  apply~ awtermt_weaken.
  apply~ complete_add_tvar.
  lets: acpltctxsubst_complete sub; auto.
  lets: acpltctxsubst_ctxsubst_a2d wf sub.
  rewrite~ tsubst_add_tvar.
Qed.

Fixpoint ASolveCtx (G : ACtx) {struct G} : ACtx :=
  match G with
  | nil => nil
  | cons (x, p) t =>
    match p with
    | AC_Unsolved_EVar => ASolveCtx t & x ~ AC_Solved_EVar (AT_Expr AE_Star)
    | _ => ASolveCtx t & x ~ p
    end
  end.

Lemma resolve_evar_awf_preservation: forall G a m s t H,
    AResolveForall G a m s t H ->
    AWf G ->
    AWf H.
Proof.
  introv res wf.
  induction res; auto.
  assert (AWf (G1 & a1 ~ AC_Unsolved_EVar &
               a ~ AC_Unsolved_EVar & G2)).
  rewrite <- concat_assoc.
  apply~ awf_weakening_insert_unsolved.
  rewrite~ concat_assoc.
  lets: IHres H1. auto.
Qed.

Lemma resolve_forall_extension: forall G a m s t H,
    AResolveForall G a m s t H ->
    AWf G ->
    ExtCtx G H.
Proof.
  introv res wfg.
  lets: resolve_forall_awf_preservation res wfg.
  lets: awf_is_ok wfg.
  lets: resolve_forall_wextctx res H1.
  lets: weak_extension_to_extension H2 wfg H0.
  auto.
Qed.

Lemma resolve_forall_inserts2: forall G1 G2 a m e t H,
    AResolveForall (G1 & a ~ AC_Unsolved_EVar & G2) a m e t H ->
    ok (G1 & a ~ AC_Unsolved_EVar & G2) ->
    exists I, H = G1 & I & a ~ AC_Unsolved_EVar & G2 /\
         (forall a v, binds a v I -> v = AC_Unsolved_EVar).
Proof.
  introv res okg. gen_eq S: (G1 & a ~ AC_Unsolved_EVar & G2). gen G1.
  induction res; introv sinfo; subst; try(solve[exists~ empty]).

  apply ok_middle_eq2 in sinfo; auto.
  destruct sinfo as [? [? ?]]. subst.
  assert(ok (G3 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & G2)).
  rewrite <- concat_assoc. apply ok_insert; auto. rewrite~ concat_assoc.
  forwards*: IHres H1. destruct H3 as (I & [hinfo un]).
  exists~ (a1 ~ AC_Unsolved_EVar & I).
  split. repeat rewrite~ concat_assoc.
  intros n nv bdn.
  destruct (binds_concat_inv bdn).
  lets: un H3. auto.
  destruct H3. apply binds_single_inv in H4. destruct H4. auto.
  rewrite~ <- sinfo.

  forwards*: IHres1 okg.
  destruct H0 as (I1 & [h1info bdn]).
  lets: resolve_forall_ok_preservation res1 okg.
  lets: IHres2 H0 h1info.
  destruct H2 as (I2 & [hinfo bdn2]).
  exists~ (I1 & I2). split. repeat rewrite~ concat_assoc.
  intros n nv bdnv.
  destruct (binds_concat_inv bdnv).
  lets: bdn2 H2. auto.
  destruct H2. lets: bdn H3. auto.

  forwards*: IHres1 okg.
  destruct H0 as (I1 & [h1info bdn]).
  lets: resolve_forall_ok_preservation res1 okg.
  lets: IHres2 H0 h1info.
  destruct H2 as (I2 & [hinfo bdn2]).
  exists~ (I1 & I2). split. repeat rewrite~ concat_assoc.
  intros n nv bdnv.
  destruct (binds_concat_inv bdnv).
  lets: bdn2 H2. auto.
  destruct H2. lets: bdn H3. auto.

  exists~ (empty: ACtx).
  split.
  rewrite~ concat_empty_r.
  intros n nv bdnv.
  false binds_empty_inv bdnv.
Qed.

Lemma actxtsubst_all_unsolved: forall G e,
    ok G ->
    (forall a v, binds a v G -> v = AC_Unsolved_EVar) ->
    ACtxTSubst G e = e.
Proof.
  introv okg bd.
  induction G using env_ind.
  rewrite~ tsubst_empty_env.
  assert (binds x v (G & x ~ v)). apply~ binds_push_eq.
  lets: bd H. subst.
  rewrite~ tsubst_add_evar.
  apply~ IHG.
  intros a v bdav.
  assert (binds a v (G & x ~ AC_Unsolved_EVar)). apply~ binds_push_neq.
  introv neq. subst. destruct (ok_push_inv okg).
  false binds_fresh_inv bdav H1.
  lets: bd H0. auto.
Qed.

Lemma resolve_forall_eq_ctxsubst: forall G a m s t H e,
    AResolveForall G a m s t H ->
    AWf G ->
    ACtxTSubst G e = ACtxTSubst H e.
Proof.
  introv res wf.
  induction res; auto.

  assert (AWf (G1 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & G2)).
  rewrite <- concat_assoc.
  apply~ awf_weakening_insert_unsolved.
  rewrite~ concat_assoc.
  lets: IHres H1.
  do 2 rewrite tsubst_add_ctx in H2.
  rewrite tsubst_add_evar in H2.
  do 2 rewrite <- tsubst_add_ctx in H2. auto.

  lets: IHres1 wf.
  lets: resolve_forall_awf_preservation res1 wf.
  lets: IHres2 H2.
  rewrite H3 in H0. auto.

  lets: IHres1 wf.
  lets: resolve_forall_awf_preservation res1 wf.
  lets: IHres2 H2.
  rewrite H3 in H0. auto.
Qed.

Lemma resolve_forall_eq_g: forall G a m s t H,
    AResolveForall G a m s t H ->
    AWf G ->
    s = ACtxTSubst G s ->
    t = ACtxTSubst G t.
Proof.
  introv res wf sub.
  induction res; auto.
  assert (s @@#' AT_EVar a1 =
          ACtxTSubst (G1 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & G2)
                     (s @@#' AT_EVar a1)).
  rewrite tsubst_add_ctx.
  rewrite tsubst_add_ctx.
  rewrite tsubst_add_evar.
  do 2 rewrite <- tsubst_add_ctx.
  rewrite~ actxtsubst_topen.
  rewrite~ actxtsubst_evar_notin.
  rewrite actxtsubst_expr in sub.
  rewrite actxsubst_forall in sub. inversion~ sub.
  rewrite~ <- H2. rewrite~ <- H2.
  lets: IHres H1.
  rewrite <- concat_assoc.
  apply~ awf_weakening_insert_unsolved.
  rewrite~ concat_assoc.
  rewrite tsubst_add_ctx in H2.
  rewrite tsubst_add_ctx in H2.
  rewrite tsubst_add_evar in H2.
  rewrite <- tsubst_add_ctx in H2. rewrite <- tsubst_add_ctx in H2. auto.

  (* PI1 *)
  rewrite actxtsubst_expr in sub.
  rewrite actxsubst_pi in sub.
  inversion~ sub.
  lets: IHres1 wf H2. clear IHres1.

  lets: resolve_forall_awf_preservation res1 wf.
  assert (s2 = ACtxTSubst H1 s2).
  lets: resolve_forall_eq_ctxsubst s2 res1 wf.
  rewrite~ <- H5.
  lets: IHres2 H4 H5.
  lets: resolve_forall_eq_ctxsubst t2 res1 wf.

  rewrite actxtsubst_expr. f_equal.
  rewrite actxsubst_pi. f_equal~.
  rewrite <- H7 in H6. auto.

  (* PI2 *)
  rewrite actxtsubst_expr in sub.
  rewrite actxsubst_pi in sub.
  inversion~ sub.
  lets: IHres1 wf H2. clear IHres1.

  lets: resolve_forall_awf_preservation res1 wf.
  assert (s2 = ACtxTSubst H1 s2).
  lets: resolve_forall_eq_ctxsubst s2 res1 wf.
  rewrite~ <- H5.
  lets: IHres2 H4 H5.
  lets: resolve_forall_eq_ctxsubst t2 res1 wf.

  rewrite actxtsubst_expr. f_equal.
  rewrite actxsubst_pi. f_equal~.
  rewrite <- H7 in H6. auto.
Qed.

Lemma resolve_forall_eq_h: forall G a m s t H,
    AResolveForall G a m s t H ->
    AWf G ->
    s = ACtxTSubst G s ->
    t = ACtxTSubst H t.
Proof.
  intros.
  lets: resolve_forall_eq_g H0 H1 H2.
  apply resolve_forall_eq_ctxsubst with (e:=t) in H0; auto.
  rewrite~ <- H0.
Qed.

Inductive AResolveForall2 : ACtx -> var -> ARFMode -> AType -> AType -> ACtx -> Prop :=
  | AResolveForall2_Poly: forall a G1 G2 H s t a1,
      a1 # (G1 & a ~ AC_Unsolved_EVar & G2) ->
      AResolveForall2 (G1 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & G2)
                     a Plus (s @@#' (AT_EVar a1)) t H ->
      AResolveForall2 (G1 & a ~ AC_Unsolved_EVar & G2) a Plus (AT_Expr (AE_Forall s)) t H
  | AResolveForall2_Pi1: forall G s1 s2 t1 t2 H1 H a L,
      AResolveForall2 G a Plus s1 t1 H1 ->
      (forall x , x \notin L -> AResolveForall2 (H1 & x ~ AC_Typ s1) a Minus s2 t2 (H & x ~ AC_Typ s1)) ->
      AResolveForall2 G a Minus (AT_Expr (AE_Pi s1 s2)) (AT_Expr (AE_Pi t1 t2)) H
  | AResolveForall2_Pi2: forall G s1 s2 t1 t2 H1 H a L,
      AResolveForall2 G a Minus s1 t1 H1 ->
      (forall x, x \notin L -> AResolveForall2 (H1 & x ~ AC_Typ s1) a Plus s2 t2 (H & x ~ AC_Typ s1)) ->
      AResolveForall2 G a Plus (AT_Expr (AE_Pi s1 s2)) (AT_Expr (AE_Pi t1 t2)) H
  | AResolveForall2_Mono : forall G a m t,
      ATMono t -> AResolveForall2 G a m t t G.

Hint Constructors AResolveForall2.

Lemma resolve_forall_ok_preservation_inv: forall G a m s t H,
    AResolveForall G a m s t H ->
    ok H ->
    ok G.
Proof.
  introv res okh.
  induction res; auto.
  lets: IHres okh.
  rewrite <- concat_assoc.
  rewrite <- concat_assoc in H1.
  apply* ok_remove.
Qed.

Lemma resolve_forall_weakening: forall G a m s t H I,
    AResolveForall G a m s t H ->
    ok (H & I) ->
    AResolveForall (G & I) a m s t (H & I).
Proof.
  introv res okg.
  induction res; auto.

  lets: IHres okg. clear IHres.
  rewrite <- concat_assoc.
  apply AResolveForall_Poly with a1; auto.
  lets: resolve_forall_ok_preservation_inv H1 okg.
  do 2 rewrite <- concat_assoc in H2.
  destruct (ok_middle_inv H2). auto.
  rewrite~ concat_assoc.

  apply AResolveForall_Pi1 with (H1:= (H1 & I)); auto.
  apply IHres1.
  lets: IHres2 okg.
  lets: resolve_forall_ok_preservation_inv H0 okg. auto.


  apply AResolveForall_Pi2 with (H1:= (H1 & I)); auto.
  apply IHres1.
  lets: IHres2 okg.
  lets: resolve_forall_ok_preservation_inv H0 okg. auto.
Qed.

Lemma resolve_forall2_ok_preservation: forall G a m s t H,
    AResolveForall2 G a m s t H ->
    ok G -> ok H.
Proof.
  introv res okg.
  induction res; auto.
  apply IHres.
  rewrite <- concat_assoc. apply ok_insert. rewrite~ concat_assoc. auto.

  pick_fresh y.
  assert (y \notin L) by auto.
  lets: IHres okg.
  assert (ok (H1 & y ~ AC_Typ s1)) by apply~ ok_push.
  lets: H2 H3 H5.
  destruct (ok_push_inv H6). auto.

  pick_fresh y.
  assert (y \notin L) by auto.
  lets: IHres okg.
  assert (ok (H1 & y ~ AC_Typ s1)) by apply~ ok_push.
  lets: H2 H3 H5.
  destruct (ok_push_inv H6). auto.
Qed.

Lemma resolve_forall2_ok_preservation_inv: forall G a m s t H,
    AResolveForall2 G a m s t H ->
    ok H -> ok G.
Proof.
  introv res okh.
  induction res; auto.
  lets: IHres okh.
  rewrite <- concat_assoc.
  rewrite <- concat_assoc in H1.
  apply* ok_remove.

  pick_fresh y.
  assert (y \notin L) by auto.
  assert (ok (H & y ~ AC_Typ s1)) by apply~ ok_push.
  lets: H2 H3 H4.
  destruct (ok_push_inv H5).
  lets: IHres H6. auto.

  pick_fresh y.
  assert (y \notin L) by auto.
  assert (ok (H & y ~ AC_Typ s1)) by apply~ ok_push.
  lets: H2 H3 H4.
  destruct (ok_push_inv H5).
  lets: IHres H6. auto.
Qed.

Lemma resolve_forall2_wextctx: forall G a m s t H,
    AResolveForall2 G a m s t H ->
    ok G ->
    WExtCtx G H.
Proof.
  introv res okg.
  lets: resolve_forall2_ok_preservation res okg.
  induction res; auto.

  (* POLY *)
  assert(ok (G1 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & G2)).
  rewrite <- concat_assoc.
  apply ok_insert; auto.
  rewrite~ concat_assoc.
  lets: IHres H2 H0.
  rewrite <- concat_assoc in H3.
  lets: weak_extension_order_unsolved_evar H3.
  destruct H4 as (I1 & I2 & [hinfo [g1h1 [? exg2h2]]]).
  destruct hinfo as [hinfo | (t0 & hinfo)].
  rewrite hinfo.
  rewrite <- concat_assoc.
  apply~ weak_extension_append_ex.
  apply~ WExtCtx_Add.
  rewrite hinfo in H0. apply ok_middle_inv_l in H0. auto.
  rewrite~ concat_assoc.
  rewrite hinfo in H0; auto.
  rewrite hinfo.
  rewrite <- concat_assoc.
  apply~ weak_extension_append_ex.
  apply~ WExtCtx_AddSolved.
  rewrite hinfo in H0. apply ok_middle_inv_l in H0. auto.
  rewrite~ concat_assoc.
  rewrite hinfo in H0; auto.

  (* PI1 *)
  pick_fresh y. assert (y \notin L) by auto.
  lets: H2 H4. clear H2.
  lets: resolve_forall2_ok_preservation res okg.
  lets: IHres okg H2. clear IHres.
  assert (ok (H1 & y ~ AC_Typ s1)) by apply~ ok_push.
  assert (ok (H & y ~ AC_Typ s1)) by apply~ ok_push.
  lets: H3 H4 H7 H8.
  lets: weak_extension_remove_typvar H9.
  lets: weak_extension_transitivity H6 H10. auto.

  (* PI2 *)
  pick_fresh y. assert (y \notin L) by auto.
  lets: H2 H4. clear H2.
  lets: resolve_forall2_ok_preservation res okg.
  lets: IHres okg H2. clear IHres.
  assert (ok (H1 & y ~ AC_Typ s1)) by apply~ ok_push.
  assert (ok (H & y ~ AC_Typ s1)) by apply~ ok_push.
  lets: H3 H4 H7 H8.
  lets: weak_extension_remove_typvar H9.
  lets: weak_extension_transitivity H6 H10. auto.
Qed.

Lemma weak_extension_var_preservation_inv: forall G H x,
    WExtCtx G H ->
    x # H -> x # G.
Proof.
  introv ex.
  induction ex; auto.
Qed.

Lemma resolve_forall2_renaming: forall x y G1 G2 t1 t2 H1 H2 a m s t,
    x <> y ->
    ok (G1 & x ~ AC_Typ t1 & G2) ->
    ok (H1 & y ~ AC_Typ t1 & H2) ->
    AResolveForall2 (G1 & x ~ AC_Typ t1 & G2) a m s t (H1 & x ~ AC_Typ t1 & H2) ->
    AResolveForall2 (G1 & y ~ AC_Typ t1 & G2) a m s t (H1 & y ~ AC_Typ t2 & H2).
Proof.
  introv neq okx oky res.
  assert (ok (G1 & y ~ AC_Typ t1 & G2)).
  apply ok_insert; auto.
  destruct (ok_middle_inv oky).
  assert (y # (H1 & x ~ AC_Typ t1 & H2)). auto.
  lets: resolve_forall2_wextctx res okx.
  lets: weak_extension_var_preservation_inv H4 H3. auto.

  gen_eq S: (G1 & x ~ AC_Typ t1 & G2).
  gen_eq M: (H1 & x ~ AC_Typ t1 & H2). gen G1 G2 H1 H2.
  induction res; introv okyg okyh minfo sinfo; subst; auto.

  admit.

  lets: resolve_forall2_ok_preservation res okx.
  lets: resolve_forall2_wextctx res okx.
  lets: weak_extension_order_typvar H5.
  destruct H6 as (I1 & I2 & [h1info _]). subst.
  forwards ~ : IHres okx okyg I1 I2.


  apply ok_middle

Lemma resolve_forall2_weakening: forall x y G1 G2 t1 t2 H1 H2 a m s t,
    x <> y ->
    ok (G1 & x ~ AC_Typ t1 & y ~ AC_Typ t2 & G2) ->
    AResolveForall2 (G1 & x ~ AC_Typ t1 & y ~ AC_Typ t2 & G2) a m s t (H1 & x ~ AC_Typ t1 & y ~ AC_Typ t2 & H2) ->
    AResolveForall2 (G1 & y ~ AC_Typ t2 & x ~ AC_Typ t2 & G2) a m s t (H1 & y ~ AC_Typ t2 & x ~ AC_Typ t1 & H2).
Proof.
  introv neq okg res.
  gen_eq S: (G1 & x ~ AC_Typ t1 & y ~ AC_Typ t2 & G2).
  gen_eq M: (H1 & x ~ AC_Typ t1 & y ~ AC_Typ t2 & H2).
  gen G1 G2 H1 H2.
  induction res; introv minfo sinfo; subst.

  admit.

  lets: resolve_forall2_wextctx res okg.
  lets: weak_extension

  admit.

  lets: resolve_forall2_wextctx res.


  apply IHres.
  introv neq res.
  inductions res; auto.

  assert (ok (G1 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & G2)).
  rewrite <- concat_assoc. apply ok_insert; auto.
  rewrite~ concat_assoc.
  lets: resolve_forall2_ok_preservation res H.
  lets: IHres H. clear IHres.


Lemma resolve_forall2_weakening: forall G a m s t H y v,
    AResolveForall2 G a m s t H ->
    ok (H & y ~ AC_Typ v) ->
    AResolveForall2 (G & y ~ AC_Typ v) a m s t (H & y ~ AC_Typ v).
Proof.
  introv res okh.
  induction res; auto.
  rewrite <- concat_assoc.
  destruct (ok_push_inv okh).
  lets: IHres okh. clear IHres.
  apply AResolveForall2_Poly with a1; auto.
  lets: resolve_forall2_ok_preservation_inv H3 okh.
  do 2 rewrite <- concat_assoc in H4.
  destruct (ok_middle_inv H4). auto.
  repeat rewrite~ concat_assoc in H3.
  repeat rewrite~ concat_assoc.

  apply AResolveForall2_Pi1 with (H1:=H1 & y ~ AC_Typ v) (L:= L \u dom H \u dom H1 \u \{y}).
  pick_fresh z. assert (z \notin L) by auto.
  assert (ok (H & z ~ AC_Typ s1 & y ~ AC_Typ v)). apply ok_insert; auto.
  lets: H2 H3 H4. clear H2.
  lets: resolve_forall2_ok_preservation_inv H5 H4.
  lets: ok_remove H2.
  lets: IHres H6. auto.

  intros z notin.
  assert (z \notin L) by auto.
  assert (ok (H & z ~ AC_Typ s1 & y ~ AC_Typ v)). apply ok_insert; auto.
  lets: H2 H3 H4.

Lemma resolve_forall2_weakening: forall G1 G2 a m s t H I,
    AResolveForall2 (G1 & G2) a m s t H ->
    ok (H & I) ->
    exists H1 H2, H = H1 & H2 /\ AResolveForall2 (G1 & I & G2) a m s t (H1 & I & H2).
Proof.
  introv res okg. gen_eq S: (G1 & G2). gen G1 G2.
  induction res; introv sinfo; subst; auto.

  (* POLY *)
  assert (ok H). destruct (ok_concat_inv okg). auto.
  assert (ok (G1 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & G2)).
  lets: resolve_forall2_ok_preservation_inv res H1. auto.
  assert (ok (G1 & a ~ AC_Unsolved_EVar & G2)).
  rewrite <- concat_assoc in H2.
  lets: ok_remove H2.
  rewrite~ <- concat_assoc.
  assert (binds a AC_Unsolved_EVar (G0 & G3)).
  rewrite <- sinfo. apply~ binds_middle_eq.
  destruct (ok_middle_inv H3). auto.

  destruct (binds_concat_inv H4).
  apply split_bind_context in H5.
  destruct H5 as (M1 & M2 & g3info). subst.
  repeat rewrite concat_assoc in sinfo.
  apply ok_middle_eq2 in sinfo; auto.
  destruct sinfo as [? [_ ?]]. subst.
  assert (G0 & M1 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & M2 =
          G0 & (M1 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & M2)).
  repeat rewrite~ concat_assoc.
  lets: IHres okg H5. clear IHres.
  destruct H6 as (M3 & M4 & [hinfo res2]). subst.
  exists~ M3 M4. split~.
  repeat rewrite concat_assoc in *.
  apply AResolveForall2_Poly with (a1:=a1); auto.
  assert (ok (M3 & I & M4)).
  admit.
  lets: resolve_forall2_ok_preservation_inv res2 H.
  rewrite <- concat_assoc in H6.
  destruct (ok_middle_inv H6). auto.
  rewrite~ <- sinfo.

  destruct H5.
  apply split_bind_context in H6.
  destruct H6 as (M1 & M2 & g0info). subst.
  assert (sinfo' : G1 & a ~ AC_Unsolved_EVar & G2 = M1 & a ~ AC_Unsolved_EVar & (M2 & G3)).
  repeat rewrite~ concat_assoc.
  apply ok_middle_eq2 in sinfo'; auto.
  destruct sinfo' as [? [_ ?]]. subst.
  assert (M1 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & (M2 & G3) =
          (M1 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & M2) & G3).
  repeat rewrite~ concat_assoc.
  lets: IHres okg H6. clear IHres.
  destruct H7 as (M3 & M4 & [hinfo res2]). subst.
  exists~ M3 M4. split~.
  assert (AResolveForall2
           (M1 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & (M2 & I & G3)) a
           Plus (s @@#' AT_EVar a1) t (M3 & I & M4)).
  repeat rewrite~ concat_assoc.
  lets: AResolveForall2_Poly H.
  assert (ok (M3 & I & M4)).
  admit.
  lets: resolve_forall2_ok_preservation_inv res2 H7.
  do 3 rewrite <- concat_assoc in H8.
  destruct (ok_middle_inv H8). auto.
  repeat rewrite concat_assoc in H7. auto.
  rewrite~ <- sinfo'.

  (* PI1 *)
  pick_fresh y. assert (y \notin L) by auto.
  lets: H0 H3. clear H0.
  assert (ok (H & y ~ AC_Typ s1)). apply~ ok_push.
  lets: resolve_forall2_ok_preservation_inv H4 H0.
  assert (ok (H1 & I)). admit.
  forwards *: IHres H6.
  destruct H7 as (M1 & M2 & [h1info res2]). subst.
  assert (ok (H & y ~ AC_Typ s1 & I)). apply ok_insert; auto.
  assert (M1 & M2 & y ~ AC_Typ s1 =
          M1 & (M2 & y ~ AC_Typ s1)). repeat rewrite~ concat_assoc.
  lets: H2 H3 H1 H7.
  destruct H8 as (M3 & M4 & [hinfo  res3]).
  assert (binds y (AC_Typ s1) (M3 & M4)).
  rewrite <- hinfo. apply~ binds_push_eq.
  destruct (binds_concat_inv H8).
  apply split_bind_context in H9.
  destruct H9 as (M5 & M6 & m4info). subst.
  symmetry in hinfo.
  repeat rewrite concat_assoc in *.
  apply tail_empty_eq2 in hinfo; auto.
  destruct hinfo as [? [_ ?]]. subst.
  repeat rewrite concat_empty_r in *.
  exists~ M3 M5. split; auto.
  apply AResolveForall2_Pi1 with (H1:=(M1 & I & M2))
         (L:=(((((((((L \u \{ a}) \u ATFv s1) \u ATFv s2) \u ATFv t1) \u ATFv t2) \u dom I) \u dom (M1 & M2)) \u dom (M3 & M5)) \u dom G1)); auto.
  intros z notinz.
  admit.
  rewrite~ hinfo.

  destruct H9.
  apply split_bind_context in H10.
  destruct H10 as (M5 & M6 & m4info). subst.
  symmetry in hinfo. rewrite <- concat_assoc in hinfo.
  apply tail_empty_eq2 in hinfo; auto.
  destruct hinfo as [? [_ ?]]. symmetry in H11. lets: empty_concat_inv H11. destruct H12. subst.
  repeat rewrite concat_empty_r in *.
  assert (I = empty).
  induction I using env_ind; auto. clear IHI.
  repeat rewrite concat_assoc in *.
  assert (AResolveForall2 (M1 & I & x ~ v & M2 & y ~ AC_Typ s1 & empty) a Minus s2 t2
                          (M5 & y ~ AC_Typ s1 & I & x ~ v & empty)).
  repeat rewrite~ concat_empty_r.
  assert (ok (M1 & I & x ~ v & M2 & y ~ AC_Typ s1 & empty)). repeat rewrite~ concat_empty_r. lets: resolve_forall2_ok_preservation_inv res3 H1. auto.
  lets: resolve_forall2_wextctx H H10.
  forwards*: weak_declaration_order_preservation H12.
  destruct H13 as (? & ? & ? & ? & ? &?).
  lets: reverse_order_inv H13; auto.
  rewrite~ concat_empty_r.
  rewrite <- H13. rewrite~ concat_empty_r. false H14.

  subst.
  exists~ M5 (empty: ACtx).
  repeat rewrite concat_empty_r in *. split; auto.
  repeat rewrite concat_assoc in *.
  apply AResolveForall2_Pi1 with (H1:=(M1 & M2))
         (L:=(((((((((L \u \{ a}) \u ATFv s1) \u ATFv s2) \u ATFv t1) \u ATFv t2) \u dom (M1 & M2)) \u dom (M5)) \u dom G1))); auto.
  intros z notinz.

  admit.
  rewrite~ hinfo.

  admit.

  exists~ G1 G2.
Qed.

Lemma resolve_is_resolve2: forall G a m s t H,
    AResolveForall G a m s t H ->
    AResolveForall2 G a m s t H.
Proof.
  introv res.
  induction res; auto.
  apply~ AResolveForall2_Poly.

  apply AResolveForall2_Pi1 with (H1:=H1) (L:=dom H); auto.
  intros y notin.
  apply~ resolve_forall_weakening.
       apply~ resolve_forall_Weakening


Lemma resolve_forall_awftyp_preservation: forall G a m s t H,
    AResolveForall G a m s t H ->
    AWfTyp G s ->
    AWfTyp H t.
Proof.
  introv res wf.
  induction res; auto.
  admit.

  lets: awftyp_pi1 wf.
  lets: IHres1 H0.
  lets: awftyp_awf wf.
  lets: resolve_forall_extension res1 H3.
  lets: awftyp_pi2 wf.
Admitted.

Lemma subtyping_extension: forall G t s H,
    ASubtyping G t s H ->
    AWf G ->
    AWfTyp G t ->
    AWfTyp G s ->
    t = ACtxTSubst G t ->
    s = ACtxTSubst G s ->
    AWf H /\ ExtCtx G H.
Proof.
  introv sub wfg wtt wts subt subs.
  induction sub.

  (* POLYR *)
  assert (I1: AWf (G & v ~ AC_TVar)). apply~ AWf_TVar.
  assert (I2: AWfTyp (G & v ~ AC_TVar) s1). apply~ awftyp_weakening.
  assert (I3: AWfTyp (G & v ~ AC_TVar) (s2 @@#' AT_TFVar v)). apply~ awftyp_forall.
  assert (I4: s1 = ACtxTSubst (G & v ~ AC_TVar) s1). rewrite~ tsubst_add_tvar.
  assert (I5: s2 @@#' AT_TFVar v = ACtxTSubst (G & v ~ AC_TVar) (s2 @@#' AT_TFVar v)).
  rewrite tsubst_add_tvar.
  rewrite~ actxtsubst_topen. rewrite~ actxtsubst_tfvar_notin.
  rewrite actxtsubst_expr in subs.
  rewrite actxsubst_forall in subs.
  inversion~ subs. rewrite~ <- H2. rewrite~ <- H2.
  lets: IHsub I1 I2 I3 I4 I5.
  destruct H1.
  split. lets: AWf_left H1. auto.
  lets: extension_remove_tvar H2. auto.

  (* POLYL *)
  assert (I1: AWf (G & b ~ AC_Marker & a ~ AC_Unsolved_EVar)).
  apply~ AWf_Ctx_Unsolved_EVar.
  assert (I2: AWfTyp (G & b ~ AC_Marker & a ~ AC_Unsolved_EVar)
                     (s1 @@#' AT_EVar a)).
  apply~ awftyp_forall_evar.
  apply~ awftyp_weakening.
  assert (I3: AWfTyp (G & b ~ AC_Marker & a ~ AC_Unsolved_EVar) s2).
  apply~ awftyp_weakening.
  apply~ awftyp_weakening.
  assert (I4: s1 @@#' AT_EVar a =
              ACtxTSubst (G & b ~ AC_Marker & a ~ AC_Unsolved_EVar)
                         (s1 @@#' AT_EVar a)).
  rewrite tsubst_add_evar.
  rewrite tsubst_add_marker.
  rewrite~ actxtsubst_topen.
  rewrite~ actxtsubst_evar_notin.
  rewrite actxtsubst_expr in subt.
  rewrite actxsubst_forall in subt.
  inversion~ subt. repeat rewrite~ <- H4.
  assert (I5: s2 = ACtxTSubst (G & b ~ AC_Marker & a ~ AC_Unsolved_EVar) s2).
  rewrite tsubst_add_evar.
  rewrite~ tsubst_add_marker.
  lets: IHsub I1 I2 I3 I4 I5.
  destruct H3.
  split. do 2 apply AWf_left in H3. auto.
  lets: extension_order_marker H4.
  destruct H5 as (M1 & M2 & [hinfo [gh1 _]]).
  apply ok_middle_eq2 in hinfo; auto.
  destruct hinfo as [? [? ?]]. rewrite~ H5.
  rewrite~ <- hinfo.

  (* PI *)
  rewrite actxtsubst_expr in subt.
  rewrite actxsubst_pi in subt.
  rewrite actxtsubst_expr in subs.
  rewrite actxsubst_pi in subs.
  destruct IHsub1; auto. apply awftyp_pi1 in wts; auto.
  apply awftyp_pi1 in wtt; auto.
  inversion~ subs. rewrite~ <- H3.
  inversion~ subt. rewrite~ <- H3.

  assert (I1: AWf (H1 & x ~ AC_Typ s1)).
  apply~ AWf_TyVar. apply awftyp_pi1 in wtt.
  lets: extension_weakening_awftyp wtt H3. auto.
  assert (I2: AWfTyp (H1 & x ~ AC_Typ s1)
                     (ACtxTSubst H1 (s2 @@' AE_FVar x))).
  rewrite <- tsubst_add_typvar with (x:=x) (t:=s1).
  apply -> awftyp_subst.
  assert (x # G). lets: declaration_preservation_inv H3 H0. auto.
  lets: awftyp_pi2 wtt H4.
  assert (ExtCtx (G & x ~ AC_Typ s1) (H1 & x ~ AC_Typ s1)).
  apply~ ExtCtx_TypVar.
  apply~ AWf_TyVar. apply awftyp_pi1 in wtt; auto.
  lets: extension_weakening_awftyp H5 H6. auto.
  assert (I3: AWfTyp (H1 & x ~ AC_Typ s1) (ACtxTSubst H1 (s4 @@' AE_FVar x))).
  admit.
  assert (I4: ACtxTSubst H1 (s2 @@' AE_FVar x) =
              ACtxTSubst (H1 & x ~ AC_Typ s1)
                         (ACtxTSubst H1 (s2 @@' AE_FVar x))).
  rewrite tsubst_add_typvar.
  rewrite~ ctxtsubst_twice.
  assert (I5: ACtxTSubst H1 (s4 @@' AE_FVar x) =
              ACtxTSubst (H1 & x ~ AC_Typ s1)
                         (ACtxTSubst H1 (s4 @@' AE_FVar x))).
  rewrite tsubst_add_typvar.
  rewrite~ ctxtsubst_twice.
  lets: IHsub2 I1 I2 I3 I4 I5.
  destruct H4.

  split. lets: AWf_left H4. auto.
  lets: extension_remove_tyvar H5.
  lets: extension_transitivity H3 H6. auto.

  (* EVARL *)
  lets: resolve_forall_extension H2 wfg.
  lets: resolve_forall_awf_preservation H2 wfg.

  assert (I1: t = ACtxTSubst H1 t).
  lets: resolve_forall_eq_h H2 wfg subs. auto.
  assert (I2: AT_EVar a = ACtxTSubst H1 (AT_EVar a)).
  lets: resolve_forall_eq_ctxsubst (AT_EVar a) H2 wfg.
  rewrite H6 in subt. auto.
  assert (I3: AWfTyp H1 t).
  lets: resolve_forall_awftyp_preservation H2 wts. auto.
  assert (I4: AWfTyp H1 (AT_EVar a)).
  lets: extension_weakening_awftyp wtt H4. auto.
  forwards: unify_extension H3 H5 I1 I2 I3. auto.
  destruct H6.
  split; auto.
  lets: extension_transitivity H4 H7. auto.

  (* EVARR *)
  lets: resolve_forall_extension H2 wfg.
  lets: resolve_forall_awf_preservation H2 wfg.

  assert (I1: t = ACtxTSubst H1 t).
  lets: resolve_forall_eq_h H2 wfg subt. auto.
  assert (I2: AT_EVar a = ACtxTSubst H1 (AT_EVar a)).
  lets: resolve_forall_eq_ctxsubst (AT_EVar a) H2 wfg.
  rewrite H6 in subs. auto.
  assert (I3: AWfTyp H1 t).
  lets: resolve_forall_awftyp_preservation H2 wtt. auto.
  assert (I4: AWfTyp H1 (AT_EVar a)).
  lets: extension_weakening_awftyp wts H4. auto.
  forwards: unify_extension H3 H5 I1 I2 I3. auto.
  destruct H6.
  split; auto.
  lets: extension_transitivity H4 H7. auto.

  (* UNIFY *)
  forwards: unify_extension H0; auto.
Qed.

Theorem subtyping_soundness: forall G H I t1 t2 H' t1' t2',
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
  lets: awf_preservation H4. auto.
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
  lets: IHASubtyping I1 I2 I3 I4 I5. clear IHASubtyping.
  lets: awf_is_ok I3.
  lets: subtyping_ok_preservation H3 H15.

  assert (Softness I).
  forwards ~ : subtyping_wextctx H3.
  lets: weak_extension_order_marker H18.
  destruct H19 as (M1 & M2 & [hinfo [_ [sf _]]]).
  apply ok_middle_eq2 in hinfo; auto.
  destruct hinfo as [? [_ ?]]. rewrite H20.
  apply~ sf. apply soft_single_unsolved.
  rewrite~ <- hinfo.

  assert (binds a AC_Unsolved_EVar (G & b ~ AC_Marker & a ~ AC_Unsolved_EVar)). apply~ binds_push_eq.
  forwards: subtyping_evar_preservation H3 H19; auto.
  destruct H20 as [bdun | (ta & bdso)].

  (* a is unsolved in I *)
  assert (a # (H & b ~ AC_Marker)).
  lets: subtyping_wextctx H3 H15.
  assert ((G & b ~ AC_Marker & a ~ AC_Unsolved_EVar) = (G & b ~ AC_Marker & empty & a ~ AC_Unsolved_EVar & empty)) by repeat rewrite~ concat_empty_r.
  lets: weak_declaration_order_preservation H20 H21.
  destruct H22 as (? & ? & ? & ? & ? & ?).
  assert( H & b ~ AC_Marker & I =
          x1 & b ~ x & (x2 & a ~ x0 & x3)) by repeat rewrite~ concat_assoc.
  apply ok_middle_eq2 in H23; auto.
  destruct H23 as [? [? ?]]. rewrite H23 in *.
  rewrite H22 in H17. apply ok_middle_inv_l in H17. auto.
  rewrite~ <- H23.

  assert (I6: ExtCtx (H & b ~ AC_Marker & I)
                     (I0 & b ~ AC_Marker & I)).
  apply~ extension_append.
  apply~ ExtCtx_Marker.
  assert (I6: ExtCtx (H & b ~ AC_Marker & I)
                     (I0 & b ~ AC_Marker & (ASolveCtx I))).

  lets: binds_concat_right_inv bdun H20. clear bdun H20.



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

  admit.

  (* EVARL *)
  lets: resolve_forall_awf_preservation H2 H8.
  inversion H2; subst.

  (* resolve pi *)
  inversion H12; subst.
  admit.

  (* resolve mono *)
  forwards ~ : unif_soundness_same H3 H6 H13 H11 H12.
  rewrite H1. apply DSub_AEq.

  (* EVARR *)
  lets: resolve_forall_awf_preservation H2 H8.
  inversion H2; subst.

  (* resolve forall *)
  false H0. reflexivity.

  (* resolve pi *)
  admit.

  (* resolve mono *)
  forwards ~ : unif_soundness_same H3 H6 H13 H12 H11.
  rewrite H1. apply DSub_AEq.

  (* UNIFY *)
  forwards * : unif_soundness_same H0 H5 H6 H7.
  rewrite H11. apply DSub_AEq.
Qed.
