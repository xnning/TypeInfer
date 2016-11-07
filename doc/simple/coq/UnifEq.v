Require Import CtxExtension.
Require Import LibLN.
Require Import AlgoDef.
Require Import UtilityEnv.
Require Import DeclDef.
Require Import AlgoInfra.
Require Import DeclInfra.
Require Import Subst.
Require Import Exists.
Require Import UtilityMore.
Require Import WeakExtension.
Require Import UtilityAlgo.

(***********************)
(* EQUIVALENCE OF UNIFY *)
(***********************)

Inductive AUMode := UType | UExpr.

Inductive ATUnify : AUMode -> ACtx -> AType -> AType -> ACtx -> Prop :=
  | ATUnify_Var : forall x G, binds x AC_Var G -> ATUnify UExpr G (AT_Expr (AE_FVar x)) (AT_Expr (AE_FVar x)) G
  | ATUnify_Typed_Var : forall x G t, binds x (AC_Typ t) G -> ATUnify UExpr G (AT_Expr (AE_FVar x)) (AT_Expr (AE_FVar x)) G
  | ATUnify_EVar : forall a G, binds a AC_Unsolved_EVar G -> ATUnify UType G (AT_EVar a) (AT_EVar a) G
  | ATUnify_TVar : forall a G, binds a AC_TVar G -> ATUnify UType G (AT_TFVar a) (AT_TFVar a) G
  | ATUnify_Star : forall G, ATUnify UExpr G (AT_Expr (AE_Star)) (AT_Expr (AE_Star)) G
  | ATUnify_App : forall t1 t2 t3 t4 G H1 H,
      ATUnify UExpr G (AT_Expr t1) (AT_Expr t2) H1 ->
      ATUnify UExpr H1 (AT_Expr (ACtxSubst H1 t3)) (AT_Expr (ACtxSubst H1 t4)) H ->
      ATUnify UExpr G (AT_Expr (AE_App t1 t3)) (AT_Expr (AE_App t2 t4)) H
  | ATUnify_Lam : forall t1 t2 G H L,
      (forall x, x \notin L -> ATUnify UExpr (G & x ~ AC_Var) (AT_Expr (t1 @ x)) (AT_Expr (t2 @ x)) (H & x ~ AC_Var)) ->
      ATUnify UExpr G (AT_Expr (AE_Lam t1)) (AT_Expr (AE_Lam t2)) H
  | ATUnify_CastUp : forall t1 t2 G H,
      ATUnify UExpr G (AT_Expr t1) (AT_Expr t2) H ->
      ATUnify UExpr G (AT_Expr (AE_CastUp t1)) (AT_Expr (AE_CastUp t2)) H
  | ATUnify_CastDn : forall t1 t2 G H,
      ATUnify UExpr G (AT_Expr t1) (AT_Expr t2) H ->
      ATUnify UExpr G (AT_Expr (AE_CastDn t1)) (AT_Expr (AE_CastDn t2)) H
  | ATUnify_Pi : forall t1 t2 t3 t4 G H1 H L,
      ATUnify UType G t1 t3 H1 ->
      (forall x, x \notin L -> ATUnify UType (H1 & x ~ AC_Typ t1) (ACtxTSubst H1 (t2 @' x)) (ACtxTSubst H1 (t4 @' x)) (H & x ~ AC_Typ t1)) ->
      ATUnify UExpr G (AT_Expr (AE_Pi t1 t2)) (AT_Expr (AE_Pi t3 t4)) H
  | ATUnify_Forall : forall t1 t2 G H L,
      (forall x, x \notin L -> ATUnify UType (G & x ~ AC_TVar) (t1 @#' x) (t2 @#' x) (H & x ~ AC_TVar)) ->
      ATUnify UExpr G (AT_Expr (AE_Forall t1)) (AT_Expr (AE_Forall t2)) H
  | ATUnify_Ann : forall t1 t2 t3 t4 G H1 H,
      ATUnify UExpr G (AT_Expr t1) (AT_Expr t2) H1 ->
      ATUnify UType H1 (ACtxTSubst H1 t3) (ACtxTSubst H1 t4) H ->
      ATUnify UExpr G (AT_Expr (AE_Ann t1 t3)) (AT_Expr (AE_Ann t2 t4)) H
  | ATUnify_EVarTy : forall a t1 t2 G H1 H2,
      a \notin ATFv (t1) ->
      AResolveEVar G a t1 t2 (H1 & a ~ AC_Unsolved_EVar & H2) ->
      AWTermT H1 t2 ->
      ATUnify UType G (AT_EVar a) t1 (H1 & a ~ AC_Solved_EVar t2 & H2)
  | ATUnify_TyEVar : forall a t1 t2 G H1 H2,
      (forall n, t1 <> AT_EVar n) ->
      a \notin ATFv (t1) ->
      AResolveEVar G a t1 t2 (H1 & a ~ AC_Unsolved_EVar & H2) ->
      AWTermT H1 t2 ->
      ATUnify UType G t1 (AT_EVar a) (H1 & a ~ AC_Solved_EVar t2 & H2)
  | ATUnify_Expr: forall G t1 t2 H,
      ATUnify UExpr G t1 t2 H ->
      ATUnify UType G t1 t2 H.

Lemma atunify_ok_preservation: forall G m s t H,
    ATUnify m G s t H ->
    ok G ->
    ok H.
Proof.
  introv uni okg.
  induction uni; auto.

  pick_fresh y.
  assert (y \notin L) by auto_star.
  assert (ok (G & y ~ AC_Var)) by apply* ok_push.
  lets: H1 H2 H3.
  apply ok_concat_inv_l in H4; auto.

  pick_fresh y.
  assert (y \notin L) by auto_star.
  lets: H2 H3. clear H2.
  assert (ok (H1 & y ~ AC_Typ t1)) by apply* ok_push.
  lets: H4 H2.
  apply ok_concat_inv_l in H5; auto.

  pick_fresh y.
  assert (y \notin L) by auto_star.
  assert (ok (G & y ~ AC_TVar)) by apply* ok_push.
  lets: H1 H2 H3.
  apply ok_concat_inv_l in H4; auto.

  lets: resolve_evar_ok_preservation H0 okg.
  apply* ok_middle_change.

  lets: resolve_evar_ok_preservation H3 okg.
  apply* ok_middle_change.
Qed.

Lemma resolve_evar_middle_change: forall G1 G2 a t H1 H2 t2 v a0,
    AResolveEVar (G1 & a ~ AC_Typ t & G2) a0 v t2
                 (H1 & a ~ AC_Typ t & H2) ->
    ok (G1 & a ~ AC_Typ t & G2) ->
    AResolveEVar (G1 & a ~ AC_Var & G2) a0 v t2
                 (H1 & a ~ AC_Var & H2).
Proof.
  introv res okg.
  gen_eq S1: (G1 & a ~ AC_Typ t & G2).
  gen_eq S2: (H1 & a ~ AC_Typ t & H2). gen H1 H2 G1 G2.
  lets: resolve_evar_ok_preservation res okg.
  induction res; introv sinfo1 sinfo2; subst; auto;
    try(solve[apply ok_middle_eq2 in sinfo2; auto;
              try(destruct sinfo2 as [? [_ ?]]; subst; constructor~);
              try(rewrite~ <- sinfo2)]).

  (* EVAR BEFORE *)
  assert (binds a (AC_Typ t) (H1 & a ~ AC_Typ t & H2)).
  apply binds_middle_eq. rewrite sinfo1 in okg. apply ok_middle_inv_r in okg. auto.
  assert (a <> b). introv neq. subst.
  rewrite <- sinfo1 in H0. do 2 rewrite <- concat_assoc in H0.
  false binds_middle_eq_inv H0.
  repeat rewrite~ concat_assoc.
  assert (a <> a0). introv neq. subst.
  rewrite <- sinfo1 in H0.
  false binds_middle_eq_inv H0; auto.

  rewrite <- sinfo1 in H0.
  apply binds_remove in H0; auto.
  rewrite <- concat_assoc in H0.
  apply binds_remove in H0; auto.
  rewrite concat_assoc in H0.
  apply binds_concat_inv in H0.
  destruct H0 as [bdg3 | [noting3 bdg1g2]].
  apply split_bind_context in bdg3.
  destruct bdg3 as (I1 & I2 & g3info). subst.
  repeat rewrite concat_assoc in sinfo2.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  repeat rewrite concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.

  assert(
      AResolveEVar
     (G1 & b ~ AC_Unsolved_EVar & G2 & a0 ~ AC_Unsolved_EVar & (I1 & a ~ AC_Var & H2))
     a0 (AT_EVar b) (AT_EVar b)
     (G1 & b ~ AC_Unsolved_EVar & G2 & a0 ~ AC_Unsolved_EVar & (I1 & a ~ AC_Var & H2))).
  apply~ AResolveEVar_EVar_Before.
  repeat rewrite concat_assoc in H0; auto.

  repeat rewrite concat_assoc in H. auto.
  rewrite <- sinfo1.
  repeat rewrite concat_assoc in H. auto.
  repeat rewrite concat_assoc in H. auto.
  rewrite <- sinfo2.
  repeat rewrite concat_assoc in H. auto.

  apply binds_concat_inv in bdg1g2.
  destruct bdg1g2 as [bdg2 | [noting2 bdg1]].
  apply split_bind_context in bdg2.
  destruct bdg2 as (I1 & I2 & g2info). subst.
  repeat rewrite concat_assoc in sinfo2.
  do 2 rewrite <- concat_assoc in sinfo2.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  repeat rewrite concat_assoc in sinfo1.
  do 2 rewrite <- concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.

  assert(
   AResolveEVar
     (G1 & b ~ AC_Unsolved_EVar & (I1 & a ~ AC_Var & I2) & a0 ~ AC_Unsolved_EVar & G3)
     a0 (AT_EVar b) (AT_EVar b)
     (G1 & b ~ AC_Unsolved_EVar & (I1 & a ~ AC_Var & I2) & a0 ~ AC_Unsolved_EVar & G3)).
  apply~ AResolveEVar_EVar_Before.
  repeat rewrite concat_assoc in H0; auto.
  repeat rewrite concat_assoc. auto.

  repeat rewrite concat_assoc in *. auto.
  rewrite <- sinfo1.
  repeat rewrite concat_assoc in *. auto.
  repeat rewrite concat_assoc in *. auto.
  rewrite <- sinfo2.
  repeat rewrite concat_assoc in *. auto.

  apply split_bind_context in bdg1.
  destruct bdg1 as (I1 & I2 & g2info). subst.
  do 4 rewrite <- concat_assoc in sinfo2.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  do 4 rewrite <- concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.

  repeat rewrite concat_assoc in *.
  apply~ AResolveEVar_EVar_Before.

  repeat rewrite concat_assoc in *. auto.
  rewrite <- sinfo1.
  repeat rewrite concat_assoc in *. auto.
  repeat rewrite concat_assoc in *. auto.
  rewrite <- sinfo2.
  repeat rewrite concat_assoc in *. auto.

  (* EVAR AFTER *)
  assert( ok (H1 & a ~ AC_Typ t & H2)). rewrite <- sinfo1.
  do 3 rewrite <- concat_assoc.
  apply ok_insert; auto.
  repeat rewrite concat_assoc.
  apply* ok_middle_change.

  assert (binds a (AC_Typ t) (H1 & a ~ AC_Typ t & H2)).
  apply binds_middle_eq. apply ok_middle_inv_r in H3. auto.
  assert (a <> b). introv neq. subst.
  rewrite <- sinfo1 in H4.
  false binds_middle_eq_inv H4.
  rewrite~ sinfo1.
  assert (a <> a0). introv neq. subst.
  rewrite <- sinfo1 in H4.
  do 2 rewrite <- concat_assoc in H4.
  false binds_middle_eq_inv H4; auto.
  repeat rewrite~ concat_assoc.
  assert (a <> a1). introv neq. subst.
  rewrite <- sinfo1 in H4.
  do 3 rewrite <- concat_assoc in H4.
  false binds_middle_eq_inv H4; auto.
  repeat rewrite~ concat_assoc.

  rewrite <- sinfo1 in H4.
  apply binds_remove in H4; auto.
  rewrite <- concat_assoc in H4.
  apply binds_remove in H4; auto.
  apply binds_remove in H4; auto.
  rewrite concat_assoc in H4.
  apply binds_concat_inv in H4.
  destruct H4 as [bdg3 | [noting3 bdg1g2]].
  apply split_bind_context in bdg3.
  destruct bdg3 as (I1 & I2 & g3info). subst.
  repeat rewrite concat_assoc in sinfo2.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  repeat rewrite concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.

  assert(
   AResolveEVar
     (G1 & a0 ~ AC_Unsolved_EVar & G2 & b ~ AC_Unsolved_EVar & (I1 & a ~ AC_Var & H2))
     a0 (AT_EVar b) (AT_EVar a1)
     (G1 & a1 ~ AC_Unsolved_EVar & a0 ~ AC_Unsolved_EVar & G2 & b ~ AC_Solved_EVar (AT_EVar a1) & (I1 & a ~ AC_Var & H2))).
  apply~ AResolveEVar_EVar_After.
  repeat rewrite concat_assoc in H1; auto.

  repeat rewrite concat_assoc in *. auto.
  repeat rewrite concat_assoc in *. auto.
  rewrite <- sinfo2.
  repeat rewrite concat_assoc in *. auto.

  apply binds_concat_inv in bdg1g2.
  destruct bdg1g2 as [bdg2 | [noting2 bdg1]].
  apply split_bind_context in bdg2.
  destruct bdg2 as (I1 & I2 & g2info). subst.
  repeat rewrite concat_assoc in sinfo2.
  do 2 rewrite <- concat_assoc in sinfo2.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  repeat rewrite concat_assoc in sinfo1.
  do 2 rewrite <- concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.

  repeat rewrite concat_assoc.
  assert(
   AResolveEVar
     (G1 & a0 ~ AC_Unsolved_EVar & (I1 & a ~ AC_Var & I2) &
      b ~ AC_Unsolved_EVar & G3) a0 (AT_EVar b) (AT_EVar a1)
     (G1 & a1 ~ AC_Unsolved_EVar & a0 ~ AC_Unsolved_EVar & (I1 & a ~ AC_Var &
      I2) & b ~ AC_Solved_EVar (AT_EVar a1) & G3)).
  apply~ AResolveEVar_EVar_After.
  repeat rewrite concat_assoc in *; auto.

  repeat rewrite concat_assoc in *. auto.
  repeat rewrite concat_assoc in *. auto.
  rewrite <- sinfo2.
  repeat rewrite concat_assoc in *. auto.

  apply split_bind_context in bdg1.
  destruct bdg1 as (I1 & I2 & g2info). subst.
  do 4 rewrite <- concat_assoc in sinfo2.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  do 5 rewrite <- concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.

  repeat rewrite concat_assoc.
  apply~ AResolveEVar_EVar_After.
  repeat rewrite concat_assoc in *; auto.

  repeat rewrite concat_assoc in *. auto.
  rewrite <- sinfo2.
  repeat rewrite concat_assoc in *. auto.


  (* PI *)
  lets: resolve_evar_wextctx res okg.
  apply weak_extension_order_typvar in H0.
  destruct H0 as (I1 & I2 & [hinfo _]).
  subst.
  lets: resolve_evar_ok_preservation res okg.
  apply AResolveEVar_Pi with (L:=L \u dom (I1 & a ~ AC_Typ t & I2) \u dom (H4 & a ~ AC_Typ t & H5)) (H1:=(I1 & a ~ AC_Var & I2)).
  forwards * : IHres. clear IHres.
  intros y notin.
  assert(y \notin L) by auto.
  lets: H2 H1. clear H2.
  assert(H4 & a ~ AC_Typ t & H5 & y ~ AC_Var = H4 & a ~ AC_Typ t & (H5 & y ~ AC_Var )) by repeat rewrite~ concat_assoc.
  assert(I1 & a ~ AC_Typ t & I2 & y ~ AC_Var = I1 & a ~ AC_Typ t & (I2 & y ~ AC_Var)) by  repeat rewrite~ concat_assoc.
  assert (ok (I1 & a ~ AC_Typ t & I2 & y ~ AC_Var)) by apply~ ok_push.
  lets: H3 H1 H8 H2 H7. apply~ ok_push.
  repeat rewrite concat_assoc in H9; auto.

  rewrite tsubst_add_ctx in H9. rewrite tsubst_add_typvar in H9.
  rewrite tsubst_add_ctx. rewrite tsubst_add_var. auto.

  (* APP *)
  lets: resolve_evar_wextctx res1 okg.
  apply weak_extension_order_typvar in H0.
  destruct H0 as (I1 & I2 & [hinfo _]). subst.
  lets: resolve_evar_ok_preservation res1 okg.
  lets: resolve_evar_ok_preservation res2 H0.
  forwards * : IHres1. clear IHres1.
  forwards * : IHres2. clear IHres2.
  apply* AResolveEVar_App.

  rewrite tsubst_add_ctx in H5. rewrite tsubst_add_typvar in H5.
  rewrite tsubst_add_ctx. rewrite tsubst_add_var. auto.

  (* LAM *)
  apply AResolveEVar_Lam with (L \u dom (G1 & a ~ AC_Typ t & G2) \u dom (H3 & a ~ AC_Typ t & H4)).
  intros y notin.
  assert(y \notin L) by auto.
  lets: H1 H0. clear H1.
  assert(H3 & a ~ AC_Typ t & H4 & y ~ AC_Var = H3 & a ~ AC_Typ t & (H4 & y ~ AC_Var )) by repeat rewrite~ concat_assoc.
  assert(G1 & a ~ AC_Typ t & G2 & y ~ AC_Var = G1 & a ~ AC_Typ t & (G2 & y ~ AC_Var)) by  repeat rewrite~ concat_assoc.
  assert (ok (G1 & a ~ AC_Typ t & G2 & y ~ AC_Var)) by apply~ ok_push.
  assert (ok (H3 & a ~ AC_Typ t & H4 & y ~ AC_Var)) by apply~ ok_push.
  lets: H2 H0 H7 H8 H1 H6.
  repeat rewrite concat_assoc in H9; auto.

  (* ANN *)
  lets: resolve_evar_wextctx res1 okg.
  apply weak_extension_order_typvar in H0.
  destruct H0 as (I1 & I2 & [hinfo _]). subst.
  lets: resolve_evar_ok_preservation res1 okg.
  lets: resolve_evar_ok_preservation res2 H0.
  forwards * : IHres1. clear IHres1.
  forwards * : IHres2. clear IHres2.
  apply* AResolveEVar_Ann.

  rewrite tsubst_add_ctx in H5. rewrite tsubst_add_typvar in H5.
  rewrite tsubst_add_ctx. rewrite tsubst_add_var. auto.
Qed.

Lemma aunify_middle_change: forall e G1 G2 a t d H1 H2,
    AUnify (G1 & a ~ AC_Typ t & G2) e d (H1 & a ~ AC_Typ t & H2) ->
    ok (G1 & a ~ AC_Typ t & G2) ->
    AUnify (G1 & a ~ AC_Var & G2) e d (H1 & a ~ AC_Var & H2).
Proof.
  introv uni.
  gen_eq S1: (G1 & a ~ AC_Typ t & G2).
  gen_eq S2: (H1 & a ~ AC_Typ t & H2). gen H1 H2 G1 G2.
  induction uni; introv sinfo1 sinfo2 okg; subst.

  (* Var *)
  assert (x <> a). introv neq. subst. false binds_middle_eq_inv H. auto.
  apply binds_remove in H; auto.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  apply AUnify_Var. apply~ binds_weaken.
  apply* ok_middle_change.
  rewrite <- sinfo2. auto.

  (* TypedVar *)
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  destruct(eq_var_dec x a).
  subst.
  apply~ AUnify_Var. apply~ binds_middle_eq.
  apply ok_middle_inv_r in okg. auto.
  apply AUnify_Typed_Var with t0.
  apply binds_remove in H; auto.
  apply~ binds_weaken.
  apply* ok_middle_change.
  rewrite <- sinfo2. auto.

  (* EVar *)
  assert (a0 <> a). introv neq. subst. false binds_middle_eq_inv H. auto.
  apply binds_remove in H; auto.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  apply AUnify_EVar. apply~ binds_weaken.
  apply* ok_middle_change.
  rewrite <- sinfo2. auto.

  (* TFVar *)
  assert (a0 <> a). introv neq. subst. false binds_middle_eq_inv H. auto.
  apply binds_remove in H; auto.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  apply AUnify_TVar. apply~ binds_weaken.
  apply* ok_middle_change.
  rewrite <- sinfo2. auto.

  (* STAR *)
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  apply AUnify_Star.
  rewrite <- sinfo2. auto.

  (* APP *)
  lets: unify_wextctx uni1 okg.
  apply weak_extension_order_typvar in H.
  destruct H as (I1 & I2 & [hinfo _]). subst.
  lets: unify_ok_preservation uni1 okg.
  forwards * : IHuni1. clear IHuni1.
  forwards * : IHuni2. clear IHuni2.
  apply* AUnify_App.
  rewrite subst_add_ctx in H3.
  rewrite subst_add_typvar in H3.
  rewrite subst_add_ctx in H3.
  rewrite subst_add_typvar in H3.
  rewrite subst_add_ctx.
  rewrite subst_add_var.
  rewrite subst_add_ctx.
  rewrite subst_add_var. auto.

  (* LAM *)
  apply AUnify_Lam with (L \u dom (G1 & a ~ AC_Typ t & G2)).
  intros y notin.
  assert(H: y \notin L) by auto.
  lets: H0 H. clear H0.
  assert(H2 & a ~ AC_Typ t & H3 & y ~ AC_Var = H2 & a ~ AC_Typ t & (H3 & y ~ AC_Var )) by repeat rewrite~ concat_assoc.
  assert(G1 & a ~ AC_Typ t & G2 & y ~ AC_Var = G1 & a ~ AC_Typ t & (G2 & y ~ AC_Var)) by  repeat rewrite~ concat_assoc.
  assert (ok (G1 & a ~ AC_Typ t & G2 & y ~ AC_Var)) by apply~ ok_push.
  lets: H1 H H0 H5 H6.
  repeat rewrite concat_assoc in H7; auto.

  (* CASTUP *)
  forwards * : IHuni.

  (* CASTDOWN *)
  forwards * : IHuni.

  (* PI *)
  lets: unify_wextctx uni okg.
  apply weak_extension_order_typvar in H.
  destruct H as (I1 & I2 & [hinfo _]). subst.
  lets: unify_ok_preservation uni okg.
  apply AUnify_Pi with (L:=L \u dom (I1 & a ~ AC_Typ t & I2)) (H1:=(I1 & a ~ AC_Var & I2)).
  forwards * : IHuni. clear IHuni.
  intros y notin.
  assert(y \notin L) by auto.
  lets: H0 H1. clear H0.
  assert(H3 & a ~ AC_Typ t & H4 & y ~ AC_Var = H3 & a ~ AC_Typ t & (H4 & y ~ AC_Var )) by repeat rewrite~ concat_assoc.
  assert(I1 & a ~ AC_Typ t & I2 & y ~ AC_Var = I1 & a ~ AC_Typ t & (I2 & y ~ AC_Var)) by  repeat rewrite~ concat_assoc.
  assert (ok (I1 & a ~ AC_Typ t & I2 & y ~ AC_Var)) by apply~ ok_push.
  lets: H2 H1 H0 H6 H7.
  repeat rewrite concat_assoc in H8; auto.

  rewrite tsubst_add_ctx in H8. rewrite tsubst_add_typvar in H8.
  rewrite tsubst_add_ctx in H8. rewrite tsubst_add_typvar in H8.
  rewrite tsubst_add_ctx. rewrite tsubst_add_var.
  rewrite tsubst_add_ctx. rewrite tsubst_add_var. auto.

  (* FORALL *)
  apply AUnify_Forall with (L \u dom (G1 & a ~ AC_Typ t & G2)).
  intros y notin.
  assert(H: y \notin L) by auto.
  lets: H0 H. clear H0.
  assert(H2 & a ~ AC_Typ t & H3 & y ~ AC_TVar = H2 & a ~ AC_Typ t & (H3 & y ~ AC_TVar )) by repeat rewrite~ concat_assoc.
  assert(G1 & a ~ AC_Typ t & G2 & y ~ AC_TVar = G1 & a ~ AC_Typ t & (G2 & y ~ AC_TVar)) by  repeat rewrite~ concat_assoc.
  assert (ok (G1 & a ~ AC_Typ t & G2 & y ~ AC_TVar)) by apply~ ok_push.
  lets: H1 H H0 H5 H6.
  repeat rewrite concat_assoc in H7; auto.

  (* ANN *)
  lets: unify_wextctx uni1 okg.
  apply weak_extension_order_typvar in H.
  destruct H as (I1 & I2 & [hinfo _]). subst.
  lets: unify_ok_preservation uni1 okg.
  forwards * : IHuni1. clear IHuni1.
  forwards * : IHuni2. clear IHuni2.
  apply* AUnify_Ann.
  rewrite tsubst_add_ctx in H3. rewrite tsubst_add_typvar in H3.
  rewrite tsubst_add_ctx in H3. rewrite tsubst_add_typvar in H3.
  rewrite tsubst_add_ctx. rewrite tsubst_add_var.
  rewrite tsubst_add_ctx. rewrite tsubst_add_var. auto.

  (* EVAR TY *)
  lets: resolve_evar_ok_preservation H0 okg.
  assert(binds a0 (AC_Solved_EVar t2) (H1 & a0 ~ AC_Solved_EVar t2 & H2)).
  apply~ binds_middle_eq. apply ok_middle_inv_r in H6; auto.
  rewrite sinfo1 in H7.
  apply binds_remove in H7; auto.
  apply binds_concat_inv in H7.
  destruct H7 as [bdh2 | [notinh2 bdh1]].
  apply split_bind_context in bdh2.
  destruct bdh2 as (I1 & I2 & g2info). subst.
  repeat rewrite concat_assoc in *.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.
  apply~ AUnify_EVarTy.
  do 3 rewrite <- concat_assoc in H0.
  rewrite concat_assoc in H0.
  apply resolve_evar_middle_change in H0; auto.
  repeat rewrite concat_assoc in H0. auto.
  apply* awtermt_replace.
  apply* ok_middle_change.
  rewrite <- sinfo1. apply* ok_middle_change.

  apply split_bind_context in bdh1.
  destruct bdh1 as (I1 & I2 & g2info). subst.
  do 3 rewrite <- concat_assoc in sinfo1.
  rewrite concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.
  do 3 rewrite <- concat_assoc.
  rewrite concat_assoc.
  apply~ AUnify_EVarTy.
  repeat rewrite concat_assoc in H0.
  apply resolve_evar_middle_change in H0; auto.
  repeat rewrite concat_assoc. auto.
  apply* ok_middle_change.
  rewrite <- sinfo1. apply* ok_middle_change.

  assert(a0 <> a). introv neq. subst. false binds_middle_eq_inv H7.
  rewrite~ <- sinfo1. apply* ok_middle_change.
  auto.

  (* TY EVAR *)
  lets: resolve_evar_ok_preservation H3 okg.
  assert(binds a0 (AC_Solved_EVar t2) (H1 & a0 ~ AC_Solved_EVar t2 & H2)).
  apply~ binds_middle_eq. apply ok_middle_inv_r in H7; auto.
  rewrite sinfo1 in H8.
  apply binds_remove in H8; auto.
  apply binds_concat_inv in H8.
  destruct H8 as [bdh2 | [notinh2 bdh1]].
  apply split_bind_context in bdh2.
  destruct bdh2 as (I1 & I2 & g2info). subst.
  repeat rewrite concat_assoc in *.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.
  apply~ AUnify_TyEVar.
  do 3 rewrite <- concat_assoc in H3.
  rewrite concat_assoc in H3.
  apply resolve_evar_middle_change in H3; auto.
  repeat rewrite concat_assoc in H3. auto.
  apply* awtermt_replace.
  apply* ok_middle_change.
  rewrite <- sinfo1. apply* ok_middle_change.

  apply split_bind_context in bdh1.
  destruct bdh1 as (I1 & I2 & g2info). subst.
  do 3 rewrite <- concat_assoc in sinfo1.
  rewrite concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.
  do 3 rewrite <- concat_assoc.
  rewrite concat_assoc.
  apply~ AUnify_TyEVar.
  repeat rewrite concat_assoc in H3.
  apply resolve_evar_middle_change in H3; auto.
  repeat rewrite concat_assoc. auto.
  apply* ok_middle_change.
  rewrite <- sinfo1. apply* ok_middle_change.

  assert(a0 <> a). introv neq. subst. false binds_middle_eq_inv H8.
  rewrite~ <- sinfo1. apply* ok_middle_change.
  auto.
Qed.

Lemma atunify_is_aunify: forall G m s t H,
    ok G ->
    ATUnify m G s t H ->
    AUnify G s t H.
Proof.
  introv okg uni.
  induction uni; auto.
  apply AUnify_Typed_Var with t; auto.

  lets: atunify_ok_preservation uni1 okg.
  apply* AUnify_App.

  apply AUnify_Lam with (L \u dom G).
  intros y notin.
  assert(y \notin L) by auto.
  assert(ok (G & y ~ AC_Var)) by apply~ ok_push.
  lets: H1 H2 H3. auto.

  apply AUnify_Pi with (L:=L \u dom H1) (H1:=H1); auto.
  intros y notin.
  assert(y \notin L) by auto.
  lets: H2 H3. clear H2.
  lets: IHuni okg. clear IHuni.
  lets: unify_ok_preservation H2 okg.
  assert( ok (H1 & y ~ AC_Typ t1)) by apply~ ok_push.
  lets: H4 H6. clear H4.
  assert( AUnify (H1 & y ~ AC_Typ t1 & empty) (ACtxTSubst H1 (t2 @@' AE_FVar y))
         (ACtxTSubst H1 (t4 @@' AE_FVar y)) (H & y ~ AC_Typ t1 & empty)).
  repeat rewrite~ concat_empty_r.

  apply aunify_middle_change in H4.
  repeat rewrite concat_empty_r in *. auto.
  rewrite~ concat_empty_r.

  apply AUnify_Forall with (L \u dom G).
  intros y notin.
  assert(y \notin L) by auto.
  assert(ok (G & y ~ AC_TVar)) by apply~ ok_push.
  lets: H1 H2 H3. auto.

  lets: atunify_ok_preservation uni1 okg.
  apply* AUnify_Ann.
Qed.

Lemma resolve_evar_middle_change2: forall G1 G2 a t H1 H2 t2 v a0,
    AResolveEVar (G1 & a ~ AC_Var & G2) a0 v t2
                 (H1 & a ~ AC_Var & H2) ->
    ok (G1 & a ~ AC_Var & G2) ->
    AResolveEVar (G1 & a ~ AC_Typ t & G2) a0 v t2
                 (H1 & a ~ AC_Typ t & H2).
Proof.
  introv res okg.
  gen_eq S1: (G1 & a ~ AC_Var & G2).
  gen_eq S2: (H1 & a ~ AC_Var & H2). gen H1 H2 G1 G2.
  lets: resolve_evar_ok_preservation res okg.
  induction res; introv sinfo1 sinfo2; subst; auto;
    try(solve[apply ok_middle_eq2 in sinfo2; auto;
              try(destruct sinfo2 as [? [_ ?]]; subst; constructor~);
              try(rewrite~ <- sinfo2)]).

  (* EVAR BEFORE *)
  assert (binds a AC_Var (H1 & a ~ AC_Var & H2)).
  apply binds_middle_eq. rewrite sinfo1 in okg. apply ok_middle_inv_r in okg. auto.
  assert (a <> b). introv neq. subst.
  rewrite <- sinfo1 in H0. do 2 rewrite <- concat_assoc in H0.
  false binds_middle_eq_inv H0.
  repeat rewrite~ concat_assoc.
  assert (a <> a0). introv neq. subst.
  rewrite <- sinfo1 in H0.
  false binds_middle_eq_inv H0; auto.

  rewrite <- sinfo1 in H0.
  apply binds_remove in H0; auto.
  rewrite <- concat_assoc in H0.
  apply binds_remove in H0; auto.
  rewrite concat_assoc in H0.
  apply binds_concat_inv in H0.
  destruct H0 as [bdg3 | [noting3 bdg1g2]].
  apply split_bind_context in bdg3.
  destruct bdg3 as (I1 & I2 & g3info). subst.
  repeat rewrite concat_assoc in sinfo2.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  repeat rewrite concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.

  assert(
      AResolveEVar
     (G1 & b ~ AC_Unsolved_EVar & G2 & a0 ~ AC_Unsolved_EVar & (I1 & a ~ AC_Typ t & H2))
     a0 (AT_EVar b) (AT_EVar b)
     (G1 & b ~ AC_Unsolved_EVar & G2 & a0 ~ AC_Unsolved_EVar & (I1 & a ~ AC_Typ t & H2))).
  apply~ AResolveEVar_EVar_Before.
  repeat rewrite concat_assoc in H0; auto.

  repeat rewrite concat_assoc in H. auto.
  rewrite <- sinfo1.
  repeat rewrite concat_assoc in H. auto.
  repeat rewrite concat_assoc in H. auto.
  rewrite <- sinfo2.
  repeat rewrite concat_assoc in H. auto.

  apply binds_concat_inv in bdg1g2.
  destruct bdg1g2 as [bdg2 | [noting2 bdg1]].
  apply split_bind_context in bdg2.
  destruct bdg2 as (I1 & I2 & g2info). subst.
  repeat rewrite concat_assoc in sinfo2.
  do 2 rewrite <- concat_assoc in sinfo2.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  repeat rewrite concat_assoc in sinfo1.
  do 2 rewrite <- concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.

  assert(
   AResolveEVar
     (G1 & b ~ AC_Unsolved_EVar & (I1 & a ~ AC_Typ t & I2) & a0 ~ AC_Unsolved_EVar & G3)
     a0 (AT_EVar b) (AT_EVar b)
     (G1 & b ~ AC_Unsolved_EVar & (I1 & a ~ AC_Typ t& I2) & a0 ~ AC_Unsolved_EVar & G3)).
  apply~ AResolveEVar_EVar_Before.
  repeat rewrite concat_assoc in H0; auto.
  repeat rewrite concat_assoc. auto.

  repeat rewrite concat_assoc in *. auto.
  rewrite <- sinfo1.
  repeat rewrite concat_assoc in *. auto.
  repeat rewrite concat_assoc in *. auto.
  rewrite <- sinfo2.
  repeat rewrite concat_assoc in *. auto.

  apply split_bind_context in bdg1.
  destruct bdg1 as (I1 & I2 & g2info). subst.
  do 4 rewrite <- concat_assoc in sinfo2.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  do 4 rewrite <- concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.

  repeat rewrite concat_assoc in *.
  apply~ AResolveEVar_EVar_Before.

  repeat rewrite concat_assoc in *. auto.
  rewrite <- sinfo1.
  repeat rewrite concat_assoc in *. auto.
  repeat rewrite concat_assoc in *. auto.
  rewrite <- sinfo2.
  repeat rewrite concat_assoc in *. auto.

  (* EVAR AFTER *)
  assert( ok (H1 & a ~ AC_Var & H2)). rewrite <- sinfo1.
  do 3 rewrite <- concat_assoc.
  apply ok_insert; auto.
  repeat rewrite concat_assoc.
  apply* ok_middle_change.

  assert (binds a AC_Var (H1 & a ~ AC_Var & H2)).
  apply binds_middle_eq. apply ok_middle_inv_r in H3. auto.
  assert (a <> b). introv neq. subst.
  rewrite <- sinfo1 in H4.
  false binds_middle_eq_inv H4.
  rewrite~ sinfo1.
  assert (a <> a0). introv neq. subst.
  rewrite <- sinfo1 in H4.
  do 2 rewrite <- concat_assoc in H4.
  false binds_middle_eq_inv H4; auto.
  repeat rewrite~ concat_assoc.
  assert (a <> a1). introv neq. subst.
  rewrite <- sinfo1 in H4.
  do 3 rewrite <- concat_assoc in H4.
  false binds_middle_eq_inv H4; auto.
  repeat rewrite~ concat_assoc.

  rewrite <- sinfo1 in H4.
  apply binds_remove in H4; auto.
  rewrite <- concat_assoc in H4.
  apply binds_remove in H4; auto.
  apply binds_remove in H4; auto.
  rewrite concat_assoc in H4.
  apply binds_concat_inv in H4.
  destruct H4 as [bdg3 | [noting3 bdg1g2]].
  apply split_bind_context in bdg3.
  destruct bdg3 as (I1 & I2 & g3info). subst.
  repeat rewrite concat_assoc in sinfo2.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  repeat rewrite concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.

  assert(
   AResolveEVar
     (G1 & a0 ~ AC_Unsolved_EVar & G2 & b ~ AC_Unsolved_EVar & (I1 & a ~ AC_Typ t & H2))
     a0 (AT_EVar b) (AT_EVar a1)
     (G1 & a1 ~ AC_Unsolved_EVar & a0 ~ AC_Unsolved_EVar & G2 & b ~ AC_Solved_EVar (AT_EVar a1) & (I1 & a ~ AC_Typ t & H2))).
  apply~ AResolveEVar_EVar_After.
  repeat rewrite concat_assoc in H1; auto.

  repeat rewrite concat_assoc in *. auto.
  repeat rewrite concat_assoc in *. auto.
  rewrite <- sinfo2.
  repeat rewrite concat_assoc in *. auto.

  apply binds_concat_inv in bdg1g2.
  destruct bdg1g2 as [bdg2 | [noting2 bdg1]].
  apply split_bind_context in bdg2.
  destruct bdg2 as (I1 & I2 & g2info). subst.
  repeat rewrite concat_assoc in sinfo2.
  do 2 rewrite <- concat_assoc in sinfo2.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  repeat rewrite concat_assoc in sinfo1.
  do 2 rewrite <- concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.

  repeat rewrite concat_assoc.
  assert(
   AResolveEVar
     (G1 & a0 ~ AC_Unsolved_EVar & (I1 & a ~ AC_Typ t & I2) &
      b ~ AC_Unsolved_EVar & G3) a0 (AT_EVar b) (AT_EVar a1)
     (G1 & a1 ~ AC_Unsolved_EVar & a0 ~ AC_Unsolved_EVar & (I1 & a ~ AC_Typ t &
      I2) & b ~ AC_Solved_EVar (AT_EVar a1) & G3)).
  apply~ AResolveEVar_EVar_After.
  repeat rewrite concat_assoc in *; auto.

  repeat rewrite concat_assoc in *. auto.
  repeat rewrite concat_assoc in *. auto.
  rewrite <- sinfo2.
  repeat rewrite concat_assoc in *. auto.

  apply split_bind_context in bdg1.
  destruct bdg1 as (I1 & I2 & g2info). subst.
  do 4 rewrite <- concat_assoc in sinfo2.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  do 5 rewrite <- concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.

  repeat rewrite concat_assoc.
  apply~ AResolveEVar_EVar_After.
  repeat rewrite concat_assoc in *; auto.

  repeat rewrite concat_assoc in *. auto.
  rewrite <- sinfo2.
  repeat rewrite concat_assoc in *. auto.


  (* PI *)
  lets: resolve_evar_wextctx res okg.
  apply weak_extension_order_var in H0.
  destruct H0 as (I1 & I2 & [hinfo _]).
  subst.
  lets: resolve_evar_ok_preservation res okg.
  apply AResolveEVar_Pi with (L:=L \u dom (I1 & a ~ AC_Var & I2) \u dom (H4 & a ~ AC_Var & H5)) (H1:=(I1 & a ~ AC_Typ t & I2)).
  forwards * : IHres. clear IHres.
  intros y notin.
  assert(y \notin L) by auto.
  lets: H2 H1. clear H2.
  assert(H4 & a ~ AC_Var & H5 & y ~ AC_Var = H4 & a ~ AC_Var & (H5 & y ~ AC_Var )) by repeat rewrite~ concat_assoc.
  assert(I1 & a ~ AC_Var & I2 & y ~ AC_Var = I1 & a ~ AC_Var & (I2 & y ~ AC_Var)) by  repeat rewrite~ concat_assoc.
  assert (ok (I1 & a ~ AC_Var & I2 & y ~ AC_Var)) by apply~ ok_push.
  lets: H3 H1 H8 H2 H7. apply~ ok_push.
  repeat rewrite concat_assoc in H9; auto.

  rewrite tsubst_add_ctx in H9. rewrite tsubst_add_var in H9.
  rewrite tsubst_add_ctx. rewrite tsubst_add_typvar. auto.

  (* APP *)
  lets: resolve_evar_wextctx res1 okg.
  apply weak_extension_order_var in H0.
  destruct H0 as (I1 & I2 & [hinfo _]). subst.
  lets: resolve_evar_ok_preservation res1 okg.
  lets: resolve_evar_ok_preservation res2 H0.
  forwards * : IHres1. clear IHres1.
  forwards * : IHres2. clear IHres2.
  apply* AResolveEVar_App.

  rewrite tsubst_add_ctx in H5. rewrite tsubst_add_var in H5.
  rewrite tsubst_add_ctx. rewrite tsubst_add_typvar. auto.

  (* LAM *)
  apply AResolveEVar_Lam with (L \u dom (G1 & a ~ AC_Var & G2) \u dom (H3 & a ~ AC_Var & H4)).
  intros y notin.
  assert(y \notin L) by auto.
  lets: H1 H0. clear H1.
  assert(H3 & a ~ AC_Var & H4 & y ~ AC_Var = H3 & a ~ AC_Var & (H4 & y ~ AC_Var )) by repeat rewrite~ concat_assoc.
  assert(G1 & a ~ AC_Var & G2 & y ~ AC_Var = G1 & a ~ AC_Var & (G2 & y ~ AC_Var)) by  repeat rewrite~ concat_assoc.
  assert (ok (G1 & a ~ AC_Var & G2 & y ~ AC_Var)) by apply~ ok_push.
  assert (ok (H3 & a ~ AC_Var & H4 & y ~ AC_Var)) by apply~ ok_push.
  lets: H2 H0 H7 H8 H1 H6.
  repeat rewrite concat_assoc in H9; auto.

  (* ANN *)
  lets: resolve_evar_wextctx res1 okg.
  apply weak_extension_order_var in H0.
  destruct H0 as (I1 & I2 & [hinfo _]). subst.
  lets: resolve_evar_ok_preservation res1 okg.
  lets: resolve_evar_ok_preservation res2 H0.
  forwards * : IHres1. clear IHres1.
  forwards * : IHres2. clear IHres2.
  apply* AResolveEVar_Ann.

  rewrite tsubst_add_ctx in H5. rewrite tsubst_add_var in H5.
  rewrite tsubst_add_ctx. rewrite tsubst_add_typvar. auto.
Qed.

Lemma tunify_wextctx: forall G m s t H,
    ATUnify m G s t H ->
    ok G ->
    WExtCtx G H.
Proof.
  introv uni okg.
  lets: atunify_ok_preservation uni okg.
  induction uni; auto.

  (* APP *)
  lets: atunify_ok_preservation uni1 okg.
  lets: IHuni1 okg H2.
  lets: IHuni2 H2 H0.
  lets: weak_extension_transitivity H3 H4. auto.

  (* LAM *)
  pick_fresh y.
  assert (y \notin L) by auto.
  assert(ok (G & y ~ AC_Var)). constructor~.
  assert(ok (H & y ~ AC_Var)). constructor~.
  lets: H2 y H3 H4 H5.
  lets: weak_extension_remove_var H6.  auto.

  (* PI *)
  pick_fresh y.
  assert (y \notin L) by auto.
  assert(ok (G & y ~ AC_Typ t1)). constructor~.
  lets: atunify_ok_preservation uni okg.
  assert(ok (H1 & y ~ AC_Typ t1)). constructor~.
  assert(ok (H & y ~ AC_Typ t1)). constructor~.
  lets: H3 y H4 H7 H8.
  lets: weak_extension_remove_typvar H9.
  lets: IHuni okg H6.
  lets: weak_extension_transitivity H11 H10. auto.

  (* FORALL *)
  pick_fresh y.
  assert (y \notin L) by auto.
  assert(ok (G & y ~ AC_TVar)). constructor~.
  assert(ok (H & y ~ AC_TVar)). constructor~.
  lets: H2 H3 H4 H5.
  lets: weak_extension_remove_tvar H6.  auto.

  (* ANN *)
  lets: atunify_ok_preservation uni1 okg.
  lets: IHuni1 okg H2.
  lets: atunify_ok_preservation uni2 H2.
  lets: IHuni2 H2 H4.
  lets: weak_extension_transitivity H3 H5. auto.

  (* EVarL *)
  lets: resolve_evar_wextctx H3 okg. auto.
  lets: weak_extension_solve_middle t2 H5. auto.

  (* EVarR *)
  lets: resolve_evar_wextctx H4 okg. auto.
  lets: weak_extension_solve_middle t2 H6. auto.
Qed.

Lemma tunify_middle_change: forall e G1 G2 a m t d H1 H2,
    ATUnify m (G1 & a ~ AC_Var & G2) e d (H1 & a ~ AC_Var & H2) ->
    ok (G1 & a ~ AC_Var & G2) ->
    ATUnify m (G1 & a ~ AC_Typ t & G2) e d (H1 & a ~ AC_Typ t & H2).
Proof.
  introv uni.
  gen_eq S1: (G1 & a ~ AC_Var & G2).
  gen_eq S2: (H1 & a ~ AC_Var & H2). gen H1 H2 G1 G2.
  induction uni; introv sinfo1 sinfo2 okg; subst.

  (* Var *)
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  destruct(eq_var_dec x a).
  subst.
  apply~ ATUnify_Typed_Var. apply~ binds_middle_eq.
  apply ok_middle_inv_r in okg. auto.
  apply ATUnify_Var.
  apply binds_remove in H; auto.
  apply~ binds_weaken.
  apply* ok_middle_change.
  rewrite <- sinfo2. auto.

  (* TypedVar *)
  assert (x <> a). introv neq. subst. false binds_middle_eq_inv H. auto.
  apply binds_remove in H; auto.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  apply ATUnify_Typed_Var with t0. apply~ binds_weaken.
  apply* ok_middle_change.
  rewrite <- sinfo2. auto.

  (* EVar *)
  assert (a0 <> a). introv neq. subst. false binds_middle_eq_inv H. auto.
  apply binds_remove in H; auto.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  apply ATUnify_EVar. apply~ binds_weaken.
  apply* ok_middle_change.
  rewrite <- sinfo2. auto.

  (* TFVar *)
  assert (a0 <> a). introv neq. subst. false binds_middle_eq_inv H. auto.
  apply binds_remove in H; auto.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  apply ATUnify_TVar. apply~ binds_weaken.
  apply* ok_middle_change.
  rewrite <- sinfo2. auto.

  (* STAR *)
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  apply ATUnify_Star.
  rewrite <- sinfo2. auto.

  (* APP *)
  lets: tunify_wextctx uni1 okg.
  apply weak_extension_order_var in H.
  destruct H as (I1 & I2 & [hinfo _]). subst.
  lets: atunify_ok_preservation uni1 okg.
  forwards * : IHuni1. clear IHuni1.
  forwards * : IHuni2. clear IHuni2.
  apply* ATUnify_App.
  rewrite subst_add_ctx in H3.
  rewrite subst_add_var in H3.
  rewrite subst_add_ctx in H3.
  rewrite subst_add_var in H3.
  rewrite subst_add_ctx.
  rewrite subst_add_typvar.
  rewrite subst_add_ctx.
  rewrite subst_add_typvar. auto.

  (* LAM *)
  apply ATUnify_Lam with (L \u dom (G1 & a ~ AC_Var & G2)).
  intros y notin.
  assert(H: y \notin L) by auto.
  lets: H0 H. clear H0.
  assert(H2 & a ~ AC_Var & H3 & y ~ AC_Var = H2 & a ~ AC_Var & (H3 & y ~ AC_Var )) by repeat rewrite~ concat_assoc.
  assert(G1 & a ~ AC_Var & G2 & y ~ AC_Var = G1 & a ~ AC_Var & (G2 & y ~ AC_Var)) by  repeat rewrite~ concat_assoc.
  assert (ok (G1 & a ~ AC_Var & G2 & y ~ AC_Var)) by apply~ ok_push.
  lets: H1 H H0 H5 H6.
  repeat rewrite concat_assoc in H7; auto.

  (* CASTUP *)
  forwards * : IHuni.
  apply~ ATUnify_CastUp.

  (* CASTDOWN *)
  forwards * : IHuni.
  apply~ ATUnify_CastDn.

  (* PI *)
  lets: tunify_wextctx uni okg.
  apply weak_extension_order_var in H.
  destruct H as (I1 & I2 & [hinfo _]). subst.
  lets: atunify_ok_preservation uni okg.
  apply ATUnify_Pi with (L:=L \u dom (I1 & a ~ AC_Var & I2)) (H1:=(I1 & a ~ AC_Typ t & I2)).
  forwards * : IHuni.

  intros y notin.
  assert(y \notin L) by auto.

  assert(H3 & a ~ AC_Var & H4 & y ~ AC_Typ t1 = H3 & a ~ AC_Var & (H4 & y ~ AC_Typ t1)) by repeat rewrite~ concat_assoc.
  assert(I1 & a ~ AC_Var & I2 & y ~ AC_Typ t1 = I1 & a ~ AC_Var & (I2 & y ~ AC_Typ t1)) by repeat rewrite~ concat_assoc.
  assert(ok (I1 & a ~ AC_Var & I2 & y ~ AC_Typ t1)) by apply~ ok_push.
  lets: H2 H1 H5 H6 H7.

  repeat rewrite~ concat_assoc in H8.

  rewrite tsubst_add_ctx in H8. rewrite tsubst_add_var in H8.
  rewrite tsubst_add_ctx in H8. rewrite tsubst_add_var in H8.
  rewrite tsubst_add_ctx. rewrite tsubst_add_typvar.
  rewrite tsubst_add_ctx. rewrite tsubst_add_typvar. auto.

  (* FORALL *)
  apply ATUnify_Forall with (L \u dom (G1 & a ~ AC_Var & G2)).
  intros y notin.
  assert(H: y \notin L) by auto.
  lets: H0 H. clear H0.
  assert(H2 & a ~ AC_Var & H3 & y ~ AC_TVar = H2 & a ~ AC_Var & (H3 & y ~ AC_TVar)) by repeat rewrite~ concat_assoc.
  assert(G1 & a ~ AC_Var & G2 & y ~ AC_TVar = G1 & a ~ AC_Var &  (G2 & y ~ AC_TVar)) by repeat rewrite~ concat_assoc.
  assert (ok (G1 & a ~ AC_Var & G2 & y ~ AC_TVar)) by apply~ ok_push.
  lets: H1 H H0 H5 H6.
  repeat rewrite concat_assoc in H7; auto.

  (* ANN *)
  lets: tunify_wextctx uni1 okg.
  apply weak_extension_order_var in H.
  destruct H as (I1 & I2 & [hinfo _]). subst.
  lets: atunify_ok_preservation uni1 okg.
  forwards * : IHuni1. clear IHuni1.
  forwards * : IHuni2 H.
  apply* ATUnify_Ann.
  rewrite tsubst_add_ctx in H3. rewrite tsubst_add_var in H3.
  rewrite tsubst_add_ctx in H3. rewrite tsubst_add_var in H3.
  rewrite tsubst_add_ctx. rewrite tsubst_add_typvar.
  rewrite tsubst_add_ctx. rewrite tsubst_add_typvar. auto.

  (* EVAR TY *)
  lets: resolve_evar_ok_preservation H0 okg.
  assert(binds a0 (AC_Solved_EVar t2) (H1 & a0 ~ AC_Solved_EVar t2 & H2)).
  apply~ binds_middle_eq. apply ok_middle_inv_r in H6; auto.
  rewrite sinfo1 in H7.
  apply binds_remove in H7; auto.
  apply binds_concat_inv in H7.
  destruct H7 as [bdh2 | [notinh2 bdh1]].
  apply split_bind_context in bdh2.
  destruct bdh2 as (I1 & I2 & g2info). subst.
  repeat rewrite concat_assoc in *.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.
  apply~ ATUnify_EVarTy.
  do 3 rewrite <- concat_assoc in H0.
  rewrite concat_assoc in H0.
  apply resolve_evar_middle_change2 with (t:=t) in H0; auto.
  repeat rewrite concat_assoc in H0. auto.
  apply* awtermt_replace2.
  apply* ok_middle_change.
  rewrite <- sinfo1. apply* ok_middle_change.

  apply split_bind_context in bdh1.
  destruct bdh1 as (I1 & I2 & g2info). subst.
  do 3 rewrite <- concat_assoc in sinfo1.
  rewrite concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.
  do 3 rewrite <- concat_assoc.
  rewrite concat_assoc.
  apply~ ATUnify_EVarTy.
  repeat rewrite concat_assoc in H0.
  apply resolve_evar_middle_change2 with (t:=t) in H0; auto.
  repeat rewrite concat_assoc. auto.
  apply* ok_middle_change.
  rewrite <- sinfo1. apply* ok_middle_change.

  assert(a0 <> a). introv neq. subst. false binds_middle_eq_inv H7.
  rewrite~ <- sinfo1. apply* ok_middle_change.
  auto.

  (* TY EVAR *)
  lets: resolve_evar_ok_preservation H3 okg.
  assert(binds a0 (AC_Solved_EVar t2) (H1 & a0 ~ AC_Solved_EVar t2 & H2)).
  apply~ binds_middle_eq. apply ok_middle_inv_r in H7; auto.
  rewrite sinfo1 in H8.
  apply binds_remove in H8; auto.
  apply binds_concat_inv in H8.
  destruct H8 as [bdh2 | [notinh2 bdh1]].
  apply split_bind_context in bdh2.
  destruct bdh2 as (I1 & I2 & g2info). subst.
  repeat rewrite concat_assoc in *.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.
  apply~ ATUnify_TyEVar.
  do 3 rewrite <- concat_assoc in H3.
  rewrite concat_assoc in H3.
  apply resolve_evar_middle_change2 with (t:=t) in H3; auto.
  repeat rewrite concat_assoc in H3. auto.
  apply* awtermt_replace2.
  apply* ok_middle_change.
  rewrite <- sinfo1. apply* ok_middle_change.

  apply split_bind_context in bdh1.
  destruct bdh1 as (I1 & I2 & g2info). subst.
  do 3 rewrite <- concat_assoc in sinfo1.
  rewrite concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.
  do 3 rewrite <- concat_assoc.
  rewrite concat_assoc.
  apply~ ATUnify_TyEVar.
  repeat rewrite concat_assoc in H3.
  apply resolve_evar_middle_change2 with (t:=t) in H3; auto.
  repeat rewrite concat_assoc. auto.
  apply* ok_middle_change.
  rewrite <- sinfo1. apply* ok_middle_change.

  assert(a0 <> a). introv neq. subst. false binds_middle_eq_inv H8.
  rewrite~ <- sinfo1. apply* ok_middle_change.
  auto.

  apply ATUnify_Expr.
  forwards * : IHuni okg.
Qed.

Lemma aunify_is_atunify: forall G s t H,
    ok G ->
    AUnify G s t H ->
    ATUnify UType G s t H.
Proof.
  introv okg uni.
  induction uni; auto.
  apply ATUnify_Expr. apply~ ATUnify_Var.
  apply ATUnify_Expr. apply ATUnify_Typed_Var with t; auto.
  apply ATUnify_EVar; auto.
  apply ATUnify_TVar; auto.
  apply ATUnify_Expr. apply ATUnify_Star; auto.

  lets: unify_ok_preservation uni1 okg.
  lets: IHuni1 okg. inversion H2; subst.
  lets: IHuni2 H0. inversion H3; subst.
  apply ATUnify_Expr. apply* ATUnify_App.

  apply ATUnify_Expr.
  apply ATUnify_Lam with (L \u dom G).
  intros y notin.
  assert(y \notin L) by auto.
  assert(ok (G & y ~ AC_Var)) by apply~ ok_push.
  lets: H0 H2. clear H0.
  lets: H1 H2 H3. clear H1. inversion H0; subst.
  auto.

  lets: IHuni okg.
  inversion H0; subst.
  apply ATUnify_Expr. apply ATUnify_CastUp; auto.

  lets: IHuni okg.
  inversion H0; subst.
  apply ATUnify_Expr. apply ATUnify_CastDn; auto.

  apply ATUnify_Expr.
  apply ATUnify_Pi with (L:=L \u dom H1) (H1:=H1); auto.
  intros y notin.
  assert(y \notin L) by auto.
  lets: IHuni okg.
  lets: atunify_ok_preservation H4 okg.
  assert(ok (H1 & y ~ AC_Var)) by apply~ ok_push.
  lets: H2 H3 H6. clear H2.

  assert( ATUnify UType (H1 & y ~ AC_Var & empty) (ACtxTSubst H1 (t2 @@' AE_FVar y))
         (ACtxTSubst H1 (t4 @@' AE_FVar y)) (H & y ~ AC_Var & empty)).
  repeat rewrite~ concat_empty_r.

  apply tunify_middle_change with (t:=t1) in H2.
  repeat rewrite concat_empty_r in *. auto.
  rewrite~ concat_empty_r.

  apply ATUnify_Expr.
  apply ATUnify_Forall with (L \u dom G).
  intros y notin.
  assert(y \notin L) by auto.
  assert(ok (G & y ~ AC_TVar)) by apply~ ok_push.
  lets: H1 H2 H3. auto.

  lets: unify_ok_preservation uni1 okg.
  lets: IHuni1 okg. inversion H2; subst.
  lets: IHuni2 H0.
  apply ATUnify_Expr. apply* ATUnify_Ann.

  apply~ ATUnify_EVarTy.
  apply~ ATUnify_TyEVar.
Qed.

(***********************)
(* EQUIVALENCE OF UNIFY *)
(***********************)

Inductive AUnify2 : ACtx -> AType -> AType -> ACtx -> Prop :=
  | AUnify2_Var : forall x G, binds x AC_Var G -> AUnify2 G (AT_Expr (AE_FVar x)) (AT_Expr (AE_FVar x)) G
  | AUnify2_Typed_Var : forall x G t, binds x (AC_Typ t) G -> AUnify2 G (AT_Expr (AE_FVar x)) (AT_Expr (AE_FVar x)) G
  | AUnify2_EVar : forall a G, binds a AC_Unsolved_EVar G -> AUnify2 G (AT_EVar a) (AT_EVar a) G
  | AUnify2_TVar : forall a G, binds a AC_TVar G -> AUnify2 G (AT_TFVar a) (AT_TFVar a) G
  (* no case for solved evar since it is fully applied under context *)
  | AUnify2_Star : forall G, AUnify2 G (AT_Expr (AE_Star)) (AT_Expr (AE_Star)) G
  | AUnify2_App : forall t1 t2 t3 t4 G H1 H,
      AUnify2 G (AT_Expr t1) (AT_Expr t2) H1 ->
      AUnify2 H1 (AT_Expr (ACtxSubst H1 t3)) (AT_Expr (ACtxSubst H1 t4)) H ->
      AUnify2 G (AT_Expr (AE_App t1 t3)) (AT_Expr (AE_App t2 t4)) H
  | AUnify2_Lam : forall t1 t2 G H L,
      (forall x, x \notin L -> AUnify2 (G & x ~ AC_Var) (AT_Expr (t1 @ x)) (AT_Expr (t2 @ x)) (H & x ~ AC_Var)) ->
      AUnify2 G (AT_Expr (AE_Lam t1)) (AT_Expr (AE_Lam t2)) H
  | AUnify2_CastUp : forall t1 t2 G H,
      AUnify2 G (AT_Expr t1) (AT_Expr t2) H ->
      AUnify2 G (AT_Expr (AE_CastUp t1)) (AT_Expr (AE_CastUp t2)) H
  | AUnify2_CastDn : forall t1 t2 G H,
      AUnify2 G (AT_Expr t1) (AT_Expr t2) H ->
      AUnify2 G (AT_Expr (AE_CastDn t1)) (AT_Expr (AE_CastDn t2)) H
  | AUnify2_Pi : forall t1 t2 t3 t4 G H1 H L,
      AUnify2 G t1 t3 H1 ->
      (forall x, x \notin L -> AUnify2 (H1 & x ~ AC_Typ t1) (ACtxTSubst H1 (t2 @' x)) (ACtxTSubst H1 (t4 @' x)) (H & x ~ AC_Typ t1)) ->
      AUnify2 G (AT_Expr (AE_Pi t1 t2)) (AT_Expr (AE_Pi t3 t4)) H
  | AUnify2_Forall : forall t1 t2 G H L,
      (forall x, x \notin L -> AUnify2 (G & x ~ AC_TVar) (t1 @#' x) (t2 @#' x) (H & x ~ AC_TVar)) ->
      AUnify2 G (AT_Expr (AE_Forall t1)) (AT_Expr (AE_Forall t2)) H
  | AUnify2_Ann : forall t1 t2 t3 t4 G H1 H,
      AUnify2 G (AT_Expr t1) (AT_Expr t2) H1 ->
      AUnify2 H1 (ACtxTSubst H1 t3) (ACtxTSubst H1 t4) H ->
      AUnify2 G (AT_Expr (AE_Ann t1 t3)) (AT_Expr (AE_Ann t2 t4)) H
  | AUnify2_EVarTy : forall a t1 t2 G H1 H2,
      a \notin ATFv (t1) ->
      AResolveEVar G a t1 t2 (H1 & a ~ AC_Unsolved_EVar & H2) ->
      AWTermT H1 t2 ->
      AUnify2 G (AT_EVar a) t1 (H1 & a ~ AC_Solved_EVar t2 & H2)
  | AUnify2_TyEVar : forall a t1 t2 G H1 H2,
      (forall n, t1 <> AT_EVar n) ->
      a \notin ATFv (t1) ->
      AResolveEVar G a t1 t2 (H1 & a ~ AC_Unsolved_EVar & H2) ->
      AWTermT H1 t2 ->
      AUnify2 G t1 (AT_EVar a) (H1 & a ~ AC_Solved_EVar t2 & H2).

Hint Constructors AUnify2.

Lemma unify2_ok_preservation: forall G s t H,
    AUnify2 G s t H ->
    ok G ->
    ok H.
Proof.
  introv uni okg.
  induction uni; auto.
  pick_fresh y.
  assert (y \notin L) by auto_star.
  assert (ok (G & y ~ AC_Var)) by apply* ok_push.
  lets: H1 H2 H3.
  apply ok_concat_inv_l in H4; auto.

  lets: IHuni okg.
  pick_fresh y.
  assert (y \notin L) by auto_star.
  assert (ok (H1 & y ~ AC_Typ t1)) by apply* ok_push.
  lets: H2 H4 H5.
  apply ok_concat_inv_l in H5; auto.

  pick_fresh y.
  assert (y \notin L) by auto_star.
  assert (ok (G & y ~ AC_TVar)) by apply* ok_push.
  lets: H1 H2 H3.
  apply ok_concat_inv_l in H4; auto.

  lets: resolve_evar_ok_preservation H0 okg.
  apply* ok_middle_change.

  lets: resolve_evar_ok_preservation H3 okg.
  apply* ok_middle_change.
Qed.

Hint Resolve unify2_ok_preservation.

Lemma unify2_wextctx: forall G s t H,
    AUnify2 G s t H ->
    ok G ->
    WExtCtx G H.
Proof.
  introv uni okg.
  lets: unify2_ok_preservation uni okg.
  induction uni; auto.

  (* APP *)
  lets: unify2_ok_preservation uni1 okg.
  lets: IHuni1 okg H2.
  lets: IHuni2 H2 H0.
  lets: weak_extension_transitivity H3 H4. auto.

  (* LAM *)
  pick_fresh y.
  assert (y \notin L) by auto.
  assert(ok (G & y ~ AC_Var)). constructor~.
  assert(ok (H & y ~ AC_Var)). constructor~.
  lets: H2 y H3 H4 H5.
  lets: weak_extension_remove_var H6.  auto.

  (* PI *)
  pick_fresh y.
  assert (y \notin L) by auto.
  assert(ok (G & y ~ AC_Typ t1)). constructor~.
  lets: unify2_ok_preservation uni okg.
  assert(ok (H1 & y ~ AC_Typ t1)). constructor~.
  assert(ok (H & y ~ AC_Typ t1)). constructor~.
  lets: H3 y H4 H7 H8.
  lets: weak_extension_remove_typvar H9.
  lets: IHuni okg H6.
  lets: weak_extension_transitivity H11 H10. auto.

  (* FORALL *)
  pick_fresh y.
  assert (y \notin L) by auto.
  assert(ok (G & y ~ AC_TVar)). constructor~.
  assert(ok (H & y ~ AC_TVar)). constructor~.
  lets: H2 y H3 H4 H5.
  lets: weak_extension_remove_tvar H6.  auto.

  (* ANN *)
  lets: unify2_ok_preservation uni1 okg.
  lets: IHuni1 okg H2.
  lets: IHuni2 H2 H0.
  lets: weak_extension_transitivity H3 H4. auto.

  (* EVarL *)
  lets: resolve_evar_wextctx H3 okg. auto.
  lets: weak_extension_solve_middle t2 H5. auto.

  (* EVarR *)
  lets: resolve_evar_wextctx H4 okg. auto.
  lets: weak_extension_solve_middle t2 H6. auto.
Qed.

Lemma aunify2_middle_change: forall e G1 G2 a t d H1 H2,
    AUnify2 (G1 & a ~ AC_Var & G2) e d (H1 & a ~ AC_Var & H2) ->
    ok (G1 & a ~ AC_Var & G2) ->
    AUnify2 (G1 & a ~ AC_Typ t & G2) e d (H1 & a ~ AC_Typ t & H2).
Proof.
  introv uni.
  gen_eq S1: (G1 & a ~ AC_Var & G2).
  gen_eq S2: (H1 & a ~ AC_Var & H2). gen H1 H2 G1 G2.
  induction uni; introv sinfo1 sinfo2 okg; subst.

  (* Var *)
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  destruct(eq_var_dec x a).
  subst.
  apply~ AUnify2_Typed_Var. apply~ binds_middle_eq.
  apply ok_middle_inv_r in okg. auto.
  apply AUnify2_Var.
  apply binds_remove in H; auto.
  apply~ binds_weaken.
  apply* ok_middle_change.
  rewrite <- sinfo2. apply* ok_middle_change.

  (* TypedVar *)
  assert (x <> a). introv neq. subst. false binds_middle_eq_inv H. auto.
  apply binds_remove in H; auto.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  apply AUnify2_Typed_Var with t0. apply~ binds_weaken.
  apply* ok_middle_change.
  rewrite <- sinfo2. apply* ok_middle_change.

  (* EVar *)
  assert (a0 <> a). introv neq. subst. false binds_middle_eq_inv H. auto.
  apply binds_remove in H; auto.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  apply AUnify2_EVar. apply~ binds_weaken.
  apply* ok_middle_change.
  rewrite <- sinfo2. apply* ok_middle_change.

  (* TFVar *)
  assert (a0 <> a). introv neq. subst. false binds_middle_eq_inv H. auto.
  apply binds_remove in H; auto.
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  apply AUnify2_TVar. apply~ binds_weaken.
  apply* ok_middle_change.
  rewrite <- sinfo2. apply* ok_middle_change.

  (* STAR *)
  apply ok_middle_eq2 in sinfo2; auto.
  destruct sinfo2 as [? [_ ?]]. subst.
  apply AUnify2_Star.
  rewrite <- sinfo2. apply* ok_middle_change.

  (* APP *)
  assert (okg2: ok (G1 & a ~ AC_Var & G2)) by apply* ok_middle_change.
  lets: unify2_wextctx uni1 okg2.
  apply weak_extension_order_var in H.
  destruct H as (I1 & I2 & [hinfo _]). subst.
  lets: unify2_ok_preservation uni1 okg2.
  forwards * : IHuni1. clear IHuni1.
  forwards * : IHuni2.
  apply* AUnify2_App.
  rewrite subst_add_ctx in H3.
  rewrite subst_add_var in H3.
  rewrite subst_add_ctx in H3.
  rewrite subst_add_var in H3.
  rewrite subst_add_ctx.
  rewrite subst_add_typvar.
  rewrite subst_add_ctx.
  rewrite subst_add_typvar. auto.

  (* LAM *)
  apply AUnify2_Lam with (L \u dom (G1 & a ~ AC_Typ t & G2)).
  intros y notin.
  assert(H: y \notin L) by auto.
  lets: H0 H. clear H0.
  assert(H2 & a ~ AC_Var & H3 & y ~ AC_Var = H2 & a ~ AC_Var & (H3 & y ~ AC_Var )) by repeat rewrite~ concat_assoc.
  assert(G1 & a ~ AC_Var & G2 & y ~ AC_Var = G1 & a ~ AC_Var & (G2 & y ~ AC_Var)) by  repeat rewrite~ concat_assoc.
  assert (ok (G1 & a ~ AC_Var & G2 & y ~ AC_Var)). apply~ ok_push.
  lets: H1 H H0 H5 H6.
  repeat rewrite concat_assoc in H7; auto.

  (* CASTUP *)
  forwards * : IHuni.

  (* CASTDOWN *)
  forwards * : IHuni.

  (* PI *)
  lets: unify2_wextctx uni okg.
  apply weak_extension_order_var in H.
  destruct H as (I1 & I2 & [hinfo _]). subst.
  lets: unify2_ok_preservation uni okg.
  apply AUnify2_Pi with (L:=L \u dom (I1 & a ~ AC_Typ t & I2)) (H1:=(I1 & a ~ AC_Typ t & I2)).
  forwards * : IHuni. clear IHuni.
  intros y notin.
  assert(y \notin L) by auto.
  lets: H0 H1. clear H0.
  assert(H3 & a ~ AC_Var & H4 & y ~ AC_Typ t1 = H3 & a ~ AC_Var & (H4 & y ~ AC_Typ t1 )) by repeat rewrite~ concat_assoc.
  assert(I1 & a ~ AC_Var & I2 & y ~ AC_Typ t1 = I1 & a ~ AC_Var & (I2 & y ~ AC_Typ t1)) by  repeat rewrite~ concat_assoc.
  assert (ok (I1 & a ~ AC_Var & I2 & y ~ AC_Typ t1)).
  apply~ ok_push.
  lets: H2 H1 H0 H6 H7.
  repeat rewrite concat_assoc in H8; auto.

  rewrite tsubst_add_ctx in H8. rewrite tsubst_add_var in H8.
  rewrite tsubst_add_ctx in H8. rewrite tsubst_add_var in H8.
  rewrite tsubst_add_ctx. rewrite tsubst_add_typvar.
  rewrite tsubst_add_ctx. rewrite tsubst_add_typvar. auto.

  (* FORALL *)
  apply AUnify2_Forall with (L \u dom (G1 & a ~ AC_Typ t & G2)).
  intros y notin.
  assert(H: y \notin L) by auto.
  lets: H0 H. clear H0.
  assert(H2 & a ~ AC_Var & H3 & y ~ AC_TVar = H2 & a ~ AC_Var & (H3 & y ~ AC_TVar )) by repeat rewrite~ concat_assoc.
  assert(G1 & a ~ AC_Var & G2 & y ~ AC_TVar = G1 & a ~ AC_Var & (G2 & y ~ AC_TVar)) by  repeat rewrite~ concat_assoc.
  assert (ok (G1 & a ~ AC_Var & G2 & y ~ AC_TVar)). apply~ ok_push.
  lets: H1 H H0 H5 H6.
  repeat rewrite concat_assoc in H7; auto.

  (* ANN *)
  assert (okg2: ok (G1 & a ~ AC_Var & G2)). apply* ok_middle_change.
  lets: unify2_wextctx uni1 okg2.
  apply weak_extension_order_var in H.
  destruct H as (I1 & I2 & [hinfo _]). subst.
  lets: unify2_ok_preservation uni1 okg2.
  forwards * : IHuni1. clear IHuni1.
  forwards * : IHuni2. clear IHuni2.
  apply* AUnify2_Ann.
  rewrite tsubst_add_ctx in H3. rewrite tsubst_add_var in H3.
  rewrite tsubst_add_ctx in H3. rewrite tsubst_add_var in H3.
  rewrite tsubst_add_ctx. rewrite tsubst_add_typvar.
  rewrite tsubst_add_ctx. rewrite tsubst_add_typvar. auto.

  (* EVAR TY *)
  lets: resolve_evar_ok_preservation H0 okg.
  assert(binds a0 (AC_Solved_EVar t2) (H1 & a0 ~ AC_Solved_EVar t2 & H2)).
  apply~ binds_middle_eq. apply ok_middle_inv_r in H6; auto.
  rewrite sinfo1 in H7.
  apply binds_remove in H7; auto.
  apply binds_concat_inv in H7.
  destruct H7 as [bdh2 | [notinh2 bdh1]].
  apply split_bind_context in bdh2.
  destruct bdh2 as (I1 & I2 & g2info). subst.
  repeat rewrite concat_assoc in *.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.
  apply~ AUnify2_EVarTy.
  do 3 rewrite <- concat_assoc in H0.
  rewrite concat_assoc in H0.
  apply resolve_evar_middle_change2 with (t:=t) in H0; auto.
  repeat rewrite concat_assoc in H0. auto.
  apply* awtermt_replace2.
  apply* ok_middle_change.
  rewrite <- sinfo1. apply* ok_middle_change.

  apply split_bind_context in bdh1.
  destruct bdh1 as (I1 & I2 & g2info). subst.
  do 3 rewrite <- concat_assoc in sinfo1.
  rewrite concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.
  do 3 rewrite <- concat_assoc.
  rewrite concat_assoc.
  apply~ AUnify2_EVarTy.
  repeat rewrite concat_assoc in H0.
  apply resolve_evar_middle_change2 with (t:=t) in H0; auto.
  repeat rewrite concat_assoc. auto.
  apply* ok_middle_change.
  rewrite <- sinfo1. apply* ok_middle_change.

  assert(a0 <> a). introv neq. subst. false binds_middle_eq_inv H7.
  rewrite~ <- sinfo1. apply* ok_middle_change.
  auto.

  (* TY EVAR *)
  lets: resolve_evar_ok_preservation H3 okg.
  assert(binds a0 (AC_Solved_EVar t2) (H1 & a0 ~ AC_Solved_EVar t2 & H2)).
  apply~ binds_middle_eq. apply ok_middle_inv_r in H7; auto.
  rewrite sinfo1 in H8.
  apply binds_remove in H8; auto.
  apply binds_concat_inv in H8.
  destruct H8 as [bdh2 | [notinh2 bdh1]].
  apply split_bind_context in bdh2.
  destruct bdh2 as (I1 & I2 & g2info). subst.
  repeat rewrite concat_assoc in *.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.
  apply~ AUnify2_TyEVar.
  do 3 rewrite <- concat_assoc in H3.
  rewrite concat_assoc in H3.
  apply resolve_evar_middle_change2 with (t:=t) in H3; auto.
  repeat rewrite concat_assoc in H3. auto.
  apply* awtermt_replace2.
  apply* ok_middle_change.
  rewrite <- sinfo1. apply* ok_middle_change.

  apply split_bind_context in bdh1.
  destruct bdh1 as (I1 & I2 & g2info). subst.
  do 3 rewrite <- concat_assoc in sinfo1.
  rewrite concat_assoc in sinfo1.
  apply ok_middle_eq2 in sinfo1; auto.
  destruct sinfo1 as [? [_ ?]]. subst.
  do 3 rewrite <- concat_assoc.
  rewrite concat_assoc.
  apply~ AUnify2_TyEVar.
  repeat rewrite concat_assoc in H3.
  apply resolve_evar_middle_change2 with (t:=t) in H3; auto.
  repeat rewrite concat_assoc. auto.
  apply* ok_middle_change.
  rewrite <- sinfo1. apply* ok_middle_change.

  assert(a0 <> a). introv neq. subst. false binds_middle_eq_inv H8.
  rewrite~ <- sinfo1. apply* ok_middle_change.
  auto.
Qed.

Lemma aunify_is_aunify2: forall G H s t,
    ok G ->
    AUnify G s t H ->
    AUnify2 G s t H.
Proof.
  introv okg uni.
  induction uni; auto.
  apply* AUnify2_Typed_Var.
  apply* AUnify2_App.
  apply AUnify2_Lam with (L \u dom G).
  intros y notin. assert (y \notin L) by auto.
  apply~ H1.
  apply AUnify2_Pi with (L:=L \u dom G \u dom H1) (H1:=H1); auto.
  intros y notin. assert (y \notin L) by auto.
  assert (ok (H1 & y ~ AC_Var)). apply~ ok_push.
  lets: unify_ok_preservation uni okg. auto.
  lets: H2 H3 H4.
  assert ( AUnify2 (H1 & y ~ AC_Var & empty)
         (ACtxTSubst H1 (t2 @@' AE_FVar y))
         (ACtxTSubst H1 (t4 @@' AE_FVar y))
         (H & y ~ AC_Var & empty)).
  repeat rewrite~ concat_empty_r.
  apply aunify2_middle_change with (t:=t1) in H6.
  repeat rewrite~ concat_empty_r in H6.
  rewrite~ concat_empty_r.

  apply AUnify2_Forall with (L \u dom G).
  intros y notin. apply* H1.
  apply* AUnify2_Ann.
Qed.

Lemma aunify2_is_aunify: forall G H s t,
    ok G ->
    AUnify2 G s t H ->
    AUnify G s t H.
Proof.
  introv okg uni.
  induction uni; auto.
  apply* AUnify_Typed_Var.
  apply* AUnify_App.
  apply AUnify_Lam with (L \u dom G).
  intros y notin. assert (y \notin L) by auto.
  lets: H1 H2; auto.
  apply AUnify_Pi with (L:=L \u dom H1) (H1:=H1); auto.
  intros y notin. assert (y \notin L) by auto.
  lets: unify2_ok_preservation uni okg.
  assert (ok (H1 & y ~ AC_Typ t1)). apply* ok_push.
  lets: H2 H3 H5.
  assert (AUnify (H1 & y ~ AC_Typ t1 & empty)
         (ACtxTSubst H1 (t2 @@' AE_FVar y))
         (ACtxTSubst H1 (t4 @@' AE_FVar y))
         (H & y ~ AC_Typ t1 & empty)).
  repeat rewrite~ concat_empty_r.
  lets: aunify_middle_change H7.
  assert (ok (H1 & y ~ AC_Typ t1 & empty)). rewrite~ concat_empty_r.
  lets: H8 H9.
  repeat rewrite~ concat_empty_r in H10.

  apply AUnify_Forall with (L \u dom G).
  intros y notin.
  assert (y \notin L) by auto.
  assert (ok (G & y ~ AC_TVar)) by apply* ok_push.
  lets: H1 H2 H3. auto.

  apply* AUnify_Ann.
Qed.
