Require Import LibLN.
Require Import DeclDef.
Require Import DeclInfra.
Require Import AlgoDef.
Require Import AlgoInfra.
Require Import CtxExtension.
Require Import UtilityEnv.
Require Import Subst.
Require Import Exists.
Require Import UtilityMore.
Require Import WeakExtension.

(***********************)
(* ADMITS *)
(***********************)

Lemma awf_weakening_insert_unsolved: forall G1 G2 a,
    AWf (G1 & G2) ->
    a # (G1 & G2) ->
    AWf (G1 & a ~ AC_Unsolved_EVar & G2).
Admitted.

Lemma awf_solve_middle: forall G1 G2 a t,
    AWf (G1 & a ~ AC_Unsolved_EVar & G2) ->
    AWfTyp G1 t ->
    AWf (G1 & a ~ AC_Solved_EVar t & G2).
Admitted.

Lemma awftyp_weakening_insert_unsolved: forall G1 G2 a e,
    AWfTyp (G1 & G2) e ->
    a # (G1 & G2) ->
    AWfTyp (G1 & a ~ AC_Unsolved_EVar & G2) e.
Admitted.

Lemma awftyp_solve_middle: forall G1 G2 a e t,
    AWfTyp (G1 & a ~ AC_Unsolved_EVar & G2) e ->
    AWfTyp G1 t ->
    AWfTyp (G1 & a ~ AC_Solved_EVar t & G2) e.
Admitted.

Lemma awftyp_weakening: forall G H e,
    AWfTyp G e ->
    AWfTyp (G & H) e.
Admitted.

Lemma awftyp_subst: forall G e,
    AWfTyp G e ->
    AWfTyp G (ACtxTSubst G e).
Admitted.

(***********************)
(* OK *)
(***********************)

Lemma resolve_evar_ok_preservation: forall G s t H a,
    AResolveEVar G a s t H ->
    ok G ->
    ok H.
Proof.
  introv res okg.
  induction res; auto.
  assert(ok (G1 & (a ~ AC_Unsolved_EVar & G2 & b ~ AC_Solved_EVar (AT_EVar a1) & G3))). repeat rewrite concat_assoc. apply*  ok_middle_change.
  assert(ok (G1 & a1 ~ AC_Unsolved_EVar & (a ~ AC_Unsolved_EVar & G2 & b ~ AC_Solved_EVar (AT_EVar a1) & G3))). apply ok_insert; auto. repeat rewrite concat_assoc in H1; auto.
  lets: IHres okg.
  pick_fresh y.
  assert (ok (H1 & y ~ AC_Var)). apply~ ok_push.
  lets: H2 H4; auto.

  pick_fresh y.
  assert (ok (G & y ~ AC_Var)). apply~ ok_push.
  lets: H1 H2; auto.
Qed.

Lemma resolve_forall_ok_preservation: forall G s t H a m,
    AResolveForall G a m s t H ->
    ok G ->
    ok H.
Proof.
  introv res okg.
  induction res; auto.
  apply IHres.
  rewrite <- concat_assoc. apply ok_insert. rewrite~ concat_assoc. auto.
Qed.

Lemma unify_ok_preservation: forall G s t H,
    AUnify G s t H ->
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
  assert (ok (H1 & y ~ AC_Var)) by apply* ok_push.
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

Lemma subtyping_ok_preservation: forall G s t H,
    ASubtyping G s t H ->
    ok G ->
    ok H.
Proof.
  introv sub okg.
  induction sub; auto.
  assert (ok (G & v ~ AC_TVar)). apply~ ok_push.
  lets: IHsub H1.
  repeat apply ok_concat_inv_l in H2; auto.

  assert (ok (G & b ~ AC_Marker & a ~ AC_Unsolved_EVar)).
  constructor~.
  lets: IHsub H3.
  apply ok_concat_inv_l in H4.
  apply ok_concat_inv_l in H4. auto.

  lets: IHsub1 okg.
  assert (ok (H1 & x ~ AC_Typ s1)). apply~ ok_push.
  lets: IHsub2 H3.
  repeat apply ok_concat_inv_l in H4; auto.

  lets: resolve_forall_ok_preservation H2 okg.
  lets: unify_ok_preservation H3 H4. auto.

  lets: resolve_forall_ok_preservation H2 okg.
  lets: unify_ok_preservation H3 H4. auto.

  lets: unify_ok_preservation H0 okg. auto.
Qed.

Lemma atyping_ok : forall G m e t H,
    ATyping m G e t H ->
    ok G.
Proof.
  introv ty. induction ty; auto.
  repeat apply ok_push_inv_ok in IHty. auto.
Qed.

Lemma atyping_ok_preservation : forall G m e t H,
    ATyping m G e t H ->
    ok H.
Proof.
  introv ty.
  induction ty; auto.
  repeat apply ok_concat_inv_l in IHty2; auto.
  assert (ok (H & I)). apply ok_remove in IHty. auto.
  repeat apply ok_concat_inv_l in IHty; auto.
  apply uv_ok in H3. auto.
  repeat apply ok_concat_inv_l in IHty; auto.
  repeat apply ok_concat_inv_l in IHty; auto.

  lets: subtyping_ok_preservation H0 IHty. auto.
Qed.

(***********************)
(* TYPING *)
(***********************)

Lemma awftyp_unsolved_evar: forall G a,
    AWf G ->
    binds a AC_Unsolved_EVar G ->
    AWfTyp G (AT_EVar a).
Proof.
  introv wf bd.
  apply AWf_Expr with G; auto.
  apply ATC_Sub with G (AT_Expr AE_Star).
  apply~ ATI_EVar.
  apply~ ASub_Unify.
  rewrite actxtsubst_expr.
  rewrite subst_star.
  apply~ AUnify_Star.
Qed.

(***********************)
(* AWF *)
(***********************)

Lemma resolve_forall_awf_preservation: forall G a m s t H,
    AResolveForall G a m s t H ->
    AWf G ->
    AWf H.
Proof.
  introv res wfg.
  induction res; auto.
  apply IHres.
  rewrite <- concat_assoc.
  apply~ awf_weakening_insert_unsolved.
  rewrite~ concat_assoc.
Qed.

Lemma resolve_evar_awf_preservation: forall G a s t H,
    AResolveEVar G a s t H ->
    AWf G ->
    AWf H.
Proof.
  introv res wfg.
  induction res; auto.
  apply~ awf_solve_middle.
  do 3 rewrite <- concat_assoc.
  apply~ awf_weakening_insert_unsolved.
  do 3 rewrite~ concat_assoc.

  apply~ awftyp_unsolved_evar.
  rewrite <- concat_assoc.
  apply~ awf_weakening_insert_unsolved.
  rewrite~ concat_assoc.
  do 2 apply AWf_left in wfg; auto.

  pick_fresh y. assert(y \notin L) by auto.
  lets: H2 H3.
  assert (AWf (H1 & y ~ AC_Var)) by apply* AWf_Var.
  lets: H4 H5. apply AWf_left in H6. auto.

  pick_fresh y. assert(y \notin L) by auto.
  lets: H1 H2.
  assert (AWf (G & y ~ AC_Var)) by apply* AWf_Var.
  lets: H3 H4. apply AWf_left in H5. auto.
Qed.

Lemma unify_awf_preservation: forall G s t H,
    AUnify G s t H ->
    AWf G ->
    AWf H.
Proof.
  introv uni wfg.
  induction uni; auto.

  pick_fresh y. assert(y \notin L) by auto.
  assert (AWf (G & y ~ AC_Var)) by apply~ AWf_Var.
  lets: H1 H2 H3. apply AWf_left in H4; auto.

  lets: IHuni wfg.
  pick_fresh y. assert(y \notin L) by auto.
  assert (AWf (H1 & y ~ AC_Var)) by apply~ AWf_Var.
  lets: H2 H4 H5. apply AWf_left in H6; auto.

  pick_fresh y. assert(y \notin L) by auto.
  assert (AWf (G & y ~ AC_TVar)) by apply~ AWf_TVar.
  lets: H1 H2 H3. apply AWf_left in H4; auto.

  lets: resolve_evar_awf_preservation H0 wfg.
  apply* awf_solve_middle.
  admit. (*solve evar*)

  lets: resolve_evar_awf_preservation H3 wfg.
  apply* awf_solve_middle.
  admit. (*solve evar*)
Qed.

Lemma atyping_awf: forall G m e t H,
    ATyping m G e t H ->
    AWf G.
Proof.
  introv ty.
  induction ty; repeat apply AWf_left in IHty; auto.
Qed.

Lemma atyping_awf_preservation: forall G m e t H,
    ATyping m G e t H ->
    AWf G ->
    AWf H.
Proof.
Admitted.

(***********************)
(* WEAK EXTENSION PROOF *)
(***********************)

Hint Resolve weak_extension_reflexicity.
Lemma resolve_evar_wextctx: forall G a s t H,
    AResolveEVar G a s t H ->
    ok G ->
    WExtCtx G H.
Proof.
  introv res okg.
  lets: resolve_evar_ok_preservation res okg.
  induction res; auto.
  apply~ weak_extension_append.
  apply~ WExtCtx_Solve.
  apply~ weak_extension_append.
  apply~ WExtCtx_EVar.
  apply~ WExtCtx_Add.
  apply~ weak_extension_reflexicity.
  repeat apply ok_concat_inv_l in okg. auto.
  do 3 apply ok_concat_inv_l in okg. apply ok_push_inv in okg. destruct okg. auto.
  simpl_dom. apply notin_union. split~.
  do 3 apply ok_concat_inv_l in okg. apply ok_push_inv in okg. destruct okg. auto.
  do 1 apply ok_concat_inv_l in okg. auto.
  do 2 apply ok_concat_inv_l in H0. auto.
  do 1 apply ok_concat_inv_l in okg. apply ok_push_inv in okg. destruct okg. auto.
  do 1 apply ok_concat_inv_l in H0.  apply ok_push_inv in H0. destruct H0. auto.
  lets: resolve_evar_ok_preservation res okg.
  lets: IHres okg H4.
  pick_fresh y. assert (y \notin L) by auto.
  assert(ok (H1 & y ~ AC_Var)) by apply* ok_push.
  assert(ok (H & y ~ AC_Var)) by apply* ok_push.
  lets: H3 H6 H7 H8.
  apply weak_extension_remove_var in H9.
  lets: weak_extension_transitivity H5 H9. auto.

  lets: resolve_evar_ok_preservation res1 okg.
  lets: IHres1 okg H2.
  lets: resolve_evar_ok_preservation res2 H2.
  lets: IHres2 H2 H4.
  lets: weak_extension_transitivity H3 H5; auto.

  pick_fresh y. assert (y \notin L) by auto.
  lets: H1 H3; clear H1.
  assert (ok (G & y ~ AC_Var)) by apply~ ok_push.
  lets: resolve_evar_ok_preservation H4 H1.
  lets: H2 H3 H1 H5; clear H2.
  apply weak_extension_remove_var in H6; auto.

  lets: resolve_evar_ok_preservation res1 okg.
  lets: IHres1 okg H2.
  lets: resolve_evar_ok_preservation res2 H2.
  lets: IHres2 H2 H4.
  lets: weak_extension_transitivity H3 H5; auto.
Qed.

Lemma resolve_forall_wextctx: forall G a m s t H,
    AResolveForall G a m s t H ->
    ok G ->
    WExtCtx G H.
Proof.
  introv res okg.
  lets: resolve_forall_ok_preservation res okg.
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
  lets: resolve_forall_ok_preservation res1 okg.
  lets: IHres1 okg H2.
  lets: IHres2 H2 H0.
  lets: weak_extension_transitivity H3 H4. auto.

  (* PI2 *)
  lets: resolve_forall_ok_preservation res1 okg.
  lets: IHres1 okg H2.
  lets: IHres2 H2 H0.
  lets: weak_extension_transitivity H3 H4. auto.
Qed.

Lemma unify_wextctx: forall G s t H,
    AUnify G s t H ->
    ok G ->
    WExtCtx G H.
Proof.
  introv uni okg.
  lets: unify_ok_preservation uni okg.
  induction uni; auto.

  (* APP *)
  lets: unify_ok_preservation uni1 okg.
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
  assert(ok (G & y ~ AC_Var)). constructor~.
  lets: unify_ok_preservation uni okg.
  assert(ok (H1 & y ~ AC_Var)). constructor~.
  assert(ok (H & y ~ AC_Var)). constructor~.
  lets: H3 y H4 H7 H8.
  lets: weak_extension_remove_var H9.
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
  lets: unify_ok_preservation uni1 okg.
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

Lemma subtyping_wextctx: forall G s t H,
    ASubtyping G s t H ->
    ok G ->
    WExtCtx G H.
Proof.
  introv sub okg.
  lets: subtyping_ok_preservation sub okg.
  induction sub; auto.

  (* POLYR *)
  assert (ok (G & v ~ AC_TVar)) by constructor~.
  lets: subtyping_ok_preservation sub H2.
  lets: IHsub H2 H3.
  inversion H4;
  try(destruct (eq_push_inv H6) as [? [iv ?]]; inversion iv).
  false empty_push_inv H7.
  subst. auto.
  destruct (eq_push_inv H7) as [? [? ?]]. subst. auto.

  (* POLYL *)
  assert (ok (G & b ~ AC_Marker & a ~ AC_Unsolved_EVar)) by constructor~.
  lets: subtyping_ok_preservation sub H4.
  lets: IHsub H4 H5.
  apply weak_extension_order_marker in H6.
  destruct H6 as (S1 & S2 & [? [? ?]]).
  apply ok_middle_eq2 in H6; auto. destruct H6 as [? [? ?]].
  subst~.
  rewrite~ <- H6.

  (* PI *)
  lets: subtyping_ok_preservation sub1 okg.
  lets: IHsub1 okg H3. clear IHsub1.
  assert(ok (H1 & x ~ AC_Typ s1)) by constructor~.
  lets: subtyping_ok_preservation sub2 H5.
  lets: IHsub2 H5 H6. clear IHsub2.
  inversion H7;
  try(destruct (eq_push_inv H9) as [? [iv ?]]; inversion iv).
  false empty_push_inv H9.
  subst. auto.
  destruct (eq_push_inv H10) as [? [? ?]]. subst.
  lets: weak_extension_transitivity H4 H11. auto.

  (* EVarL *)
  lets: resolve_forall_wextctx H3 okg.
  lets: resolve_forall_ok_preservation H3 okg.
  lets: unify_wextctx H4 H6.
  lets: weak_extension_transitivity H5 H7.
  auto.

  (* EVarR *)
  lets: resolve_forall_wextctx H3 okg.
  lets: resolve_forall_ok_preservation H3 okg.
  lets: unify_wextctx H4 H6.
  lets: weak_extension_transitivity H5 H7.
  auto.

  (* UNIfy *)
  lets: unify_wextctx H1 okg. auto.
Qed.

Lemma atyping_wextctx: forall G m s t H,
    ATyping m G s t H ->
    WExtCtx G H.
Proof.
  introv ty.
  induction ty; auto.

  (* ANN *)
  lets: weak_extension_transitivity IHty1 IHty2. auto.

  (* PI *)
  assert(WExtCtx (H1 & x ~ AC_Typ t1 & empty) (H & x ~ AC_Typ t1 & I)) by rewrite~ concat_empty_r.
  apply weak_extension_order_typvar in H3.
  destruct H3 as (S1 & S2 & [hinfo [ex [sf ex2]]]).
  apply ok_middle_eq2 in hinfo; auto.
  destruct hinfo as [? [? ?]]. subst.
  lets: weak_extension_transitivity IHty1 ex. auto.
  lets: atyping_ok_preservation ty2; auto.
  rewrite <- hinfo. lets: atyping_ok_preservation ty2; auto.

  (* LAM *)
  assert(WExtCtx (G & a ~ AC_Unsolved_EVar & x ~ AC_Typ (AT_EVar a) & empty) (H & x ~ AC_Typ (AT_EVar a) & I)) by rewrite~ concat_empty_r.
  apply weak_extension_order_typvar in H3.
  destruct H3 as (S1 & S2 & [hinfo [ex [sf ex2]]]).
  apply ok_middle_eq2 in hinfo; auto.
  destruct hinfo as [? [? ?]]. subst.
  apply weak_extension_remove_evar in ex.
  apply~ weak_extension_append_soft.
  apply uv_is_soft.
  apply atyping_ok_preservation in ty. apply ok_concat_inv_r in ty. auto.
  apply~ uv_ok. apply atyping_ok_preservation in ty. apply ok_remove in ty. auto.
  apply* atyping_ok_preservation.
  rewrite <- hinfo. apply* atyping_ok_preservation.

  (* APP *)
  lets: weak_extension_transitivity IHty1 IHty2. auto.

  (* FORALL *)
  assert(WExtCtx (G & a ~ AC_TVar & empty) (H & a ~ AC_TVar & I)) by rewrite~ concat_empty_r.
  apply weak_extension_order_tvar in H2.
  destruct H2 as (S1 & S2 & [hinfo [ex [sf ex2]]]).
  apply ok_middle_eq2 in hinfo; auto.
  destruct hinfo as [? [? ?]]. subst.
  auto.
  lets: atyping_ok_preservation ty; auto.
  rewrite <- hinfo. lets: atyping_ok_preservation ty; auto.

  (* LAM CHECK *)
  assert(WExtCtx (G & x ~ AC_Typ s1 & empty) (H & x ~ AC_Typ s1 & I)) by rewrite~ concat_empty_r.
  apply weak_extension_order_typvar in H2.
  destruct H2 as (S1 & S2 & [hinfo [ex [sf ex2]]]).
  apply ok_middle_eq2 in hinfo; auto.
  destruct hinfo as [? [? ?]]. subst.
  auto.
  lets: atyping_ok_preservation ty; auto.
  rewrite <- hinfo. lets: atyping_ok_preservation ty; auto.

  (* SUB *)
  lets: atyping_ok_preservation ty.
  lets: subtyping_wextctx H0 H2.
  lets: weak_extension_transitivity IHty H3. auto.

  (* APP EVAR *)
  rewrite <- concat_assoc in IHty.
  apply weak_extension_remove_evar_middle in IHty.
  apply weak_extension_remove_evar_middle in IHty.
  rewrite concat_assoc in IHty.
  assert (WExtCtx (G1 & a ~ AC_Unsolved_EVar & G2) (G1 & a ~ AC_Solved_EVar (AT_Expr (AE_Pi (AT_EVar a1) (AT_EVar a2))) & G2)) by apply~ weak_extension_solve_middle.
  lets: weak_extension_transitivity H2 IHty.
  auto.

  (* APP FORALL *)
  apply* weak_extension_remove_evar.
Qed.

(***********************)
(* PROPERTIES ABOUT ALGORITHMIC RELATIONSHIPS *)
(***********************)

Lemma resolve_evar_evar_preservation2: forall G s t H a a0 n,
    AResolveEVar G a0 s t H ->
    ok G ->
    binds a (AC_Solved_EVar n) G ->
    binds a (AC_Solved_EVar n) H.
Proof.
  introv res okg bd.
  lets: resolve_evar_wextctx res okg.
  apply* weak_extension_binds_solved_evar.
Qed.

Lemma resolve_evar_evar_preservation: forall G s t H a a0,
    AResolveEVar G a0 s t H ->
    ok G ->
    binds a AC_Unsolved_EVar G ->
    binds a AC_Unsolved_EVar H \/ (exists n, binds a (AC_Solved_EVar n) H).
Proof.
  introv res okg bd.
  lets: resolve_evar_wextctx res okg.
  apply* weak_extension_binds_unsolved_evar.
Qed.

Lemma resolve_forall_evar_preservation2: forall G s t H a a0 n m,
    AResolveForall G a0 m s t H ->
    ok G ->
    binds a (AC_Solved_EVar n) G ->
    binds a (AC_Solved_EVar n) H.
Proof.
  introv res okg bd.
  lets: resolve_forall_wextctx res okg.
  apply* weak_extension_binds_solved_evar.
Qed.

Lemma resolve_forall_evar_preservation: forall G s t H a m a0 ,
    AResolveForall G a0 m s t H ->
    ok G ->
    binds a AC_Unsolved_EVar G ->
    binds a AC_Unsolved_EVar H \/ (exists n, binds a (AC_Solved_EVar n) H).
Proof.
  introv res okg bd.
  lets: resolve_forall_wextctx res okg.
  apply* weak_extension_binds_unsolved_evar.
Qed.

Lemma unify_evar_preservation2: forall G s t H n a,
    AUnify G s t H ->
    ok G ->
    binds a (AC_Solved_EVar n) G ->
    binds a (AC_Solved_EVar n) H.
Proof.
  introv uni okg bd.
  lets: unify_wextctx uni okg.
  apply* weak_extension_binds_solved_evar.
Qed.

Lemma unify_evar_preservation: forall G s t H a,
    AUnify G s t H ->
    ok G ->
    binds a AC_Unsolved_EVar G ->
    binds a AC_Unsolved_EVar H \/ (exists n, binds a (AC_Solved_EVar n) H).
Proof.
  introv uni okg bd.
  lets: unify_wextctx uni okg.
  apply* weak_extension_binds_unsolved_evar.
Qed.

Lemma subtyping_evar_preservation2: forall G s t H a n,
    ASubtyping G s t H ->
    ok G ->
    binds a (AC_Solved_EVar n) G ->
    binds a (AC_Solved_EVar n) H.
Proof.
  introv sub okg bd.
  lets: subtyping_wextctx sub okg.
  apply* weak_extension_binds_solved_evar.
Qed.

Lemma subtyping_evar_preservation: forall G s t H a,
    ASubtyping G s t H ->
    ok G ->
    binds a AC_Unsolved_EVar G ->
    binds a AC_Unsolved_EVar H \/ (exists n, binds a (AC_Solved_EVar n) H).
Proof.
  introv sub okg bd.
  lets: subtyping_wextctx sub okg.
  apply* weak_extension_binds_unsolved_evar.
Qed.

Lemma atyping_evar_preservation2: forall G s t H a m n,
    ATyping m G s t H ->
    binds a (AC_Solved_EVar n) G ->
    binds a (AC_Solved_EVar n) H.
Proof.
  introv ty bd.
  lets: atyping_wextctx ty.
  apply* weak_extension_binds_solved_evar.
Qed.

Lemma atyping_evar_preservation: forall G s t H a m,
    ATyping m G s t H ->
    binds a AC_Unsolved_EVar G ->
    binds a AC_Unsolved_EVar H \/ (exists n, binds a (AC_Solved_EVar n) H).
Proof.
  introv ty bd.
  lets: atyping_wextctx ty.
  apply* weak_extension_binds_unsolved_evar.
Qed.

(***********************)
(* PROPERTIES ABOUT ALGORITHMIC RELATIONSHIPS *)
(***********************)

Lemma resolve_evar_inserts: forall G1 G2 a e t H,
    AResolveEVar (G1 & a ~ AC_Unsolved_EVar & G2) a e t H ->
    ok (G1 & a ~ AC_Unsolved_EVar & G2) ->
    exists I1 I2, H = G1 & I1 & a ~ AC_Unsolved_EVar & I2.
Proof.
  introv res okg. gen_eq S: (G1 & a ~ AC_Unsolved_EVar & G2).
  gen G1 G2.
  induction res; introv sinfo; try(solve[exists~ (empty: ACtx) G2; rewrite~ concat_empty_r]).

  apply ok_middle_eq2 in sinfo; auto.
  destruct sinfo as[? [? ?]]; subst.
  exists~ (empty: ACtx) G4. rewrite~ concat_empty_r.
  rewrite~ <- sinfo.

  do 2 rewrite <- concat_assoc in sinfo.
  apply ok_middle_eq2 in sinfo; auto.
  destruct sinfo as[? [? ?]]; subst.
  exists~ (a1 ~ AC_Unsolved_EVar) (G2 & b ~ AC_Solved_EVar (AT_EVar a1) & G3).
  repeat rewrite~ concat_assoc.

  do 2 rewrite~ concat_assoc.
  rewrite <- sinfo.
  do 2 rewrite~ concat_assoc.

  lets: IHres okg sinfo.
  destruct H3 as (I1 & I2 & h1info). subst. clear IHres.
  lets: resolve_evar_ok_preservation res okg.
  pick_fresh y. assert(y \notin L) by auto.
  assert(ok (G1 & I1 & a ~ AC_Unsolved_EVar & I2 & y ~ AC_Var)) by apply* ok_push.
  assert(G1 & I1 & a ~ AC_Unsolved_EVar & I2 & y ~ AC_Var =
         (G1 & I1) & a ~ AC_Unsolved_EVar & (I2 & y ~ AC_Var)) by repeat rewrite~ concat_assoc.
  forwards*: H2 H3 H4 H5.
  destruct H6 as (I3 & I4 & ?).
  assert(y <> a). apply ok_push_inv in H4. destruct H4. simpl_dom. auto_star.
  assert(hinfo:=H6).
  apply tail_exists_eq in H6; auto.
  destruct H6 as (I5 & ?). subst.
  repeat rewrite concat_assoc in hinfo.
  destruct (eq_push_inv hinfo) as [? [? ?]]. subst.
  exists~ (I1 & I3) I5. repeat rewrite ~ concat_assoc.

  lets: IHres1 okg sinfo. clear IHres1.
  destruct H0 as (I1 & I2 & hinfo). subst.
  lets: resolve_evar_ok_preservation res1 okg.
  forwards * : IHres2 H0.
  destruct H1 as (I3 & I4 & hinfo2); subst.
  exists~ (I1 & I3) I4. repeat rewrite~ concat_assoc.

  pick_fresh y.
  assert(y \notin L) by auto.
  lets: H0 H2; clear H0.
  assert(ok (G & y ~ AC_Var)) by apply~ ok_push. subst.
  assert(G1 & a ~ AC_Unsolved_EVar & G2 & y ~ AC_Var = G1 & a ~ AC_Unsolved_EVar & (G2 & y ~ AC_Var)) by repeat rewrite~ concat_assoc.
  lets: H1 H2 H0 H4.
  destruct H5 as (I1 & I2 & hinfo); subst.
  assert(y <> a). apply ok_push_inv in H0. destruct H0. simpl_dom. auto_star.
  assert(H6:=hinfo).
  apply tail_exists_eq in H6; auto.
  destruct H6 as (I5 & ?). subst.
  repeat rewrite concat_assoc in hinfo.
  destruct (eq_push_inv hinfo) as [? [? ?]]. subst.
  exists~ I1 I5.

  lets: IHres1 okg sinfo. clear IHres1.
  destruct H0 as (I1 & I2 & hinfo). subst.
  lets: resolve_evar_ok_preservation res1 okg.
  forwards * : IHres2 H0.
  destruct H1 as (I3 & I4 & hinfo2); subst.
  exists~ (I1 & I3) I4. repeat rewrite~ concat_assoc.
Qed.

Lemma resolve_evar_unsolved: forall G a e t H,
    AResolveEVar G a e t H ->
    ok G ->
    (forall a, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H) ->
    H = G.
Proof.
  introv res okg hy.
  lets: resolve_evar_ok_preservation res okg.
  induction res; auto; auto.
  assert (binds b AC_Unsolved_EVar (G1 & a ~ AC_Unsolved_EVar & G2 & b ~ AC_Unsolved_EVar & G3)).
  apply~ binds_middle_eq.
  apply ok_middle_inv_r in H0. auto.
  lets: hy H1. clear hy H1.
  lets: binds_middle_eq_inv H2 H0.
  inversion H1.

  assert (forall a : var, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H1).
  intros n bdn.
  lets: resolve_evar_evar_preservation res okg bdn.
  destruct H4 as [? | (? & ?)]; auto.
  lets: hy bdn.
  pick_fresh y.
  assert (y \notin L) by auto.
  lets: H2 H6.
  lets: resolve_evar_ok_preservation res okg.
  assert(ok (H1 & y ~ AC_Var)) by apply* ok_push.
  assert(binds n (AC_Solved_EVar x) (H1 & y ~ AC_Var)). apply* binds_push_neq.
  lets: resolve_evar_evar_preservation2 H7 H9 H10.
  apply binds_push_neq_inv in H11.
  false binds_func H5 H11. auto_star.

  lets: resolve_evar_ok_preservation res okg.
  lets: IHres okg H4 H5. subst.

  pick_fresh y.
  assert(y \notin L) by auto.
  assert(ok (G & y ~ AC_Var)) by apply* ok_push.
  assert(forall a : var,
        binds a AC_Unsolved_EVar (G & y ~ AC_Var) ->
        binds a AC_Unsolved_EVar (H & y ~ AC_Var)).
  intros n bdn.
  assert(n <> y). intros neq. subst. apply binds_push_eq_inv in bdn. false bdn.
  apply binds_push_neq_inv in bdn; auto.
  assert(ok (H & y ~ AC_Var)) by apply* ok_push.
  lets: H3 H1 H6 H7 H8.
  destruct (eq_push_inv H9) as [? [? ?]]. auto.

  assert(forall a : var,
            binds a AC_Unsolved_EVar G ->
            binds a AC_Unsolved_EVar H1).
  intros n bdn.
  lets: resolve_evar_evar_preservation res1 okg bdn.
  destruct H2 as [? | (? & ?)]; auto.
  lets: hy bdn.
  lets: resolve_evar_ok_preservation res1 okg.
  lets: resolve_evar_evar_preservation2 res2 H4 H2.
  false binds_func H5 H3.

  lets: resolve_evar_ok_preservation res1 okg.
  lets: IHres1 okg H2 H3. subst. clear H3 IHres1 H2.
  lets: IHres2 okg hy H0. subst~.

  pick_fresh y.
  assert(y \notin L) by auto.
  assert(ok (G & y ~ AC_Var)) by apply* ok_push.
  assert(forall a : var,
        binds a AC_Unsolved_EVar (G & y ~ AC_Var) ->
        binds a AC_Unsolved_EVar (H & y ~ AC_Var)).
  intros n bdn.
  assert(n <> y). intros neq. subst. apply binds_push_eq_inv in bdn. false bdn.
  apply binds_push_neq_inv in bdn; auto.
  assert(ok (H & y ~ AC_Var)) by apply* ok_push.
  lets: H2 H3 H4 H5 H6.
  destruct (eq_push_inv H7) as [? [? ?]]. auto.

  assert(forall a : var,
            binds a AC_Unsolved_EVar G ->
            binds a AC_Unsolved_EVar H1).
  intros n bdn.
  lets: resolve_evar_evar_preservation res1 okg bdn.
  destruct H2 as [? | (? & ?)]; auto.
  lets: hy bdn.
  lets: resolve_evar_ok_preservation res1 okg.
  lets: resolve_evar_evar_preservation2 res2 H4 H2.
  false binds_func H5 H3.

  lets: resolve_evar_ok_preservation res1 okg.
  lets: IHres1 okg H2 H3. subst. clear H3 IHres1 H2.
  lets: IHres2 okg hy H0. subst~.
Qed.

Lemma resolve_forall_inserts: forall G1 G2 a m e t H,
    AResolveForall (G1 & a ~ AC_Unsolved_EVar & G2) a m e t H ->
    ok (G1 & a ~ AC_Unsolved_EVar & G2) ->
    exists I, H = G1 & I & a ~ AC_Unsolved_EVar & G2.
Proof.
  introv res okg. gen_eq S: (G1 & a ~ AC_Unsolved_EVar & G2). gen G1.
  induction res; introv sinfo; subst; try(solve[exists~ empty]).

  apply ok_middle_eq2 in sinfo; auto.
  destruct sinfo as [? [? ?]]. subst.
  assert(ok (G3 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & G2)).
  rewrite <- concat_assoc. apply ok_insert; auto. rewrite~ concat_assoc.
  forwards*: IHres H1. destruct H3 as (I & hinfo).
  exists~ (a1 ~ AC_Unsolved_EVar & I). repeat rewrite~ concat_assoc.
  rewrite~ <- sinfo.

  forwards*: IHres1 okg.
  destruct H0 as (I1 & h1info).
  lets: resolve_forall_ok_preservation res1 okg.
  lets: IHres2 H0 h1info.
  destruct H2 as (I2 & ?).
  exists~ (I1 & I2). repeat rewrite~ concat_assoc.

  forwards*: IHres1 okg.
  destruct H0 as (I1 & h1info).
  lets: resolve_forall_ok_preservation res1 okg.
  lets: IHres2 H0 h1info.
  destruct H2 as (I2 & ?).
  exists~ (I1 & I2). repeat rewrite~ concat_assoc.

  exists~ (empty: ACtx).
  rewrite~ concat_empty_r.
Qed.

Lemma resolve_forall_unsolved: forall G a0 m e t H,
    AResolveForall G a0 m e t H ->
    ok G ->
    forall a, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H.
Proof.
  introv res okg bd.
  induction res; auto.

  assert(ok (G1 & a1 ~ AC_Unsolved_EVar & a0 ~ AC_Unsolved_EVar & G2)).
  rewrite <- concat_assoc. apply ok_insert; auto. rewrite~ concat_assoc.
  assert(binds a AC_Unsolved_EVar
               (G1 & a1 ~ AC_Unsolved_EVar & a0 ~ AC_Unsolved_EVar & G2)).
  destruct (eq_var_dec a1 a).
  subst. false binds_fresh_inv bd H0.
  rewrite <- concat_assoc. apply~ binds_weaken. rewrite~ concat_assoc.
  rewrite~ concat_assoc.
  lets: IHres H1 H2. auto.

  lets: resolve_forall_ok_preservation res1 okg.
  lets: IHres1 okg bd.
  lets: IHres2 H0 H2. auto.

  lets: resolve_forall_ok_preservation res1 okg.
  lets: IHres1 okg bd.
  lets: IHres2 H0 H2. auto.
Qed.

Lemma unify_inserts: forall G1 G2 a s H,
    AUnify (G1 & a ~ AC_Unsolved_EVar & G2) (AT_EVar a) s H ->
    ok (G1 & a ~ AC_Unsolved_EVar & G2) ->
    (exists I1 I2 t,  H = G1 & I1 & a ~ AC_Solved_EVar t & I2)
      \/ (H = (G1 & a ~ AC_Unsolved_EVar & G2) /\ s = AT_EVar a).
Proof.
  introv uni okg. gen_eq S: (G1 & a ~ AC_Unsolved_EVar & G2).
  gen_eq expr: (AT_EVar a). gen G1.

  induction uni; introv einfo sinfo; auto; try(solve[false einfo]).

  subst. inversion einfo; subst.
  lets: resolve_evar_inserts H0 okg.
  destruct H4 as (I1 & I2 & ?). subst.
  apply ok_middle_eq2 in H4; auto. destruct H4 as [? [? ?]]. subst.
  left. exists~ I1 I2 t2.
  lets: resolve_evar_ok_preservation H0 okg; auto.
  rewrite <- H4. lets: resolve_evar_ok_preservation H0 okg; auto.
Qed.

Lemma unify_unsolved: forall G e t H,
    AUnify G e t H ->
    ok G ->
    (forall a, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H) ->
    H = G.
Proof.
  introv uni okg hy.
  induction uni; auto.

  (* APP *)
  assert (forall a : var, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H1).
  intros n bdn.
  lets: unify_evar_preservation uni1 okg bdn.
  destruct H0 as [? | (? & ?)]; auto.
  lets: hy bdn.
  lets: unify_ok_preservation uni1 okg.
  lets: unify_evar_preservation2 uni2 H3 H0.
  false binds_func H2 H4.

  lets: IHuni1 okg H0. subst.
  lets: IHuni2 okg hy. auto.

  (* LAM *)
  pick_fresh y.
  assert(y \notin L) by auto.
  lets: H0 H2. clear H0.
  assert (ok (G & y ~ AC_Var)) by constructor~.
  lets: H1 H2 H0. clear H1 H0.
  assert (forall a : var, binds a AC_Unsolved_EVar (G & y ~ AC_Var) -> binds a AC_Unsolved_EVar (H & y ~ AC_Var)).
  intros n bdn.
  apply binds_push_inv in bdn. destruct bdn as [ [? ?] | [? ?]]. false H1.
  lets: hy H1.
  apply~ binds_push_neq.
  lets: H4 H0. destruct (eq_push_inv H1) as [? [? ?]]. subst. auto.

  (* PI *)
  assert (forall a : var, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H1).
  intros n bdn.
  lets: unify_evar_preservation uni okg bdn.
  destruct H3 as [? | (? & ?)]; auto.
  pick_fresh y.
  assert(y \notin L) by auto.
  lets: H0 H4. clear H0.
  assert (binds n (AC_Solved_EVar x) (H1 & y ~ AC_Var)) by apply~ binds_push_neq.
  lets: unify_ok_preservation uni okg.
  assert (ok (H1 & y ~ AC_Var)) by constructor~.
  lets: unify_evar_preservation2 H5 H7 H0.
  apply binds_push_neq_inv in H8; auto.
  lets: hy bdn. false binds_func H8 H9.

  pick_fresh y.
  assert(y \notin L) by auto.
  lets: H0 H4. clear H0.
  lets: IHuni okg H3. subst.
  assert (ok (G & y ~ AC_Var)) by constructor~.
  lets: H2 H4 H0. clear H2.
  assert(forall a : var,
        binds a AC_Unsolved_EVar (G & y ~ AC_Var) ->
        binds a AC_Unsolved_EVar (H & y ~ AC_Var)).
  intros n bdn.
  apply~ binds_push_neq.
  apply binds_push_neq_inv in bdn.
  lets: hy bdn; auto.
  introv neq. subst. false binds_push_eq_inv bdn.
  introv neq. subst. false binds_push_eq_inv bdn.

  lets: H1 H2.
  apply eq_push_inv in H6. destruct H6 as [? [? ?]]. subst~.

  (* FORALL *)
  pick_fresh y.
  assert(y \notin L) by auto.
  lets: H0 H2. clear H0.
  assert (ok (G & y ~ AC_TVar)) by constructor~.
  lets: H1 H2 H0. clear H1 H0.
  assert (forall a : var, binds a AC_Unsolved_EVar (G & y ~ AC_TVar) -> binds a AC_Unsolved_EVar (H & y ~ AC_TVar)).
  intros n bdn.
  apply binds_push_inv in bdn. destruct bdn as [ [? ?] | [? ?]]. false H1.
  lets: hy H1.
  apply~ binds_push_neq.
  lets: H4 H0. destruct (eq_push_inv H1) as [? [? ?]]. subst. auto.

  (* ANN *)
  assert (forall a : var, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H1).
  intros n bdn.
  lets: unify_evar_preservation uni1 okg bdn.
  destruct H0 as [? | (? & ?)]; auto.
  lets: hy bdn.
  lets: unify_ok_preservation uni1 okg.
  lets: unify_evar_preservation2 uni2 H3 H0.
  false binds_func H2 H4.

  lets: IHuni1 okg H0. subst.
  lets: IHuni2 okg hy. auto.

  (* EVARL *)
  lets: resolve_evar_ok_preservation H0 okg.
  assert ( forall a0 : var,
       binds a0 AC_Unsolved_EVar G -> binds a0 AC_Unsolved_EVar (H1 & a ~ AC_Unsolved_EVar & H2)).
  intros n bdn.
  lets: hy bdn.
  assert (a <> n). introv neq. subst. apply binds_middle_eq_inv in H5. false H5.
  apply* ok_middle_change.
  apply binds_remove in H5; auto.
  apply~ binds_weaken.
  lets: resolve_evar_unsolved H0 okg H5.
  assert (binds a AC_Unsolved_EVar G). rewrite <- H6. apply binds_middle_eq. apply* ok_middle_inv_r.
  lets: hy H7.
  apply binds_middle_eq_inv in H8; auto. false H8.
  apply* ok_middle_change.

  (* EVARR *)
  lets: resolve_evar_ok_preservation H3 okg.
  assert ( forall a0 : var,
       binds a0 AC_Unsolved_EVar G -> binds a0 AC_Unsolved_EVar (H1 & a ~ AC_Unsolved_EVar & H2)).
  intros n bdn.
  lets: hy bdn.
  assert (a <> n). introv neq. subst. apply binds_middle_eq_inv in H6. false H6.
  apply* ok_middle_change.
  apply binds_remove in H6; auto.
  apply~ binds_weaken.
  lets: resolve_evar_unsolved H3 okg H6.
  assert (binds a AC_Unsolved_EVar G). rewrite <- H7. apply binds_middle_eq. apply* ok_middle_inv_r.
  lets: hy H8.
  apply binds_middle_eq_inv in H9; auto. false H9.
  apply* ok_middle_change.
Qed.

Lemma resolve_evar_helper: forall G H1 H2 a t1 t2,
    AResolveEVar G a t1 t2 (H1 & a ~ AC_Unsolved_EVar & H2) ->
    ok G ->
    binds a AC_Unsolved_EVar G.
Proof.
  introv res okg. gen_eq S: (H1 & a ~ AC_Unsolved_EVar & H2). gen H1 H2.
  induction res; introv sinfo; subst; auto.
  apply binds_middle_eq. apply ok_middle_inv_r in okg; auto.
  do 2  rewrite <- concat_assoc in *.
  apply binds_middle_eq. apply ok_middle_inv_r in okg; auto.
  pick_fresh y.
  assert( y \notin L) by auto.
  assert(ok (H1 & y ~ AC_Var)).
  lets: resolve_evar_ok_preservation res okg. apply~ ok_push.
  assert (H3 & a ~ AC_Unsolved_EVar & H4 & y ~ AC_Var
        = H3 & a ~ AC_Unsolved_EVar & (H4 & y ~ AC_Var)) by repeat rewrite~ concat_assoc.
  lets: H2 H H5 H6.
  apply binds_push_neq_inv in H7; auto.
  apply split_bind_context in H7.
  destruct H7 as (I1 & I2 & h1info); subst.
  forwards * : IHres.

  apply binds_middle_eq. apply ok_middle_inv_r in okg; auto.
  apply binds_middle_eq. apply ok_middle_inv_r in okg; auto.
  apply binds_middle_eq. apply ok_middle_inv_r in okg; auto.
  apply binds_middle_eq. apply ok_middle_inv_r in okg; auto.

  lets: resolve_evar_ok_preservation res1 okg.
  forwards * : IHres2.
  apply split_bind_context in H3.
  destruct H3 as (I1 & I2 & h1info); subst.
  forwards * : IHres1.

  pick_fresh y. assert (y \notin L) by auto.
  assert (ok (G & y ~ AC_Var)) by apply~ ok_push.
  assert (H2 & a ~ AC_Unsolved_EVar & H3 & y ~ AC_Var =
          H2 & a ~ AC_Unsolved_EVar & (H3 & y ~ AC_Var)) by repeat rewrite~ concat_assoc.
  lets: H1 H H4 H5.
  apply binds_push_neq_inv in H6; auto.

  apply binds_middle_eq. apply ok_middle_inv_r in okg; auto.
  apply binds_middle_eq. apply ok_middle_inv_r in okg; auto.

  lets: resolve_evar_ok_preservation res1 okg.
  forwards * : IHres2.
  apply split_bind_context in H3.
  destruct H3 as (I1 & I2 & h1info); subst.
  forwards * : IHres1.
Qed.

Lemma unify_unsolved_helper: forall I1 I2 e t H,
    AUnify (I1 & I2) e t H ->
    ok (I1 & I2) ->
    (forall a, binds a AC_Unsolved_EVar I1 -> binds a AC_Unsolved_EVar H) ->
    exists H2, H = I1 & H2.
Proof.
  introv uni okg hy; gen_eq S :(I1 & I2). gen I2.
  induction uni; introv sinfo; subst; try(solve[exists~ I2]).

  (* *)
  assert ((forall a : var,
            binds a AC_Unsolved_EVar I1 ->
            binds a AC_Unsolved_EVar H1)).
  intros n bdn.
  assert(binds n AC_Unsolved_EVar (I1 & I2)). apply~ binds_concat_left_ok.
  lets: unify_evar_preservation uni1 okg H0.
  destruct H2 as [bd_un | (nv & bd_so)]; auto.
  lets: unify_ok_preservation uni1 okg.
  lets: unify_evar_preservation2 uni2 H2 bd_so.
  lets: hy bdn. false binds_func H3 H4.

  lets: IHuni1 okg H0. clear IHuni1.
  forwards * : H2. clear H2.
  destruct H3 as (I3 & h1info). subst.
  lets: unify_ok_preservation uni1 okg; auto.
  lets: IHuni2 H1 hy.
  forwards * :  H2.

  (* LAM *)
  pick_fresh y.
  assert (y \notin L) by auto.
  assert(ok (I1 & I2 & y ~ AC_Var)). apply~ ok_push.
  assert(forall a : var,
            binds a AC_Unsolved_EVar I1 ->
            binds a AC_Unsolved_EVar (H & y ~ AC_Var)).
  intros n bdn.
  lets: hy bdn.
  apply~ binds_push_neq.
  introv neq. subst. assert(y # I1) by auto. false binds_fresh_inv bdn H5.
  lets: H1 H2 H3 H4.
  assert(I1 & I2 & y ~ AC_Var = I1 & (I2 & y ~ AC_Var)) by repeat rewrite~ concat_assoc.
  lets: H5 H6.
  destruct H7 as (I4 & hinfo).
  clear H1.

  assert(binds y (AC_Var) I4). apply binds_concat_right_inv with I1; auto. rewrite <- hinfo. apply binds_push_eq.
  apply split_bind_context in H1.
  destruct H1 as (I5 & I6 & i3info). subst.
  repeat rewrite concat_assoc in hinfo.
  symmetry in hinfo.
  apply tail_empty_eq2 in hinfo; auto.
  destruct hinfo as [? [? ?]]. subst.
  exists~ I5.
  lets: H0  H2.
  rewrite hinfo. lets: unify_ok_preservation H1 H3; auto.
  lets: H0  H2.
  lets: unify_ok_preservation H1 H3; auto.

  (* *)
  forwards * : IHuni okg hy.
  (* *)
  forwards * : IHuni okg hy.

  (* PI *)
  pick_fresh y. assert(y \notin L) by auto.
  assert ((forall a : var,
            binds a AC_Unsolved_EVar I1 ->
            binds a AC_Unsolved_EVar H1)).
  intros n bdn.
  assert(binds n AC_Unsolved_EVar (I1 & I2)). apply~ binds_concat_left_ok.
  lets: unify_evar_preservation uni okg H4.
  destruct H5 as [bd_un | (nv & bd_so)]; auto.
  assert (n <> y). introv neq. subst.
  assert (y # H1) by auto. false binds_fresh_inv bd_so H5.
  assert(binds n (AC_Solved_EVar nv) (H1 & y ~ AC_Var)). apply~ binds_push_neq.
  lets: unify_ok_preservation uni okg.
  assert(ok (H1 & y ~ AC_Var)) by apply~ ok_push.
  lets: H0 H3. clear H0.
  lets: unify_evar_preservation2 H9 H8 H6.
  apply binds_push_neq_inv in H0; auto.
  lets: hy bdn. false binds_func H0 H10.

  lets: IHuni okg H4. clear IHuni.
  forwards * : H5. clear H5.
  destruct H6 as (I3 & h1info). subst.
  assert(forall a : var,
            binds a AC_Unsolved_EVar I1 ->
            binds a AC_Unsolved_EVar (H & y ~ AC_Var)).
  intros n bdn.
  lets: hy bdn.
  apply~ binds_push_neq.
  introv neq. subst. assert(y # I1) by auto. false binds_fresh_inv bdn H5.
  assert(ok (I1 & I3 & y ~ AC_Var)). apply~ ok_push.
  lets: unify_ok_preservation uni okg; auto.
  lets: H2 H3 H5 H1.
  assert(I1 & I3 & y ~ AC_Var = I1 & (I3 & y ~ AC_Var)) by repeat rewrite~ concat_assoc.
  lets: H6 H7.
  destruct H8 as (I4 & hinfo).
  clear H2.

  assert(binds y (AC_Var) I4). apply binds_concat_right_inv with I1; auto. rewrite <- hinfo. apply binds_push_eq.
  apply split_bind_context in H2.
  destruct H2 as (I5 & I6 & i3info). subst.
  repeat rewrite concat_assoc in hinfo.
  symmetry in hinfo.
  apply tail_empty_eq2 in hinfo; auto.
  destruct hinfo as [? [? ?]]. subst.
  exists~ I5.
  lets: H0 H3.
  rewrite hinfo. lets: unify_ok_preservation H2 H5; auto.
  lets: H0 H3.
  lets: unify_ok_preservation H2 H5; auto.

  (* FORALL *)
  pick_fresh y.
  assert (y \notin L) by auto.
  assert(ok (I1 & I2 & y ~ AC_TVar)). apply~ ok_push.
  assert(forall a : var,
            binds a AC_Unsolved_EVar I1 ->
            binds a AC_Unsolved_EVar (H & y ~ AC_TVar)).
  intros n bdn.
  lets: hy bdn.
  apply~ binds_push_neq.
  introv neq. subst. assert(y # I1) by auto. false binds_fresh_inv bdn H5.
  lets: H1 H2 H3 H4.
  assert(I1 & I2 & y ~ AC_TVar = I1 & (I2 & y ~ AC_TVar)) by repeat rewrite~ concat_assoc.
  lets: H5 H6.
  destruct H7 as (I4 & hinfo).
  clear H1.

  assert(binds y (AC_TVar) I4). apply binds_concat_right_inv with I1; auto. rewrite <- hinfo. apply binds_push_eq.
  apply split_bind_context in H1.
  destruct H1 as (I5 & I6 & i3info). subst.
  repeat rewrite concat_assoc in hinfo.
  symmetry in hinfo.
  apply tail_empty_eq2 in hinfo; auto.
  destruct hinfo as [? [? ?]]. subst.
  exists~ I5.
  lets: H0  H2.
  rewrite hinfo. lets: unify_ok_preservation H1 H3; auto.
  lets: H0  H2.
  lets: unify_ok_preservation H1 H3; auto.

  (* *)
  assert ((forall a : var,
            binds a AC_Unsolved_EVar I1 ->
            binds a AC_Unsolved_EVar H1)).
  intros n bdn.
  assert(binds n AC_Unsolved_EVar (I1 & I2)). apply~ binds_concat_left_ok.
  lets: unify_evar_preservation uni1 okg H0.
  destruct H2 as [bd_un | (nv & bd_so)]; auto.
  lets: unify_ok_preservation uni1 okg.
  lets: unify_evar_preservation2 uni2 H2 bd_so.
  lets: hy bdn. false binds_func H3 H4.

  lets: IHuni1 okg H0. clear IHuni1.
  forwards * : H2. clear H2.
  destruct H3 as (I3 & h1info). subst.
  lets: unify_ok_preservation uni1 okg; auto.
  lets: IHuni2 H1 hy.
  forwards * :  H2.

  (* *)
  lets: resolve_evar_helper H0 okg.
  apply binds_concat_inv in H4.
  destruct H4 as [bd_i2 | [notin bdi1]].
  apply split_bind_context in bd_i2.
  destruct bd_i2 as (S1 & S2 & i2info). subst.
  repeat rewrite concat_assoc in *.
  lets: resolve_evar_inserts H0 okg.
  destruct H4 as (S3 & S4 & hinfo).
  apply ok_middle_eq2 in hinfo; auto.
  destruct hinfo as [? [? ?]]. subst.
  exists~ (S1 & S3 & a ~ AC_Solved_EVar t2 & S4).
  repeat rewrite~ concat_assoc.
  lets: resolve_evar_ok_preservation H0 okg; auto.
  rewrite <- hinfo.
  lets: resolve_evar_ok_preservation H0 okg; auto.

  lets: hy bdi1.
  apply binds_middle_eq_inv in H4. false H4.
  lets: resolve_evar_ok_preservation H0 okg; auto.
  apply* ok_middle_change.

  (* *)
  lets: resolve_evar_helper H3 okg.
  apply binds_concat_inv in H5.
  destruct H5 as [bd_i2 | [notin bdi1]].
  apply split_bind_context in bd_i2.
  destruct bd_i2 as (S1 & S2 & i2info). subst.
  repeat rewrite concat_assoc in *.
  lets: resolve_evar_inserts H3 okg.
  destruct H5 as (S3 & S4 & hinfo).
  apply ok_middle_eq2 in hinfo; auto.
  destruct hinfo as [? [? ?]]. subst.
  exists~ (S1 & S3 & a ~ AC_Solved_EVar t2 & S4).
  repeat rewrite~ concat_assoc.
  lets: resolve_evar_ok_preservation H3 okg; auto.
  rewrite <- hinfo.
  lets: resolve_evar_ok_preservation H3 okg; auto.

  lets: hy bdi1.
  apply binds_middle_eq_inv in H5. false H5.
  lets: resolve_evar_ok_preservation H3 okg; auto.
  apply* ok_middle_change.
Qed.

Lemma subtyping_unsolved_helper: forall I1 I2 e t H,
    ASubtyping (I1 & I2) e t H ->
    ok (I1 & I2) ->
    (forall a, binds a AC_Unsolved_EVar I1 -> binds a AC_Unsolved_EVar H) ->
    exists H2, H = I1 & H2.
Proof.
  introv sub okg hy; gen_eq S :(I1 & I2). gen I2.
  induction sub; introv sinfo; subst.

  (* POLYR *)
  assert(ok (I1 & I2 & v ~ AC_TVar)) by apply~ ok_push.
  assert(forall a : var,
           binds a AC_Unsolved_EVar I1 ->
           binds a AC_Unsolved_EVar (H & v ~ AC_TVar)).
  intros n bdn.
  apply binds_push_neq. lets: hy bdn; auto.
  introv neq. subst. assert(v # I1) by auto. false binds_fresh_inv bdn H2.
  assert(I1 & I2 & v ~ AC_TVar = I1 & (I2 & v ~ AC_TVar)) by rewrite~ concat_assoc.
  lets: IHsub H1 H2 H3.

  destruct H4 as (I3 & hinfo).
  assert(binds v AC_TVar I3). apply binds_concat_right_inv with I1; auto. rewrite <- hinfo. apply binds_push_eq.
  apply split_bind_context in H4.
  destruct H4 as (I4 & I5 & i3info). subst.
  repeat rewrite concat_assoc in hinfo.
  symmetry in hinfo.
  apply tail_empty_eq2 in hinfo; auto.
  destruct hinfo as [? [? ?]]. subst.
  exists~ I4.
  rewrite hinfo. lets: subtyping_ok_preservation sub H1; auto.
  lets: subtyping_ok_preservation sub H1; auto.

  (* POLYL *)
  assert (ok (I1 & I2 & b ~ AC_Marker & a ~ AC_Unsolved_EVar)). apply~ ok_push.
  assert (forall a : var,
           binds a AC_Unsolved_EVar I1 ->
           binds a AC_Unsolved_EVar (H & b ~ AC_Marker & I)).
  intros n bdn. lets: hy bdn.
  rewrite <- concat_assoc. apply~ binds_concat_left_ok.
  rewrite concat_assoc. lets: subtyping_ok_preservation sub H3; auto.
  assert (I1 & I2 & b ~ AC_Marker & a ~ AC_Unsolved_EVar =
          I1 & (I2 & b ~ AC_Marker & a ~ AC_Unsolved_EVar)) by repeat rewrite~ concat_assoc.
  lets: IHsub H3 H4 H5.
  destruct H6 as (I3 & hinfo).

  assert(binds b AC_Marker I3). apply binds_concat_right_inv with I1; auto. rewrite <- hinfo. apply binds_middle_eq. lets: subtyping_ok_preservation sub H3. apply ok_middle_inv_r in H6; auto.
  apply split_bind_context in H6.
  destruct H6 as (I4 & I5 & i3info). subst.
  repeat rewrite concat_assoc in hinfo.
  apply ok_middle_eq2 in hinfo; auto.
  destruct hinfo as [? [? ?]]. subst.
  exists~ I4.
  lets: subtyping_ok_preservation sub H3; auto.
  rewrite <- hinfo. lets: subtyping_ok_preservation sub H3; auto.

  (* PI *)
  assert ((forall a : var,
            binds a AC_Unsolved_EVar I1 ->
            binds a AC_Unsolved_EVar H1)).
  intros n bdn.
  assert(binds n AC_Unsolved_EVar (I1 & I2)). apply~ binds_concat_left_ok.
  lets: subtyping_evar_preservation sub1 okg H2.
  destruct H3 as [bd_un | (nv & bd_so)]; auto.
  assert (n <> x). introv neq. subst.
  false binds_fresh_inv bd_so H0.
  assert(binds n (AC_Solved_EVar nv) (H1 & x ~ AC_Typ s1)). apply~ binds_push_neq.
  lets: subtyping_ok_preservation sub1 okg.
  assert(ok (H1 & x ~ AC_Typ s1)) by apply~ ok_push.
  lets: subtyping_evar_preservation2 sub2 H6 H4.
  apply binds_push_neq_inv in H7; auto.
  lets: hy bdn. false binds_func H7 H8.

  lets: IHsub1 okg H2. clear IHsub1.
  forwards * : H3. clear H3.
  destruct H4 as (I3 & h1info). subst.
  assert(forall a : var,
            binds a AC_Unsolved_EVar I1 ->
            binds a AC_Unsolved_EVar (H & x ~ AC_Typ s1)).
  intros n bdn.
  lets: hy bdn.
  apply~ binds_push_neq.
  introv neq. subst. assert(x # I1) by auto. false binds_fresh_inv bdn H3.
  assert(ok (I1 & I3 & x ~ AC_Typ s1)). apply~ ok_push.
  lets: subtyping_ok_preservation sub1 okg; auto.
  lets: IHsub2 H3 H1.
  assert(I1 & I3 & x ~ AC_Typ s1 = I1 & (I3 & x ~ AC_Typ s1)) by repeat rewrite~ concat_assoc.
  lets: H4 H5.
  destruct H6 as (I4 & hinfo).
  clear IHsub2.

  assert(binds x (AC_Typ s1) I4). apply binds_concat_right_inv with I1; auto. rewrite <- hinfo. apply binds_push_eq.
  apply split_bind_context in H6.
  destruct H6 as (I5 & I6 & i3info). subst.
  repeat rewrite concat_assoc in hinfo.
  symmetry in hinfo.
  apply tail_empty_eq2 in hinfo; auto.
  destruct hinfo as [? [? ?]]. subst.
  exists~ I5.
  rewrite hinfo. lets: subtyping_ok_preservation sub2 H3; auto.
  lets: subtyping_ok_preservation sub2 H3; auto.

  (* EVARL *)
  lets: resolve_forall_inserts H2 okg.
  destruct H4 as (I3 & h1info). subst.
  rewrite sinfo in H2.
  rewrite sinfo in okg.
  lets: resolve_forall_ok_preservation H2 okg.
  lets: unify_inserts H3 H1.
  destruct H4 as [(I4 & I5 & t2 & hinfo1) | hinfo2].
  assert(binds a AC_Unsolved_EVar (I1 & I2)).
  rewrite <- sinfo.
  apply binds_middle_eq. apply ok_middle_inv_r in H1; auto.
  apply binds_concat_inv in H4.
  destruct H4 as [bdi2 | [notin bdi1]].
  apply split_bind_context in bdi2.
  destruct bdi2 as (I6 & I7 & i2info). subst.
  repeat rewrite concat_assoc in sinfo.
  apply ok_middle_eq2 in sinfo.
  destruct sinfo as [? [? ?]]. subst.
  exists~ (I6 & I3 & I4 & a ~ AC_Solved_EVar t2 & I5).
  repeat rewrite~ concat_assoc.
  rewrite sinfo. repeat rewrite concat_assoc in okg; auto.
  repeat rewrite concat_assoc in okg; auto.
  lets: hy bdi1.
  rewrite hinfo1 in H4.
  apply binds_middle_eq_inv in H4. false H4.
  rewrite <- hinfo1.
  lets: resolve_forall_ok_preservation H2 okg; auto.
  lets: unify_ok_preservation H3 H5; auto.

  destruct hinfo2 as [hinfo2 tinfo]. subst.
  inversion H2; subst.
  exists~ I2.

  (* EVARR *)
  lets: resolve_forall_inserts H2 okg.
  destruct H4 as (I3 & h1info). subst.
  rewrite sinfo in H2.
  rewrite sinfo in okg.
  lets: resolve_forall_ok_preservation H2 okg.
  lets: unify_inserts H3 H1.
  destruct H4 as [(I4 & I5 & t2 & hinfo1) | hinfo2].
  assert(binds a AC_Unsolved_EVar (I1 & I2)).
  rewrite <- sinfo.
  apply binds_middle_eq. apply ok_middle_inv_r in H1; auto.
  apply binds_concat_inv in H4.
  destruct H4 as [bdi2 | [notin bdi1]].
  apply split_bind_context in bdi2.
  destruct bdi2 as (I6 & I7 & i2info). subst.
  repeat rewrite concat_assoc in sinfo.
  apply ok_middle_eq2 in sinfo.
  destruct sinfo as [? [? ?]]. subst.
  exists~ (I6 & I3 & I4 & a ~ AC_Solved_EVar t2 & I5).
  repeat rewrite~ concat_assoc.
  rewrite sinfo. repeat rewrite concat_assoc in okg; auto.
  repeat rewrite concat_assoc in okg; auto.
  lets: hy bdi1.
  rewrite hinfo1 in H4.
  apply binds_middle_eq_inv in H4. false H4.
  rewrite <- hinfo1.
  lets: resolve_forall_ok_preservation H2 okg; auto.
  lets: unify_ok_preservation H3 H5; auto.

  destruct hinfo2 as [hinfo2 tinfo]. subst.
  inversion H2; subst.
  lets: H0 s0. false~ H.
  exists~ I2.

  lets: unify_unsolved_helper H0 okg hy. auto.
Qed.

Lemma subtyping_unsolved: forall I e t H,
    ASubtyping I e t H ->
    ok I ->
    (forall a, binds a AC_Unsolved_EVar I -> binds a AC_Unsolved_EVar H) ->
    H = I.
Proof.
  introv sub oki hy.
  induction sub; auto.

  (* POLYR *)
  assert(ok (G & v ~ AC_TVar)) by apply~ ok_push.
  assert(forall a : var,
           binds a AC_Unsolved_EVar (G & v ~ AC_TVar) ->
           binds a AC_Unsolved_EVar (H & v ~ AC_TVar)).
  intros n bdn.
  assert( n <> v). introv neq; subst. false binds_push_eq_inv bdn.
  apply~ binds_push_neq.
  apply binds_push_neq_inv in bdn; auto.
  lets: IHsub H1 H2.
  destruct (eq_push_inv H3) as [? [? ?]]. subst~.

  (* POLYL *)
  assert(ok (G & b ~ AC_Marker & a ~ AC_Unsolved_EVar)) by apply~ ok_push.
  assert (forall a : var, binds a AC_Unsolved_EVar (G & b ~ AC_Marker) ->
                    binds a AC_Unsolved_EVar (H & b ~ AC_Marker & I)).
  intros n bdn.
  assert (n <> b). introv neq; subst.
  false binds_push_eq_inv bdn.
  apply binds_push_neq_inv in bdn; auto.
  lets: hy bdn.
  rewrite <- concat_assoc.
  apply~ binds_concat_left_ok.
  rewrite concat_assoc.
  lets: subtyping_ok_preservation sub H3. auto.
  lets: subtyping_unsolved_helper sub H3 H4.
  destruct H5 as (I1 & hinfo).
  apply ok_middle_eq2 in hinfo; auto.
  destruct hinfo as [? [? ?]]. auto.
  lets: subtyping_ok_preservation sub H3. auto.
  rewrite <- hinfo.
  lets: subtyping_ok_preservation sub H3. auto.

  (* PI *)
  lets: IHsub1 oki. clear IHsub1.
  assert(forall a : var, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H1).
  intros n bdn.
  lets: subtyping_evar_preservation sub1 oki bdn.
  destruct H3 as [bd_un | (nt & bd_so)]; auto.

  lets: hy bdn.
  assert (x <> n). introv neq; subst. false binds_fresh_inv bd_so H0.
  assert( binds n (AC_Solved_EVar nt) (H1 & x ~ AC_Typ s1)).
  apply~ binds_push_neq.
  lets: subtyping_ok_preservation sub1 oki.
  assert( ok (H1 & x ~ AC_Typ s1)). apply~ ok_push.
  lets: subtyping_evar_preservation2 sub2 H7 H5.
  apply binds_push_neq_inv in H8; auto.
  false binds_func H3 H8.

  lets: H2 H3. subst. clear H2 H3.
  assert (ok (G & x ~ AC_Typ s1)) by apply~ ok_push.
  assert(forall a : var,
            binds a AC_Unsolved_EVar (G & x ~ AC_Typ s1) ->
            binds a AC_Unsolved_EVar (H & x ~ AC_Typ s1)).
  intros n bdn.
  assert (n <> x). introv neq. subst. false binds_push_eq_inv bdn.
  apply~ binds_push_neq.
  apply binds_push_neq_inv in bdn; auto.
  lets: IHsub2 H1 H2.
  destruct (eq_push_inv H3) as [? [? ?]]. auto.

  (* EVARL *)
  lets: resolve_forall_inserts H2 oki.
  destruct H4 as (I1 & h1info); subst.
  inversion H3; subst.
  inversion H2; subst. auto.
  assert(binds a AC_Unsolved_EVar (G1 & a ~ AC_Unsolved_EVar & G2)).
  apply binds_middle_eq. apply ok_middle_inv_r in oki; auto.
  lets: hy H. apply binds_middle_eq_inv in H5. false H5.
  lets: resolve_forall_ok_preservation H2 oki.
  lets: unify_ok_preservation H3 H8. auto.
  false H5. reflexivity.

  (* EVARR *)
  lets: resolve_forall_inserts H2 oki.
  destruct H4 as (I1 & h1info); subst.
  inversion H3; subst.
  inversion H2; subst.
  false H0. reflexivity. auto.

  assert(binds a AC_Unsolved_EVar (G1 & a ~ AC_Unsolved_EVar & G2)).
  apply binds_middle_eq. apply ok_middle_inv_r in oki; auto.
  lets: hy H. apply binds_middle_eq_inv in H5. false H5.
  lets: resolve_forall_ok_preservation H2 oki.
  lets: unify_ok_preservation H3 H8. auto.

  false H5. reflexivity.

  (* UNIFY *)
  lets: unify_unsolved H0 oki hy. auto.
Qed.

(***********************)
(* Extension *)
(***********************)

Theorem resolve_evar_extension: forall G a s t H,
    AResolveEVar G a s t H ->
    AWf G ->
    ExtCtx G H.
Proof.
  introv res wf.
  lets: resolve_evar_awf_preservation res wf.
  assert (ok G) by apply* awf_is_ok.
  lets: resolve_evar_wextctx res H1.
  lets: weak_extension_to_extension H2 wf H0. auto.
Qed.

Theorem unify_extension: forall G s t H,
    AUnify G s t H ->
    AWf G ->
    AWf H /\ ExtCtx G H.
Admitted.

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