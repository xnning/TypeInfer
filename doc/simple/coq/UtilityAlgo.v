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

  lets: resolve_forall_ok_preservation H0 okg.
  lets: unify_ok_preservation H2 H3. auto.

  lets: resolve_forall_ok_preservation H0 okg.
  lets: unify_ok_preservation H2 H3. auto.

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
  lets: resolve_forall_wextctx H2 okg.
  lets: resolve_forall_ok_preservation H2 okg.
  lets: unify_wextctx H3 H5.
  lets: weak_extension_transitivity H4 H6.
  auto.

  (* EVarR *)
  lets: resolve_forall_wextctx H2 okg.
  lets: resolve_forall_ok_preservation H2 okg.
  lets: unify_wextctx H3 H5.
  lets: weak_extension_transitivity H4 H6.
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
