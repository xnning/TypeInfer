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
  lets: H2 y H3; auto.
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

Lemma atyping_awf: forall G m e t H,
    ATyping m G e t H ->
    AWf G.
Proof.
  introv ty.
  induction ty; repeat apply AWf_left in IHty; auto.
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
(* WEAK EXTENSION *)
(***********************)

Inductive WExtCtx : ACtx -> ACtx -> Prop :=
  | WExtCtx_Empty: WExtCtx empty empty
  | WExtCtx_Var : forall G H x,
      WExtCtx G H ->
      x # G -> x # H ->
      WExtCtx (G & x ~ AC_Var) (H & x ~ AC_Var)
  | WExtCtx_TypVar : forall G H x t,
      WExtCtx G H ->
      x # G -> x # H ->
      WExtCtx (G & x ~ AC_Typ t) (H & x ~ AC_Typ t)
  | WExtCtx_TVar : forall G H a,
      WExtCtx G H ->
      a # G -> a # H ->
      WExtCtx (G & a ~ AC_TVar) (H & a ~ AC_TVar)
  | WExtCtx_Marker : forall G H a,
      WExtCtx G H ->
      a # G -> a # H ->
      WExtCtx (G & a ~ AC_Marker) (H & a ~ AC_Marker)
  | WExtCtx_EVar : forall G H a,
      WExtCtx G H ->
      a # G -> a # H ->
      WExtCtx (G & a ~ AC_Unsolved_EVar) (H & a ~ AC_Unsolved_EVar)
  | WExtCtx_SolvedEVar: forall G H a t,
      WExtCtx G H ->
      a # G -> a # H ->
      WExtCtx (G & a ~ AC_Solved_EVar t) (H & a ~ AC_Solved_EVar t)
  | WExtCtx_Solve : forall G H a t,
      WExtCtx G H ->
      a # G -> a # H ->
      WExtCtx (G & a ~ AC_Unsolved_EVar) (H & a ~ AC_Solved_EVar t)
  | WExtCtx_Add : forall G H a,
      WExtCtx G H ->
      a # H ->
      WExtCtx G (H & a ~ AC_Unsolved_EVar)
  | WExtCtx_AddSolved: forall G H a t,
      WExtCtx G H ->
      a # H ->
      WExtCtx G (H & a ~ AC_Solved_EVar t)
.

Lemma weak_extension_var_preservation: forall G H x,
    WExtCtx G H ->
    x \in dom G ->
    x \in dom H.
Proof.
  introv ex okg.
  induction ex; auto.
  simpl_dom. rewrite in_union in okg. destruct okg as [inx0 | ing].
  apply union_left; auto.
  lets: IHex ing. apply union_right; auto.

  simpl_dom. rewrite in_union in okg. destruct okg as [inx0 | ing].
  apply union_left; auto.
  lets: IHex ing. apply union_right; auto.

  simpl_dom. rewrite in_union in okg. destruct okg as [inx0 | ing].
  apply union_left; auto.
  lets: IHex ing. apply union_right; auto.

  simpl_dom. rewrite in_union in okg. destruct okg as [inx0 | ing].
  apply union_left; auto.
  lets: IHex ing. apply union_right; auto.

  simpl_dom. rewrite in_union in okg. destruct okg as [inx0 | ing].
  apply union_left; auto.
  lets: IHex ing. apply union_right; auto.

  simpl_dom. rewrite in_union in okg. destruct okg as [inx0 | ing].
  apply union_left; auto.
  lets: IHex ing. apply union_right; auto.

  simpl_dom. rewrite in_union in okg. destruct okg as [inx0 | ing].
  apply union_left; auto.
  lets: IHex ing. apply union_right; auto.

  simpl_dom.
  lets: IHex okg. apply union_right; auto.

  simpl_dom.
  lets: IHex okg. apply union_right; auto.
Qed.

Lemma weak_extension_ok: forall G H,
    WExtCtx G H ->
    ok G.
Proof.
  introv ex. induction ex; auto.
Qed.

Lemma weak_extension_ok_preservation: forall G H,
    WExtCtx G H ->
    ok H.
Proof.
  introv ex.
  induction ex; auto.
Qed.

Lemma weak_extension_reflexicity: forall G,
    ok G ->
    WExtCtx G G.
Proof.
  introv okg.
  induction G using env_ind.
  apply WExtCtx_Empty.
  induction v.
  apply~ WExtCtx_Var. apply* ok_push_inv. apply* ok_push_inv.
  apply~ WExtCtx_TypVar. apply* ok_push_inv. apply* ok_push_inv.
  apply~ WExtCtx_TVar. apply* ok_push_inv. apply* ok_push_inv.
  apply~ WExtCtx_EVar. apply* ok_push_inv. apply* ok_push_inv.
  apply~ WExtCtx_SolvedEVar. apply* ok_push_inv. apply* ok_push_inv.
  apply~ WExtCtx_Marker. apply* ok_push_inv. apply* ok_push_inv.
Qed.

Lemma weak_extension_transitivity: forall G H I,
    WExtCtx G H ->
    WExtCtx H I ->
    WExtCtx G I.
Proof.
  introv gh hi.
  assert (ok G). apply* weak_extension_ok.
  assert (ok H). apply* weak_extension_ok.
  assert (ok I). apply* weak_extension_ok_preservation.
  gen G.
  induction hi; introv gh okg; auto.

  (* VAR *)
  inversion gh;
  try(apply eq_push_inv in H5; destruct H5 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H6; inversion H6.
  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H6 okg. apply~ WExtCtx_Var.

  (* TYPVAR *)
  inversion gh;
  try(apply eq_push_inv in H5; destruct H5 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H6; inversion H6.
  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H6 okg. apply~ WExtCtx_TypVar.

  (* TVAR *)
  inversion gh;
  try(apply eq_push_inv in H5; destruct H5 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H6; inversion H6.
  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H6 okg. apply~ WExtCtx_TVar.

  (* MARKER *)
  inversion gh;
  try(apply eq_push_inv in H5; destruct H5 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H6; inversion H6.
  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H6 okg. apply~ WExtCtx_Marker.

  (* EVAR *)
  inversion gh;
  try(apply eq_push_inv in H5; destruct H5 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H6; inversion H6.
  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H6 okg. apply~ WExtCtx_EVar.

  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2.
  lets: IHhi H1 H2 H6 okg. apply~ WExtCtx_Add.

  (* SOLVED EVAR *)
  inversion gh;
  try(apply eq_push_inv in H5; destruct H5 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H6; inversion H6.
  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H6 okg. apply~ WExtCtx_SolvedEVar.

  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H6 okg. apply~ WExtCtx_Solve.

  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2.
  lets: IHhi H1 H2 H6 okg. apply~ WExtCtx_AddSolved.

  (* SOLVE *)
  inversion gh;
  try(apply eq_push_inv in H5; destruct H5 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H6; inversion H6.
  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H6 okg. apply~ WExtCtx_Solve.

  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2.
  lets: IHhi H1 H2 H6 okg. apply~ WExtCtx_AddSolved.

  (* ADD *)
  apply ok_push_inv_ok in H2.
  lets: IHhi H1 H2 gh okg. apply~ WExtCtx_Add.

  (* ADD SOLVED *)
  apply ok_push_inv_ok in H2.
  lets: IHhi H1 H2 gh okg. apply~ WExtCtx_AddSolved.
Qed.

Lemma weak_extension_append_soft: forall G H I,
    WExtCtx G H ->
    Softness I ->
    ok (H & I) ->
    WExtCtx G (H & I).
Proof.
  introv ex sf wfhi.
  induction I using env_ind.
  repeat rewrite concat_empty_r in *. auto.
  repeat rewrite concat_assoc in *. auto.
  inversion sf.
  false empty_push_inv H1.
  apply eq_push_inv in H0.  destruct H0 as [? [? ?]]. subst.
  apply~ WExtCtx_Add. apply* ok_push_inv.
  apply eq_push_inv in H0.  destruct H0 as [? [? ?]]. subst.
  apply~ WExtCtx_AddSolved. apply* ok_push_inv.
Qed.

Lemma weak_extension_append: forall G H I,
    WExtCtx G H ->
    ok (G & I) ->
    ok (H & I) ->
    WExtCtx (G & I) (H & I).
Proof.
  introv ex wfgi wfhi.
  induction I using env_ind.
  repeat rewrite concat_empty_r in *. auto.
  repeat rewrite concat_assoc in *. auto.
  induction v; auto.
  apply~ WExtCtx_Var. apply* ok_push_inv. apply* ok_push_inv.
  apply~ WExtCtx_TypVar. apply* ok_push_inv. apply* ok_push_inv.
  apply~ WExtCtx_TVar. apply* ok_push_inv. apply* ok_push_inv.
  apply~ WExtCtx_EVar. apply* ok_push_inv. apply* ok_push_inv.
  apply~ WExtCtx_SolvedEVar. apply* ok_push_inv. apply* ok_push_inv.
  apply~ WExtCtx_Marker. apply* ok_push_inv. apply* ok_push_inv.
Qed.

Lemma weak_extension_append_ex: forall G H I S,
    WExtCtx G H ->
    WExtCtx I S ->
    ok (G & I) ->
    ok (H & S) ->
    WExtCtx (G & I) (H & S).
Proof.
  introv GH IS okgi okhs.
  induction IS.
  repeat rewrite concat_empty_r in *. auto.
  repeat rewrite concat_assoc in *.
  assert (ok (G & G0)) by apply* ok_push_inv.
  assert (ok (H & H0)) by apply* ok_push_inv.
  lets: IHIS H3 H4.
  apply~ WExtCtx_Var. apply* ok_push_inv.  apply* ok_push_inv.

  repeat rewrite concat_assoc in *.
  assert (ok (G & G0)) by apply* ok_push_inv.
  assert (ok (H & H0)) by apply* ok_push_inv.
  lets: IHIS H3 H4.
  apply~ WExtCtx_TypVar. apply* ok_push_inv.  apply* ok_push_inv.

  repeat rewrite concat_assoc in *.
  assert (ok (G & G0)) by apply* ok_push_inv.
  assert (ok (H & H0)) by apply* ok_push_inv.
  lets: IHIS H3 H4.
  apply~ WExtCtx_TVar. apply* ok_push_inv.  apply* ok_push_inv.

  repeat rewrite concat_assoc in *.
  assert (ok (G & G0)) by apply* ok_push_inv.
  assert (ok (H & H0)) by apply* ok_push_inv.
  lets: IHIS H3 H4.
  apply~ WExtCtx_Marker. apply* ok_push_inv.  apply* ok_push_inv.

  repeat rewrite concat_assoc in *.
  assert (ok (G & G0)) by apply* ok_push_inv.
  assert (ok (H & H0)) by apply* ok_push_inv.
  lets: IHIS H3 H4.
  apply~ WExtCtx_EVar. apply* ok_push_inv.  apply* ok_push_inv.

  repeat rewrite concat_assoc in *.
  assert (ok (G & G0)) by apply* ok_push_inv.
  assert (ok (H & H0)) by apply* ok_push_inv.
  lets: IHIS H3 H4.
  apply~ WExtCtx_SolvedEVar. apply* ok_push_inv.  apply* ok_push_inv.

  repeat rewrite concat_assoc in *.
  assert (ok (G & G0)) by apply* ok_push_inv.
  assert (ok (H & H0)) by apply* ok_push_inv.
  lets: IHIS H3 H4.
  apply~ WExtCtx_Solve. apply* ok_push_inv.  apply* ok_push_inv.

  repeat rewrite concat_assoc in *.
  assert (ok (H & H0)) by apply* ok_push_inv.
  lets: IHIS okgi H2.
  apply~ WExtCtx_Add. apply* ok_push_inv.

  repeat rewrite concat_assoc in *.
  assert (ok (H & H0)) by apply* ok_push_inv.
  lets: IHIS okgi H2.
  apply~ WExtCtx_AddSolved. apply* ok_push_inv.
Qed.

Lemma weak_extension_order_unsolved_evar : forall G1 G2 H x,
    WExtCtx (G1 & x ~ AC_Unsolved_EVar & G2) H ->
    exists H1 H2, (H = H1 & x ~ AC_Unsolved_EVar & H2 \/ exists t, H = H1 & x ~ AC_Solved_EVar t & H2) /\ WExtCtx G1 H1 /\ (Softness G2 -> Softness H2) /\ WExtCtx G2 H2.
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Unsolved_EVar & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H4 (H5 & x0 ~ AC_Var). split; auto.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t. rewrite HH2. rewrite* concat_assoc.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [eqa [eqv eqg]]. inversion eqv.
  subst. apply~ WExtCtx_Var.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.
  destruct HH as [? | (? & ?)]; subst; auto.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t) (G & x0 ~ AC_Typ t)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & [HH [EXG1H1 [SoftG3H2 EXG3H4]]]).
  exists* H3 (H4 & x0 ~ AC_Typ t). split; auto.
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t1. rewrite HH2. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5.
  subst. apply~ WExtCtx_TypVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.
  destruct HH as [? | (? & ?)]; subst; auto.

  (* AC_TVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_TVar (G & a ~ AC_TVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [EXG3H5 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_TVar). split; auto.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t. rewrite HH2. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.
  subst. apply~ WExtCtx_TVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.
  destruct HH as [? | (? & ?)]; subst; auto.

  (* AC_Marker *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Marker (G & a ~ AC_Marker)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [EXG3H5 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_Marker). split; auto.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t. rewrite HH2. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.
  subst. apply~ WExtCtx_Marker.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.
  destruct HH as [? | (? & ?)]; subst; auto.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  exists* H (empty: ACtx). split. rewrite* concat_empty_r.
  split. symmetry in IG. apply tail_empty_eq2 in IG; auto.
  destruct IG as [IG _]. subst. auto.
  rewrite IG. constructor. apply weak_extension_ok in EX; auto. auto.
  constructor. apply weak_extension_ok in EX. auto. auto.
  split; auto. constructor.
  symmetry in IG. apply tail_empty_eq2 in IG; auto. destruct IG as [? [? ?]]. subst. constructor.
  rewrite IG. constructor~. apply* weak_extension_ok.
  constructor~. apply* weak_extension_ok.

  assert (IG2 := IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3 := IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H11 & H2 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H11 (H2 & a ~ AC_Unsolved_EVar). split; auto.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t. rewrite HH2. rewrite concat_assoc. auto.
  split; auto. split; auto.
  intros. constructor. apply* SoftG3H2. rewrite HG2 in H3. inversion H3. apply empty_push_inv in H5. inversion H5. apply eq_push_inv in H4. destruct H4 as [eqa [_ eqg]]. rewrite eqg in H5. auto. apply eq_push_inv in H4. destruct H4 as [_ [eqv _]]. inversion eqv.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1 in H1. auto. rewrite HH2 in H1. auto.
  subst. apply~ WExtCtx_EVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.
  destruct HH as [? | (? & ?)]; subst; auto.


  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t) (G & a ~ AC_Solved_EVar t)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor~. apply* weak_extension_ok.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H5]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t1. rewrite HH2. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption.
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1 in H1. auto.
  rewrite HH2 in H1. auto.
  subst. apply~ WExtCtx_SolvedEVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.
  destruct HH as [? | (? & ?)]; subst; auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  exists* H (empty: ACtx).
  split. right. exists t. rewrite concat_empty_r. auto.
  split. apply tail_empty_eq with (G0:= G & a ~ AC_Unsolved_EVar) (G3 := G) (I := G1 & a ~ AC_Unsolved_EVar & G2) (I1:= G1) (I2:=G2) (x:=a) (vx:=AC_Unsolved_EVar) (vy:=AC_Unsolved_EVar)in IG; auto.
  destruct IG as [IG _]. subst. auto.
  rewrite <- IG. constructor. apply* weak_extension_ok. auto.
  constructor. apply* weak_extension_ok. auto.
  split; auto. constructor.
  symmetry in IG. apply tail_empty_eq2 in IG; auto. destruct IG as [? [? ?]]. subst. constructor.
  rewrite IG. constructor~. apply* weak_extension_ok.
  constructor~. apply* weak_extension_ok.

  assert (IG2 := IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3 := IG). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [EXG1H1 [SoftG3H2 EXG3H3]]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t). split; auto.
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t1. rewrite HH2. rewrite concat_assoc. auto.
  split; auto. split; auto.
  intros. constructor. apply* SoftG3H2. rewrite HG2 in H4. inversion H4. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H5. destruct H5 as [eqa [_ eqg]]. rewrite eqg in H6. auto. apply eq_push_inv in H5. destruct H5 as [_ [eqv _]]. inversion eqv.
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1 in H1. auto.
  rewrite HH2 in H1. auto.
  subst. apply~ WExtCtx_Solve.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.
  destruct HH as [? | (? & ?)]; subst; auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 [SoftG2H2 EXG2H2]]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar).
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1. split. rewrite concat_assoc. auto.
  split. auto. split; auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH1 in H0. auto.
  apply~ WExtCtx_Add. subst; auto.

  split. right. exists t1. rewrite HH2. rewrite concat_assoc. auto.
  split. auto. split. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH2 in H0.  auto.
  apply~ WExtCtx_Add. subst; auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 [SoftG2H2 EXG2H3]]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t).

  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1. split. rewrite concat_assoc. auto.
  split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH1 in H0. auto.
  apply~ WExtCtx_AddSolved. subst; auto.

  split. right. exists t1. rewrite HH2. rewrite concat_assoc. auto.
  split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH2 in H0. auto.
  apply~ WExtCtx_AddSolved. subst; auto.
Qed.

Lemma weak_extension_order_tvar : forall G1 G2 H x,
    WExtCtx (G1 & x ~ AC_TVar & G2) H ->
    exists H1 H2, H = H1 & x ~ AC_TVar & H2 /\ WExtCtx G1 H1 /\ (Softness G2 -> Softness H2) /\ WExtCtx G2 H2.
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_TVar & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H4 (H5 & x0 ~ AC_Var). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [eqa [eqv eqg]]. inversion eqv.
  subst. apply~ WExtCtx_Var.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t) (G & x0 ~ AC_Typ t)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & [HH [EXG1H1 [SoftG3H2 EXG3H4]]]).
  exists* H3 (H4 & x0 ~ AC_Typ t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5.
  subst. apply~ WExtCtx_TypVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_TVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_TVar (G & a ~ AC_TVar)).
  apply* binds_push_eq. exists~ H (empty:ACtx). repeat rewrite concat_empty_r.
  symmetry in IG. apply tail_empty_eq2 in IG; auto.
  destruct IG as [IG [_ IG2]]. subst. split; auto. split; auto. split; auto. constructor.
  rewrite IG. constructor. apply weak_extension_ok in EX; auto. auto.
  constructor. apply weak_extension_ok in EX; auto. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [EXG3H5 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_TVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.
  subst. apply~ WExtCtx_TVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Marker *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Marker (G & a ~ AC_Marker)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [EXG3H5 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_Marker). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.
  subst. apply~ WExtCtx_Marker.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.
  subst. apply~ WExtCtx_EVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t) (G & a ~ AC_Solved_EVar t)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor~. apply* weak_extension_ok.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H5]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption.
  rewrite HH in H1. auto.
  subst. apply~ WExtCtx_SolvedEVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.
  subst. apply~ WExtCtx_Solve.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 [SoftG2H2 EXG2H2]]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar).
  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto. split; auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.
  apply~ WExtCtx_Add. subst; auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 [SoftG2H2 EXG2H3]]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t).

  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.
  apply~ WExtCtx_AddSolved. subst; auto.
Qed.

Lemma weak_extension_order_var : forall G1 G2 H x,
    WExtCtx (G1 & x ~ AC_Var & G2) H ->
    exists H1 H2, H = H1 & x ~ AC_Var & H2 /\ WExtCtx G1 H1 /\ (Softness G2 -> Softness H2) /\ WExtCtx G2 H2.
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Var & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. exists~ H (empty:ACtx). repeat rewrite concat_empty_r.
  symmetry in IG. apply tail_empty_eq2 in IG; auto.
  destruct IG as [IG [_ IG2]]. subst. split; auto. split; auto. split; auto. constructor.
  rewrite IG. constructor. apply weak_extension_ok in EX; auto. auto.
  constructor. apply weak_extension_ok in EX; auto. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [EXG3H5 SoftG3H2]]]).
  exists* H4 (H5 & x0 ~ AC_Var). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.
  subst. apply~ WExtCtx_Var.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t) (G & x0 ~ AC_Typ t)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & [HH [EXG1H1 [SoftG3H2 EXG3H4]]]).
  exists* H3 (H4 & x0 ~ AC_Typ t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5.
  subst. apply~ WExtCtx_TypVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_TVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_TVar (G & a ~ AC_TVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [EXG3H5 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_TVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.
  subst. apply~ WExtCtx_TVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Marker *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Marker (G & a ~ AC_Marker)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [EXG3H5 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_Marker). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.
  subst. apply~ WExtCtx_Marker.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.
  subst. apply~ WExtCtx_EVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t) (G & a ~ AC_Solved_EVar t)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor~. apply* weak_extension_ok.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H5]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption.
  rewrite HH in H1. auto.
  subst. apply~ WExtCtx_SolvedEVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.
  subst. apply~ WExtCtx_Solve.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 [SoftG2H2 EXG2H2]]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar).
  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto. split; auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.
  apply~ WExtCtx_Add. subst; auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 [SoftG2H2 EXG2H3]]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t).

  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.
  apply~ WExtCtx_AddSolved. subst; auto.
Qed.

Lemma weak_extension_order_solved_evar : forall G1 G2 H x t,
    WExtCtx (G1 & x ~ AC_Solved_EVar t & G2) H ->
    exists H1 H2, H = H1 & x ~ AC_Solved_EVar t & H2 /\ WExtCtx G1 H1 /\ (Softness G2 -> Softness H2) /\ WExtCtx G2 H2.
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Solved_EVar t & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H4 (H5 & x0 ~ AC_Var). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [eqa [eqv eqg]]. inversion eqv.
  subst. apply~ WExtCtx_Var.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t0) (G & x0 ~ AC_Typ t0)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & [HH [EXG1H1 [SoftG3H2 EXG3H4]]]).
  exists* H3 (H4 & x0 ~ AC_Typ t0). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5.
  subst. apply~ WExtCtx_TypVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_TVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_TVar (G & a ~ AC_TVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [EXG3H5 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_TVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.
  subst. apply~ WExtCtx_TVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Marker *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Marker (G & a ~ AC_Marker)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [EXG3H5 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_Marker). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.
  subst. apply~ WExtCtx_Marker.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.
  subst. apply~ WExtCtx_EVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t0) (G & a ~ AC_Solved_EVar t0)).
  apply* binds_push_eq. exists~ H (empty:ACtx). repeat rewrite concat_empty_r.
  symmetry in IG. apply tail_empty_eq2 in IG; auto.
  destruct IG as [IG [eqv IG2]]. inversion eqv. subst. split; auto. split; auto. split; auto. constructor.
  rewrite IG. constructor. apply weak_extension_ok in EX; auto. auto.
  constructor. apply weak_extension_ok in EX; auto. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H5]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t0). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption.
  rewrite HH in H1. auto.
  subst. apply~ WExtCtx_SolvedEVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t0). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.
  subst. apply~ WExtCtx_Solve.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 [SoftG2H2 EXG2H2]]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar).
  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto. split; auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.
  apply~ WExtCtx_Add. subst; auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 [SoftG2H2 EXG2H3]]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t0).

  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.
  apply~ WExtCtx_AddSolved. subst; auto.
Qed.

Lemma weak_extension_order_typvar : forall G1 G2 H x t,
    WExtCtx (G1 & x ~ AC_Typ t & G2) H ->
    exists H1 H2, H = H1 & x ~ AC_Typ t & H2 /\ WExtCtx G1 H1 /\ (Softness G2 -> Softness H2) /\ WExtCtx G2 H2.
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Typ t & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H4 (H5 & x0 ~ AC_Var). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [eqa [eqv eqg]]. inversion eqv.
  subst. apply~ WExtCtx_Var.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t0) (G & x0 ~ AC_Typ t0)).
  apply* binds_push_eq. exists~ H (empty:ACtx). repeat rewrite concat_empty_r.
  symmetry in IG. apply tail_empty_eq2 in IG; auto.
  destruct IG as [IG [eqv IG2]]. inversion eqv. subst. split; auto. split; auto. split; auto. constructor.
  rewrite IG. constructor. apply weak_extension_ok in EX; auto. auto.
  constructor. apply weak_extension_ok in EX; auto. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & [HH [EXG1H1 [SoftG3H2 EXG3H4]]]).
  exists* H3 (H4 & x0 ~ AC_Typ t0). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5.
  subst. apply~ WExtCtx_TypVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_TVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_TVar (G & a ~ AC_TVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [EXG3H5 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_TVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.
  subst. apply~ WExtCtx_TVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Marker *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Marker (G & a ~ AC_Marker)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [EXG3H5 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_Marker). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.
  subst. apply~ WExtCtx_Marker.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.
  subst. apply~ WExtCtx_EVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t0) (G & a ~ AC_Solved_EVar t0)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor~. apply* weak_extension_ok.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H5]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t0). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption.
  rewrite HH in H1. auto.
  subst. apply~ WExtCtx_SolvedEVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t0). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.
  subst. apply~ WExtCtx_Solve.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 [SoftG2H2 EXG2H2]]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar).
  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto. split; auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.
  apply~ WExtCtx_Add. subst; auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 [SoftG2H2 EXG2H3]]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t0).

  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.
  apply~ WExtCtx_AddSolved. subst; auto.
Qed.

Lemma weak_extension_order_marker : forall G1 G2 H x,
    WExtCtx (G1 & x ~ AC_Marker & G2) H ->
    exists H1 H2, H = H1 & x ~ AC_Marker & H2 /\ WExtCtx G1 H1 /\ (Softness G2 -> Softness H2) /\ WExtCtx G2 H2.
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Marker & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H4 (H5 & x0 ~ AC_Var). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [eqa [eqv eqg]]. inversion eqv.
  subst. apply~ WExtCtx_Var.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t) (G & x0 ~ AC_Typ t)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & [HH [EXG1H1 [SoftG3H2 EXG3H4]]]).
  exists* H3 (H4 & x0 ~ AC_Typ t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5.
  subst. apply~ WExtCtx_TypVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_TVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_TVar (G & a ~ AC_TVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [EXG3H5 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_TVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.
  subst. apply~ WExtCtx_TVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Marker *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Marker (G & a ~ AC_Marker)).
  apply* binds_push_eq. exists~ H (empty:ACtx). repeat rewrite concat_empty_r.
  symmetry in IG. apply tail_empty_eq2 in IG; auto.
  destruct IG as [IG [_ IG2]]. subst. split; auto. split; auto. split; auto. constructor.
  rewrite IG. constructor. apply weak_extension_ok in EX; auto. auto.
  constructor. apply weak_extension_ok in EX; auto. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [EXG3H5 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_Marker). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.
  subst. apply~ WExtCtx_Marker.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.
  subst. apply~ WExtCtx_EVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t) (G & a ~ AC_Solved_EVar t)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor~. apply* weak_extension_ok.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H5]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption.
  rewrite HH in H1. auto.
  subst. apply~ WExtCtx_SolvedEVar.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* weak_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 [SoftG3H2 EXG3H2]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto. split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.
  subst. apply~ WExtCtx_Solve.
  rewrite concat_assoc in IG3.
  apply eq_push_inv in IG3. destruct IG3 as [? [? ?]]. subst. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 [SoftG2H2 EXG2H2]]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar).
  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto. split; auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.
  apply~ WExtCtx_Add. subst; auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 [SoftG2H2 EXG2H3]]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t).

  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.
  apply~ WExtCtx_AddSolved. subst; auto.
Qed.

Lemma weak_extension_remove_var: forall G H x,
    WExtCtx (G & x ~ AC_Var) (H & x ~ AC_Var) ->
    WExtCtx G H.
Proof.
  introv ex.
  inversion ex;
  try(apply eq_push_inv in H1; destruct H1 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H2; inversion H2.
  subst. clear EQV.
  apply eq_push_inv in H2. destruct H2 as [? [? ?]]. subst~.
Qed.

Lemma weak_extension_remove_typvar: forall G H x t,
    WExtCtx (G & x ~ AC_Typ t) (H & x ~ AC_Typ t) ->
    WExtCtx G H.
Proof.
  introv ex.
  inversion ex;
  try(apply eq_push_inv in H1; destruct H1 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H2; inversion H2.
  subst. clear EQV.
  apply eq_push_inv in H2. destruct H2 as [? [? ?]]. subst~.
Qed.

Lemma weak_extension_remove_tvar: forall G H x,
    WExtCtx (G & x ~ AC_TVar) (H & x ~ AC_TVar) ->
    WExtCtx G H.
Proof.
  introv ex.
  inversion ex;
  try(apply eq_push_inv in H1; destruct H1 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H2; inversion H2.
  subst. clear EQV.
  apply eq_push_inv in H2. destruct H2 as [? [? ?]]. subst~.
Qed.

Lemma weak_extension_remove_marker: forall G H x,
    WExtCtx (G & x ~ AC_Marker) (H & x ~ AC_Marker) ->
    WExtCtx G H.
Proof.
  introv ex.
  inversion ex;
  try(apply eq_push_inv in H1; destruct H1 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H2; inversion H2.
  subst. clear EQV.
  apply eq_push_inv in H2. destruct H2 as [? [? ?]]. subst~.
Qed.

Lemma weak_extension_remove_evar: forall G H x,
    WExtCtx (G & x ~ AC_Unsolved_EVar) H ->
    WExtCtx G H.
Proof.
  introv ex.
  assert(WExtCtx (G & x ~ AC_Unsolved_EVar & empty) H) by rewrite~ concat_empty_r.
  lets: weak_extension_order_unsolved_evar H0.
  destruct H1 as (S1 & S2 & [hinfo [ex1 [sf ex2]]]).
  destruct hinfo as [hinfo | (t & hinfo)].
  rewrite hinfo.
  apply weak_extension_append_soft.
  apply~ WExtCtx_Add.
  apply weak_extension_ok_preservation in H0. rewrite hinfo in H0. apply ok_concat_inv_l in H0. apply* ok_push_inv.
  apply~ sf. constructor.
  apply weak_extension_ok_preservation in H0. rewrite hinfo in H0. auto.

  rewrite hinfo.
  apply weak_extension_append_soft.
  apply~ WExtCtx_AddSolved.
  apply weak_extension_ok_preservation in H0. rewrite hinfo in H0. apply ok_concat_inv_l in H0. apply* ok_push_inv.
  apply~ sf. constructor.
  apply weak_extension_ok_preservation in H0. rewrite hinfo in H0. auto.
Qed.

Lemma weak_extension_remove_evar_middle: forall G H I x,
    WExtCtx (G & x ~ AC_Unsolved_EVar & I) H ->
    WExtCtx (G & I) H.
Proof.
  introv ex. gen H.
  induction I using env_ind; introv ex.
  rewrite concat_empty_r in *.
  lets: weak_extension_remove_evar ex. auto.

  rewrite concat_assoc in *.
  induction v.

  (* VAR *)
  assert (WExtCtx (G & x ~ AC_Unsolved_EVar & I & x0 ~ AC_Var & empty) H) by rewrite~ concat_empty_r.
  apply weak_extension_order_var in H0.
  destruct H0 as (S1 & S2 & [hinfo [ex1 [sf ex2]]]).
  subst.
  apply~ weak_extension_append_soft.
  apply~ WExtCtx_Var.
  lets: weak_extension_ok ex. apply ok_push_inv in H. destruct H.
  auto.
  lets: weak_extension_ok_preservation ex. apply ok_middle_inv in H. destruct H. auto.
  apply~ sf. constructor.
  apply* weak_extension_ok_preservation.

  (* TYPVAR *)
  assert(WExtCtx (G & x ~ AC_Unsolved_EVar & I & x0 ~ AC_Typ a & empty) H) by rewrite~ concat_empty_r.
  apply weak_extension_order_typvar in H0.
  destruct H0 as (S1 & S2 & [hinfo [ex1 [sf ex2]]]).
  subst.
  apply~ weak_extension_append_soft.
  apply~ WExtCtx_TypVar.
  lets: weak_extension_ok ex. apply ok_push_inv in H. destruct H.
  auto.
  lets: weak_extension_ok_preservation ex. apply ok_middle_inv in H. destruct H. auto.
  apply~ sf. constructor.
  apply* weak_extension_ok_preservation.

  (* TVAR *)
  assert(WExtCtx (G & x ~ AC_Unsolved_EVar & I & x0 ~ AC_TVar & empty) H) by rewrite~ concat_empty_r.
  apply weak_extension_order_tvar in H0.
  destruct H0 as (S1 & S2 & [hinfo [ex1 [sf ex2]]]).
  subst.
  apply~ weak_extension_append_soft.
  apply~ WExtCtx_TVar.
  lets: weak_extension_ok ex. apply ok_push_inv in H. destruct H.
  auto.
  lets: weak_extension_ok_preservation ex. apply ok_middle_inv in H. destruct H. auto.
  apply~ sf. constructor.
  apply* weak_extension_ok_preservation.

  (* UNSOLVED EVAR *)
  assert(WExtCtx (G & x ~ AC_Unsolved_EVar & I & x0 ~ AC_Unsolved_EVar & empty) H) by rewrite~ concat_empty_r.
  apply weak_extension_order_unsolved_evar in H0.
  destruct H0 as (S1 & S2 & [hinfo [ex1 [sf ex2]]]).
  destruct hinfo as [hinfo | (n & hinfo)]; subst.

  apply~ weak_extension_append_soft.
  apply~ WExtCtx_EVar.
  lets: weak_extension_ok ex. apply ok_push_inv in H. destruct H.
  auto.
  lets: weak_extension_ok_preservation ex. apply ok_middle_inv in H. destruct H. auto.
  apply~ sf. constructor.
  apply* weak_extension_ok_preservation.

  apply~ weak_extension_append_soft.
  apply~ WExtCtx_Solve.
  lets: weak_extension_ok ex. apply ok_push_inv in H. destruct H.
  auto.
  lets: weak_extension_ok_preservation ex. apply ok_middle_inv in H. destruct H. auto.
  apply~ sf. constructor.
  apply* weak_extension_ok_preservation.

  (* SOLVED EVAR *)
  assert(WExtCtx (G & x ~ AC_Unsolved_EVar & I & x0 ~ (AC_Solved_EVar a) & empty) H) by rewrite~ concat_empty_r.
  apply weak_extension_order_solved_evar in H0.
  destruct H0 as (S1 & S2 & [hinfo [ex1 [sf ex2]]]).
  subst.
  apply~ weak_extension_append_soft.
  apply~ WExtCtx_SolvedEVar.
  lets: weak_extension_ok ex. apply ok_push_inv in H. destruct H.
  auto.
  lets: weak_extension_ok_preservation ex. apply ok_middle_inv in H. destruct H. auto.
  apply~ sf. constructor.
  apply* weak_extension_ok_preservation.

  (* MARKER *)
  assert(WExtCtx (G & x ~ AC_Unsolved_EVar & I & x0 ~ AC_Marker & empty) H) by rewrite~ concat_empty_r.
  apply weak_extension_order_marker in H0.
  destruct H0 as (S1 & S2 & [hinfo [ex1 [sf ex2]]]).
  subst.
  apply~ weak_extension_append_soft.
  apply~ WExtCtx_Marker.
  lets: weak_extension_ok ex. apply ok_push_inv in H. destruct H.
  auto.
  lets: weak_extension_ok_preservation ex. apply ok_middle_inv in H. destruct H. auto.
  apply~ sf. constructor.
  apply* weak_extension_ok_preservation.

Qed.

Lemma weak_extension_solve_middle: forall G H1 H2 a t,
   WExtCtx G (H1 & a ~ AC_Unsolved_EVar & H2) ->
   WExtCtx G (H1 & a ~ AC_Solved_EVar t & H2).
Proof.
  introv ex. gen G.
  induction H2 using env_ind; introv ex.
  rewrite concat_empty_r in *.
  gen_eq I: (H1 & a ~ AC_Unsolved_EVar).
  induction ex; introv iinfo;
    try(destruct (eq_push_inv iinfo) as [? [? ?]]);
    try(solve[false]).
  false empty_push_inv iinfo.
  subst. apply~ WExtCtx_Solve.
  subst. apply~ WExtCtx_AddSolved.

  rewrite concat_assoc in *.
  induction v.

  inversion ex;
  try(apply eq_push_inv in H0; destruct H0 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H3; inversion H3.
  subst. lets: IHenv H3. apply~ WExtCtx_Var.

  inversion ex;
  try(apply eq_push_inv in H0; destruct H0 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H3; inversion H3.
  subst. lets: IHenv H3. apply~ WExtCtx_TypVar.

  inversion ex;
  try(apply eq_push_inv in H0; destruct H0 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H3; inversion H3.
  subst. lets: IHenv H3. apply~ WExtCtx_TVar.

  inversion ex;
  try(apply eq_push_inv in H0; destruct H0 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H3; inversion H3.
  subst. lets: IHenv H3. apply~ WExtCtx_EVar.
  subst. lets: IHenv H3. apply~ WExtCtx_Add.

  inversion ex;
  try(apply eq_push_inv in H0; destruct H0 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H3; inversion H3.
  subst. lets: IHenv H3. apply~ WExtCtx_SolvedEVar.
  subst. lets: IHenv H3. apply~ WExtCtx_Solve.
  subst. lets: IHenv H3. apply~ WExtCtx_AddSolved.

  inversion ex;
  try(apply eq_push_inv in H0; destruct H0 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H3; inversion H3.
  subst. lets: IHenv H3. apply~ WExtCtx_Marker.
Qed.

Lemma weak_extension_binds_solved_evar: forall G H a n,
    WExtCtx G H ->
    binds a (AC_Solved_EVar n) G ->
    binds a (AC_Solved_EVar n) H.
Proof.
  introv H0 bd.
  apply split_bind_context in bd.
  destruct bd as (S1 & S2 & ginfo). subst.
  lets: weak_extension_order_solved_evar H0.
  destruct H1 as (T1 & T2 & [hfin _]). subst.
  apply~ binds_middle_eq.
  lets: weak_extension_ok_preservation H0.
  apply ok_middle_inv_r in H. auto.
Qed.

Lemma weak_extension_binds_unsolved_evar: forall G H a,
    WExtCtx G H ->
    binds a AC_Unsolved_EVar G ->
    binds a AC_Unsolved_EVar H \/ (exists n, binds a (AC_Solved_EVar n) H).
Proof.
  introv H0 bd.
  apply split_bind_context in bd.
  destruct bd as (S1 & S2 & ginfo). subst.
  lets: weak_extension_order_unsolved_evar H0.
  destruct H1 as (T1 & T2 & [hfin _]). subst.
  destruct hfin as [hfin1 | (n & hfin2)]; subst.
  left. apply~ binds_middle_eq.
  lets: weak_extension_ok_preservation H0.
  apply ok_middle_inv_r in H. auto.
  right. exists n. apply~ binds_middle_eq.
  lets: weak_extension_ok_preservation H0.
  apply ok_middle_inv_r in H. auto.
Qed.

Lemma weak_extension_to_extension: forall G H,
    WExtCtx G H ->
    AWf G ->
    AWf H ->
    ExtCtx G H.
Proof.
  introv ex wfg wfh.
  induction ex; auto.
  apply~ ExtCtx_Var. apply IHex. apply AWf_left in wfg; auto. apply AWf_left in wfh; auto.
  apply~ ExtCtx_TypVar. apply IHex. apply AWf_left in wfg; auto. apply AWf_left in wfh; auto.
  apply~ ExtCtx_TVar. apply IHex. apply AWf_left in wfg; auto. apply AWf_left in wfh; auto.
  apply~ ExtCtx_Marker. apply IHex. apply AWf_left in wfg; auto. apply AWf_left in wfh; auto.
  apply~ ExtCtx_EVar. apply IHex. apply AWf_left in wfg; auto. apply AWf_left in wfh; auto.
  apply~ ExtCtx_SolvedEVar. apply IHex. apply AWf_left in wfg; auto. apply AWf_left in wfh; auto.
  apply~ ExtCtx_Solve. apply IHex. apply AWf_left in wfg; auto. apply AWf_left in wfh; auto.
  apply~ ExtCtx_Add. apply~ IHex. apply AWf_left in wfh; auto.
  apply~ ExtCtx_AddSolved. apply~ IHex. apply AWf_left in wfh; auto.
Qed.

Lemma resolve_forall_awf_preservation: forall G a m s t H,
    AResolveForall G a m s t H ->
    AWf G ->
    AWf H.
Proof.
  introv res wfg.
  induction res; auto.
  apply IHres.
  admit. (* insert unsolved evar*)
Qed.

Lemma resolve_evar_awf_preservation: forall G a s t H,
    AResolveEVar G a s t H ->
    AWf G ->
    AWf H.
Proof.
  introv res wfg.
  induction res; auto.
  admit. (* insert unsolved evar; solve evar *)
  pick_fresh y. assert(y \notin L) by auto.
  lets: H2 H3.
  apply H4. apply~ IHres.
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
  admit. (*solve evar*)

  lets: resolve_evar_awf_preservation H3 wfg.
  admit. (*solve evar*)
Qed.

Lemma atyping_awf_preservation: forall G m e t H,
    ATyping m G e t H ->
    AWf G.
Proof.
  introv ty.
  induction ty; repeat apply AWf_left in IHty; auto.
Qed.

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
  lets: H3 y H6 H4 H0.
  lets: weak_extension_transitivity H5 H7. auto.
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

Lemma uv_is_soft: forall G,
    ok G ->
    Softness (ACtxUV G).
Proof.
  introv okg. induction G using env_ind.
  rewrite empty_uv. constructor.
  induction v.
  rewrite~ uv_add_var.
  rewrite~ uv_add_typvar.
  rewrite~ uv_add_tvar.
  rewrite~ uv_add_evar. constructor. apply IHG. apply* ok_push_inv. apply notin_uv. apply* ok_push_inv.
  rewrite~ uv_add_solved_evar.
  rewrite~ uv_add_marker.
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

  pick_fresh y.
  assert (y \notin L) by auto.
  lets: H2 H4.
  lets: resolve_evar_ok_preservation res okg.
  assert (forall a : var, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H1).
  intros n bdn.
  lets: resolve_evar_evar_preservation res okg bdn.
  destruct H7 as [? | (? & ?)]; auto.
  lets: hy bdn.
  lets: resolve_evar_evar_preservation2 H5 H6 H7.
  false binds_func H8 H9.
  lets: IHres okg H7 H6. subst.
  lets: H3 H4 H6 hy H0. auto.
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
  forwards*: H2 H3 H1.
  destruct H4 as (I3 & I4 & ?). subst.
  exists~ (I1 & I3) I4. repeat rewrite ~ concat_assoc.
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

Lemma subtyping_unsolved': forall G e t H S,
    ASubtyping (G & S) e t H ->
    ok (G & S) ->
    (forall a, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H) ->
    exists I, H = G & I.
Proof.
  introv sub okg hy. gen_eq T : (G & S). gen S.
  induction sub; introv ginfo; auto; try(solve[exists~ S]); subst.

  (* POLYR *)
  subst. assert (ok (G & S & v ~ AC_TVar)) by constructor~.
  lets: subtyping_ok_preservation sub H1.
  assert(forall a : var, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar (H & v ~ AC_TVar)).
  intros n bdn.
  assert (binds n AC_Unsolved_EVar (G & S & v ~ AC_TVar)).
  rewrite <- concat_assoc in H1.
  rewrite <- concat_assoc.
  apply~ binds_concat_left_ok.
  lets: subtyping_evar_preservation sub H1 H3.
  destruct H4 as [bd_un | (m & bd_so)]; auto.
  assert (n <> v). introv neq. subst. false binds_push_eq_inv bd_so.
  apply binds_push_neq_inv in bd_so; auto.
  assert( G & S & v ~ AC_TVar = G & (S & v ~ AC_TVar)) by rewrite~ concat_assoc.
  lets: IHsub H1 H3 H4.
  destruct H5 as (T & hinfo).
  assert (binds v AC_TVar (G & T)). rewrite <- hinfo. apply~ binds_push_eq.
  apply binds_concat_inv in H5.
  destruct H5 as [bdt | [neq bdg]].
  apply split_bind_context in bdt; auto.
  destruct bdt as (M1 & M2 & tinfo). subst.
  assert( H & v ~ AC_TVar & empty = G & (M1 & v ~ AC_TVar & M2)) by rewrite~ concat_empty_r.
  repeat rewrite concat_assoc in H5.
  apply ok_middle_eq2 in H5; auto.
  destruct H5 as [? [? ?]]. subst. exists~ M1.
  rewrite~ concat_empty_r.
  rewrite~ <- H5. rewrite~ concat_empty_r.

  apply ok_push_inv in H1. simpl_dom. rewrite notin_union in H1. destruct H1 as [? [? ?]]. false binds_fresh_inv bdg H5.

  (* POLYL *)
  assert( ok (G & S & b ~ AC_Marker & a ~ AC_Unsolved_EVar)) by constructor~.
  assert(forall a : var,
           binds a AC_Unsolved_EVar G ->
           binds a AC_Unsolved_EVar (H & b ~ AC_Marker & I)).
  intros n bdn.
  lets: hy bdn.
  rewrite <- concat_assoc.
  apply~ binds_concat_left_ok. rewrite~ concat_assoc.
  lets: subtyping_ok_preservation sub H3; auto.
  assert(G & S & b ~ AC_Marker & a ~ AC_Unsolved_EVar = G & (S & b ~ AC_Marker & a ~ AC_Unsolved_EVar)) by repeat rewrite~ concat_assoc.
  lets: IHsub H3 H4 H5.

  destruct H6 as (T & sinfo).
  lets: subtyping_ok_preservation sub H3.
  assert (binds b AC_Marker (G & T)). rewrite <- sinfo. apply~ binds_middle_eq. apply ok_middle_inv_r in H6; auto.
  apply binds_concat_inv in H7.
  destruct H7 as [bdt | [neq bdg]].
  apply split_bind_context in bdt; auto.
  destruct bdt as (M1 & M2 & tinfo). subst.
  repeat rewrite concat_assoc in sinfo.
  apply ok_middle_eq2 in sinfo; auto.
  destruct sinfo as [? [? ?]]. subst. exists~ M1.
  rewrite <- sinfo; auto.

  simpl_dom. rewrite notin_union in H1. destruct H1 as [? ?]. false binds_fresh_inv bdg H1.

  (* PI *)
  assert (forall a : var, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H1).
  intros n bdn.
  assert (binds n AC_Unsolved_EVar (G & S)). apply~ binds_concat_left_ok.
  lets: subtyping_evar_preservation sub1 okg H2.
  destruct H3 as [? | (? & ?)]; auto.
  assert (x <> n). introv neq. subst. false binds_fresh_inv H3 H0.
  assert (binds n (AC_Solved_EVar x0) (H1 & x ~ AC_Typ s1)) by apply~ binds_push_neq.
  lets: subtyping_ok_preservation sub1 okg.
  assert (ok (H1 & x ~ AC_Typ s1)) by constructor~.
  lets: subtyping_evar_preservation2 sub2 H7 H5.
  lets: hy bdn.
  lets: subtyping_ok_preservation sub2 H7.
  apply split_bind_context in H9.
  destruct H9 as (M1 & M2 & hinfo); subst.
  do 1 rewrite <- concat_assoc in H8.
  do 1 rewrite <- concat_assoc in H10.
  apply binds_middle_eq_inv in H8; auto. false H8.

  lets: IHsub1 okg H2. clear IHsub1.
  assert ((G & S) = (G & S)) by auto.
  lets: H3 H4. clear H3 H4.
  destruct H5 as (T & h1info). subst.

  lets: subtyping_ok_preservation sub1 okg.
  assert ( ok (G & T & x ~ AC_Typ s1)) by constructor~.
  lets: IHsub2 H3. clear IHsub2.
  assert( (forall a : var, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar (H & x ~ AC_Typ s1 ))).
  intros n bdn.
  lets: H2 bdn. clear H2.
  assert (x <> n). introv neq. subst. false binds_fresh_inv H5 H0.
  assert( binds n AC_Unsolved_EVar (G & T & x ~ AC_Typ s1)) by apply~ binds_push_neq.
  lets: subtyping_evar_preservation sub2 H3 H6.
  destruct H7 as [? | (m & ?)]; auto.

  lets: H4 H5. clear H4.
  assert (G & T & x ~ AC_Typ s1 = G & ( T & x ~ AC_Typ s1)) by rewrite~ concat_assoc.
  lets: H6 H4. clear H6.
  destruct H7 as (M & hinfo).

  assert (binds x (AC_Typ s1) (G & M)). rewrite <- hinfo. apply~ binds_push_eq.
  apply binds_concat_right_inv in H6.
  apply split_bind_context in H6.
  destruct H6 as (N1 & N2 & minfo). subst.
  repeat rewrite concat_assoc in hinfo.
  assert( H & x ~ AC_Typ s1 & empty = G & N1 & x ~ AC_Typ s1 & N2) by rewrite~ concat_empty_r.
  apply ok_middle_eq2 in H6; auto.
  destruct H6 as [? [? ?]]. subst. exists~ N1.
  lets: subtyping_ok_preservation sub2 H3; auto. rewrite~ concat_empty_r.
  rewrite <- hinfo. lets: subtyping_ok_preservation sub2 H3; auto.
  auto.

  (* EVARL *)
  assert (binds a AC_Unsolved_EVar (G1 & a ~ AC_Unsolved_EVar & G2)).
  apply~ binds_middle_eq. apply ok_middle_inv_r in okg; auto.
  assert (binds a AC_Unsolved_EVar (G & S)) by rewrite~ <- ginfo.
  apply binds_concat_inv in H4.

  destruct H4 as [bd_s | [notins bd_g]].
  apply split_bind_context in bd_s.
  destruct bd_s as (N1 & N2 & sinfo). subst.
  lets: resolve_forall_unsolved H0 okg H3.
  lets: resolve_forall_inserts H0 okg.
  destruct H5 as (I1 & H1info).
  subst.
  lets: resolve_forall_ok_preservation H0 okg.
  lets: unify_inserts H2 H1.
  destruct H5 as [? | ?].
  destruct H5 as (I2 & I3 & t2 & hinfo).
  repeat rewrite concat_assoc in ginfo.
  apply ok_middle_eq2 in ginfo; auto.
  destruct ginfo as [? [? ?]]. subst.
  exists~ ( N1 & I1 & I2 & a ~ AC_Solved_EVar t2 & I3).
  repeat rewrite~ concat_assoc.
  rewrite~ <- ginfo.

  destruct H5 as [? ?].
  repeat rewrite concat_assoc in ginfo.
  apply ok_middle_eq2 in ginfo; auto.
  destruct ginfo as [? [? ?]]. subst.
  exists~ ( N1 & I1 & a ~ AC_Unsolved_EVar & N2).
  repeat rewrite~ concat_assoc.
  rewrite~ <- ginfo.

  lets: resolve_forall_inserts H0 okg.
  destruct H4 as (I1 & H1info).
  subst. assert(bd_g2 := bd_g).
  apply split_bind_context in bd_g.
  destruct bd_g as (I2 & I3 & gh); subst.
  assert( G1 & a ~ AC_Unsolved_EVar & G2 = I2 & a ~ AC_Unsolved_EVar & (I3 & S)) by rewrite~ concat_assoc.
  apply ok_middle_eq2 in H1.
  destruct H1 as [? [? ?]]; subst.
  destruct H4 as (I4 & I5 & [hinfo | (t2 & hinfo)]); subst. clear ginfo.
  lets: resolve_forall_ok_preservation H0 okg.
  lets: unify_inserts H2 H1.
  destruct H4 as [? | ?].
  destruct H4 as (I4 & I5 & t2 & hinfo); subst.

  lets: hy bd_g2.
  false binds_middle_eq_inv H.
  lets: unify_ok_preservation H2 H1; auto.

  destruct H4 as [? ?]; subst.
  inversion H0; subst. exists~ S. rewrite~ concat_assoc.
  lets: resolve_forall_ok_preservation H0 okg; auto.
  rewrite <- H1.
  lets: resolve_forall_ok_preservation H0 okg; auto.

  (* EVARL *)
  admit.
  (* UNIFY *)
Admitted.

Lemma atyping_unsolved': forall G e t H m S,
    ATyping m (G & S) e t H ->
    (forall a, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H) ->
    exists I, H = G & I.
Proof.
  introv ty hy. gen_eq T : (G & S). gen S.
  induction ty; introv ginfo; auto; try(solve[exists~ S]).

  (* ANN *)
  assert (forall a : var, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H1).
  introv bd.
  assert (binds a AC_Unsolved_EVar G0). rewrite ginfo. apply~ binds_concat_left_ok. rewrite <- ginfo. apply* atyping_ok.
  lets: atyping_evar_preservation ty1 H2.
  destruct H3 as [bd_un | bd_so]. auto.
  destruct bd_so as (n & bd_so).
  lets: atyping_evar_preservation2 ty2 bd_so.
  lets: hy bd.
  lets: binds_func H3 H4. inversion H5.

  lets: IHty1 H2. clear IHty1.
  lets: H3 ginfo.
  destruct H4 as (G1 & hinfo). subst.

  clear H2 H3.
  apply ( IHty2 hy G1); auto.

  (* PI *)
  assert (forall a : var, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H1).
  introv bd.
  assert (binds a AC_Unsolved_EVar G0). rewrite ginfo. apply~ binds_concat_left_ok. rewrite <- ginfo. apply* atyping_ok.
  lets: atyping_evar_preservation ty1 H3.
  destruct H4 as [bd_un | bd_so]. auto.
  destruct bd_so as (n & bd_so).
  assert (a <> x). introv neq. subst. false binds_fresh_inv H3 H2.
  assert (binds a (AC_Solved_EVar n) (H1 & x ~ AC_Typ t1)). apply~ binds_push_neq.
  lets: atyping_evar_preservation2 ty2 H5.
  lets: hy bd.
  assert (binds a AC_Unsolved_EVar (H & x ~ (AC_Typ t1) & I)). rewrite <- concat_assoc. apply~ binds_concat_left_ok. rewrite~ concat_assoc. apply* atyping_ok_preservation.
  lets: binds_func H6 H8. inversion H9.

  lets: IHty1 H3. clear IHty1.
  lets: H4 ginfo.
  destruct H5 as (G1 & hinfo). subst.

  clear H3 H4.
  assert (forall a, binds a AC_Unsolved_EVar G ->
               binds a AC_Unsolved_EVar (H & x ~ (AC_Typ t1) & I)).
  introv bd.
  lets: hy bd.
  rewrite <- concat_assoc.
  apply~ binds_concat_left_ok.
  rewrite concat_assoc. apply* atyping_ok_preservation.
  assert (G & G1 & x ~ AC_Typ t1 = G & (G1 & x ~ AC_Typ t1)) by rewrite~ concat_assoc.
  lets: IHty2 H1 (G1 & x ~ (AC_Typ t1)) H3.
  destruct H4 as (I1 & hinfo).
  assert (x \in dom (G & I1)). rewrite <- hinfo. simpl_dom. apply union_left. apply union_right. apply in_singleton_self.
  assert (x \in dom I1). simpl_dom. rewrite in_union in H4. destruct H4 as [inv | ?]; auto. rewrite notin_union in H2. destruct H2 as [inv2 _]. lets: inv2 inv.  false.
  destruct (split_context H5) as (I2 & I3 & v & iinfo).
  subst.
  repeat rewrite concat_assoc in hinfo.
  apply ok_middle_eq2 in hinfo; auto.
  destruct hinfo as [? ? ?]. exists~ I2.
  apply* atyping_ok_preservation.
  rewrite <- hinfo. apply* atyping_ok_preservation.

  (* LAM INFER *)
  assert (forall a0 : var, binds a0 AC_Unsolved_EVar G ->
                      binds a0 AC_Unsolved_EVar (H & x ~ AC_Typ (AT_EVar a) & I)).
  introv bd. lets: hy bd. clear hy.
  assert (a0 <> x). introv neq. subst. simpl_dom. apply notin_union in H1. destruct H1 as [? ?]. false binds_fresh_inv bd H1.
  apply~ binds_weaken.
  apply~ binds_concat_left_ok.
  lets: atyping_ok_preservation ty. apply ok_remove in H5. auto.
  apply binds_concat_inv in H3.
  destruct H3 as [? | [notin bdh]]; auto.
  lets: atyping_wextctx ty.
  subst.
  assert(WExtCtx (G & S & a ~ AC_Unsolved_EVar & x ~ AC_Typ (AT_EVar a) & empty)
                 (H & x ~ AC_Typ (AT_EVar a) & I)) by rewrite~ concat_empty_r.
  apply weak_extension_order_typvar in H6.
  destruct H6 as (T1 & T2 & [hinfo [ex1 [sf ex2]]]). subst.
  apply ok_middle_eq2 in hinfo; auto.
  destruct hinfo as [? [? ?]]; subst.
  assert (a0 \in dom (G & S & a ~ AC_Unsolved_EVar)). simpl_dom. apply union_right. apply union_left. apply* get_some_inv.
  lets: weak_extension_var_preservation ex1 H.
  lets: atyping_ok_preservation ty.
  clear ty IHty.
  apply uv_ok in H8.
  apply split_bind_context in H3.
  destruct H3 as (S1 & S2 & iinfo). subst.
  rewrite iinfo in H8.
  repeat rewrite concat_assoc in H8.
  apply ok_middle_inv_l in H8. simpl_dom.
  apply notin_union in H8.
  destruct H8.
  apply notin_union in H3.
  destruct H3.
  false H3 H6.
  lets: atyping_ok_preservation ty; auto.
  rewrite <- hinfo. lets: atyping_ok_preservation ty; auto.

  apply* atyping_ok_preservation.
  subst.
  assert( G & S & a ~ AC_Unsolved_EVar & x ~ AC_Typ (AT_EVar a) = G & (S & a ~ AC_Unsolved_EVar & x ~ AC_Typ (AT_EVar a))). repeat rewrite~ concat_assoc.
  lets: IHty H3 H4.
  destruct H5 as (I1 & hinfo).
  assert (x \in dom (G & I1)). rewrite <- hinfo. simpl_dom. apply union_left. apply union_right. apply in_singleton_self.
  assert (x \in dom I1). simpl_dom. rewrite in_union in H5. destruct H5 as [inv | ?]; auto. rewrite notin_union in H1. destruct H1 as [inv2 _]. lets: inv2 inv.  false.
  destruct (split_context H6) as (I2 & I3 & v & iinfo).
  subst.
  repeat rewrite concat_assoc in hinfo.
  apply ok_middle_eq2 in hinfo; auto.
  destruct hinfo as [? ? ?]. exists~ (I2 & ACtxUV I). subst. rewrite~ concat_assoc.
  apply* atyping_ok_preservation.
  rewrite <- hinfo. apply* atyping_ok_preservation.

  (* APP *)
  assert (forall a : var, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H1).
  introv bd.
  assert (binds a AC_Unsolved_EVar G0). rewrite ginfo. apply~ binds_concat_left_ok. rewrite <- ginfo. apply* atyping_ok.
  lets: atyping_evar_preservation ty1 H2.
  destruct H3 as [bd_un | bd_so]. auto.
  destruct bd_so as (n & bd_so).
  lets: atyping_evar_preservation2 ty2 bd_so.
  lets: hy bd.
  lets: binds_func H3 H4. inversion H5.

  lets: IHty1 H2. clear IHty1.
  lets: H3 ginfo.
  destruct H4 as (G1 & hinfo). subst.

  clear H2 H3.
  apply ( IHty2 hy G1); auto.

  (* CASTDOWN *)
  lets: IHty hy ginfo. auto.

  (* FORALL *)
  assert (forall a0 : var, binds a0 AC_Unsolved_EVar G ->
                      binds a0 AC_Unsolved_EVar (H & a ~ AC_TVar & I)).
  introv bd. lets: hy bd.
  assert (a0 <> a). introv neq. subst. simpl_dom. apply notin_union in H1. destruct H1 as [? ?]. false binds_fresh_inv bd H1.
  apply~ binds_weaken.
  apply~ binds_concat_left_ok.
  lets: atyping_ok_preservation ty. apply ok_remove in H4. auto.
  apply* atyping_ok_preservation.
  subst.
  assert( G & S & a ~ AC_TVar = G & (S & a ~ AC_TVar)) by rewrite~ concat_assoc.
  lets: IHty H2 H3.
  destruct H4 as (I1 & hinfo).
  assert (a \in dom (G & I1)). rewrite <- hinfo. simpl_dom. apply union_left. apply union_right. apply in_singleton_self.
  assert (a \in dom I1). simpl_dom. rewrite in_union in H4. destruct H4 as [inv | ?]; auto. rewrite notin_union in H1. destruct H1 as [inv2 _]. lets: inv2 inv.  false.
  destruct (split_context H5) as (I2 & I3 & v & iinfo).
  subst.
  repeat rewrite concat_assoc in hinfo.
  apply ok_middle_eq2 in hinfo; auto.
  destruct hinfo as [? ? ?]. exists~ I2.
  apply* atyping_ok_preservation.
  rewrite <- hinfo. apply* atyping_ok_preservation.

  (* LAM CHECK *)
  assert (forall a0 : var, binds a0 AC_Unsolved_EVar G ->
                      binds a0 AC_Unsolved_EVar (H & x ~ AC_Typ s1 & I)).
  introv bd. lets: hy bd.
  assert (a0 <> x). introv neq. subst. simpl_dom. apply notin_union in H1. destruct H1 as [? ?]. false binds_fresh_inv bd H1.
  apply~ binds_weaken.
  apply~ binds_concat_left_ok.
  lets: atyping_ok_preservation ty. apply ok_remove in H4. auto.
  apply* atyping_ok_preservation.
  subst.
  assert(G & S & x ~ AC_Typ s1 = G & (S & x ~ AC_Typ s1)). repeat rewrite~ concat_assoc.
  lets: IHty H2 H3.
  destruct H4 as (I1 & hinfo).
  assert (x \in dom (G & I1)). rewrite <- hinfo. simpl_dom. apply union_left. apply union_right. apply in_singleton_self.
  assert (x \in dom I1). simpl_dom. rewrite in_union in H4. destruct H4 as [inv | ?]; auto. rewrite notin_union in H1. destruct H1 as [inv2 _]. lets: inv2 inv.  false.
  destruct (split_context H5) as (I2 & I3 & v & iinfo).
  subst.
  repeat rewrite concat_assoc in hinfo.
  apply ok_middle_eq2 in hinfo; auto.
  destruct hinfo as [? ? ?]. exists~ I2.
  apply* atyping_ok_preservation.
  rewrite <- hinfo. apply* atyping_ok_preservation.

  (* CASTUP *)
  lets: IHty hy ginfo. auto.

  (* Sub *)
  assert(forall a : var, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H1). introv bd.
  assert (binds a AC_Unsolved_EVar G0). rewrite ginfo. apply~ binds_concat_left_ok. rewrite <- ginfo. apply* atyping_ok.
  lets: atyping_evar_preservation ty H2.
  destruct H3 as [bd_un | bd_so]. auto.
  destruct bd_so as (n & bd_so).
  lets: subtyping_evar_preservation2 H0 bd_so.
  apply* atyping_ok_preservation.
  lets: hy bd.
  lets: binds_func H3 H4. inversion H5.

  lets: IHty H2. clear IHty.
  lets: H3 ginfo.
  destruct H4 as (G1 & hinfo). subst.

  clear H2.
  lets: subtyping_unsolved H0 hy. auto.

  (* APP PI *)
  lets: IHty hy ginfo. auto.

  (* APP EVAR *)
  assert(binds a AC_Unsolved_EVar (G & S)).
  rewrite <- ginfo. apply~ binds_middle_eq. apply awf_is_ok in H0. apply ok_middle_inv_r in H0; auto.
  destruct (binds_concat_inv H2) as  [? | ?]; clear H2.
  destruct (split_bind_context H3) as (I1 & I2 & sinfo). subst.
  repeat rewrite concat_assoc in ginfo.
  apply ok_middle_eq2 in ginfo; auto.
  destruct ginfo as [? ? ?]. subst.
  assert(G & I1 & a2 ~ AC_Unsolved_EVar & a1 ~ AC_Unsolved_EVar & a ~ AC_Solved_EVar (AT_Expr (AE_Pi (AT_EVar a1) (AT_EVar a2))) & G2 =
         G & (I1 & a2 ~ AC_Unsolved_EVar & a1 ~ AC_Unsolved_EVar & a ~ AC_Solved_EVar (AT_Expr (AE_Pi (AT_EVar a1) (AT_EVar a2))) & G2)) by repeat rewrite~ concat_assoc.
  lets: IHty hy H2. auto.
  rewrite <- ginfo. apply* awf_is_ok.
  destruct H3 as [_ H3].
  lets: hy H3.
  assert (binds a (AC_Solved_EVar (AT_Expr (AE_Pi (AT_EVar a1) (AT_EVar a2)))) H).
  apply* atyping_evar_preservation2.
  apply~ binds_middle_eq. apply awf_is_ok in H0. apply ok_middle_inv_r in H0. auto.
  lets: binds_func H2 H4. inversion H5.

  (* APP FORALL *)
  assert(G0 & a ~ AC_Unsolved_EVar = G & (S & a ~ AC_Unsolved_EVar)). rewrite ginfo. repeat rewrite~ concat_assoc.
  lets: IHty hy H2. auto.
Qed.

Lemma atyping_unsolved: forall G e t H m,
    ATyping m G e t H ->
    (forall a, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H) ->
    exists I, H = G & I.
Proof.
  introv ty hy.
  assert (ATyping m (G & empty) e t H) by rewrite~ concat_empty_r.
  apply* atyping_unsolved'.
Qed.

Lemma awftyp_eq : forall G e,
    AWfTyp G e <->
    (exists H, ATyping Chk G e (AT_Expr AE_Star) H /\
     forall a, binds a AC_Unsolved_EVar G -> binds a AC_Unsolved_EVar H).
Proof.
  introv. split.

  (* LEFT *)
  introv wf.
  inversion wf; subst.
  exists (G & H). split~.
  introv bd. apply~ binds_concat_left_ok.
  apply* atyping_ok_preservation.

  (* RIGHT *)
  introv H.
  destruct H as (H & [ty bd]).
  lets: atyping_unsolved ty bd.
  destruct H0 as (I & hinfo). subst.
  apply AWf_Expr with I; auto.
Qed.
