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

Lemma weak_extension_weakening_awtermt : forall G H a,
    AWTermT G a ->
    WExtCtx G H ->
    AWTermT H a.
Proof.
  introv ga gh. assert (wf: ok H). apply* weak_extension_ok_preservation.
  gen H.
  induction ga; introv gh wf; auto; try(apply split_bind_context in H; destruct H as (G1 & G2 & gi); rewrite gi in gh).
  apply weak_extension_order_var in gh. destruct gh as (H1 & H2 & [hi _]).
  rewrite hi. constructor*.
  apply* binds_middle_eq.
  rewrite hi in wf. apply* ok_middle_inv_r.

  apply weak_extension_order_typvar in gh. destruct gh as (H1 & H2  & [hi _]).
  rewrite hi. apply* AWTermT_TypVar.
  apply* binds_middle_eq.
  rewrite hi in wf. apply* ok_middle_inv_r.

  apply AWTermT_Lam with (L:=L \u dom H1 \u dom G). introv notin. apply* H0.
  apply~ WExtCtx_Var.

  apply AWTermT_Pi with (L:=L \u dom H1 \u dom G). apply* IHga.
  intros. apply* H0. apply~ WExtCtx_Var.

  apply AWTermT_Forall with (L:=L \u dom H1 \u dom G).
  intros. apply* H0.
  apply~ WExtCtx_TVar.


  apply weak_extension_order_tvar in gh. destruct gh as (H1 & H2 & [hi _]).
  rewrite hi. apply* AWTermT_TFVar.
  apply* binds_middle_eq.
  rewrite hi in wf. apply* ok_middle_inv_r.

  apply weak_extension_order_unsolved_evar in gh. destruct gh as (H1 & H2 & [hi _]).
  destruct hi as [hi1 | (t & hi1)];
    try(rewrite hi1);
    [apply* AWTermT_Unsolved_EVar | apply* AWTermT_Solved_EVar];
    try(rewrite hi1 in wf; apply* binds_middle_eq);try(apply* ok_middle_inv_r).

  apply weak_extension_order_solved_evar in gh. destruct gh as (H1 & H2 & [hi _]).
  rewrite hi. apply* AWTermT_Solved_EVar.
  rewrite hi in wf. apply* binds_middle_eq.
  apply* ok_middle_inv_r.
Qed.

Set Implicit Arguments.

Lemma weak_declaration_order_preservation : forall G I G1 G2 G3 x y xv1 yv1,
    WExtCtx G I ->
    G = G1 & x ~ xv1 & G2 & y ~ yv1 & G3 ->
    exists xv2 yv2 I1 I2 I3, I = I1 & x ~ xv2 & I2 & y ~ yv2 & I3.
Proof.
  introv HE HG.
  gen G1 G2 G3 x y xv1 yv1.
  assert (ok G). apply* weak_extension_ok.
  induction HE; intros* HG.
  (* ExtCtx_Empty *)
  eapply empty_middle_inv in HG. inversion HG.

  (* ExtCtx_Var  *)
  assert (x0 <> y).  rewrite HG in H. apply (ok_non_eq H).
  destruct (eq_var_dec x y); subst.
  assert (x0 \in (dom (G & y ~ AC_Var))). rewrite HG. simpl_dom. apply union_left. apply union_left. apply union_left. apply union_right. apply in_singleton_self.
  assert (x0 \in (dom G)). simpl_dom . rewrite in_union in H4. destruct H4 as [H11 | H12]. rewrite in_singleton in H11. apply H3 in H11. inversion H11. auto.
  apply (weak_extension_var_preservation G H0 x0 HE) in H5.
  apply split_context in H5. destruct H5 as (G1' & G2' & v' & H4'); subst.
  exists v' AC_Var G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & x ~ AC_Var). apply (tail_exists_eq n) in HG. auto.
  inversion H4. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (weak_extension_ok G H0 HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I4 & I5 & I3 & HGG').
  subst.
  exists* xv2 yv2 I4 I5 (I3 & x ~ AC_Var). rewrite* concat_assoc.

  (* ExtCtx_TypVar  *)
  assert (x0 <> y).  rewrite HG in H. apply (ok_non_eq H).
  destruct (eq_var_dec x y); subst.
  assert (x0 \in (dom (G & y ~ AC_Typ t))). rewrite HG. simpl_dom. apply union_left. apply union_left. apply union_left. apply union_right. apply in_singleton_self.
  assert (x0 \in (dom G)). simpl_dom . rewrite in_union in H4. destruct H4 as [H11 | H12]. rewrite in_singleton in H11. apply H3 in H11. inversion H11. auto.
  apply (weak_extension_var_preservation G H0 x0 HE) in H5.
  apply split_context in H5. destruct H5 as (G1' & G2' & v' & H5'); subst.
  exists v' (AC_Typ t) G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & x ~ AC_Typ t). apply (tail_exists_eq n) in HG. auto.
  inversion H4. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (weak_extension_ok G H0 HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I4 & I5 & I6 & HGG').
  subst.
  exists* xv2 yv2 I4 I5 (I6 & x ~ AC_Typ t). rewrite* concat_assoc.

  (* ExtCtx_TVar *)
  assert (x <> y).  rewrite HG in H. apply (ok_non_eq H).
  destruct (eq_var_dec a y); subst.
  assert (x \in (dom (G & y ~ AC_TVar))). rewrite HG. simpl_dom. apply union_left. apply union_left. apply union_left. apply union_right. apply in_singleton_self.
  assert (x \in (dom G)). simpl_dom . rewrite in_union in H4. destruct H4 as [H11 | H12]. rewrite in_singleton in H11. apply H3 in H11. inversion H11. auto.
  apply (weak_extension_var_preservation G H0 x HE) in H5.
  apply split_context in H5. destruct H5 as (G1' & G2' & v' & H6'); subst.
  exists v' (AC_TVar) G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & a ~ AC_TVar). apply (tail_exists_eq n) in HG. auto.
  inversion H4. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (weak_extension_ok G H0 HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I4 & I5 & I3 & HGG').
  subst.
  exists* xv2 yv2 I4 I5 (I3 & a ~ AC_TVar). rewrite* concat_assoc.

  (* Marker *)
  assert (x <> y).  rewrite HG in H. apply (ok_non_eq H).
  destruct (eq_var_dec a y); subst.
  assert (x \in (dom (G & y ~ AC_Marker))). rewrite HG. simpl_dom. apply union_left. apply union_left. apply union_left. apply union_right. apply in_singleton_self.
  assert (x \in (dom G)). simpl_dom . rewrite in_union in H4. destruct H4 as [H11 | H12]. rewrite in_singleton in H11. apply H3 in H11. inversion H11. auto.
  apply (weak_extension_var_preservation G H0 x HE) in H5.
  apply split_context in H5. destruct H5 as (G1' & G2' & v' & H6'); subst.
  exists v' (AC_Marker) G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & a ~ AC_Marker). apply (tail_exists_eq n) in HG. auto.
  inversion H4. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (weak_extension_ok G H0 HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I4 & I5 & I3 & HGG').
  subst.
  exists* xv2 yv2 I4 I5 (I3 & a ~ AC_Marker). rewrite* concat_assoc.

  (* ExtCtx_EVar *)
  assert (x <> y).  rewrite HG in H. apply (ok_non_eq H).
  destruct (eq_var_dec a y); subst.
  assert (x \in (dom (G & y ~ AC_Unsolved_EVar))). rewrite HG. simpl_dom. apply union_left. apply union_left. apply union_left. apply union_right. apply in_singleton_self.
  assert (x \in (dom G)). simpl_dom . rewrite in_union in H4. destruct H4 as [H11 | H12]. rewrite in_singleton in H11. apply H3 in H11. inversion H11. auto.
  apply (weak_extension_var_preservation G H0 x HE) in H5.
  apply split_context in H5. destruct H5 as (G1' & G2' & v' & H4'); subst.
  exists v' AC_Unsolved_EVar G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & a ~ AC_Unsolved_EVar). apply (tail_exists_eq n) in HG. auto.
  inversion H4. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (weak_extension_ok G H0 HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I4 & I5 & I6 & HGG').
  subst.
  exists* xv2 yv2 I4 I5 (I6 & a ~ AC_Unsolved_EVar). rewrite* concat_assoc.

  (* ExtCtx_SolvedEVar *)
  assert (x <> y).  rewrite HG in H. apply (ok_non_eq H).
  destruct (eq_var_dec a y); subst.
  assert (x \in (dom (G & y ~ AC_Solved_EVar t))). rewrite HG. simpl_dom. apply union_left. apply union_left. apply union_left. apply union_right. apply in_singleton_self.
  assert (x \in (dom G)). simpl_dom . rewrite in_union in H4. destruct H4 as [H11 | H12]. rewrite in_singleton in H11. apply H3 in H11. inversion H11. auto.
  apply (weak_extension_var_preservation G H0 x HE) in H5.
  apply split_context in H5. destruct H5 as (G1' & G2' & v' & H5'); subst.
  exists v' (AC_Solved_EVar t) G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & a ~ AC_Solved_EVar t). apply (tail_exists_eq n) in HG. auto.
  inversion H4. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (weak_extension_ok G H0 HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I4 & I5 & I6 & HGG').
  subst.
  exists* xv2 yv2 I4 I5 (I6 & a ~ AC_Solved_EVar t). rewrite* concat_assoc.

  (* ExtCtx_Solve *)
  assert (x <> y).  rewrite HG in H. apply (ok_non_eq H).
  destruct (eq_var_dec a y); subst.
  assert (x \in (dom (G & y ~ AC_Unsolved_EVar))). rewrite HG. simpl_dom. apply union_left. apply union_left. apply union_left. apply union_right. apply in_singleton_self.
  assert (x \in (dom G)). simpl_dom . rewrite in_union in H4. destruct H4 as [H11 | H12]. rewrite in_singleton in H11. apply H3 in H11. inversion H11. auto.
  apply (weak_extension_var_preservation G H0 x HE) in H5.
  apply split_context in H5. destruct H5 as (G1' & G2' & v' & H5'); subst.
  exists v' (AC_Solved_EVar t) G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & a ~ AC_Unsolved_EVar). apply (tail_exists_eq n) in HG. auto.
  inversion H4. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (weak_extension_ok G H0 HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I4 & I5 & I6 & HGG').
  subst.
  exists* xv2 yv2 I4 I5 (I6 & a ~ AC_Solved_EVar t). rewrite* concat_assoc.

  (* ExtCtx_Add *)
  assert (x <> y).  rewrite HG in H. apply (ok_non_eq H).
  apply (IHHE H) in HG.
  destruct HG as (xv2 & yv2 & I1 & I2 & I3 & HH0); subst.
  exists* xv2 yv2 I1 I2 (I3 & a ~ AC_Unsolved_EVar).
  rewrite* concat_assoc.

  (* ExtCtx_AddSolved *)
  assert (x <> y).  rewrite HG in H. apply (ok_non_eq H).
  apply (IHHE H) in HG.
  destruct HG as (xv2 & yv2 & I1 & I2 & I3 & HH0); subst.
  exists* xv2 yv2 I1 I2 (I3 & a ~ AC_Solved_EVar t).
  rewrite* concat_assoc.
Qed.

Lemma weak_extentension_reverse_var_preservation: forall G I x,
    WExtCtx G I ->
    binds x AC_Var I ->
    binds x AC_Var G.
Proof.
  introv ex bd.
  induction ex; auto;
    try(destruct (binds_push_inv bd);
        destruct H2;
        [solve[false H3] |
         lets: IHex H3; apply~ binds_push_neq]).

  destruct (binds_push_inv bd).
  destruct H2. subst. apply~ binds_push_eq.
  destruct H2. lets: IHex H3. apply~ binds_push_neq.

  destruct (binds_push_inv bd).
  destruct H1. false H2.
  destruct H1. lets: IHex H2. auto.

  destruct (binds_push_inv bd).
  destruct H1. false H2.
  destruct H1. lets: IHex H2. auto.
Qed.

Lemma weak_extentension_reverse_typvar_preservation: forall G I x t,
    WExtCtx G I ->
    binds x (AC_Typ t) I ->
    binds x (AC_Typ t) G.
Proof.
  introv ex bd.
  induction ex; auto;
    try(destruct (binds_push_inv bd);
        destruct H2;
        [solve[false H3] |
         lets: IHex H3; apply~ binds_push_neq]).

  destruct (binds_push_inv bd).
  destruct H2. inversion H3. subst. apply~ binds_push_eq.
  destruct H2. lets: IHex H3. apply~ binds_push_neq.

  destruct (binds_push_inv bd).
  destruct H1. false H2.
  destruct H1. lets: IHex H2. auto.

  destruct (binds_push_inv bd).
  destruct H1. false H2.
  destruct H1. lets: IHex H2. auto.
Qed.

Lemma weak_extentension_reverse_tvar_preservation: forall G I x,
    WExtCtx G I ->
    binds x AC_TVar I ->
    binds x AC_TVar G.
Proof.
  introv ex bd.
  induction ex; auto;
    try(destruct (binds_push_inv bd);
        destruct H2;
        [solve[false H3] |
         lets: IHex H3; apply~ binds_push_neq]).

  destruct (binds_push_inv bd).
  destruct H2. subst. apply~ binds_push_eq.
  destruct H2. lets: IHex H3. apply~ binds_push_neq.

  destruct (binds_push_inv bd).
  destruct H1. false H2.
  destruct H1. lets: IHex H2. auto.

  destruct (binds_push_inv bd).
  destruct H1. false H2.
  destruct H1. lets: IHex H2. auto.
Qed.

Lemma weak_extentension_reverse_marker_preservation: forall G I x,
    WExtCtx G I ->
    binds x AC_Marker I ->
    binds x AC_Marker G.
Proof.
  introv ex bd.
  induction ex; auto;
    try(destruct (binds_push_inv bd);
        destruct H2;
        [solve[false H3] |
         lets: IHex H3; apply~ binds_push_neq]).

  destruct (binds_push_inv bd).
  destruct H2. subst. apply~ binds_push_eq.
  destruct H2. lets: IHex H3. apply~ binds_push_neq.

  destruct (binds_push_inv bd).
  destruct H1. false H2.
  destruct H1. lets: IHex H2. auto.

  destruct (binds_push_inv bd).
  destruct H1. false H2.
  destruct H1. lets: IHex H2. auto.
Qed.
