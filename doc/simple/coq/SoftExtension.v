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
Require Import AWt.

(***********************)
(* SOFT EXTENSION *)
(***********************)

Inductive SExtCtx : ACtx -> ACtx -> Prop :=
  | SExtCtx_Empty: SExtCtx empty empty
  | SExtCtx_Var : forall G H x,
      SExtCtx G H ->
      x # G -> x # H ->
      SExtCtx (G & x ~ AC_Var) (H & x ~ AC_Var)
  | SExtCtx_TypVar : forall G H x t,
      SExtCtx G H ->
      x # G -> x # H ->
      AWTermT G t ->
      SExtCtx (G & x ~ AC_Typ t) (H & x ~ AC_Typ t)
  | SExtCtx_TVar : forall G H a,
      SExtCtx G H ->
      a # G -> a # H ->
      SExtCtx (G & a ~ AC_TVar) (H & a ~ AC_TVar)
  | SExtCtx_Marker : forall G H a,
      SExtCtx G H ->
      a # G -> a # H ->
      SExtCtx (G & a ~ AC_Marker) (H & a ~ AC_Marker)
  | SExtCtx_EVar : forall G H a,
      SExtCtx G H ->
      a # G -> a # H ->
      SExtCtx (G & a ~ AC_Unsolved_EVar) (H & a ~ AC_Unsolved_EVar)
  | SExtCtx_SolvedEVar: forall G H a t,
      SExtCtx G H ->
      a # G -> a # H ->
      AWTermT G t ->
      SExtCtx (G & a ~ AC_Solved_EVar t) (H & a ~ AC_Solved_EVar t)
  | SExtCtx_Solve : forall G H a t,
      SExtCtx G H ->
      a # G -> a # H ->
      AWTermT H t ->
      SExtCtx (G & a ~ AC_Unsolved_EVar) (H & a ~ AC_Solved_EVar t)
  | SExtCtx_Add : forall G H a,
      SExtCtx G H ->
      a # H ->
      SExtCtx G (H & a ~ AC_Unsolved_EVar)
  | SExtCtx_AddSolved: forall G H a t,
      SExtCtx G H ->
      a # H ->
      AWTermT H t ->
      SExtCtx G (H & a ~ AC_Solved_EVar t)
.

Lemma soft_extension_var_preservation: forall G H x,
    SExtCtx G H ->
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

Lemma soft_extension_ok: forall G H,
    SExtCtx G H ->
    ok G.
Proof.
  introv ex. induction ex; auto.
Qed.

Lemma soft_extension_awt: forall G H,
    SExtCtx G H ->
    AWt G.
Proof.
  introv ex. induction ex; auto.
Qed.

Lemma soft_extension_ok_preservation: forall G H,
    SExtCtx G H ->
    ok H.
Proof.
  introv ex.
  induction ex; auto.
Qed.

Lemma soft_extension_reflexicity: forall G,
    AWt G ->
    SExtCtx G G.
Proof.
  introv okg.
  induction G using env_ind.
  apply SExtCtx_Empty.
  assert (x # G).
  apply awt_is_ok in okg. destruct (ok_push_inv okg). auto.
  induction v.
  apply~ SExtCtx_Var. apply* IHG.
  apply~ SExtCtx_TypVar. apply* IHG.
  lets: awtermt_awt' okg. auto.
  apply~ SExtCtx_TVar. apply* IHG.
  apply~ SExtCtx_EVar.  apply* IHG.
  apply~ SExtCtx_SolvedEVar. apply* IHG.
  lets: awtermt_awt_solved_evar' okg. auto.
  apply~ SExtCtx_Marker.  apply* IHG.
Qed.

Lemma soft_extension_append_soft: forall G H I,
    SExtCtx G H ->
    Softness I ->
    AWt (H & I) ->
    SExtCtx G (H & I).
Proof.
  introv ex sf wfhi.
  induction I using env_ind.
  repeat rewrite concat_empty_r in *. auto.
  repeat rewrite concat_assoc in *. auto.
  inversion sf.
  false empty_push_inv H1.
  apply eq_push_inv in H0.  destruct H0 as [? [? ?]]. subst.
  apply~ SExtCtx_Add. apply* IHI.
  lets: awt_is_ok wfhi. destruct (ok_push_inv H0). auto.
  apply eq_push_inv in H0.  destruct H0 as [? [? ?]]. subst.
  apply~ SExtCtx_AddSolved. apply* IHI.
  lets: awt_is_ok wfhi. destruct (ok_push_inv H0). auto.
  lets: awtermt_awt_solved_evar' wfhi. auto.
Qed.

Lemma soft_extension_append: forall G H I,
    SExtCtx G H ->
    AWt (G & I) ->
    AWt (H & I) ->
    SExtCtx (G & I) (H & I).
Proof.
  introv ex wfgi wfhi.
  induction I using env_ind.
  repeat rewrite concat_empty_r in *. auto.
  repeat rewrite concat_assoc in *. auto.
  lets: awt_is_ok wfgi. destruct (ok_push_inv H0). auto.
  lets: awt_is_ok wfhi. destruct (ok_push_inv H3). auto.
  induction v; auto.
  apply~ SExtCtx_Var. apply* IHI.
  apply~ SExtCtx_TypVar. apply* IHI.
  lets: awtermt_awt' wfgi. auto.
  apply~ SExtCtx_TVar. apply* IHI.
  apply~ SExtCtx_EVar.  apply* IHI.
  apply~ SExtCtx_SolvedEVar. apply* IHI.
  lets: awtermt_awt_solved_evar' wfgi. auto.
  apply~ SExtCtx_Marker.  apply* IHI.
Qed.

Hint Resolve awt_is_ok.
Lemma soft_extension_append_ex: forall G H I S,
    SExtCtx G H ->
    SExtCtx I S ->
    AWt (G & I) ->
    AWt (H & S) ->
    SExtCtx (G & I) (H & S).
Proof.
  introv GH IS okgi okhs.
  induction IS.
  repeat rewrite concat_empty_r in *. auto.
  repeat rewrite concat_assoc in *.
  assert (AWt (G & G0)) by auto_star.
  assert (AWt (H & H0)) by auto_star.
  lets: IHIS H3 H4.
  apply~ SExtCtx_Var. apply* ok_push_inv.  apply* ok_push_inv.

  repeat rewrite concat_assoc in *.
  assert (AWt (G & G0)) by auto_star.
  assert (AWt (H & H0)) by auto_star.
  lets: IHIS H4 H5.
  apply~ SExtCtx_TypVar. apply* ok_push_inv.  apply* ok_push_inv.
  lets: awtermt_awt' okgi. auto.

  repeat rewrite concat_assoc in *.
  assert (AWt (G & G0)) by auto_star.
  assert (AWt (H & H0)) by auto_star.
  lets: IHIS H3 H4.
  apply~ SExtCtx_TVar. apply* ok_push_inv.  apply* ok_push_inv.

  repeat rewrite concat_assoc in *.
  assert (AWt (G & G0)) by auto_star.
  assert (AWt (H & H0)) by auto_star.
  lets: IHIS H3 H4.
  apply~ SExtCtx_Marker. apply* ok_push_inv.  apply* ok_push_inv.

  repeat rewrite concat_assoc in *.
  assert (AWt (G & G0)) by auto_star.
  assert (AWt (H & H0)) by auto_star.
  lets: IHIS H3 H4.
  apply~ SExtCtx_EVar. apply* ok_push_inv.  apply* ok_push_inv.

  repeat rewrite concat_assoc in *.
  assert (AWt (G & G0)) by auto_star.
  assert (AWt (H & H0)) by auto_star.
  lets: IHIS H4 H5.
  apply~ SExtCtx_SolvedEVar. apply* ok_push_inv.  apply* ok_push_inv.
  lets: awtermt_awt_solved_evar' okgi. auto.

  repeat rewrite concat_assoc in *.
  assert (AWt (G & G0)) by auto_star.
  assert (AWt (H & H0)) by auto_star.
  lets: IHIS H4 H5.
  apply~ SExtCtx_Solve. apply* ok_push_inv.  apply* ok_push_inv.
  lets: awtermt_awt_solved_evar' okhs. auto.

  repeat rewrite concat_assoc in *.
  assert (AWt (H & H0)) by auto_star.
  lets: IHIS okgi H2.
  apply~ SExtCtx_Add. apply* ok_push_inv.

  repeat rewrite concat_assoc in *.
  assert (AWt (H & H0)) by auto_star.
  lets: IHIS okgi H3.
  apply~ SExtCtx_AddSolved. apply* ok_push_inv.
  lets: awtermt_awt_solved_evar' okhs. auto.
Qed.

Lemma soft_extension_order_unsolved_evar : forall G1 G2 H x,
    SExtCtx (G1 & x ~ AC_Unsolved_EVar & G2) H ->
    exists H1 H2, (H = H1 & x ~ AC_Unsolved_EVar & H2 \/ exists t, H = H1 & x ~ AC_Solved_EVar t & H2) /\ SExtCtx G1 H1 /\ (Softness G2 -> Softness H2).
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Unsolved_EVar & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2 ]]).
  exists* H4 (H5 & x0 ~ AC_Var). split; auto.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t. rewrite HH2. rewrite* concat_assoc.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [eqa [eqv eqg]]. inversion eqv.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t) (G & x0 ~ AC_Typ t)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & [HH [EXG1H1 SoftG3H2]]).
  exists* H3 (H4 & x0 ~ AC_Typ t). split; auto.
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t1. rewrite HH2. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H5. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6.

  (* AC_TVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_TVar (G & a ~ AC_TVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 EXG3H5]]).
  exists* H4 (H5 & a ~ AC_TVar). split; auto.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t. rewrite HH2. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.

  (* AC_Marker *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Marker (G & a ~ AC_Marker)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Marker). split; auto.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t. rewrite HH2. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  exists* H (empty: ACtx). split. rewrite* concat_empty_r.
  split. symmetry in IG. apply tail_empty_eq2 in IG; auto.
  destruct IG as [IG _]. subst. auto.
  rewrite IG. constructor. apply soft_extension_ok in EX; auto. auto.
  constructor. apply soft_extension_ok in EX. auto. auto.
  constructor.

  assert (IG2 := IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3 := IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H11 & H2 & [HH [EXG1H1 SoftG3H2]]).
  exists* H11 (H2 & a ~ AC_Unsolved_EVar). split; auto.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t. rewrite HH2. rewrite concat_assoc. auto.
  split; auto.
  intros. constructor. apply* SoftG3H2. rewrite HG2 in H3. inversion H3. apply empty_push_inv in H5. inversion H5. apply eq_push_inv in H4. destruct H4 as [eqa [_ eqg]]. rewrite eqg in H5. auto. apply eq_push_inv in H4. destruct H4 as [_ [eqv _]]. inversion eqv.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1 in H1. auto. rewrite HH2 in H1. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t) (G & a ~ AC_Solved_EVar t)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor~. apply* soft_extension_ok.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t1. rewrite HH2. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption.
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1 in H1. auto.
  rewrite HH2 in H1. auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  exists* H (empty: ACtx).
  split. right. exists t. rewrite concat_empty_r. auto.
  split. apply tail_empty_eq with (G0:= G & a ~ AC_Unsolved_EVar) (G3 := G) (I := G1 & a ~ AC_Unsolved_EVar & G2) (I1:= G1) (I2:=G2) (x:=a) (vx:=AC_Unsolved_EVar) (vy:=AC_Unsolved_EVar)in IG; auto.
  destruct IG as [IG _]. subst. auto.
  rewrite <- IG. constructor. apply* soft_extension_ok. auto.
  constructor. apply* soft_extension_ok. auto.
  constructor.

  assert (IG2 := IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3 := IG). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & [HH [EXG1H1 SoftG3H2]]).
  exists* H3 (H4 & a ~ AC_Solved_EVar t). split; auto.
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t1. rewrite HH2. rewrite concat_assoc. auto.
  split; auto.
  intros. constructor. apply* SoftG3H2. rewrite HG2 in H5. inversion H5. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [eqa [_ eqg]]. rewrite eqg in H7. auto. apply eq_push_inv in H6. destruct H6 as [_ [eqv _]]. inversion eqv.
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1 in H1. auto.
  rewrite HH2 in H1. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar).
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1. split. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH1 in H0. auto.

  split. right. exists t1. rewrite HH2. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH2 in H0.  auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t).

  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1. split. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH1 in H0. auto.

  split. right. exists t1. rewrite HH2. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH2 in H0. auto.
Qed.

Lemma soft_extension_order_tvar : forall G1 G2 H x,
    SExtCtx (G1 & x ~ AC_TVar & G2) H ->
    exists H1 H2, H = H1 & x ~ AC_TVar & H2 /\ SExtCtx G1 H1 /\ (Softness G2 -> Softness H2).
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_TVar & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & x0 ~ AC_Var). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [eqa [eqv eqg]]. inversion eqv.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t) (G & x0 ~ AC_Typ t)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & [HH [EXG1H1 SoftG3H2]]).
  exists* H3 (H4 & x0 ~ AC_Typ t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H5. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6.

  (* AC_TVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_TVar (G & a ~ AC_TVar)).
  apply* binds_push_eq. exists~ H (empty:ACtx). repeat rewrite concat_empty_r.
  symmetry in IG. apply tail_empty_eq2 in IG; auto.
  destruct IG as [IG [_ IG2]]. subst. split; auto.
  rewrite IG. constructor. apply soft_extension_ok in EX; auto. auto.
  constructor. apply soft_extension_ok in EX; auto. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_TVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.

  (* AC_Marker *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Marker (G & a ~ AC_Marker)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Marker). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t) (G & a ~ AC_Solved_EVar t)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor~. apply* soft_extension_ok.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption.
  rewrite HH in H1. auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar).
  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t).

  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto.  intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.
Qed.

Lemma soft_extension_order_var : forall G1 G2 H x,
    SExtCtx (G1 & x ~ AC_Var & G2) H ->
    exists H1 H2, H = H1 & x ~ AC_Var & H2 /\ SExtCtx G1 H1 /\ (Softness G2 -> Softness H2).
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Var & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. exists~ H (empty:ACtx). repeat rewrite concat_empty_r.
  symmetry in IG. apply tail_empty_eq2 in IG; auto.
  destruct IG as [IG [_ IG2]]. subst. split; auto.
  rewrite IG. constructor. apply soft_extension_ok in EX; auto. auto.
  constructor. apply soft_extension_ok in EX; auto. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & x0 ~ AC_Var). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t) (G & x0 ~ AC_Typ t)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & [HH [EXG1H1 SoftG3H2]]).
  exists* H3 (H4 & x0 ~ AC_Typ t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H5. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6.

  (* AC_TVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_TVar (G & a ~ AC_TVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_TVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.

  (* AC_Marker *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Marker (G & a ~ AC_Marker)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Marker). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t) (G & a ~ AC_Solved_EVar t)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor~. apply* soft_extension_ok.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption.
  rewrite HH in H1. auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar).
  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t).

  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.
Qed.

Lemma soft_extension_order_solved_evar : forall G1 G2 H x t,
    SExtCtx (G1 & x ~ AC_Solved_EVar t & G2) H ->
    exists H1 H2, H = H1 & x ~ AC_Solved_EVar t & H2 /\ SExtCtx G1 H1 /\ (Softness G2 -> Softness H2).
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Solved_EVar t & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & x0 ~ AC_Var). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [eqa [eqv eqg]]. inversion eqv.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t0) (G & x0 ~ AC_Typ t0)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & [HH [EXG1H1 SoftG3H2]]).
  exists* H3 (H4 & x0 ~ AC_Typ t0). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H5. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6.

  (* AC_TVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_TVar (G & a ~ AC_TVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_TVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.

  (* AC_Marker *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Marker (G & a ~ AC_Marker)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Marker). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t0) (G & a ~ AC_Solved_EVar t0)).
  apply* binds_push_eq. exists~ H (empty:ACtx). repeat rewrite concat_empty_r.
  symmetry in IG. apply tail_empty_eq2 in IG; auto.
  destruct IG as [IG [eqv IG2]]. inversion eqv. subst. split; auto.
  rewrite IG. constructor. apply soft_extension_ok in EX; auto. auto.
  constructor. apply soft_extension_ok in EX; auto. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t0). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption.
  rewrite HH in H1. auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t0). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar).
  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t0).

  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto.  auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.
Qed.

Lemma soft_extension_order_typvar : forall G1 G2 H x t,
    SExtCtx (G1 & x ~ AC_Typ t & G2) H ->
    exists H1 H2, H = H1 & x ~ AC_Typ t & H2 /\ SExtCtx G1 H1 /\ (Softness G2 -> Softness H2).
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Typ t & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & x0 ~ AC_Var). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [eqa [eqv eqg]]. inversion eqv.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t0) (G & x0 ~ AC_Typ t0)).
  apply* binds_push_eq. exists~ H (empty:ACtx). repeat rewrite concat_empty_r.
  symmetry in IG. apply tail_empty_eq2 in IG; auto.
  destruct IG as [IG [eqv IG2]]. inversion eqv. subst. split; auto.
  rewrite IG. constructor. apply soft_extension_ok in EX; auto. auto.
  constructor. apply soft_extension_ok in EX; auto. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & [HH [EXG1H1 SoftG3H2]]).
  exists* H3 (H4 & x0 ~ AC_Typ t0). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H5. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6.

  (* AC_TVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_TVar (G & a ~ AC_TVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_TVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.

  (* AC_Marker *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Marker (G & a ~ AC_Marker)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Marker). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t0) (G & a ~ AC_Solved_EVar t0)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor~. apply* soft_extension_ok.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t0). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption.
  rewrite HH in H1. auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t0). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar).
  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t0).

  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto.  intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.
Qed.

Lemma soft_extension_order_marker : forall G1 G2 H x,
    SExtCtx (G1 & x ~ AC_Marker & G2) H ->
    exists H1 H2, H = H1 & x ~ AC_Marker & H2 /\ SExtCtx G1 H1 /\ (Softness G2 -> Softness H2).
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Marker & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & x0 ~ AC_Var). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [eqa [eqv eqg]]. inversion eqv.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t) (G & x0 ~ AC_Typ t)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & [HH [EXG1H1 SoftG3H2]]).
  exists* H3 (H4 & x0 ~ AC_Typ t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H5. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6.

  (* AC_TVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_TVar (G & a ~ AC_TVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_TVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.

  (* AC_Marker *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Marker (G & a ~ AC_Marker)).
  apply* binds_push_eq. exists~ H (empty:ACtx). repeat rewrite concat_empty_r.
  symmetry in IG. apply tail_empty_eq2 in IG; auto.
  destruct IG as [IG [_ IG2]]. subst. split; auto.
  rewrite IG. constructor. apply soft_extension_ok in EX; auto. auto.
  constructor. apply soft_extension_ok in EX; auto. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Marker). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3. apply eq_push_inv in H3. destruct H3 as [_ [H3 _]]. inversion H3.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t) (G & a ~ AC_Solved_EVar t)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor~. apply* soft_extension_ok.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption.
  rewrite HH in H1. auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Unsolved_EVar (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* soft_extension_ok. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2).
  assert (IG3:=IG).
  rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv.
  rewrite HH in H1. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar).
  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto.  intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t).

  rewrite HH. split. rewrite concat_assoc. auto.
  split. auto.  intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. auto.
Qed.

Lemma soft_extension_remove_var: forall G H x,
    SExtCtx (G & x ~ AC_Var) (H & x ~ AC_Var) ->
    SExtCtx G H.
Proof.
  introv ex.
  inversion ex;
  try(apply eq_push_inv in H1; destruct H1 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H2; inversion H2.
  subst. clear EQV.
  apply eq_push_inv in H2. destruct H2 as [? [? ?]]. subst~.
Qed.

Lemma soft_extension_remove_typvar: forall G H x t,
    SExtCtx (G & x ~ AC_Typ t) (H & x ~ AC_Typ t) ->
    SExtCtx G H.
Proof.
  introv ex.
  inversion ex;
  try(apply eq_push_inv in H1; destruct H1 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H2; inversion H2.
  subst. clear EQV.
  apply eq_push_inv in H2. destruct H2 as [? [? ?]]. subst~.
Qed.

Lemma soft_extension_remove_tvar: forall G H x,
    SExtCtx (G & x ~ AC_TVar) (H & x ~ AC_TVar) ->
    SExtCtx G H.
Proof.
  introv ex.
  inversion ex;
  try(apply eq_push_inv in H1; destruct H1 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H2; inversion H2.
  subst. clear EQV.
  apply eq_push_inv in H2. destruct H2 as [? [? ?]]. subst~.
Qed.

Lemma soft_extension_remove_marker: forall G H x,
    SExtCtx (G & x ~ AC_Marker) (H & x ~ AC_Marker) ->
    SExtCtx G H.
Proof.
  introv ex.
  inversion ex;
  try(apply eq_push_inv in H1; destruct H1 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H2; inversion H2.
  subst. clear EQV.
  apply eq_push_inv in H2. destruct H2 as [? [? ?]]. subst~.
Qed.

Lemma soft_extension_weakening_awtermt : forall G H a,
    AWTermT G a ->
    SExtCtx G H ->
    AWTermT H a.
Proof.
  introv ga gh. assert (wf: ok H). apply* soft_extension_ok_preservation.
  gen H.
  induction ga; introv gh wf; auto; try(apply split_bind_context in H; destruct H as (G1 & G2 & gi); rewrite gi in gh).
  apply soft_extension_order_var in gh. destruct gh as (H1 & H2 & [hi _]).
  rewrite hi. constructor*.
  apply* binds_middle_eq.
  rewrite hi in wf. apply* ok_middle_inv_r.

  apply soft_extension_order_typvar in gh. destruct gh as (H1 & H2  & [hi _]).
  rewrite hi. apply* AWTermT_TypVar.
  apply* binds_middle_eq.
  rewrite hi in wf. apply* ok_middle_inv_r.

  apply AWTermT_Lam with (L:=L \u dom H1 \u dom G). introv notin. apply* H0.
  apply~ SExtCtx_Var.

  apply AWTermT_Pi with (L:=L \u dom H1 \u dom G). apply* IHga.
  intros. apply* H0. apply~ SExtCtx_Var.

  apply AWTermT_Forall with (L:=L \u dom H1 \u dom G).
  intros. apply* H0.
  apply~ SExtCtx_TVar.


  apply soft_extension_order_tvar in gh. destruct gh as (H1 & H2 & [hi _]).
  rewrite hi. apply* AWTermT_TFVar.
  apply* binds_middle_eq.
  rewrite hi in wf. apply* ok_middle_inv_r.

  apply soft_extension_order_unsolved_evar in gh. destruct gh as (H1 & H2 & [hi _]).
  destruct hi as [hi1 | (t & hi1)];
    try(rewrite hi1);
    [apply* AWTermT_Unsolved_EVar | apply* AWTermT_Solved_EVar];
    try(rewrite hi1 in wf; apply* binds_middle_eq);try(apply* ok_middle_inv_r).

  apply soft_extension_order_solved_evar in gh. destruct gh as (H1 & H2 & [hi _]).
  rewrite hi. apply* AWTermT_Solved_EVar.
  rewrite hi in wf. apply* binds_middle_eq.
  apply* ok_middle_inv_r.
Qed.

Lemma soft_extension_awt_preservation: forall G H,
    SExtCtx G H ->
    AWt H.
Proof.
  introv ex.
  induction ex; auto.
  apply~ AWt_TyVar. lets: soft_extension_weakening_awtermt H2 ex. auto.
  apply~ AWt_Ctx_Solved_EVar. lets: soft_extension_weakening_awtermt H2 ex. auto.
Qed.

Lemma soft_extension_remove_evar: forall G H x,
    SExtCtx (G & x ~ AC_Unsolved_EVar) H ->
    SExtCtx G H.
Proof.
  introv ex.
  assert(SExtCtx (G & x ~ AC_Unsolved_EVar & empty) H) by rewrite~ concat_empty_r.
  lets: soft_extension_order_unsolved_evar H0.
  destruct H1 as (S1 & S2 & [hinfo [ex1 sf]]).
  destruct hinfo as [hinfo | (t & hinfo)].
  rewrite hinfo.
  apply soft_extension_append_soft.
  apply~ SExtCtx_Add.
  apply soft_extension_ok_preservation in H0. rewrite hinfo in H0. apply ok_concat_inv_l in H0. apply* ok_push_inv.
  apply~ sf. constructor.
  apply soft_extension_awt_preservation in H0. rewrite hinfo in H0. auto.

  rewrite hinfo.
  apply soft_extension_append_soft.
  apply~ SExtCtx_AddSolved.
  apply soft_extension_ok_preservation in H0. rewrite hinfo in H0. apply ok_concat_inv_l in H0. apply* ok_push_inv.
  rewrite hinfo in H0.
  lets: soft_extension_awt_preservation H0.
  lets: awtermt_awt_solved_evar H1. auto.
  apply~ sf. constructor.
  rewrite hinfo in H0.
  lets: soft_extension_awt_preservation H0. auto.
Qed.

Lemma soft_extension_solve_middle: forall G H1 H2 a t,
   SExtCtx G (H1 & a ~ AC_Unsolved_EVar & H2) ->
   AWTermT H1 t ->
   SExtCtx G (H1 & a ~ AC_Solved_EVar t & H2).
Proof.
  introv ex wt. gen G.
  induction H2 using env_ind; introv ex.
  rewrite concat_empty_r in *.
  gen_eq I: (H1 & a ~ AC_Unsolved_EVar).
  induction ex; introv iinfo;
    try(destruct (eq_push_inv iinfo) as [? [? ?]]);
    try(solve[false]).
  false empty_push_inv iinfo.
  subst. apply~ SExtCtx_Solve.
  subst. apply~ SExtCtx_AddSolved.

  rewrite concat_assoc in *.
  induction v.

  inversion ex;
  try(apply eq_push_inv in H0; destruct H0 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H3; inversion H3.
  subst. lets: IHenv H3. apply~ SExtCtx_Var.

  inversion ex;
  try(apply eq_push_inv in H0; destruct H0 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H3; inversion H3.
  subst. lets: IHenv H3. apply~ SExtCtx_TypVar.

  inversion ex;
  try(apply eq_push_inv in H0; destruct H0 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H3; inversion H3.
  subst. lets: IHenv H3. apply~ SExtCtx_TVar.

  inversion ex;
  try(apply eq_push_inv in H0; destruct H0 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H3; inversion H3.
  subst. lets: IHenv H3. apply~ SExtCtx_EVar.
  subst. lets: IHenv H3. apply~ SExtCtx_Add.

  inversion ex;
  try(apply eq_push_inv in H0; destruct H0 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H3; inversion H3.
  subst. lets: IHenv H3. apply~ SExtCtx_SolvedEVar.
  subst. lets: IHenv H3. apply~ SExtCtx_Solve.
  apply* awtermt_middle_solve.
  subst. lets: IHenv H3. apply~ SExtCtx_AddSolved.
  apply* awtermt_middle_solve.

  inversion ex;
  try(apply eq_push_inv in H0; destruct H0 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H3; inversion H3.
  subst. lets: IHenv H3. apply~ SExtCtx_Marker.
Qed.

Lemma soft_extension_binds_solved_evar: forall G H a n,
    SExtCtx G H ->
    binds a (AC_Solved_EVar n) G ->
    binds a (AC_Solved_EVar n) H.
Proof.
  introv H0 bd.
  apply split_bind_context in bd.
  destruct bd as (S1 & S2 & ginfo). subst.
  lets: soft_extension_order_solved_evar H0.
  destruct H1 as (T1 & T2 & [hfin _]). subst.
  apply~ binds_middle_eq.
  lets: soft_extension_ok_preservation H0.
  apply ok_middle_inv_r in H. auto.
Qed.

Lemma soft_extension_binds_unsolved_evar: forall G H a,
    SExtCtx G H ->
    binds a AC_Unsolved_EVar G ->
    binds a AC_Unsolved_EVar H \/ (exists n, binds a (AC_Solved_EVar n) H).
Proof.
  introv H0 bd.
  apply split_bind_context in bd.
  destruct bd as (S1 & S2 & ginfo). subst.
  lets: soft_extension_order_unsolved_evar H0.
  destruct H1 as (T1 & T2 & [hfin _]). subst.
  destruct hfin as [hfin1 | (n & hfin2)]; subst.
  left. apply~ binds_middle_eq.
  lets: soft_extension_ok_preservation H0.
  apply ok_middle_inv_r in H. auto.
  right. exists n. apply~ binds_middle_eq.
  lets: soft_extension_ok_preservation H0.
  apply ok_middle_inv_r in H. auto.
Qed.

Lemma soft_extension_to_extension: forall G H,
    SExtCtx G H ->
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

Lemma soft_extension_transitivity: forall G H I,
    SExtCtx G H ->
    SExtCtx H I ->
    SExtCtx G I.
Proof.
  introv gh hi.
  assert (ok G). apply* soft_extension_ok.
  assert (ok H). apply* soft_extension_ok.
  assert (ok I). apply* soft_extension_ok_preservation.
  gen G.
  induction hi; introv gh okg; auto.

  (* VAR *)
  inversion gh;
  try(apply eq_push_inv in H5; destruct H5 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H6; inversion H6.
  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H6 okg. apply~ SExtCtx_Var.

  (* TYPVAR *)
  inversion gh;
  try(apply eq_push_inv in H6; destruct H6 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H7; inversion H7.
  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H7 okg. apply~ SExtCtx_TypVar.

  (* TVAR *)
  inversion gh;
  try(apply eq_push_inv in H5; destruct H5 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H6; inversion H6.
  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H6 okg. apply~ SExtCtx_TVar.

  (* MARKER *)
  inversion gh;
  try(apply eq_push_inv in H5; destruct H5 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H6; inversion H6.
  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H6 okg. apply~ SExtCtx_Marker.

  (* EVAR *)
  inversion gh;
  try(apply eq_push_inv in H5; destruct H5 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H6; inversion H6.
  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H6 okg. apply~ SExtCtx_EVar.

  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2.
  lets: IHhi H1 H2 H6 okg. apply~ SExtCtx_Add.

  (* SOLVED EVAR *)
  inversion gh;
  try(apply eq_push_inv in H6; destruct H6 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H7; inversion H7.
  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H7 okg. apply~ SExtCtx_SolvedEVar.

  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H7 okg. apply~ SExtCtx_Solve.
  lets: soft_extension_weakening_awtermt H4 hi. auto.

  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2.
  lets: IHhi H1 H2 H7 okg. apply~ SExtCtx_AddSolved.
  lets: soft_extension_weakening_awtermt H4 hi. auto.

  (* SOLVE *)
  inversion gh;
  try(apply eq_push_inv in H6; destruct H6 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H7; inversion H7.
  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2. apply ok_push_inv_ok in okg.
  lets: IHhi H1 H2 H7 okg. apply~ SExtCtx_Solve.

  subst. clear EQV.
  apply ok_push_inv_ok in H1. apply ok_push_inv_ok in H2.
  lets: IHhi H1 H2 H7 okg. apply~ SExtCtx_AddSolved.

  (* ADD *)
  apply ok_push_inv_ok in H2.
  lets: IHhi H1 H2 gh okg. apply~ SExtCtx_Add.

  (* ADD SOLVED *)
  apply ok_push_inv_ok in H2.
  lets: IHhi H1 H2 gh okg. apply~ SExtCtx_AddSolved.
Qed.

Lemma soft_substitution_extension_invariance_right: forall G t H,
    SExtCtx G H ->
    ACtxSubst H t = ACtxSubst G (ACtxSubst H t)
with
soft_substitution_extension_invariance_right2: forall G t H,
    SExtCtx G H ->
    ACtxTSubst H t = ACtxTSubst G (ACtxTSubst H t).
Proof.
  introv gh.
  assert (wf: AWt H). apply* soft_extension_awt_preservation.
  gen t. induction gh; introv.
  rewrite* subst_empty_env.
  rewrite* subst_empty_env.

  repeat(rewrite subst_add_var). apply awt_left in wf. apply* IHgh.

  repeat(rewrite subst_add_typvar). apply awt_left in wf. apply* IHgh.

  repeat(rewrite subst_add_tvar). apply* IHgh.
  repeat(rewrite subst_add_marker). apply* IHgh.

  repeat(rewrite subst_add_evar).
  apply awt_left in wf.
  apply* IHgh.

  repeat(rewrite subst_add_solved_evar).
  assert (wfh:=wf). apply awt_left in wfh.
  lets: soft_extension_awt gh.
  rewrite distributivity_ctxsubst_substt_awt; auto.
  rewrite distributivity_ctxsubst_substt_awt; auto.
  rewrite distributivity_ctxsubst_substt_awt; auto.
  rewrite <- IHgh; auto.
  rewrite <- distributivity_ctxsubst_substt_awt; auto.
  rewrite <- soft_substitution_extension_invariance_right2; auto.
  rewrite <- distributivity_ctxsubst_substt_awt; auto.
  rewrite asubstt_fresh with (u:= (ACtxTSubst G t)); auto.
  apply* notin_ctxsubst_ftv_awt.
  apply* notin_substt_self.
  apply* notin_tfv_tftv.
  lets:  notin_solved_evar_awt wf. auto.

  rewrite subst_add_evar.
  repeat(rewrite subst_add_solved_evar).
  apply awt_left in wf.
  apply* IHgh.

  repeat(rewrite subst_add_evar).
  apply awt_left in wf.
  apply* IHgh.

  repeat(rewrite subst_add_solved_evar).
  apply awt_left in wf.
  apply* IHgh.
Proof.
  introv gh.
  assert (wf: AWt H). apply* soft_extension_awt_preservation.
  gen t. induction gh; introv.
  rewrite* tsubst_empty_env.
  rewrite* tsubst_empty_env.

  repeat(rewrite tsubst_add_var). apply awt_left in wf. apply* IHgh.

  repeat(rewrite tsubst_add_typvar). apply awt_left in wf. apply* IHgh.

  repeat(rewrite tsubst_add_tvar). apply* IHgh.
  repeat(rewrite tsubst_add_marker). apply* IHgh.

  repeat(rewrite tsubst_add_evar).
  apply awt_left in wf.
  apply* IHgh.

  repeat(rewrite tsubst_add_solved_evar).
  assert (wfh:=wf). apply awt_left in wfh.
  lets: soft_extension_awt gh.
  rewrite distributivity_ctxtsubst_tsubstt_awt; auto.
  rewrite distributivity_ctxtsubst_tsubstt_awt; auto.
  rewrite distributivity_ctxtsubst_tsubstt_awt; auto.
  rewrite <- IHgh; auto.
  rewrite <- distributivity_ctxtsubst_tsubstt_awt; auto.
  rewrite <- soft_substitution_extension_invariance_right2; auto.
  rewrite <- distributivity_ctxtsubst_tsubstt_awt; auto.
  rewrite atsubstt_fresh with (u:= (ACtxTSubst G t)); auto.
  apply* notin_ctxtsubst_ftv_awt.
  apply* notin_tsubstt_self.
  apply* notin_tfv_tftv. apply* notin_solved_evar_awt.

  rewrite tsubst_add_evar.
  repeat(rewrite tsubst_add_solved_evar).
  apply awt_left in wf.
  apply* IHgh.

  repeat(rewrite tsubst_add_evar).
  apply awt_left in wf.
  apply* IHgh.

  repeat(rewrite tsubst_add_solved_evar).
  apply awt_left in wf.
  apply* IHgh.
Qed.

Lemma soft_substitution_extension_invariance_left: forall G t H,
    SExtCtx G H ->
    ACtxSubst H t = ACtxSubst H (ACtxSubst G t)
with
soft_substitution_extension_invariance_left2: forall G t H,
    SExtCtx G H ->
    ACtxTSubst H t = ACtxTSubst H (ACtxTSubst G t).
Proof.
  introv gh.
  assert (wf: AWt H). apply* soft_extension_awt_preservation.
  gen t. induction gh; introv.
  rewrite* subst_empty_env.
  rewrite* subst_empty_env.

  repeat(rewrite subst_add_var). apply awt_left in wf. apply* IHgh.
  repeat(rewrite subst_add_typvar). apply awt_left in wf. apply* IHgh.
  repeat(rewrite subst_add_tvar). apply awt_left in wf. apply* IHgh.
  repeat(rewrite subst_add_marker). apply awt_left in wf. apply* IHgh.
  repeat(rewrite subst_add_evar). apply awt_left in wf. apply* IHgh.

  repeat(rewrite subst_add_solved_evar).
  apply awt_left in wf.
  rewrite distributivity_ctxsubst_substt_awt; auto.
  rewrite distributivity_ctxsubst_substt_awt; auto.
  rewrite <- IHgh; auto.
  rewrite <- distributivity_ctxsubst_substt_awt; auto.
  rewrite <- distributivity_ctxsubst_substt_awt; auto.
  rewrite* substt_twice. apply notin_tfv_tftv.
  apply notin_awtermt with (G:=G); auto.

  rewrite subst_add_evar.
  repeat(rewrite subst_add_solved_evar).
  apply awt_left in wf.
  rewrite distributivity_ctxsubst_substt_awt; auto.
  rewrite distributivity_ctxsubst_substt_awt; auto.
  rewrite <- IHgh; auto.

  repeat(rewrite subst_add_evar).
  apply awt_left in wf.
  apply* IHgh.

  repeat(rewrite subst_add_solved_evar).
  apply awt_left in wf.
  rewrite distributivity_ctxsubst_substt_awt; auto.
  rewrite distributivity_ctxsubst_substt_awt; auto.
  rewrite <- IHgh; auto.
Proof.
  introv gh.
  assert (wf: AWt H). apply* soft_extension_awt_preservation.
  gen t. induction gh; introv.
  rewrite* tsubst_empty_env.
  rewrite* tsubst_empty_env.

  repeat(rewrite tsubst_add_var). apply awt_left in wf. apply* IHgh.
  repeat(rewrite tsubst_add_typvar). apply awt_left in wf. apply* IHgh.
  repeat(rewrite tsubst_add_tvar). apply awt_left in wf. apply* IHgh.
  repeat(rewrite tsubst_add_marker). apply awt_left in wf. apply* IHgh.
  repeat(rewrite tsubst_add_evar). apply awt_left in wf. apply* IHgh.

  repeat(rewrite tsubst_add_solved_evar).
  apply awt_left in wf.
  rewrite distributivity_ctxtsubst_tsubstt_awt; auto.
  rewrite distributivity_ctxtsubst_tsubstt_awt; auto.
  rewrite <- IHgh; auto.
  rewrite <- distributivity_ctxtsubst_tsubstt_awt; auto.
  rewrite <- distributivity_ctxtsubst_tsubstt_awt; auto.
  rewrite* tsubstt_twice. apply notin_tfv_tftv.
  apply notin_awtermt with (G:=G); auto.

  rewrite tsubst_add_evar.
  repeat(rewrite tsubst_add_solved_evar).
  apply awt_left in wf.
  rewrite distributivity_ctxtsubst_tsubstt_awt; auto.
  rewrite distributivity_ctxtsubst_tsubstt_awt; auto.
  rewrite <- IHgh; auto.

  repeat(rewrite tsubst_add_evar).
  apply awt_left in wf.
  apply* IHgh.

  repeat(rewrite tsubst_add_solved_evar).
  apply awt_left in wf.
  rewrite distributivity_ctxtsubst_tsubstt_awt; auto.
  rewrite distributivity_ctxtsubst_tsubstt_awt; auto.
  rewrite <- IHgh; auto.
Qed.

(***********************)
(* SOFT EXTENSION PROOF *)
(***********************)

Hint Resolve soft_extension_reflexicity.
Lemma resolve_evar_sextctx: forall G a s t H,
    AResolveEVar G a s t H ->
    AWt G ->
    SExtCtx G H.
Proof.
  introv res okg.
  lets: resolve_evar_awt_preservation res okg.
  induction res; auto.
  apply~ soft_extension_append.
  apply~ SExtCtx_Solve.
  apply~ soft_extension_append.
  apply~ SExtCtx_EVar.
  apply~ SExtCtx_Add.
  apply~ soft_extension_reflexicity.
  repeat apply awt_left in okg. auto.
  lets: awt_is_ok okg.
  do 3 apply ok_concat_inv_l in H1. apply ok_push_inv in H1. destruct H1. auto.
  simpl_dom. apply notin_union. split~.
  lets: awt_is_ok okg.
  do 3 apply ok_concat_inv_l in H1. apply ok_push_inv in H1. destruct H1. auto.
  do 2 apply awt_left in okg. auto.
  do 2 apply awt_left in H0. auto.
  lets: awt_is_ok okg.
  do 1 apply ok_concat_inv_l in H1. apply ok_push_inv in H1. destruct H1. auto.
  lets: awt_is_ok H0.
  do 1 apply ok_concat_inv_l in H1. apply ok_push_inv in H1. destruct H1. auto.
  lets: resolve_evar_awt_preservation res okg.
  lets: IHres okg H4.
  pick_fresh y. assert (y \notin L) by auto.
  assert(AWt (H1 & y ~ AC_Var)) by apply* AWt_Var.
  assert(AWt (H & y ~ AC_Var)) by apply* AWt_Var.
  lets: H3 H6 H7 H8.
  apply soft_extension_remove_var in H9.
  lets: soft_extension_transitivity H5 H9. auto.

  lets: resolve_evar_awt_preservation res1 okg.
  lets: IHres1 okg H2.
  lets: resolve_evar_awt_preservation res2 H2.
  lets: IHres2 H2 H4.
  lets: soft_extension_transitivity H3 H5; auto.

  pick_fresh y. assert (y \notin L) by auto.
  lets: H1 H3; clear H1.
  assert (AWt (G & y ~ AC_Var)) by apply~ AWt_Var.
  lets: resolve_evar_awt_preservation H4 H1.
  lets: H2 H3 H1 H5; clear H2.
  apply soft_extension_remove_var in H6; auto.

  lets: resolve_evar_awt_preservation res1 okg.
  lets: IHres1 okg H2.
  lets: resolve_evar_awt_preservation res2 H2.
  lets: IHres2 H2 H4.
  lets: soft_extension_transitivity H3 H5; auto.
Qed.

Lemma unify_sextctx: forall G s t H,
    AUnify G s t H ->
    AWt G ->
    SExtCtx G H.
Proof.
  introv uni okg.
  lets: unify_awt_preservation uni okg.
  induction uni; auto.

  (* APP *)
  lets: unify_awt_preservation uni1 okg.
  lets: IHuni1 okg H2.
  lets: IHuni2 H2 H0.
  lets: soft_extension_transitivity H3 H4. auto.

  (* LAM *)
  pick_fresh y.
  assert (y \notin L) by auto.
  assert(AWt (G & y ~ AC_Var)). constructor~.
  assert(AWt (H & y ~ AC_Var)). constructor~.
  lets: H2 y H3 H4 H5.
  lets: soft_extension_remove_var H6.  auto.

  (* PI *)
  pick_fresh y.
  assert (y \notin L) by auto.
  assert(AWt (G & y ~ AC_Var)). constructor~.
  lets: unify_awt_preservation uni okg.
  assert(AWt (H1 & y ~ AC_Var)). constructor~.
  assert(AWt (H & y ~ AC_Var)). constructor~.
  lets: H3 y H4 H7 H8.
  lets: soft_extension_remove_var H9.
  lets: IHuni okg H6.
  lets: soft_extension_transitivity H11 H10. auto.

  (* FORALL *)
  pick_fresh y.
  assert (y \notin L) by auto.
  assert(AWt (G & y ~ AC_TVar)). constructor~.
  assert(AWt (H & y ~ AC_TVar)). constructor~.
  lets: H2 y H3 H4 H5.
  lets: soft_extension_remove_tvar H6.  auto.

  (* ANN *)
  lets: unify_awt_preservation uni1 okg.
  lets: IHuni1 okg H2.
  lets: IHuni2 H2 H0.
  lets: soft_extension_transitivity H3 H4. auto.

  (* EVarL *)
  lets: resolve_evar_sextctx H3 okg. auto.
  lets: soft_extension_solve_middle t2 H5. auto.

  (* EVarR *)
  lets: resolve_evar_sextctx H4 okg. auto.
  lets: soft_extension_solve_middle t2 H6. auto.
Qed.
