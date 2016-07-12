
Require Import DeclDef.
Require Import AlgoDef.
Require Import LibLN.
Require Import UtilityEnv.

(* Context extension *)

Inductive ExtCtx : ACtx -> ACtx -> Prop :=
  | ExtCtx_Empty: ExtCtx empty empty
  | ExtCtx_Var : forall G H x, ExtCtx G H -> x # H -> ExtCtx (G & x ~ AC_Var) (H & x ~ AC_Var)
  | ExtCtx_TypVar : forall G H x t1 t2,
      ExtCtx G H -> x # H -> ACtxSubst H t1 = ACtxSubst H t2 -> ExtCtx (G & x ~ AC_Typ t1) (H & x ~ AC_Typ t2)
  | ExtCtx_LetVar : forall G H x s1 s2 t1 t2,
      ExtCtx G H -> x # H -> ACtxTSubst H s1 = ACtxTSubst H s2 ->  ACtxSubst H t1 = ACtxSubst H t2 ->
      ExtCtx (G & x ~ AC_Bnd s1 t1) (H & x ~ AC_Bnd s2 t2)
  | ExtCtx_EVar : forall G H a, ExtCtx G H -> a # H -> ExtCtx (G & a ~ AC_Unsolved_EVar) (H & a ~ AC_Unsolved_EVar)
  | ExtCtx_SolvedEVar: forall G H a t1 t2, ExtCtx G H -> a # H -> ACtxSubst H t1 = ACtxSubst H t2 ->
                                      ExtCtx (G & a ~ AC_Solved_EVar t1) (H & a ~ AC_Solved_EVar t1)
  | ExtCtx_Solve : forall G H a t, ExtCtx G H -> a # H -> AWfTyp H (AT_Expr t) ->
                              ExtCtx (G & a ~ AC_Unsolved_EVar) (H & a ~ AC_Solved_EVar t)
  | ExtCtx_Add : forall G H a, ExtCtx G H -> a # H ->ExtCtx G (H & a ~ AC_Unsolved_EVar)
  | ExtCtx_AddSolved: forall G H a t, ExtCtx G H -> a # H -> AWfTyp H (AT_Expr t) ->
                               ExtCtx G (H & a ~ AC_Solved_EVar t)
.

Definition CompleteCtx (ctx : ACtx) :=
  forall x v, binds x v ctx -> v <> AC_Unsolved_EVar.

Inductive ACpltCtxSubst : ACtx -> AExpr -> DExpr -> Prop :=
  | ACpltCtxSubst_BVar : forall G (x:nat),
      CompleteCtx G -> ACpltCtxSubst G (AE_BVar x) (DE_BVar x)
  | ACpltCtxSubst_FVar : forall G x v,
      CompleteCtx G -> binds x v G -> ACpltCtxSubst G (AE_FVar x) (DE_FVar x)
  | ACpltCtxSubst_EVar : forall G1 G2 a t d,
      CompleteCtx G1 -> CompleteCtx G2 ->
      ACpltCtxSubst G1 t d -> ACpltCtxSubst (G1 & a ~ (AC_Solved_EVar t) & G2) (AE_EVar a) d
  | ACpltCtxSubst_Star : forall G, ACpltCtxSubst G AE_Star DE_Star
  | ACpltCtxSubst_App : forall G t1 t2 d1 d2,
      ACpltCtxSubst G t1 d1 -> ACpltCtxSubst G t2 d2 ->
      ACpltCtxSubst G (AE_App t1 t2) (DE_App d1 d2)
  | ACpltCtxSubst_Lam : forall G t d, ACpltCtxSubst G t d -> ACpltCtxSubst G (AE_Lam t) (DE_Lam d)
  | ACpltCtxSubst_Pi : forall G t1 t2 d1 d2,
      ACpltCtxSubst G t1 d1 -> ACpltCtxSubst G t2 d2 ->
      ACpltCtxSubst G (AE_Pi t1 t2) (DE_Pi d1 d2)
  | ACpltCtxSubst_Let : forall G t1 t2 d1 d2,
      ACpltCtxSubst G t1 d1 -> ACpltCtxSubst G t2 d2 ->
      ACpltCtxSubst G (AE_Let t1 t2) (DE_Let d1 d2)
  | ACpltCtxSubst_CastUp : forall G t d,
      ACpltCtxSubst G t d -> ACpltCtxSubst G (AE_CastUp t) (DE_CastUp d)
  | ACpltCtxSubst_CastDn : forall G t d,
      ACpltCtxSubst G t d -> ACpltCtxSubst G (AE_CastUp t) (DE_CastDn d)
  | ACpltCtxSubst_Ann : forall G t1 t2 d1 d2,
      ACpltCtxSubst G t1 d1 -> ACpltCtxSubst G t2 d2 ->
      ACpltCtxSubst G (AE_Ann t1 t2) (DE_Ann d1 d2)
.

Inductive ACpltCtxTSubst : ACtx -> AType -> DType -> Prop :=
  | ACpltCtxTSubst_Poly : forall G s1 s2,
      ACpltCtxTSubst G s1 s2 -> ACpltCtxTSubst G (AT_Forall s1) (DT_Forall s2)
  | ACpltCtxTSubst_Expr : forall G t1 t2,
      ACpltCtxSubst G t1 t2 -> ACpltCtxTSubst G (AT_Expr t1) (DT_Expr t2)
.

Inductive ACpltCtxSubstCtx : ACtx -> ACtx -> DCtx -> Prop :=
  | ACpltCtxSubstCtx_Empty : ACpltCtxSubstCtx empty empty empty
  (* TODO : ACpltCtxSubstCtx_Var*)
  | ACpltCtxSubstCtx_TypVar : forall H G I x t1 t2 t1',
      CompleteCtx H -> ACpltCtxSubstCtx H G I -> ACtxSubst H t1 =  ACtxSubst H t2 ->
      ACpltCtxSubst H t1 t1' ->
      ACpltCtxSubstCtx (H & x ~ AC_Typ t1) (G & x ~ AC_Typ t2) (I & x ~ DC_Typ t1')
  | ACpltCtxSubstCtx_BndVar : forall H G I x s1 s2 t1 t2 s1' t1',
      CompleteCtx H -> ACpltCtxSubstCtx H G I ->
      ACtxSubst H t1 = ACtxSubst H t2 ->
      ACtxTSubst H s1 = ACtxTSubst H s2 ->
      ACpltCtxSubst H t1 t1' ->
      ACpltCtxTSubst H s1 s1' ->
      ACpltCtxSubstCtx (H & x ~ AC_Bnd s1 t1) (G & x ~ AC_Bnd s2 t2) (I & x ~ DC_Bnd s1' t1')
  | ACpltCtxSubstCtx_Solved_Unsolved_EVar: forall H G I a t,
      CompleteCtx H -> ACpltCtxSubstCtx H G I ->
      ACpltCtxSubstCtx (H & a ~ AC_Solved_EVar t) (G & a ~ AC_Unsolved_EVar) I
  | ACpltCtxSubstCtx_Solved_Solved_EVar: forall H G I t1 t2 a,
      CompleteCtx H -> ACpltCtxSubstCtx H G I ->
      ACtxSubst H t1 = ACtxSubst H t2 ->
      ACpltCtxSubstCtx (H & a ~ AC_Solved_EVar t1) (G & a ~ AC_Solved_EVar t2) I
  | ACpltCtxSubstCtx_Solved_EVar: forall H G I t a,
      CompleteCtx H -> ACpltCtxSubstCtx H G I -> a # G ->
      ACpltCtxSubstCtx (H & a ~ AC_Solved_EVar t) G I
.

(* Properties *)

Set Implicit Arguments.

Definition declaration_preservation_def := forall G I x v1,
    ExtCtx G I -> binds x v1 G -> exists v2, binds x v2 I.

Definition declaration_preservation_dom_def := forall G I x,
    ExtCtx G I -> x \in (dom G) -> x \in (dom I).

Definition ok_context_def := forall G I, ExtCtx G I -> ok G.

Definition ok_preservation_def := forall G I, ExtCtx G I -> ok I.

Definition declaration_order_preservation_def := forall G I G1 G2 G3 x y xv1 yv1,
    ExtCtx G I ->
    G = G1 & x ~ xv1 & G2 & y ~ yv1 & G3 ->
    exists xv2 yv2 I1 I2 I3, I = I1 & x ~ xv2 & I2 & y ~ yv2 & I3.

(* Proofs *)

Lemma declaration_preservation : declaration_preservation_def.
Proof.
  introv H0 H1. induction H0; auto;
  try(binds_cases H1; eauto; apply IHExtCtx in B; inversion B as (x1 & HG); exists* x1).
  exists* v1.
  apply IHExtCtx in H1; inversion H1 as (x1 & HG); exists* x1.
  assert (a <> x). unfold not; intros; subst; eapply binds_fresh_inv; eauto.
  apply* binds_push_neq.
  apply IHExtCtx in H1; inversion H1 as (x1 & HG); exists x1.
  assert (a <> x). unfold not; intros; subst; eapply binds_fresh_inv; eauto.
  apply* binds_push_neq.
Qed.

Lemma declaration_preservation_dom : declaration_preservation_dom_def.
Proof.
  introv HE HX. induction HE; auto;
  try(
  try(destruct (eq_var_dec x x0); subst);
  try(destruct (eq_var_dec x a); subst);
  try(simpl_dom; apply union_left; apply in_singleton_self);
  try(simpl_dom; apply union_right; apply* IHHE);
  try(rewrite in_union in HX; destruct HX as [HX1 | HX2];auto;
  rewrite in_singleton in HX1; subst; auto_star)).
Qed.

Lemma ok_context : ok_context_def.
Proof.
  introv H. induction H; auto;
  try(apply ok_push; eauto;

  unfold notin; unfold not; intros HV; apply (declaration_preservation_dom H0) in HV; apply* H1).
Qed.

Lemma ok_preservation : ok_preservation_def.
Proof.
  introv H.
  assert (ok G). apply* ok_context.
  induction H; subst; auto_star.
Qed.

Lemma declaration_order_preservation : declaration_order_preservation_def.
Proof.
  introv HE HG.
  gen G1 G2 G3 x y xv1 yv1.
  assert (ok G). apply* ok_context.
  induction HE; intros* HG.
  (* ExtCtx_Empty *)
  eapply empty_middle_inv in HG. inversion HG.

  (* ExtCtx_Var  *)
  assert (x0 <> y).  rewrite HG in H. apply (ok_non_eq H).
  destruct (eq_var_dec x y); subst.
  assert (x0 \in (dom (G & y ~ AC_Var))). rewrite HG. simpl_dom. apply union_left. apply union_left. apply union_left. apply union_right. apply in_singleton_self.
  assert (x0 \in (dom G)). simpl_dom . rewrite in_union in H3. destruct H3 as [H11 | H12]. rewrite in_singleton in H11. apply H2 in H11. inversion H11. auto.
  apply (declaration_preservation_dom HE) in H4.
  apply split_context in H4. destruct H4 as (G1' & G2' & v' & H4'); subst.
  exists v' AC_Var G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & x ~ AC_Var). apply (tail_exists_eq n) in HG. auto.
  inversion H3. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (ok_context HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I1 & I2 & I3 & HGG').
  subst.
  exists* xv2 yv2 I1 I2 (I3 & x ~ AC_Var). rewrite* concat_assoc.

  (* ExtCtx_TypVar  *)
  assert (x0 <> y).  rewrite HG in H. apply (ok_non_eq H).
  destruct (eq_var_dec x y); subst.
  assert (x0 \in (dom (G & y ~ AC_Typ t1))). rewrite HG. simpl_dom. apply union_left. apply union_left. apply union_left. apply union_right. apply in_singleton_self.
  assert (x0 \in (dom G)). simpl_dom . rewrite in_union in H4. destruct H4 as [H11 | H12]. rewrite in_singleton in H11. apply H3 in H11. inversion H11. auto.
  apply (declaration_preservation_dom HE) in H5.
  apply split_context in H5. destruct H5 as (G1' & G2' & v' & H5'); subst.
  exists v' (AC_Typ t2) G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & x ~ AC_Typ t1). apply (tail_exists_eq n) in HG. auto.
  inversion H4. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (ok_context HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I1 & I2 & I3 & HGG').
  subst.
  exists* xv2 yv2 I1 I2 (I3 & x ~ AC_Typ t2). rewrite* concat_assoc.

  (* ExtCtx_LetVar *)
  assert (x0 <> y).  rewrite HG in H. apply (ok_non_eq H).
  destruct (eq_var_dec x y); subst.
  assert (x0 \in (dom (G & y ~ AC_Bnd s1 t1))). rewrite HG. simpl_dom. apply union_left. apply union_left. apply union_left. apply union_right. apply in_singleton_self.
  assert (x0 \in (dom G)). simpl_dom . rewrite in_union in H5. destruct H5 as [H11 | H12]. rewrite in_singleton in H11. apply H4 in H11. inversion H11. auto.
  apply (declaration_preservation_dom HE) in H6.
  apply split_context in H6. destruct H6 as (G1' & G2' & v' & H6'); subst.
  exists v' (AC_Bnd s2 t2) G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & x ~ AC_Bnd s1 t1). apply (tail_exists_eq n) in HG. auto.
  inversion H5. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (ok_context HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I1 & I2 & I3 & HGG').
  subst.
  exists* xv2 yv2 I1 I2 (I3 & x ~ AC_Bnd s2 t2). rewrite* concat_assoc.

  (* ExtCtx_EVar *)
  assert (x <> y).  rewrite HG in H. apply (ok_non_eq H).
  destruct (eq_var_dec a y); subst.
  assert (x \in (dom (G & y ~ AC_Unsolved_EVar))). rewrite HG. simpl_dom. apply union_left. apply union_left. apply union_left. apply union_right. apply in_singleton_self.
  assert (x \in (dom G)). simpl_dom . rewrite in_union in H3. destruct H3 as [H11 | H12]. rewrite in_singleton in H11. apply H2 in H11. inversion H11. auto.
  apply (declaration_preservation_dom HE) in H4.
  apply split_context in H4. destruct H4 as (G1' & G2' & v' & H4'); subst.
  exists v' AC_Unsolved_EVar G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & a ~ AC_Unsolved_EVar). apply (tail_exists_eq n) in HG. auto.
  inversion H3. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (ok_context HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I1 & I2 & I3 & HGG').
  subst.
  exists* xv2 yv2 I1 I2 (I3 & a ~ AC_Unsolved_EVar). rewrite* concat_assoc.

  (* ExtCtx_SolvedEVar *)
  assert (x <> y).  rewrite HG in H. apply (ok_non_eq H).
  destruct (eq_var_dec a y); subst.
  assert (x \in (dom (G & y ~ AC_Solved_EVar t1))). rewrite HG. simpl_dom. apply union_left. apply union_left. apply union_left. apply union_right. apply in_singleton_self.
  assert (x \in (dom G)). simpl_dom . rewrite in_union in H4. destruct H4 as [H11 | H12]. rewrite in_singleton in H11. apply H3 in H11. inversion H11. auto.
  apply (declaration_preservation_dom HE) in H5.
  apply split_context in H5. destruct H5 as (G1' & G2' & v' & H5'); subst.
  exists v' (AC_Solved_EVar t1) G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & a ~ AC_Solved_EVar t1). apply (tail_exists_eq n) in HG. auto.
  inversion H4. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (ok_context HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I1 & I2 & I3 & HGG').
  subst.
  exists* xv2 yv2 I1 I2 (I3 & a ~ AC_Solved_EVar t1). rewrite* concat_assoc.

  (* ExtCtx_Solve *)
  assert (x <> y).  rewrite HG in H. apply (ok_non_eq H).
  destruct (eq_var_dec a y); subst.
  assert (x \in (dom (G & y ~ AC_Unsolved_EVar))). rewrite HG. simpl_dom. apply union_left. apply union_left. apply union_left. apply union_right. apply in_singleton_self.
  assert (x \in (dom G)). simpl_dom . rewrite in_union in H4. destruct H4 as [H11 | H12]. rewrite in_singleton in H11. apply H3 in H11. inversion H11. auto.
  apply (declaration_preservation_dom HE) in H5.
  apply split_context in H5. destruct H5 as (G1' & G2' & v' & H5'); subst.
  exists v' (AC_Solved_EVar t) G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & a ~ AC_Unsolved_EVar). apply (tail_exists_eq n) in HG. auto.
  inversion H4. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (ok_context HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I1 & I2 & I3 & HGG').
  subst.
  exists* xv2 yv2 I1 I2 (I3 & a ~ AC_Solved_EVar t). rewrite* concat_assoc.

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
