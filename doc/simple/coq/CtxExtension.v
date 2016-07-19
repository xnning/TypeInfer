
Require Import DeclDef.
Require Import AlgoDef.
Require Import LibLN.
Require Import UtilityEnv.

(* Context extension *)

Inductive ExtCtx : ACtx -> ACtx -> Prop :=
  | ExtCtx_Empty: ExtCtx empty empty
  | ExtCtx_Var : forall G H x,
      ExtCtx G H -> x # H ->
      ExtCtx (G & x ~ AC_Var) (H & x ~ AC_Var)
  | ExtCtx_TypVar : forall G H x t1 t2,
      ExtCtx G H -> x # H -> AWf (G & x ~ AC_Typ t1) ->
      ACtxSubst H t1 = ACtxSubst H t2 ->
      ExtCtx (G & x ~ AC_Typ t1) (H & x ~ AC_Typ t2)
  | ExtCtx_LetVar : forall G H x s1 s2 t1 t2,
      ExtCtx G H -> x # H -> AWf (G & x ~ AC_Bnd s1 t1) ->
      ACtxTSubst H s1 = ACtxTSubst H s2 ->
      ACtxSubst H t1 = ACtxSubst H t2 ->
      ExtCtx (G & x ~ AC_Bnd s1 t1) (H & x ~ AC_Bnd s2 t2)
  | ExtCtx_EVar : forall G H a,
      ExtCtx G H -> a # H ->
      ExtCtx (G & a ~ AC_Unsolved_EVar) (H & a ~ AC_Unsolved_EVar)
  | ExtCtx_SolvedEVar: forall G H a t1 t2,
      ExtCtx G H -> a # H -> AWf (G & a ~ AC_Solved_EVar t1) ->
      ACtxSubst H t1 = ACtxSubst H t2 ->
      ExtCtx (G & a ~ AC_Solved_EVar t1) (H & a ~ AC_Solved_EVar t2)
  | ExtCtx_Solve : forall G H a t,
      ExtCtx G H -> a # H -> AWfTyp H (AT_Expr t) ->
      ExtCtx (G & a ~ AC_Unsolved_EVar) (H & a ~ AC_Solved_EVar t)
  | ExtCtx_Add : forall G H a,
      ExtCtx G H -> a # H ->
      ExtCtx G (H & a ~ AC_Unsolved_EVar)
  | ExtCtx_AddSolved: forall G H a t,
      ExtCtx G H -> a # H -> AWfTyp H (AT_Expr t) ->
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

Definition declaration_preservation_inv_def := forall G I x,
    ExtCtx G I -> x # I -> x # G.

Definition ok_context_def := forall G I, ExtCtx G I -> ok G.

Definition ok_preservation_def := forall G I, ExtCtx G I -> ok I.

Definition awf_context_def := forall G I, ExtCtx G I -> AWf G.

Definition declaration_order_preservation_def := forall G I G1 G2 G3 x y xv1 yv1,
    ExtCtx G I ->
    G = G1 & x ~ xv1 & G2 & y ~ yv1 & G3 ->
    exists xv2 yv2 I1 I2 I3, I = I1 & x ~ xv2 & I2 & y ~ yv2 & I3.

Definition reverse_declaration_order_preservation_def := forall G I x y xv2 yv2 I1 I2 I3,
    ExtCtx G I ->
    x \in dom G ->
    y \in dom G ->
    I = I1 & x ~ xv2 & I2 & y ~ yv2 & I3 ->
    exists G1 G2 G3 xv1 yv1, G = G1 & x ~ xv1 & G2 & y ~ yv1 & G3.

Definition extension_reflexivity_def := forall G,
    AWf G -> ExtCtx G G.

Inductive Softness : ACtx -> Prop :=
  | Softness_Empty: Softness empty
  | Softness_Unsolved: forall G a, Softness G -> a # G -> Softness (G & a ~ AC_Unsolved_EVar)
  | Softness_Solved: forall G a t, Softness G -> a # G -> Softness (G & a ~ AC_Solved_EVar t).

Definition  right_softness_def := forall G I H,
    ExtCtx G I ->
    Softness H ->
    AWf (I & H) ->
    ExtCtx G (I & H).

Definition evar_input_def := forall (G H: ACtx) a,
    ExtCtx (G & a ~ AC_Unsolved_EVar) H ->
    exists H1 H2 H3, H = H1 & H2 & H3 /\ ExtCtx G H1 /\ (H2 = a ~ AC_Unsolved_EVar \/ exists t, H2 = a ~ AC_Solved_EVar t) /\ Softness H3.

Definition solution_admissibility_for_extension_def := forall G a t H,
    AWf (G & a ~ AC_Unsolved_EVar & H) ->
    AWfTyp G (AT_Expr t) ->
    ExtCtx (G & a ~ AC_Unsolved_EVar & H) (G & a ~ AC_Solved_EVar t & H).

Definition solved_variable_addition_for_extension_def := forall G H a t,
    AWf (G & H) ->
    AWf (G & a ~ AC_Solved_EVar t & H) ->
    ExtCtx (G & H) (G & a ~ AC_Solved_EVar t & H).

Definition unsolved_variable_addition_for_extension_def := forall G H a,
    AWf (G & H) ->
    AWf (G & a ~ AC_Unsolved_EVar & H) ->
    ExtCtx (G & H) (G & a ~ AC_Unsolved_EVar & H).

Definition extension_order_var_def := forall (G1 G2 H: ACtx) x,
    ExtCtx (G1 & x ~ AC_Var & G2) H ->
    exists H1 H2, H = H1 & x ~ AC_Var & H2 /\ ExtCtx G1 H1 /\ (Softness G2 -> Softness H2).

Definition extension_order_typvar_def := forall (G1 G2 H: ACtx) x t1,
    ExtCtx (G1 & x ~ AC_Typ t1 & G2) H ->
    exists H1 H2 t2, H = H1 & x ~ AC_Typ t2 & H2 /\ ExtCtx G1 H1 /\ ACtxSubst H1 t1 = ACtxSubst H1 t2 /\ (Softness G2 -> Softness H2).

Definition extension_order_bndvar_def := forall (G1 G2 H: ACtx) x t1 s1,
    ExtCtx (G1 & x ~ AC_Bnd s1 t1 & G2) H ->
    exists H1 H2 s2 t2, H = H1 & x ~ AC_Bnd s2 t2 & H2 /\ ExtCtx G1 H1 /\ ACtxTSubst H1 s1 = ACtxTSubst H1 s2 /\ ACtxSubst H1 t1 = ACtxSubst H1 t2 /\ (Softness G2 -> Softness H2).

Definition extension_order_unsolved_evar_def := forall (G1 G2 H: ACtx) x,
    ExtCtx (G1 & x ~ AC_Unsolved_EVar & G2) H ->
    exists H1 H2, (H = H1 & x ~ AC_Unsolved_EVar & H2 \/ exists t, H = H1 & x ~ AC_Solved_EVar t & H2) /\ ExtCtx G1 H1 /\ (Softness G2 -> Softness H2).

Definition extension_order_solved_evar_def := forall (G1 G2 H: ACtx) a t1,
    ExtCtx (G1 & a ~ AC_Solved_EVar t1 & G2) H ->
    exists H1 H2 t2, H = H1 & a ~ AC_Solved_EVar t2 & H2 /\ ExtCtx G1 H1 /\ ACtxSubst H1 t1 = ACtxSubst H1 t2 /\ (Softness G2 -> Softness H2).

(* Proofs *)

Hint Constructors ExtCtx.
Hint Constructors AWf.

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

Lemma declaration_preservation_inv : forall G I x,
    ExtCtx G I -> x # I -> x # G.
Proof.
  introv GI XI.
  induction GI; auto.
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

Hint Resolve declaration_preservation_inv.
Lemma awf_context : awf_context_def.
Proof.
  introv H. induction H; auto;
  try(constructor*).
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
  assert (x0 \in (dom G)). simpl_dom . rewrite in_union in H5. destruct H5 as [H11 | H12]. rewrite in_singleton in H11. apply H4 in H11. inversion H11. auto.
  apply (declaration_preservation_dom HE) in H6.
  apply split_context in H6. destruct H6 as (G1' & G2' & v' & H5'); subst.
  exists v' (AC_Typ t2) G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & x ~ AC_Typ t1). apply (tail_exists_eq n) in HG. auto.
  inversion H5. subst.
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
  assert (x0 \in (dom G)). simpl_dom . rewrite in_union in H6. destruct H6 as [H11 | H12]. rewrite in_singleton in H11. apply H5 in H11. inversion H11. auto.
  apply (declaration_preservation_dom HE) in H7.
  apply split_context in H7. destruct H7 as (G1' & G2' & v' & H6'); subst.
  exists v' (AC_Bnd s2 t2) G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & x ~ AC_Bnd s1 t1). apply (tail_exists_eq n) in HG. auto.
  inversion H6. subst.
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
  assert (x \in (dom G)). simpl_dom . rewrite in_union in H5. destruct H5 as [H11 | H12]. rewrite in_singleton in H11. apply H4 in H11. inversion H11. auto.
  apply (declaration_preservation_dom HE) in H6.
  apply split_context in H6. destruct H6 as (G1' & G2' & v' & H5'); subst.
  exists v' (AC_Solved_EVar t2) G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & a ~ AC_Solved_EVar t1). apply (tail_exists_eq n) in HG. auto.
  inversion H5. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (ok_context HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I1 & I2 & I3 & HGG').
  subst.
  exists* xv2 yv2 I1 I2 (I3 & a ~ AC_Solved_EVar t2). rewrite* concat_assoc.

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

Lemma reverse_declaration_order_preservation : reverse_declaration_order_preservation_def.
Proof.
  introv HE Hx Hy HI.
  assert (HX := Hx).
  apply split_context in Hx.
  destruct Hx as (Gx1 & Gx2 & v1 & Hx).
  assert (HY := Hy).
  rewrite Hx in Hy.
  simpl_dom.
  repeat (rewrite in_union in Hy).
  destruct Hy as [[Hy1 | Hy2] | Hy3].
  (* y in the left of x *)
  apply split_context in Hy1.
  destruct Hy1 as (Gx3 & Gx4 & yv1 & Hy1). rewrite Hy1 in Hx.
  assert (HYD := Hx).
  apply (declaration_order_preservation HE) in Hx.
  destruct Hx as (xv2' & yv2' & I1' & I2' & I3' & I').
  rewrite I' in HI.
  apply reverse_order_inv in HI. inversion HI.
  apply ok_preservation in HE. rewrite* <- I'.
  apply ok_preservation in HE. rewrite* <- HI. rewrite* <- I'.
  (* y in the \{x\} *)
  assert (y <> x). apply ok_preservation in HE. rewrite HI in HE.
  apply ok_non_eq in HE. auto.
  rewrite in_singleton in Hy2. apply H in Hy2. inversion Hy2.
  (* y in the right of x *)
  apply split_context in Hy3. destruct Hy3 as (G1' & G2' & v' & Hy3).
  rewrite Hy3 in Hx.
  exists* Gx1 G1' G2' v1 v'.
  rewrite concat_assoc in Hx.
  rewrite concat_assoc in Hx. auto.
Qed.

Lemma extension_reflexivity : extension_reflexivity_def.
Proof.
  introv OKG.
  induction OKG; auto.
  apply ExtCtx_LetVar with (t2:=t); auto.
  apply* AWf_LetVar.
  apply* ExtCtx_LetVar.
Qed.

Lemma right_softness: right_softness_def.
Proof.
  introv GI SI IH. gen G I.
  induction H using env_ind; introv GI IH.
  rewrite* concat_empty_r.
  rewrite concat_assoc.
  inversion SI.
  apply empty_push_inv in H1. inversion H1.
  apply eq_push_inv in H0. destruct H0 as [EQAX [EQV EQGH]]; subst.
  constructor*. apply* IHenv.
  rewrite concat_assoc in IH.
  inversion IH; try(apply empty_push_inv in H3; inversion H3);
  try(apply eq_push_inv in H0; destruct H0 as [EQIG [EQX EQAC]];
  inversion EQX).
  apply eq_push_inv in H3; destruct H3 as [EQIG [EQX EQAC]];
  inversion EQX.
  rewrite EQAC in H3. auto.
  rewrite concat_assoc in IH.
  inversion IH; try(apply empty_push_inv in H3; inversion H3);
  try(apply eq_push_inv in H0; destruct H0 as [EQIG [EQX EQAC]];
  inversion EQX).
  apply eq_push_inv in H3; destruct H3 as [EQIG [EQX EQAC]];
  inversion EQX.
  rewrite EQAC in H4. rewrite <- EQIG. auto.

  apply eq_push_inv in H0. destruct H0 as [EQAX [EQV EQGH]]; subst.
  constructor*. apply* IHenv.
  rewrite concat_assoc in IH.
  inversion IH; try(apply empty_push_inv in H3; inversion H3);
  try(apply eq_push_inv in H0; destruct H0 as [EQIG [EQX EQAC]];
  inversion EQX).
  apply eq_push_inv in H3; destruct H3 as [EQIG [EQX EQAC]];
  inversion EQX.
  rewrite EQAC in H3. auto.
  rewrite concat_assoc in IH.
  inversion IH; try(apply empty_push_inv in H3; inversion H3);
  try(apply eq_push_inv in H0; destruct H0 as [EQIG [EQX EQAC]];
  inversion EQX).
  apply eq_push_inv in H3; destruct H3 as [EQIG [EQX EQAC]];
  inversion EQX.
  rewrite EQAC in H4. rewrite <- EQIG. auto.

  rewrite concat_assoc in IH.
  inversion IH; try(apply empty_push_inv in H3; inversion H3);
  try(apply eq_push_inv in H0; destruct H0 as [EQIG [EQX EQAC]];
  inversion EQX).
  apply eq_push_inv in H3; destruct H3 as [EQIG [EQX EQAC]];
  inversion EQX.
  rewrite EQAC in H5. rewrite <- H6. auto.
Qed.

Lemma evar_input: evar_input_def.
Proof.
  introv GH.
  gen_eq GG : (G & a ~ AC_Unsolved_EVar). introv GInfo.
  induction GH;
  try(apply eq_push_inv in GInfo; destruct GInfo as [ eqa [inv eqg]]; subst; inversion inv).
  apply empty_push_inv in GInfo; inversion GInfo.
  exists* H (a ~ AC_Unsolved_EVar) (empty:ACtx).
  rewrite* concat_empty_r. split; auto.  split; auto.
  split; auto. constructor.

  exists* H (a ~ AC_Solved_EVar t) (empty:ACtx).
  rewrite* concat_empty_r. split; auto.  split; auto.
  split. right; exists* t. constructor.

  assert (neqa: a0 <> a).
    assert (a \in dom H). apply (declaration_preservation_dom GH). rewrite* GInfo. simpl_dom; apply union_left. apply in_singleton_self.
    unfold not. intros eqa. subst.
    apply get_some in H1. destruct H1 as (v & H1).
    apply binds_fresh_inv with (x:= a) (E:=H) (v:=v); auto.
  apply IHGH in GInfo.
  destruct GInfo as (H1 & H2 & H3 & [HInfo [GH1 [GH2 GH3]]]).
  exists* H1 H2 (H3 & a0 ~ AC_Unsolved_EVar).
  rewrite* concat_assoc. subst. split; auto.  split; auto.
  split; auto. constructor; auto.

  assert (neqa: a0 <> a).
    assert (a \in dom H). apply (declaration_preservation_dom GH). rewrite* GInfo. simpl_dom; apply union_left. apply in_singleton_self.
    unfold not. intros eqa. subst.
    apply get_some in H2. destruct H2 as (v & H2).
    apply binds_fresh_inv with (x:= a) (E:=H) (v:=v); auto.
  apply IHGH in GInfo.
  destruct GInfo as (H1' & H2 & H3 & [HInfo [GH1 [GH2 GH3]]]).
  exists* H1' H2 (H3 & a0 ~ AC_Solved_EVar t).
  rewrite* concat_assoc. subst. split; auto.  split; auto.
  split; auto. constructor; auto.
Qed.

Lemma solution_admissibility_for_extension : solution_admissibility_for_extension_def.
Proof.
  introv. gen G a t.
  induction H using env_ind.
  introv WF WFTyp.
  repeat(rewrite concat_empty_r).
  constructor. apply extension_reflexivity.
  rewrite concat_empty_r in WF.
  inversion WF;
    try(apply eq_push_inv in H; destruct H as [eqg [H eqt]]; subst; auto; inversion H);
    try(apply eq_push_inv in H0; destruct H0 as [eqg [H0 eqt]]; subst; auto; inversion H0).
  apply empty_push_inv in H0; inversion H0.
  inversion WF; rewrite concat_empty_r in *;
    try(apply eq_push_inv in H; destruct H as [eqg [H eqt]]; subst; auto; inversion H);
    try(apply eq_push_inv in H0; destruct H0 as [eqg [H0 eqt]]; subst; auto; inversion H0).
  apply empty_push_inv in H0; inversion H0.
  auto.

  introv WF WFTyp.
  repeat(rewrite concat_assoc).
  rewrite concat_assoc in WF.
  induction v; constructor*;

  try(apply* IHenv; apply AWf_left in WF; auto);
  try(apply AWf_push_inv in WF; auto).
Qed.

Lemma solved_variable_addition_for_extension:
  solved_variable_addition_for_extension_def.
Proof.
  introv. gen G a t.
  induction H using env_ind.
  introv WFGH WFGAH.
  repeat(rewrite concat_empty_r in *).
  constructor. apply extension_reflexivity.
  auto.  apply AWf_push_inv with (v:= AC_Solved_EVar t) . auto.
  inversion WFGAH;
    try(apply eq_push_inv in H; destruct H as [eqg [H eqt]]; subst; auto; inversion H);
    try(apply eq_push_inv in H0; destruct H0 as [eqg [H0 eqt]]; subst; auto; inversion H0).
  apply empty_push_inv in H0; inversion H0.
  inversion H. subst; auto.

  introv WF WFTyp.
  repeat(rewrite concat_assoc in *).
  induction v; constructor*;
  try(apply IHenv; apply AWf_left in WF; auto;
  apply AWf_left in WFTyp; auto);
  try(apply AWf_push_inv in WFTyp; auto).
Qed.

Lemma unsolved_variable_addition_for_extension:
  unsolved_variable_addition_for_extension_def.
Proof.
  introv. gen G a.
  induction H using env_ind.
  introv WFGH WFGAH.
  repeat(rewrite concat_empty_r in *).
  constructor. apply extension_reflexivity.
  auto. apply AWf_push_inv in WFGAH. auto.

  introv WF WFTyp.
  repeat(rewrite concat_assoc in *).
  induction v; constructor*;
  try(apply IHenv; apply AWf_left in WF; auto;
  apply AWf_left in WFTyp; auto);
  try(apply AWf_push_inv in WFTyp; auto).
Qed.

Lemma extension_order_var : extension_order_var_def.
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Var & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  exists* H (empty: ACtx). split. rewrite* concat_empty_r.
  split. apply tail_empty_eq with (G0:= G & x0 ~ AC_Var) (G3 := G) (I := G1 & x0 ~ AC_Var & G2) (I1:= G1) (I2:=G2) (x:=x0) (vx:=AC_Var) (vy:=AC_Var)in IG; auto.
  destruct IG as [IG _]. subst. auto.
  rewrite <- IG. constructor. apply ok_context in EX. auto.
  apply (declaration_preservation_inv EX) in H0. auto.
  constructor. apply ok_context in EX. auto.
  apply (declaration_preservation_inv EX) in H0. auto.
  constructor.

  assert (IG2 := IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [EXG1H1 SoftG3H2]]).
  exists* H1 (H2 & x0 ~ AC_Var). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H3. apply empty_push_inv in H5. inversion H5. apply eq_push_inv in H4. destruct H4 as [_ [H4 _]]. inversion H4. apply eq_push_inv in H4. destruct H4 as [_ [H4 _]]. inversion H4.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t1) (G & x0 ~ AC_Typ t1)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & [HH [EXG1H1 SoftG3H2]]).
  exists* H3 (H4 & x0 ~ AC_Typ t2). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H5. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6.

  (* AC_Bnd *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Bnd s1 t1) (G & x0 ~ AC_Bnd s1 t1)).
  apply* binds_push_eq. rewrite IG in H4. apply binds_middle_eq_inv in H4. inversion H4. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & x0 ~ AC_Bnd s2 t2). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H6. apply empty_push_inv in H8. inversion H8. apply eq_push_inv in H7. destruct H7 as [_ [H7 _]]. inversion H7. apply eq_push_inv in H7. destruct H7 as [_ [H7 _]]. inversion H7.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Unsolved_EVar) (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H1. apply binds_middle_eq_inv in H1. inversion H1. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H1. apply empty_push_inv in H3. inversion H3. apply eq_push_inv in H2. destruct H2 as [EQA [_ eqg]]. rewrite eqg in H3. assumption. apply eq_push_inv in H2.  destruct H2 as [_ [neq _]]. inversion neq. rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t1) (G & a ~ AC_Solved_EVar t1)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t2). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption. rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Unsolved_EVar) (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]].  rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar). rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t). rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.
Qed.

Lemma extension_order_typvar : extension_order_typvar_def.
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Typ t1 & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H1. apply binds_middle_eq_inv in H1. inversion H1. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & t2 & [HH [EXG1H1 [eqt1t2 SoftG3H2]]]).
  exists* H3 (H4 & x0 ~ AC_Var) t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. inversion H1. apply empty_push_inv in H5. inversion H5. apply eq_push_inv in H2. destruct H2 as [_ [H2 _]]. inversion H2. apply eq_push_inv in H2. destruct H2 as [_ [H2 _]]. inversion H2.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  apply tail_empty_eq with (G0:= G & x0 ~ AC_Typ t0) (G3 := G) (I := G1 & x0 ~ AC_Typ t1 & G2) (I1:= G1) (I2:=G2) (x:=x0) (vx:=AC_Typ t0) (vy:=AC_Typ t1) in IG; auto.
  destruct IG as [IG [eqt _]]. subst. auto.
  exists* H (empty: ACtx) t2. split. rewrite* concat_empty_r.
  split. auto.
  split; auto. inversion eqt; subst; auto. constructor.

  rewrite <- IG. constructor. apply ok_context in EX. auto.
  apply (declaration_preservation_inv EX) in H0. auto.
  constructor. apply ok_context in EX. auto.
  apply (declaration_preservation_inv EX) in H0. auto.

  assert (IG2 := IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & t3 & [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H3 (H4 & x0 ~ AC_Typ t2) t3. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. inversion H5. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6.

  (* AC_Bnd *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Bnd s1 t0) (G & x0 ~ AC_Bnd s1 t0)).
  apply* binds_push_eq. rewrite IG in H4. apply binds_middle_eq_inv in H4. inversion H4. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & t3 & [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H4 (H5 & x0 ~ AC_Bnd s2 t2) t3. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. inversion H6. apply empty_push_inv in H8. inversion H8. apply eq_push_inv in H7. destruct H7 as [_ [H7 _]]. inversion H7. apply eq_push_inv in H7. destruct H7 as [_ [H7 _]]. inversion H7.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Unsolved_EVar) (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H1. apply binds_middle_eq_inv in H1. inversion H1. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & t2 & [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar) t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H1. apply empty_push_inv in H3. inversion H3. apply eq_push_inv in H2. destruct H2 as [EQA [_ eqg]]. rewrite eqg in H3. assumption. apply eq_push_inv in H2.  destruct H2 as [_ [neq _]]. inversion neq. rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t0) (G & a ~ AC_Solved_EVar t0)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & t3 & [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t2) t3. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption. rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Unsolved_EVar) (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & t2 &  [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t) t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]].  rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & t2 & [HH [ExtG1H1 [t1t2 SoftG2H2]]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar) t2. rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & t2 &  [HH [ExtG1H1 [t1t2 SoftG2H2]]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t) t2. rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.
Qed.

Lemma extension_order_bndvar : extension_order_bndvar_def.
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Bnd s1 t1 & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H1. apply binds_middle_eq_inv in H1. inversion H1. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & s2 & t2 & [HH [EXG1H1 [eqs1s2 [eqt1t2 SoftG3H2]]]]).
  exists* H3 (H4 & x0 ~ AC_Var) s2 t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. inversion H1. apply empty_push_inv in H5. inversion H5. apply eq_push_inv in H2. destruct H2 as [_ [H2 _]]. inversion H2. apply eq_push_inv in H2. destruct H2 as [_ [H2 _]]. inversion H2.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t0) (G & x0 ~ AC_Typ t0)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & s2 & t3 & [HH [EXG1H1 [s1s2 [t1t1 SoftG3H2]]]]).
  exists* H3 (H4 & x0 ~ AC_Typ t2) s2 t3. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. inversion H5. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6.

  (* AC_Bnd *)
  destruct (eq_var_dec x x0); subst.
  apply tail_empty_eq with (G0:= G & x0 ~ AC_Bnd s0 t0) (G3 := G) (I := G1 & x0 ~ AC_Bnd s1 t1 & G2) (I1:= G1) (I2:=G2) (x:=x0) (vx:=AC_Bnd s0 t0) (vy:=AC_Bnd s1 t1) in IG; auto.
  destruct IG as [IG [eqt _]]. inversion eqt. subst.
  exists* H (empty: ACtx) s2 t2. split. rewrite* concat_empty_r.
  split. auto.
  split; auto. split; auto. constructor.

  rewrite <- IG. constructor. apply ok_context in EX. auto.
  apply (declaration_preservation_inv EX) in H0. auto.
  constructor. apply ok_context in EX. auto.
  apply (declaration_preservation_inv EX) in H0. auto.

  assert (IG2 := IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & s3 & t3 & [HH [EXG1H1 [s1s2 [t1t2 SoftG3H2]]]]).
  exists* H4 (H5 & x0 ~ AC_Bnd s2 t2) s3 t3. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. inversion H6. apply empty_push_inv in H8. inversion H8. apply eq_push_inv in H7. destruct H7 as [_ [H7 _]]. inversion H7. apply eq_push_inv in H7. destruct H7 as [_ [H7 _]]. inversion H7.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Unsolved_EVar) (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H1. apply binds_middle_eq_inv in H1. inversion H1. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & s2 & t2 & [HH [EXG1H1 [s1s2 [t1t2 SoftG3H2]]]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar) s2 t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H1. apply empty_push_inv in H3. inversion H3. apply eq_push_inv in H2. destruct H2 as [EQA [_ eqg]]. rewrite eqg in H3. assumption. apply eq_push_inv in H2.  destruct H2 as [_ [neq _]]. inversion neq. rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t0) (G & a ~ AC_Solved_EVar t0)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & s2 & t3 & [HH [EXG1H1 [s1s2 [t1t2 SoftG3H2]]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t2) s2 t3. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption. rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Unsolved_EVar) (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & s2 & t2 &  [HH [EXG1H1 [s1s2 [t1t2 SoftG3H2]]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t) s2 t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]].  rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & s2 & t2 & [HH [ExtG1H1 [s1s2 [t1t2 SoftG2H2]]]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar) s2 t2. rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & s2 & t2 &  [HH [ExtG1H1 [s1s2 [t1t2 SoftG2H2]]]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t) s2 t2. rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. split. auto.  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.
Qed.

Lemma extension_order_unsolved_evar :
  extension_order_unsolved_evar_def.
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Unsolved_EVar & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H1. apply binds_middle_eq_inv in H1. inversion H1. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & x0 ~ AC_Var). split; auto.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t. rewrite HH2. rewrite* concat_assoc.
  split; auto.
  rewrite HG2. intros. inversion H1. apply empty_push_inv in H3. inversion H3. apply eq_push_inv in H2. destruct H2 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H2. destruct H2 as [eqa [eqv eqg]]. inversion eqv.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t1) (G & x0 ~ AC_Typ t1)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & [HH [EXG1H1 SoftG3H2]]).
  exists* H3 (H4 & x0 ~ AC_Typ t2). split; auto.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t. rewrite HH2. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H5. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6.

  (* AC_Bnd *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Bnd s1 t1) (G & x0 ~ AC_Bnd s1 t1)).
  apply* binds_push_eq. rewrite IG in H4. apply binds_middle_eq_inv in H4. inversion H4. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & x0 ~ AC_Bnd s2 t2). split; auto.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t. rewrite HH2. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H6. apply empty_push_inv in H8. inversion H8. apply eq_push_inv in H7. destruct H7 as [_ [H7 _]]. inversion H7. apply eq_push_inv in H7. destruct H7 as [_ [H7 _]]. inversion H7.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec x a); subst.
  exists* H (empty: ACtx). split. rewrite* concat_empty_r.
  split. apply tail_empty_eq with (G0:= G & a ~ AC_Unsolved_EVar) (G3 := G) (I := G1 & a ~ AC_Unsolved_EVar & G2) (I1:= G1) (I2:=G2) (x:=a) (vx:=AC_Unsolved_EVar) (vy:=AC_Unsolved_EVar)in IG; auto.
  destruct IG as [IG _]. subst. auto.
  rewrite <- IG. constructor. apply ok_context in EX. auto.
  apply (declaration_preservation_inv EX) in H0. auto.
  constructor. apply ok_context in EX. auto.
  apply (declaration_preservation_inv EX) in H0. auto.
  constructor.

  assert (IG2 := IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [EXG1H1 SoftG3H2]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar). split; auto.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t. rewrite HH2. rewrite concat_assoc. auto.
  split; auto.
  intros. constructor. apply* SoftG3H2. rewrite HG2 in H3. inversion H3. apply empty_push_inv in H5. inversion H5. apply eq_push_inv in H4. destruct H4 as [eqa [_ eqg]]. rewrite eqg in H5. auto. apply eq_push_inv in H4. destruct H4 as [_ [eqv _]]. inversion eqv.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1 in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ notin]. auto.
  rewrite HH2 in H0. simpl_dom.  apply notin_union in H0. destruct H0 as [_ notin]. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t1) (G & a ~ AC_Solved_EVar t1)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t2). split; auto.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t. rewrite HH2. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1 in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.
  rewrite HH2 in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  exists* H (empty: ACtx).
  split. right. exists t. rewrite concat_empty_r. auto.
  split. apply tail_empty_eq with (G0:= G & a ~ AC_Unsolved_EVar) (G3 := G) (I := G1 & a ~ AC_Unsolved_EVar & G2) (I1:= G1) (I2:=G2) (x:=a) (vx:=AC_Unsolved_EVar) (vy:=AC_Unsolved_EVar)in IG; auto.
  destruct IG as [IG _]. subst. auto.
  rewrite <- IG. constructor. apply ok_context in EX. auto.
  apply (declaration_preservation_inv EX) in H0. auto.
  constructor. apply ok_context in EX. auto.
  apply (declaration_preservation_inv EX) in H0. auto.
  constructor.

  assert (IG2 := IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [EXG1H1 SoftG3H2]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t). split; auto.
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t1. rewrite HH2. rewrite concat_assoc. auto.
  split; auto.
  intros. constructor. apply* SoftG3H2. rewrite HG2 in H4. inversion H4. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H5. destruct H5 as [eqa [_ eqg]]. rewrite eqg in H6. auto. apply eq_push_inv in H5. destruct H5 as [_ [eqv _]]. inversion eqv.
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1 in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ notin]. auto.
  rewrite HH2 in H0. simpl_dom.  apply notin_union in H0. destruct H0 as [_ notin]. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar).
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1. split. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH1 in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.
  split. right. exists t1. rewrite HH2. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH2 in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t).

  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1. split. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH1 in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.
  split. right. exists t1. rewrite HH2. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH2 in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.
Qed.

Lemma extension_order_solved_evar :
  extension_order_solved_evar_def.
Proof.
  introv EX. gen_eq G : (G1 & a ~ AC_Solved_EVar t1 & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x a); subst.
  assert (binds a AC_Var (G & a ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H1. apply binds_middle_eq_inv in H1. inversion H1. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & t2 & [HH [EXG1H1 [eqt1t2 SoftG3H2]]]).
  exists* H3 (H4 & x ~ AC_Var) t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. inversion H1. apply empty_push_inv in H5. inversion H5. apply eq_push_inv in H2. destruct H2 as [_ [H2 _]]. inversion H2. apply eq_push_inv in H2. destruct H2 as [_ [H2 _]]. inversion H2.

  (* AC_Typ *)
  destruct (eq_var_dec x a); subst.
  apply tail_empty_eq with (G0:= G & a ~ AC_Typ t0) (G3 := G) (I := G1 & a ~ AC_Solved_EVar t1 & G2) (I1:= G1) (I2:=G2) (x:=a) (vx:=AC_Typ t0) (vy:=AC_Solved_EVar t1) in IG; auto.
  destruct IG as [IG [eqt _]]. inversion eqt.
  rewrite <- IG. constructor. apply ok_context in EX. auto.
  apply (declaration_preservation_inv EX) in H0. auto.
  constructor. apply ok_context in EX. auto.
  apply (declaration_preservation_inv EX) in H0. auto.

  assert (IG2 := IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & t3 & [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H3 (H4 & x ~ AC_Typ t2) t3. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. inversion H5. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6. apply eq_push_inv in H6. destruct H6 as [_ [H6 _]]. inversion H6.

  (* AC_Bnd *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Bnd s1 t0) (G & a ~ AC_Bnd s1 t0)).
  apply* binds_push_eq. rewrite IG in H4. apply binds_middle_eq_inv in H4. inversion H4. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & t3 & [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H4 (H5 & x ~ AC_Bnd s2 t2) t3. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. inversion H6. apply empty_push_inv in H8. inversion H8. apply eq_push_inv in H7. destruct H7 as [_ [H7 _]]. inversion H7. apply eq_push_inv in H7. destruct H7 as [_ [H7 _]]. inversion H7.

  (* AC_Unsolved_EVar *)
  destruct (eq_var_dec a0 a); subst.
  assert (binds a (AC_Unsolved_EVar) (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H1. apply binds_middle_eq_inv in H1. inversion H1. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & t2 & [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H4 (H5 & a0 ~ AC_Unsolved_EVar) t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H1. apply empty_push_inv in H3. inversion H3. apply eq_push_inv in H2. destruct H2 as [EQA [_ eqg]]. rewrite eqg in H3. assumption. apply eq_push_inv in H2.  destruct H2 as [_ [neq _]]. inversion neq. rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec a0 a); subst.
  exists* H (empty: ACtx) t2.
  rewrite concat_empty_r.
  split; auto.
  apply tail_empty_eq with (G0:= G & a ~ AC_Solved_EVar t0) (G3 := G) (I := G1 & a ~ AC_Solved_EVar t1 & G2) (I1:= G1) (I2:=G2) (x:=a) (vx:=AC_Solved_EVar t0) (vy:=AC_Solved_EVar t1)in IG; auto.
  destruct IG as [IG [eqt _]]. rewrite IG in EX. auto.
  split. auto. inversion eqt. subst.
  split. auto.
  constructor.
  rewrite <- IG. constructor. apply ok_context in EX. auto.
  apply (declaration_preservation_inv EX) in H0. auto.
  constructor. apply ok_context in EX. auto.
  apply (declaration_preservation_inv EX) in H0. auto.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & t3 & [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H4 (H5 & a0 ~ AC_Solved_EVar t2) t3. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption. rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_Solve *)
  destruct (eq_var_dec a0 a); subst.
  assert (binds a (AC_Unsolved_EVar) (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* declaration_preservation_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & t2 &  [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H4 (H5 & a0 ~ AC_Solved_EVar t) t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]].  rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & t2 & [HH [ExtG1H1 [t1t2 SoftG2H2]]]).
  exists* H1 (H2 & a0 ~ AC_Unsolved_EVar) t2. rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & t2 &  [HH [ExtG1H1 [t1t2 SoftG2H2]]]).
  exists* H2 (H3 & a0 ~ AC_Solved_EVar t) t2. rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. simpl_dom. apply notin_union in H0. destruct H0 as [_ H0]. auto.
Qed.
