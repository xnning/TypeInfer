
Require Import DeclDef.
Require Import AlgoDef.
Require Import LibLN.
Require Import UtilityEnv.
Require Import AlgoInfra.


(* Context extension *)

Inductive ExtCtx : ACtx -> ACtx -> Prop :=
  | ExtCtx_Empty: ExtCtx empty empty
  | ExtCtx_Var : forall G H x,
      ExtCtx G H ->
      AWf (G & x ~ AC_Var) ->
      AWf (H & x ~ AC_Var) ->
      ExtCtx (G & x ~ AC_Var) (H & x ~ AC_Var)
  | ExtCtx_TypVar : forall G H x t1 t2,
      ExtCtx G H ->
      AWf (G & x ~ AC_Typ t1) ->
      AWf (H & x ~ AC_Typ t2) ->
      ACtxSubst H t1 = ACtxSubst H t2 ->
      ExtCtx (G & x ~ AC_Typ t1) (H & x ~ AC_Typ t2)
  | ExtCtx_LetVar : forall G H x s1 s2 t1 t2,
      ExtCtx G H ->
      AWf (G & x ~ AC_Bnd s1 t1) ->
      AWf (H & x ~ AC_Bnd s2 t2) ->
      ACtxTSubst H s1 = ACtxTSubst H s2 ->
      ACtxSubst H t1 = ACtxSubst H t2 ->
      ExtCtx (G & x ~ AC_Bnd s1 t1) (H & x ~ AC_Bnd s2 t2)
  | ExtCtx_EVar : forall G H a,
      ExtCtx G H ->
      AWf (G & a ~ AC_Unsolved_EVar) ->
      AWf (H & a ~ AC_Unsolved_EVar) ->
      ExtCtx (G & a ~ AC_Unsolved_EVar) (H & a ~ AC_Unsolved_EVar)
  | ExtCtx_SolvedEVar: forall G H a t1 t2,
      ExtCtx G H ->
      AWf (G & a ~ AC_Solved_EVar t1) ->
      AWf (H & a ~ AC_Solved_EVar t2) ->
      ACtxSubst H t1 = ACtxSubst H t2 ->
      ExtCtx (G & a ~ AC_Solved_EVar t1) (H & a ~ AC_Solved_EVar t2)
  | ExtCtx_Solve : forall G H a t,
      ExtCtx G H ->
      AWf (G & a ~ AC_Unsolved_EVar) ->
      AWf (H & a ~ AC_Solved_EVar t) ->
      ExtCtx (G & a ~ AC_Unsolved_EVar) (H & a ~ AC_Solved_EVar t)
  | ExtCtx_Add : forall G H a,
      ExtCtx G H ->
      AWf (H & a ~ AC_Unsolved_EVar) ->
      ExtCtx G (H & a ~ AC_Unsolved_EVar)
  | ExtCtx_AddSolved: forall G H a t,
      ExtCtx G H ->
      AWf (H & a ~ AC_Solved_EVar t) ->
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
      ok (G1 & a ~ (AC_Solved_EVar t) & G2) ->
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
      ACpltCtxSubst G t d -> ACpltCtxSubst G (AE_CastDn t) (DE_CastDn d)
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
  | ACpltCtxSubstCtx_Var : forall H G I x,
      CompleteCtx H -> ACpltCtxSubstCtx H G I ->
      ACpltCtxSubstCtx (H & x ~ AC_Var) (G & x ~ AC_Var) I
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

Definition awf_preservation_def := forall G H, ExtCtx G H -> AWf H.

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
    AWf (G & a ~ AC_Solved_EVar t & H) ->
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

Definition extension_weakening_awterm_def := forall G H a,
    AWTerm G a ->
    ExtCtx G H ->
    AWTerm H a.

Definition extension_equality_preservation_def := forall a b G H,
    ACtxTSubst G a = ACtxTSubst G b ->
    ExtCtx G H ->
    ACtxTSubst H a = ACtxTSubst H b.

Definition substitution_extension_invariance_def := forall G t H,
    ExtCtx G H ->
    ACtxSubst H t = ACtxSubst H (ACtxSubst G t) /\
    ACtxSubst H t = ACtxSubst G (ACtxSubst H t).

Definition extension_transitivity_def := forall G H I,
    ExtCtx G H ->
    ExtCtx H I ->
    ExtCtx G I.

Definition parallel_extension_solution_def:= forall G1 G2 H1 H2 a t1 t2,
    ExtCtx (G1 & a ~ AC_Unsolved_EVar & G2) (H1 & a ~ AC_Solved_EVar t1 & H2) ->
    ACtxSubst H1 t1 = ACtxSubst H1 t2 ->
    AWf (G1 & a ~ AC_Solved_EVar t2 & G2) ->
    ExtCtx (G1 & a ~ AC_Solved_EVar t2 & G2) (H1 & a ~ AC_Solved_EVar t1 & H2).

Definition parallel_variable_update_def := forall G1 G2 H1 H2 a t0 t1 t2,
    ExtCtx (G1 & a ~ AC_Unsolved_EVar & G2) (H1 & a ~ AC_Solved_EVar t0 & H2) ->
    ACtxSubst H1 t0 = ACtxSubst H1 t1 ->
    ACtxSubst H1 t1 = ACtxSubst H1 t2 ->
    AWf (G1 & a ~ AC_Solved_EVar t1 & G2) ->
    AWf (H1 & a ~ AC_Solved_EVar t2 & H2) ->
    ExtCtx (G1 & a ~ AC_Solved_EVar t1 & G2) (H1 & a ~ AC_Solved_EVar t2 & H2).

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
  apply* AWf_push_inv.
  apply* binds_push_neq.
  apply IHExtCtx in H1; inversion H1 as (x1 & HG); exists x1.
  assert (a <> x). unfold not. intros. subst. eapply binds_fresh_inv; eauto.
  apply* AWf_push_inv.
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

Lemma declaration_preservation_inv : declaration_preservation_inv_def.
Proof.
  introv GI XI.
  induction GI; auto.
Qed.

Lemma awf_context : awf_context_def.
Proof.
  introv H. induction H; auto.
Qed.

Lemma awf_preservation: awf_preservation_def.
Proof.
  introv gh.
  induction gh; auto_star.
Qed.

Lemma ok_context : ok_context_def.
Proof.
  introv H. apply awf_context in H. apply* awf_is_ok.
Qed.

Lemma ok_preservation : ok_preservation_def.
Proof.
  introv H.
  assert (ok G). apply* ok_context.
  induction H; subst; auto;
  try(apply awf_is_ok in H3; auto).
  apply awf_is_ok in H2. auto.
  apply awf_is_ok in H2. auto.
Qed.

Hint Resolve declaration_preservation_inv.

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
  assert (x0 \in (dom G)). simpl_dom . rewrite in_union in H4. destruct H4 as [H11 | H12]. rewrite in_singleton in H11. apply H3 in H11. inversion H11. auto.
  apply (declaration_preservation_dom HE) in H5.
  apply split_context in H5. destruct H5 as (G1' & G2' & v' & H4'); subst.
  exists v' AC_Var G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & x ~ AC_Var). apply (tail_exists_eq n) in HG. auto.
  inversion H4. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (ok_context HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I4 & I5 & I3 & HGG').
  subst.
  exists* xv2 yv2 I4 I5 (I3 & x ~ AC_Var). rewrite* concat_assoc.

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
  destruct HGG as (xv2 & yv2 & I4 & I5 & I6 & HGG').
  subst.
  exists* xv2 yv2 I4 I5 (I6 & x ~ AC_Typ t2). rewrite* concat_assoc.

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
  destruct HGG as (xv2 & yv2 & I4 & I5 & I6 & HGG').
  subst.
  exists* xv2 yv2 I4 I5 (I6 & x ~ AC_Bnd s2 t2). rewrite* concat_assoc.

  (* ExtCtx_EVar *)
  assert (x <> y).  rewrite HG in H. apply (ok_non_eq H).
  destruct (eq_var_dec a y); subst.
  assert (x \in (dom (G & y ~ AC_Unsolved_EVar))). rewrite HG. simpl_dom. apply union_left. apply union_left. apply union_left. apply union_right. apply in_singleton_self.
  assert (x \in (dom G)). simpl_dom . rewrite in_union in H4. destruct H4 as [H11 | H12]. rewrite in_singleton in H11. apply H3 in H11. inversion H11. auto.
  apply (declaration_preservation_dom HE) in H5.
  apply split_context in H5. destruct H5 as (G1' & G2' & v' & H4'); subst.
  exists v' AC_Unsolved_EVar G1' G2' (empty: ACtx).
  rewrite* concat_empty_r.

  assert (exists G', G3 = G' & a ~ AC_Unsolved_EVar). apply (tail_exists_eq n) in HG. auto.
  inversion H4. subst.
  rewrite concat_assoc in HG.
  apply eq_push_inv in HG.
  destruct HG as [_ [_ HGG]].
  apply (IHHE (ok_context HE)) in HGG.
  destruct HGG as (xv2 & yv2 & I4 & I5 & I6 & HGG').
  subst.
  exists* xv2 yv2 I4 I5 (I6 & a ~ AC_Unsolved_EVar). rewrite* concat_assoc.

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
  destruct HGG as (xv2 & yv2 & I4 & I5 & I6 & HGG').
  subst.
  exists* xv2 yv2 I4 I5 (I6 & a ~ AC_Solved_EVar t2). rewrite* concat_assoc.

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

  apply ExtCtx_LetVar; auto.
  apply AWf_LetVar with (H:=H); auto.
  apply AWf_LetVar with (H:=H); auto.

  apply ExtCtx_LetVar; auto.
  apply AWf_LetVar2 with (L:=L); auto.
  apply AWf_LetVar2 with (L:=L); auto.
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
  rewrite concat_assoc in IH. assert (WF:=IH). assert (x # I & H). apply AWf_push_inv in IH. auto.  apply AWf_left in IH.
  apply IHenv in GI; auto.

  apply eq_push_inv in H0. destruct H0 as [EQAX [EQV EQGH]]; subst.
  rewrite concat_assoc in IH.
  assert (x # I & H). apply AWf_push_inv in IH. auto.
  assert (IH2:=IH).
  apply AWf_left in IH.
  apply ExtCtx_AddSolved; auto.
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
    apply* AWf_push_inv.
  apply IHGH in GInfo.
  destruct GInfo as (H1 & H2 & H3 & [HInfo [GH1 [GH2 GH3]]]).
  exists* H1 H2 (H3 & a0 ~ AC_Unsolved_EVar).
  rewrite* concat_assoc. subst. split; auto.  split; auto.
  split; auto. constructor; auto. apply AWf_push_inv in H0. auto_star.

  assert (neqa: a0 <> a).
    assert (a \in dom H). apply (declaration_preservation_dom GH). rewrite* GInfo. simpl_dom; apply union_left. apply in_singleton_self.
    unfold not. intros eqa. subst.
    apply get_some in H1. destruct H1 as (v & H1).
    apply binds_fresh_inv with (x:= a) (E:=H) (v:=v); auto.
    apply* AWf_push_inv.
  apply IHGH in GInfo.
  destruct GInfo as (H1' & H2 & H3 & [HInfo [GH1 [GH2 GH3]]]).
  exists* H1' H2 (H3 & a0 ~ AC_Solved_EVar t).
  rewrite* concat_assoc. subst. split; auto.  split; auto.
  split; auto. constructor; auto.
  apply AWf_push_inv in H0. auto_star.
Qed.

Lemma solution_admissibility_for_extension : solution_admissibility_for_extension_def.
Proof.
  introv. gen G a t.
  induction H using env_ind.
  introv WFH WFG.
  repeat(rewrite concat_empty_r in *).
  apply ExtCtx_Solve; auto.
  apply AWf_left in WFH.
  apply* extension_reflexivity.

  introv WFH WFG.
  repeat(rewrite concat_assoc in *).
  induction v.

  apply ExtCtx_Var; auto.
  apply AWf_left in WFG.
  apply AWf_left in WFH.
  apply* IHenv.

  apply ExtCtx_TypVar; auto.
  apply AWf_left in WFG.
  apply AWf_left in WFH.
  apply* IHenv.

  apply ExtCtx_LetVar; auto.
  apply AWf_left in WFG.
  apply AWf_left in WFH.
  apply* IHenv.

  apply ExtCtx_EVar; auto.
  apply AWf_left in WFG.
  apply AWf_left in WFH.
  apply* IHenv.

  apply ExtCtx_SolvedEVar; auto.
  apply AWf_left in WFG.
  apply AWf_left in WFH.
  apply* IHenv.
Qed.

Lemma solved_variable_addition_for_extension:
  solved_variable_addition_for_extension_def.
Proof.
  introv. gen G a t.
  induction H using env_ind.
  introv WFG WFH.
  repeat(rewrite concat_empty_r in *).
  apply ExtCtx_AddSolved ; auto.
  apply AWf_left in WFH.
  apply* extension_reflexivity.

  introv WFG WFH.
  repeat(rewrite concat_assoc in *).
  induction v.

  apply ExtCtx_Var; auto.
  apply AWf_left in WFG.
  apply AWf_left in WFH.
  apply* IHenv.

  apply ExtCtx_TypVar; auto.
  apply AWf_left in WFG.
  apply AWf_left in WFH.
  apply* IHenv.

  apply ExtCtx_LetVar; auto.
  apply AWf_left in WFG.
  apply AWf_left in WFH.
  apply* IHenv.

  apply ExtCtx_EVar; auto.
  apply AWf_left in WFG.
  apply AWf_left in WFH.
  apply* IHenv.

  apply ExtCtx_SolvedEVar; auto.
  apply AWf_left in WFG.
  apply AWf_left in WFH.
  apply* IHenv.
Qed.

Lemma unsolved_variable_addition_for_extension:
  unsolved_variable_addition_for_extension_def.
Proof.
  introv. gen G a.
  induction H using env_ind.
  introv WFG WFH.
  repeat(rewrite concat_empty_r in *).
  apply* ExtCtx_Add.
  apply* extension_reflexivity.

  introv WFG WFH.
  repeat(rewrite concat_assoc in *).
  induction v.

  apply* ExtCtx_Var; auto.
  apply AWf_left in WFG.
  apply AWf_left in WFH.
  apply* IHenv.

  apply ExtCtx_TypVar; auto.
  apply AWf_left in WFG.
  apply AWf_left in WFH.
  apply* IHenv.

  apply ExtCtx_LetVar; auto.
  apply AWf_left in WFG.
  apply AWf_left in WFH.
  apply* IHenv.

  apply* ExtCtx_EVar.
  apply AWf_left in WFG.
  apply AWf_left in WFH.
  apply* IHenv.

  apply ExtCtx_SolvedEVar; auto.
  apply AWf_left in WFG.
  apply AWf_left in WFH.
  apply* IHenv.
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
  rewrite <- IG. constructor. apply ok_context in EX. auto. apply* AWf_push_inv.
  constructor. apply ok_context in EX. auto. apply* AWf_push_inv.
  constructor.

  assert (IG2 := IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H11 & H2 & [HH [EXG1H1 SoftG3H2]]).
  exists* H11 (H2 & x0 ~ AC_Var). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H3. apply empty_push_inv in H5. inversion H5. apply eq_push_inv in H4. destruct H4 as [_ [H4 _]]. inversion H4. apply eq_push_inv in H4. destruct H4 as [_ [H4 _]]. inversion H4.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t1) (G & x0 ~ AC_Typ t1)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H33 & H4 & [HH [EXG1H1 SoftG3H2]]).
  exists* H33 (H4 & x0 ~ AC_Typ t2). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. inversion H3. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5.

  (* AC_Bnd *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Bnd s1 t1) (G & x0 ~ AC_Bnd s1 t1)).
  apply* binds_push_eq. rewrite IG in H4. apply binds_middle_eq_inv in H4. inversion H4. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

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
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [_ eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3.  destruct H3 as [_ [neq _]]. inversion neq. assert (a # H). apply* AWf_push_inv. rewrite HH in H3. auto_star.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t1) (G & a ~ AC_Solved_EVar t1)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t2). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption. rewrite HH in H1. apply AWf_push_inv in H1. simpl_dom. auto_star.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Unsolved_EVar) (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t). split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]].  rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. rewrite HH in H1. apply AWf_push_inv in H1. auto_star.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar). rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  apply AWf_push_inv in H0. rewrite HH in H0. auto_star.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t). rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. apply AWf_push_inv in H0. auto_star.
Qed.

Lemma extension_order_typvar : extension_order_typvar_def.
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Typ t1 & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & t2 & [HH [EXG1H1 [eqt1t2 SoftG3H2]]]).
  exists* H3 (H4 & x0 ~ AC_Var) t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  apply tail_empty_eq with (G0:= G & x0 ~ AC_Typ t0) (G3 := G) (I := G1 & x0 ~ AC_Typ t1 & G2) (I1:= G1) (I2:=G2) (x:=x0) (vx:=AC_Typ t0) (vy:=AC_Typ t1) in IG; auto.
  destruct IG as [IG [eqt _]]. subst. auto.
  exists* H (empty: ACtx) t2. split. rewrite* concat_empty_r.
  split. auto.
  split; auto. inversion eqt; subst; auto. constructor.

  rewrite <- IG. constructor. apply ok_context in EX. auto. apply* AWf_push_inv.
  apply* awf_is_ok.

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
  apply* binds_push_eq. rewrite IG in H4. apply binds_middle_eq_inv in H4. inversion H4. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

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
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & t2 & [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar) t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [_ eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3.  destruct H3 as [_ [neq _]]. inversion neq. apply AWf_push_inv in H1. rewrite HH in H1. auto_star.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t0) (G & a ~ AC_Solved_EVar t0)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & t3 & [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t2) t3. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption. rewrite HH in H1. apply AWf_push_inv in H1. auto_star.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Unsolved_EVar) (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & t2 &  [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t) t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]].  rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. rewrite HH in H1. apply AWf_push_inv in H1. auto_star.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & t2 & [HH [ExtG1H1 [t1t2 SoftG2H2]]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar) t2. rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  apply AWf_push_inv in H0. rewrite HH in H0. auto_star.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & t2 &  [HH [ExtG1H1 [t1t2 SoftG2H2]]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t) t2. rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. apply AWf_push_inv in H0. auto_star.
Qed.

Lemma extension_order_bndvar : extension_order_bndvar_def.
Proof.
  introv EX. gen_eq G : (G1 & x ~ AC_Bnd s1 t1 & G2).
  gen G1 G2. induction EX; introv IG.
  apply empty_middle_inv in IG. inversion IG.
  (* AC_Var *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 AC_Var (G & x0 ~ AC_Var)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & s2 & t2 & [HH [EXG1H1 [eqs1s2 [eqt1t2 SoftG3H2]]]]).
  exists* H3 (H4 & x0 ~ AC_Var) s2 t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t0) (G & x0 ~ AC_Typ t0)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

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

  rewrite <- IG. apply* awf_is_ok. apply* awf_is_ok.

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
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & s2 & t2 & [HH [EXG1H1 [s1s2 [t1t2 SoftG3H2]]]]).
  exists* H4 (H5 & a ~ AC_Unsolved_EVar) s2 t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [_ eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3.  destruct H3 as [_ [neq _]]. inversion neq. apply AWf_push_inv in H1. rewrite HH in H1. auto_star.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t0) (G & a ~ AC_Solved_EVar t0)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. apply* awf_is_ok.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & s2 & t3 & [HH [EXG1H1 [s1s2 [t1t2 SoftG3H2]]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t2) s2 t3. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption. rewrite HH in H1. apply AWf_push_inv in H1. auto_star.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Unsolved_EVar) (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & s2 & t2 &  [HH [EXG1H1 [s1s2 [t1t2 SoftG3H2]]]]).
  exists* H4 (H5 & a ~ AC_Solved_EVar t) s2 t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]].  rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. rewrite HH in H1. apply AWf_push_inv in H1. auto_star.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & s2 & t2 & [HH [ExtG1H1 [s1s2 [t1t2 SoftG2H2]]]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar) s2 t2. rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  apply AWf_push_inv in H0. rewrite HH in H0. auto_star.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & s2 & t2 &  [HH [ExtG1H1 [s1s2 [t1t2 SoftG2H2]]]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t) s2 t2. rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. split. auto.  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. apply AWf_push_inv in H0. auto_star.
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
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & [HH [EXG1H1 SoftG3H2]]).
  exists* H4 (H5 & x0 ~ AC_Var). split; auto.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t. rewrite HH2. rewrite* concat_assoc.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H3. destruct H3 as [eqa [eqv eqg]]. inversion eqv.

  (* AC_Typ *)
  destruct (eq_var_dec x x0); subst.
  assert (binds x0 (AC_Typ t1) (G & x0 ~ AC_Typ t1)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

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
  apply* binds_push_eq. rewrite IG in H4. apply binds_middle_eq_inv in H4. inversion H4. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

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
  rewrite <- IG. constructor. apply ok_context in EX. auto. apply* AWf_push_inv.
  constructor. apply ok_context in EX. auto. apply* AWf_push_inv.
  constructor.

  assert (IG2 := IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H11 & H2 & [HH [EXG1H1 SoftG3H2]]).
  exists* H11 (H2 & a ~ AC_Unsolved_EVar). split; auto.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1. rewrite concat_assoc. auto.
  right. exists t. rewrite HH2. rewrite concat_assoc. auto.
  split; auto.
  intros. constructor. apply* SoftG3H2. rewrite HG2 in H3. inversion H3. apply empty_push_inv in H5. inversion H5. apply eq_push_inv in H4. destruct H4 as [eqa [_ eqg]]. rewrite eqg in H5. auto. apply eq_push_inv in H4. destruct H4 as [_ [eqv _]]. inversion eqv.
  destruct HH as [HH1 | (t & HH2)].
  rewrite HH1 in H1. apply AWf_push_inv in H1. auto_star.
  rewrite HH2 in H1. apply AWf_push_inv in H1. auto_star.

  (* AC_Solved_EVar *)
  destruct (eq_var_dec x a); subst.
  assert (binds a (AC_Solved_EVar t1) (G & a ~ AC_Solved_EVar t1)).
  apply* binds_push_eq. rewrite IG in H3. apply binds_middle_eq_inv in H3. inversion H3. rewrite <- IG. apply* awf_is_ok.

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
  rewrite HH1 in H1. apply AWf_push_inv in H1. auto_star.
  rewrite HH2 in H1. apply AWf_push_inv in H1. auto_star.

  (* AC_Solve *)
  destruct (eq_var_dec x a); subst.
  exists* H (empty: ACtx).
  split. right. exists t. rewrite concat_empty_r. auto.
  split. apply tail_empty_eq with (G0:= G & a ~ AC_Unsolved_EVar) (G3 := G) (I := G1 & a ~ AC_Unsolved_EVar & G2) (I1:= G1) (I2:=G2) (x:=a) (vx:=AC_Unsolved_EVar) (vy:=AC_Unsolved_EVar)in IG; auto.
  destruct IG as [IG _]. subst. auto.
  rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.
  constructor. apply* ok_context. apply* AWf_push_inv.
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
  rewrite HH1 in H1. apply AWf_push_inv in H1. auto_star.
  rewrite HH2 in H1. apply AWf_push_inv in H1. auto_star.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H1 (H2 & a ~ AC_Unsolved_EVar).
  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1. split. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH1 in H0. apply AWf_push_inv in H0. auto_star.
  split. right. exists t1. rewrite HH2. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH2 in H0.  apply AWf_push_inv in H0. auto_star.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & [HH [ExtG1H1 SoftG2H2]]).
  exists* H2 (H3 & a ~ AC_Solved_EVar t).

  destruct HH as [HH1 | (t1 & HH2)].
  rewrite HH1. split. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH1 in H0. apply AWf_push_inv in H0. auto_star.
  split. right. exists t1. rewrite HH2. rewrite concat_assoc. auto.
  split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH2 in H0. apply AWf_push_inv in H0. auto_star.
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
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H3 & H4 & t2 & [HH [EXG1H1 [eqt1t2 SoftG3H2]]]).
  exists* H3 (H4 & x ~ AC_Var) t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5. apply eq_push_inv in H5. destruct H5 as [_ [H5 _]]. inversion H5.

  (* AC_Typ *)
  destruct (eq_var_dec x a); subst.
  apply tail_empty_eq with (G0:= G & a ~ AC_Typ t0) (G3 := G) (I := G1 & a ~ AC_Solved_EVar t1 & G2) (I1:= G1) (I2:=G2) (x:=a) (vx:=AC_Typ t0) (vy:=AC_Solved_EVar t1) in IG; auto.
  destruct IG as [IG [eqt _]]. inversion eqt.
  rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.
  apply* awf_is_ok.

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
  apply* binds_push_eq. rewrite IG in H4. apply binds_middle_eq_inv in H4. inversion H4. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

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
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & t2 & [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H4 (H5 & a0 ~ AC_Unsolved_EVar) t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [_ eqg]]. rewrite eqg in H6. assumption. apply eq_push_inv in H3.  destruct H3 as [_ [neq _]]. inversion neq. apply AWf_push_inv in H1. rewrite HH in H1. auto_star.

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
  rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.
  apply* awf_is_ok.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & t3 & [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H4 (H5 & a0 ~ AC_Solved_EVar t2) t3. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H3. apply empty_push_inv in H7. inversion H7. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. inversion eqv. apply eq_push_inv in H6. destruct H6 as [EQA [eqv eqg]]. rewrite eqg in H7. assumption. rewrite HH in H1. apply AWf_push_inv in H1. auto_star.

  (* AC_Solve *)
  destruct (eq_var_dec a0 a); subst.
  assert (binds a (AC_Unsolved_EVar) (G & a ~ AC_Unsolved_EVar)).
  apply* binds_push_eq. rewrite IG in H2. apply binds_middle_eq_inv in H2. inversion H2. rewrite <- IG. constructor. apply* ok_context. apply* AWf_push_inv.

  assert (IG2:=IG). apply tail_exists_eq in IG2; auto. destruct IG2 as (G3 & HG2). rewrite HG2 in IG. rewrite concat_assoc in IG.
  apply eq_push_inv in IG. destruct IG as [_ [_ IG]].
  apply IHEX in IG. destruct IG as (H4 & H5 & t2 &  [HH [EXG1H1 [t1t2 SoftG3H2]]]).
  exists* H4 (H5 & a0 ~ AC_Solved_EVar t) t2. split; auto.
  rewrite HH. rewrite concat_assoc. auto.
  split; auto.
  split; auto.
  rewrite HG2. intros. constructor. apply SoftG3H2. inversion H2. apply empty_push_inv in H6. inversion H6. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]].  rewrite eqg in H6. assumption. apply eq_push_inv in H3. destruct H3 as [EQA [eqv eqg]]. inversion eqv. rewrite HH in H1. apply AWf_push_inv in H1. auto_star.

  (* AC_Add *)
  apply IHEX in IG. destruct IG as (H1 & H2 & t2 & [HH [ExtG1H1 [t1t2 SoftG2H2]]]).
  exists* H1 (H2 & a0 ~ AC_Unsolved_EVar) t2. rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. apply AWf_push_inv in H0. auto_star.

  (* AC_AddSolved *)
  apply IHEX in IG. destruct IG as (H2 & H3 & t2 &  [HH [ExtG1H1 [t1t2 SoftG2H2]]]).
  exists* H2 (H3 & a0 ~ AC_Solved_EVar t) t2. rewrite HH.
  split. rewrite concat_assoc. auto.
  split. auto. split. auto. intros SoftG2. constructor. apply* SoftG2H2.
  rewrite HH in H0. apply AWf_push_inv in H0. auto_star.
Qed.

Lemma extension_weakening_awterm: extension_weakening_awterm_def.
Proof.
  introv ga gh. assert (wf: ok H). apply* ok_preservation.
  gen H.
  induction ga; introv gh wf; auto; try(apply split_bind_context in H; destruct H as (G1 & G2 & gi); rewrite gi in gh).
  apply extension_order_var in gh. destruct gh as (H1 & H2 & [hi _]).
  rewrite hi. constructor*.
  apply* binds_middle_eq.
  rewrite hi in wf. apply* ok_middle_inv_r.

  apply extension_order_typvar in gh. destruct gh as (H1 & H2 & t2 & [hi _]).
  rewrite hi. apply* AWTerm_TypVar.
  apply* binds_middle_eq.
  rewrite hi in wf. apply* ok_middle_inv_r.

  apply extension_order_bndvar in gh. destruct gh as (H1 & H2 & s2 & t2 & [hi _]).
  rewrite hi. apply* AWTerm_LetVar.
  rewrite hi in wf. apply* binds_middle_eq.
  apply* ok_middle_inv_r.

  apply extension_order_unsolved_evar in gh. destruct gh as (H1 & H2 & [hi _]).
  destruct hi as [hi1 | (t & hi1)];
    try(rewrite hi1);
    [apply* AWTerm_EVar | apply* AWTerm_Solved_EVar];
    try(rewrite hi1 in wf; apply* binds_middle_eq);try(apply* ok_middle_inv_r).

  apply extension_order_solved_evar in gh. destruct gh as (H1 & H2 & t2 & [hi _]).
  rewrite hi. apply* AWTerm_Solved_EVar.
  rewrite hi in wf. apply* binds_middle_eq.
  apply* ok_middle_inv_r.

  assert (AWf G). apply awf_context in gh. assumption.
  assert (AWf H1). apply awf_preservation in gh. assumption.
  apply AWTerm_Lam with (L:=L \u dom H1 \u dom G). introv notin. apply* H0.

  assert (AWf G). apply awf_context in gh. assumption.
  assert (AWf H1). apply awf_preservation in gh. assumption.
  apply AWTerm_Pi with (L:=L \u dom H1 \u dom G). apply* IHga.
  introv notin. apply* H0.

  assert (AWf G). apply awf_context in gh. assumption.
  assert (AWf H1). apply awf_preservation in gh. assumption.
  apply AWTerm_Let with (L:=L \u dom H1 \u dom G). apply* IHga.
  introv notin. apply* H0.
Qed.

Lemma extension_equality_preservation: extension_equality_preservation_def.
Proof.
  introv EQ GH.
  assert (WF: AWf H). apply* awf_preservation.
  gen a b. induction GH; introv EQ; auto; apply AWf_left in WF.

  rewrite tsubst_add_var in *.
  rewrite tsubst_add_var in *.
  apply* IHGH.

  rewrite tsubst_add_typvar in *.
  rewrite tsubst_add_typvar in *.
  apply* IHGH.

  assert (EQ2 :ACtxTSubst G (ATSubst x t1 a) = ACtxTSubst G (ATSubst x t1 b)).
  rewrite <- cons_to_push in *.
  unfold ACtxTSubst in *. simpl in EQ. auto.
  clear EQ.
  apply IHGH in EQ2; auto.
  rewrite tsubst_add_bndvar.
  rewrite tsubst_add_bndvar.
  assert (x # H). apply* AWf_push_inv.
  apply AWf_left in H1.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  rewrite <- H3.
  rewrite <- distributivity_ctxtsubst_tsubst; auto.
  rewrite <- distributivity_ctxtsubst_tsubst; auto.

  rewrite tsubst_add_evar in *.
  rewrite tsubst_add_evar in *.
  apply* IHGH.

  assert (EQ2 :ACtxTSubst G (ATSubst a t1 a0) = ACtxTSubst G (ATSubst a t1 b)).
  rewrite <- cons_to_push in *.
  unfold ACtxTSubst in *. simpl in EQ. auto.
  clear EQ.
  assert (a # H). apply* AWf_push_inv.
  apply AWf_left in H1.
  apply IHGH in EQ2; auto.
  rewrite tsubst_add_solved_evar.
  rewrite tsubst_add_solved_evar.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  rewrite <- H2.
  rewrite <- distributivity_ctxtsubst_tsubst; auto.
  rewrite <- distributivity_ctxtsubst_tsubst; auto.

  rewrite tsubst_add_evar in EQ.
  rewrite tsubst_add_evar in EQ.
  assert (a # H). apply* AWf_push_inv.
  apply AWf_left in H1.
  apply IHGH in EQ; auto.
  rewrite tsubst_add_solved_evar.
  rewrite tsubst_add_solved_evar.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  rewrite EQ. auto.

  rewrite * tsubst_add_evar.
  rewrite * tsubst_add_evar.

  rewrite tsubst_add_solved_evar.
  rewrite tsubst_add_solved_evar.
  assert (a # H). apply* AWf_push_inv.
  apply AWf_left in H0.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  apply IHGH in EQ; auto.
  rewrite EQ. auto.
Qed.

Lemma substitution_extension_invariance_right: forall G t H,
    ExtCtx G H ->
    ACtxSubst H t = ACtxSubst G (ACtxSubst H t).
Proof.
  introv gh.
  assert (wf: AWf H). apply* awf_preservation.
  gen t. induction gh; introv.
  rewrite* subst_empty_env.
  rewrite* subst_empty_env.

  repeat(rewrite subst_add_var). apply AWf_left in wf. apply* IHgh.

  repeat(rewrite subst_add_typvar). apply AWf_left in wf. apply* IHgh.

  repeat(rewrite subst_add_bndvar).
  assert (wfh:=wf). apply AWf_left in wfh.
  assert (wfg:=H0). apply AWf_left in wfg.
  assert (x # H). apply* AWf_push_inv.
  assert (x # G). apply* AWf_push_inv.
  rewrite distributivity_ctxsubst_subst; auto.
  rewrite distributivity_ctxsubst_subst; auto.
  rewrite distributivity_ctxsubst_subst; auto.
  rewrite <- IHgh; auto.
  rewrite <- IHgh; auto.
  repeat(rewrite <- H3).
  rewrite <- distributivity_ctxsubst_subst; auto.
  rewrite asubst_fresh with (u:= (ACtxSubst G t1)); auto.
  apply* notin_ctxsubst.
  apply* notin_subst.
  apply* notin_bnd.

  repeat(rewrite subst_add_evar).
  apply AWf_left in wf.
  apply* IHgh.

  repeat(rewrite subst_add_solved_evar).
  assert (wfh:=wf). apply AWf_left in wfh.
  assert (wfg:=H0). apply AWf_left in wfg.
  assert (a # H). apply* AWf_push_inv.
  assert (a # G). apply* AWf_push_inv.
  rewrite distributivity_ctxsubst_subst; auto.
  rewrite distributivity_ctxsubst_subst; auto.
  rewrite distributivity_ctxsubst_subst; auto.
  rewrite <- IHgh; auto.
  rewrite <- IHgh; auto.
  repeat(rewrite <- H2).
  rewrite <- distributivity_ctxsubst_subst; auto.
  rewrite asubst_fresh with (u:= (ACtxSubst G t1)); auto.
  apply* notin_ctxsubst.
  apply* notin_subst.
  apply* notin_solved_evar.

  rewrite subst_add_evar.
  repeat(rewrite subst_add_solved_evar).
  apply AWf_left in wf.
  apply* IHgh.

  repeat(rewrite subst_add_evar).
  apply AWf_left in wf.
  apply* IHgh.

  repeat(rewrite subst_add_solved_evar).
  apply AWf_left in wf.
  apply* IHgh.
Qed.

Lemma substitution_extension_invariance_left: forall G t H,
    ExtCtx G H ->
    ACtxSubst H t = ACtxSubst H (ACtxSubst G t).
Proof.
  introv gh.
  assert (wf: AWf H). apply* awf_preservation.
  gen t. induction gh; introv.
  rewrite* subst_empty_env.
  rewrite* subst_empty_env.

  repeat(rewrite subst_add_var). apply AWf_left in wf. apply* IHgh.

  repeat(rewrite subst_add_typvar). apply AWf_left in wf. apply* IHgh.

  repeat(rewrite subst_add_bndvar).
  apply AWf_left in wf.
  assert (x # H). apply* AWf_push_inv.
  rewrite distributivity_ctxsubst_subst; auto.
  rewrite distributivity_ctxsubst_subst; auto.
  rewrite <- IHgh; auto.
  repeat(rewrite <- H3).
  rewrite <- distributivity_ctxsubst_subst; auto.
  rewrite <- distributivity_ctxsubst_subst; auto.
  rewrite* subst_twice. apply* notin_bnd.

  repeat(rewrite subst_add_evar).
  apply AWf_left in wf.
  apply* IHgh.

  repeat(rewrite subst_add_solved_evar).
  apply AWf_left in wf.
  assert (a # H). apply* AWf_push_inv.
  rewrite distributivity_ctxsubst_subst; auto.
  rewrite distributivity_ctxsubst_subst; auto.
  rewrite <- IHgh; auto.
  repeat(rewrite <- H2).
  rewrite <- distributivity_ctxsubst_subst; auto.
  rewrite <- distributivity_ctxsubst_subst; auto.
  rewrite* subst_twice. apply* notin_solved_evar.

  rewrite subst_add_evar.
  repeat(rewrite subst_add_solved_evar).
  apply AWf_left in wf.
  assert (a # H). apply* AWf_push_inv.
  rewrite distributivity_ctxsubst_subst; auto.
  rewrite distributivity_ctxsubst_subst; auto.
  rewrite <- IHgh; auto.

  repeat(rewrite subst_add_evar).
  apply AWf_left in wf.
  apply* IHgh.

  repeat(rewrite subst_add_solved_evar).
  apply AWf_left in wf.
  assert (a # H). apply* AWf_push_inv.
  rewrite distributivity_ctxsubst_subst; auto.
  rewrite distributivity_ctxsubst_subst; auto.
  rewrite <- IHgh; auto.
Qed.

Lemma substitution_extension_invariance: substitution_extension_invariance_def.
Proof.
  introv. split.
  apply* substitution_extension_invariance_left.
  apply* substitution_extension_invariance_right.
Qed.

Lemma substitution_extension_invariance_type_left: forall G t H,
    ExtCtx G H ->
    ACtxTSubst H t = ACtxTSubst H (ACtxTSubst G t).
Proof.
  introv gh.
  assert (wf:AWf H). apply* awf_preservation.
  gen t. induction gh; introv.
  rewrite* tsubst_empty_env.
  rewrite* tsubst_empty_env.

  repeat(rewrite tsubst_add_var). apply AWf_left in wf. apply* IHgh.

  repeat(rewrite tsubst_add_typvar). apply AWf_left in wf. apply* IHgh.

  repeat(rewrite tsubst_add_bndvar).
  apply AWf_left in wf.
  assert (x # H). apply* AWf_push_inv.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  rewrite <- IHgh; auto.
  repeat(rewrite <- H3).
  rewrite <- distributivity_ctxtsubst_tsubst; auto.
  rewrite <- distributivity_ctxtsubst_tsubst; auto.
  rewrite* tsubst_twice. apply* notin_bnd.

  repeat(rewrite tsubst_add_evar).
  apply AWf_left in wf.
  apply* IHgh.

  repeat(rewrite tsubst_add_solved_evar).
  apply AWf_left in wf.
  assert (a # H). apply* AWf_push_inv.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  rewrite <- IHgh; auto.
  repeat(rewrite <- H2).
  rewrite <- distributivity_ctxtsubst_tsubst; auto.
  rewrite <- distributivity_ctxtsubst_tsubst; auto.
  rewrite* tsubst_twice. apply* notin_solved_evar.

  rewrite tsubst_add_evar.
  repeat(rewrite tsubst_add_solved_evar).
  apply AWf_left in wf.
  assert (a # H). apply* AWf_push_inv.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  rewrite <- IHgh; auto.

  repeat(rewrite tsubst_add_evar).
  apply AWf_left in wf.
  apply* IHgh.

  repeat(rewrite tsubst_add_solved_evar).
  apply AWf_left in wf.
  assert (a # H). apply* AWf_push_inv.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  rewrite distributivity_ctxtsubst_tsubst; auto.
  rewrite <- IHgh; auto.
Qed.

Lemma extension_transitivity : extension_transitivity_def.
Proof.
  introv GH HI.
  assert (WFI:AWf I). apply* awf_preservation.
  assert (WFH:AWf H). apply* awf_context.
  assert (WFG:AWf G). apply* awf_context.
  gen G.

  (* ExtCtx_Empty *)
  induction HI; introv GH WFG; auto;
  try(assert (WFI2:=WFI); apply AWf_left in WFI2);
  try(assert (WFH2:=WFH); apply AWf_left in WFH2).

  (* ExtCtx_Var *)
  inversion GH;
  try(apply eq_push_inv in H3; destruct H3 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H4; inversion H4.
  subst. clear EQV.
  apply AWf_left in WFG.
  apply IHHI in H4; auto.

  (* ExtCtx_TypVar *)
  inversion GH;
  try(apply eq_push_inv in H4; destruct H4 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H5; inversion H5.
  subst. clear EQV.
  assert (WFG2:=WFG). apply AWf_left in WFG2.

  apply IHHI with (G0:=G1) in H5; auto.
  apply ExtCtx_TypVar; auto.
  assert (ACtxSubst H (ACtxSubst G t0) = ACtxSubst H (ACtxSubst G t1)). rewrite* H9.
  rewrite <- substitution_extension_invariance_left in H3; auto.
  rewrite <- substitution_extension_invariance_left in H3; auto.
  rewrite H3; auto.

  (* ExtCtx_LetVar *)
  inversion GH;
  try(apply eq_push_inv in H5; destruct H5 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H6; inversion H6.
  subst. clear EQV.
  assert (WFG2:=WFG). apply AWf_left in WFG2.

  apply IHHI with (G0:=G1) in H6; auto.
  apply ExtCtx_LetVar; auto.
  assert (ACtxTSubst H (ACtxTSubst G s0) = ACtxTSubst H (ACtxTSubst G s1)). rewrite* H9.
  repeat(rewrite <- substitution_extension_invariance_type_left in H4; auto).
  rewrite <- H2; auto.
  assert (ACtxSubst H (ACtxSubst G t0) = ACtxSubst H (ACtxSubst G t1)). rewrite* H11.
  repeat(rewrite <- substitution_extension_invariance_left in H4; auto).
  rewrite H4; auto.

  (* ExtCtx_EVar *)
  inversion GH;
  try(apply eq_push_inv in H3; destruct H3 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H4; inversion H4.
  subst. clear EQV. apply* ExtCtx_EVar.
  assert (WFG2:=WFG). apply AWf_left in WFG2.
  apply IHHI with (G0:=G1)  in H4; auto.

  subst. clear EQV.
  apply IHHI with (G0:=G0)  in H4; auto.

  (* ExtCtx_SolvedEVar *)
  inversion GH;
  try(apply eq_push_inv in H4; destruct H4 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H5; inversion H5.
  subst. clear EQV.
  assert (WFG2:=WFG). apply AWf_left in WFG2.
  apply IHHI with (G0:=G1)  in H5; auto.
  apply ExtCtx_SolvedEVar; auto.
  assert (ACtxSubst H (ACtxSubst G t0) = ACtxSubst H (ACtxSubst G t1)). rewrite* H9.
  repeat(rewrite <- substitution_extension_invariance_left in H3; auto).
  rewrite H3; auto.

  subst. clear EQV.
  assert (WFG2:=WFG). apply AWf_left in WFG2.
  apply IHHI with (G0:=G1)  in H5; auto.

  subst. clear EQV.
  apply IHHI with (G0:=G0)  in H5; auto.

  (* ExtCtx_Solve *)
  inversion GH;
  try(apply eq_push_inv in H3; destruct H3 as [EQX [EQV EQ]]; inversion EQV).
  apply empty_push_inv in H4; inversion H4.
  subst. clear EQV.
  assert (WFG2:=WFG). apply AWf_left in WFG2.
  apply IHHI with (G0:=G1)  in H4; auto.

  subst. clear EQV.
  apply IHHI with (G0:=G0)  in H4; auto.

  (* ExtCtx_Add *)
  apply IHHI in GH; auto.

  (* ExtCtx_AddSolved *)
  apply IHHI in GH; auto.
Qed.

Lemma tail_empty: forall G1 G2 G3 a v,
    AWf (G1 & a ~ v) ->
    AWf (G2 & a ~ v & G3) ->
    G1 & a ~ v = G2 & a ~ v & G3 ->
    G3 = empty.
Proof.
  introv wf1 wf2 sub.
  induction G3 using env_ind; auto.
  assert (a # (G3 & x ~ v0)). apply awf_is_ok in wf2. apply ok_middle_inv in wf2. auto_star.
  rewrite concat_assoc in sub.
  apply eq_push_inv in sub.
  destruct sub as [eqx [eqv eqg]]. subst.
  assert (x \in dom (G3 & x ~ v0)). simpl_dom. apply union_left. apply in_singleton_self. apply H in H0. inversion H0.
Qed.

Lemma parallel_extension_solution: parallel_extension_solution_def.
Proof.
  introv ext sub wfg.
  gen G2. induction H2 using env_ind; introv ext wfg.
  rewrite concat_empty_r in *.

  inversion ext;
  try(apply eq_push_inv in H2;
  destruct H2 as [eqx [eqv eqh]]; inversion eqv).
  apply empty_push_inv in H; inversion H.
  subst.
    assert (binds a AC_Unsolved_EVar (G1 & a ~ AC_Unsolved_EVar & G2)).
    apply binds_middle_eq. apply awf_is_ok in wfg. apply* ok_middle_inv_r.
    rewrite <- H0 in H. apply binds_push_eq_inv in H. inversion H.
  subst.
    assert (G2=empty). apply tail_empty in H0; auto. apply* awf_context.
    subst. rewrite concat_empty_r in *. apply* ExtCtx_SolvedEVar. apply eq_push_inv in H0. destruct H0 as [_ [_ eqg]]. subst. auto_star.

  apply eq_push_inv in H0; destruct H0 as [_ [inv _]]; inversion inv.
  apply eq_push_inv in H0. destruct H0 as [x1 [x2 x3]]. subst.
  assert (a \in dom H1). apply* declaration_preservation_dom. simpl_dom. apply union_left. apply union_right. apply in_singleton_self.
  apply AWf_push_inv in H4. apply H4 in H. false H.

  inversion ext; rewrite concat_assoc in *;
    try(apply eq_push_inv in H3; destruct H3 as [eqx [eqv eqh]]; subst);
    try(assert (a <> x);
        [apply awf_is_ok in H6; rewrite <- concat_empty_r in H6; apply ok_non_eq in H6; auto |]);
    try(assert (H00:=H0);
        try(apply tail_exists_eq in H0; auto);
        try(destruct H0 as (G22 & H0); subst; rewrite concat_assoc in *));
    try(apply eq_push_inv in H00; destruct H00 as [_ [_ eqg]]; subst);
    try(apply IHenv in H4).

  apply empty_push_inv in H; inversion H.

  apply* ExtCtx_Var. apply* AWf_left.
  apply* ExtCtx_TypVar. apply* AWf_left.
  apply* ExtCtx_LetVar. apply* AWf_left.
  apply* ExtCtx_EVar. apply* AWf_left.
  apply* ExtCtx_SolvedEVar. apply* AWf_left.
  apply* ExtCtx_Solve. apply* AWf_left.
  apply* ExtCtx_Add. auto.
Qed.

Lemma parallel_variable_update: parallel_variable_update_def.
Proof.
  introv ext t0t1 t1t2 wfg wfh.
  gen G2. induction H2 using env_ind; introv ext wfg.
  rewrite concat_empty_r in *.

  inversion ext;
  try(apply eq_push_inv in H2;
  destruct H2 as [eqx [eqv eqh]]; inversion eqv).
  apply empty_push_inv in H; inversion H.
  subst.
    assert (binds a AC_Unsolved_EVar (G1 & a ~ AC_Unsolved_EVar & G2)).
    apply binds_middle_eq. apply awf_is_ok in wfg. apply* ok_middle_inv_r.
    rewrite <- H0 in H. apply binds_push_eq_inv in H. inversion H.
  subst.
    assert (G2=empty). apply tail_empty in H0; auto. apply* awf_context.
    subst. rewrite concat_empty_r in *. apply* ExtCtx_SolvedEVar. apply eq_push_inv in H0. destruct H0 as [_ [_ eqg]]. subst. auto_star.

  apply eq_push_inv in H0; destruct H0 as [_ [inv _]]; inversion inv.
  apply eq_push_inv in H0. destruct H0 as [x1 [x2 x3]]. subst.
  assert (a \in dom H1). apply* declaration_preservation_dom. simpl_dom. apply union_left. apply union_right. apply in_singleton_self.
  apply AWf_push_inv in H4. apply H4 in H. false H.

  inversion ext; rewrite concat_assoc in *;
    try(apply eq_push_inv in H3; destruct H3 as [eqx [eqv eqh]]; subst);
    try(assert (a <> x);
        [apply awf_is_ok in H6; rewrite <- concat_empty_r in H6; apply ok_non_eq in H6; auto |]);
    try(assert (H00:=H0);
        try(apply tail_exists_eq in H0; auto);
        try(destruct H0 as (G22 & H0); subst; rewrite concat_assoc in *));
    try(apply eq_push_inv in H00; destruct H00 as [_ [_ eqg]]; subst);
    try(apply IHenv in H4).

  apply empty_push_inv in H; inversion H.

  apply* ExtCtx_Var. apply* AWf_left. apply* AWf_left.

  apply* ExtCtx_TypVar.
  rewrite subst_add_ctx. pattern (ACtxSubst (H1 & a ~ AC_Solved_EVar t2 & H2) t4) at 1 ; rewrite subst_add_ctx. repeat(rewrite subst_add_solved_evar).
  assert (AWf H1). repeat(apply* AWf_left).
  assert (a # H1). do 2 apply AWf_left in wfh. apply AWf_push_inv in wfh; auto.
  repeat(rewrite distributivity_ctxsubst_subst; auto). repeat(rewrite <- t1t2). repeat(rewrite<- t0t1). repeat(rewrite <- distributivity_ctxsubst_subst; auto). repeat(rewrite <- subst_add_solved_evar). repeat(rewrite <- subst_add_ctx). auto.
    apply* AWf_left. apply* AWf_left.

  apply* ExtCtx_LetVar.
  rewrite tsubst_add_ctx. pattern (ACtxTSubst (H1 & a ~ AC_Solved_EVar t2 & H2) s2) at 1 ; rewrite tsubst_add_ctx. repeat(rewrite tsubst_add_solved_evar).
  assert (AWf H1). repeat(apply* AWf_left).
  assert (a # H1). do 2 apply AWf_left in wfh. apply AWf_push_inv in wfh; auto.
  repeat(rewrite distributivity_ctxtsubst_tsubst; auto). repeat(rewrite <- t1t2). repeat(rewrite<- t0t1). repeat(rewrite <- distributivity_ctxtsubst_tsubst; auto). repeat(rewrite <- tsubst_add_solved_evar). repeat(rewrite <- tsubst_add_ctx). auto.

  rewrite subst_add_ctx. pattern (ACtxSubst (H1 & a ~ AC_Solved_EVar t2 & H2) t4) at 1 ; rewrite subst_add_ctx. repeat(rewrite subst_add_solved_evar).
  assert (AWf H1). repeat(apply* AWf_left).
  assert (a # H1). do 2 apply AWf_left in wfh. apply AWf_push_inv in wfh; auto.
  repeat(rewrite distributivity_ctxsubst_subst; auto). repeat(rewrite <- t1t2). repeat(rewrite<- t0t1). repeat(rewrite <- distributivity_ctxsubst_subst; auto). repeat(rewrite <- subst_add_solved_evar). repeat(rewrite <- subst_add_ctx). auto.
    apply* AWf_left. apply* AWf_left.

  apply* ExtCtx_EVar. apply* AWf_left. apply* AWf_left.
  apply* ExtCtx_SolvedEVar.
  rewrite subst_add_ctx. pattern (ACtxSubst (H1 & a ~ AC_Solved_EVar t2 & H2) t4) at 1 ; rewrite subst_add_ctx. repeat(rewrite subst_add_solved_evar).
  assert (AWf H1). repeat(apply* AWf_left).
  assert (a # H1). do 2 apply AWf_left in wfh. apply AWf_push_inv in wfh; auto.
  repeat(rewrite distributivity_ctxsubst_subst; auto). repeat(rewrite <- t1t2). repeat(rewrite<- t0t1). repeat(rewrite <- distributivity_ctxsubst_subst; auto). repeat(rewrite <- subst_add_solved_evar). repeat(rewrite <- subst_add_ctx). auto.
    apply* AWf_left. apply* AWf_left.

  apply* ExtCtx_Solve. apply* AWf_left. apply* AWf_left.

  apply eq_push_inv in H0; auto.
  destruct H0 as [eqx [eqv eqh]]. subst.
  apply IHenv in H3; auto.
  apply* AWf_left.

  apply eq_push_inv in H0; auto.
  destruct H0 as [eqx [eqv eqh]]. subst.
  apply IHenv in H3; auto.
  apply* AWf_left.
Qed.