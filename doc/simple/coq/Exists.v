Require Import CtxExtension.
Require Import LibLN.
Require Import AlgoDef.
Require Import UtilityEnv.
Require Import DeclDef.
Require Import DeclInfra.
Require Import AlgoInfra.
Require Import Subst.
Require Import LibReflect.

Definition cpltctxsubst_exists_def := forall G e,
    AWf G ->
    AWTermT G e ->
    CompleteCtx G ->
    exists t, ACpltCtxSubst G e t
.

(* admitted lemma with issue about quantification *)

Lemma lam_solve: forall G x e t,
    AWf (G & x ~ AC_Var) ->
    ACpltCtxSubst (G & x ~ AC_Var) (AT_Expr (e @ x)) t ->
    exists d, ACpltCtxSubst G (AT_Expr (AE_Lam e)) d.
Admitted.

Lemma pi_solve: forall G x e1 e2 t1 t2,
    AWf (G & x ~ AC_Var) ->
    ACpltCtxSubst G e1 t1 ->
    ACpltCtxSubst (G & x ~ AC_Var) (e2 @' x) t2 ->
    exists d, ACpltCtxSubst G (AT_Expr (AE_Pi e1 e2)) d.
Admitted.

Lemma forall_solve: forall G x e t,
    AWf (G & x ~ AC_TVar) ->
    ACpltCtxSubst (G & x ~ AC_TVar) (e @#' x) t ->
    exists d, ACpltCtxSubst G (AT_Expr (AE_Forall e)) d.
Admitted.

(* another form of awterm, which does not care about bound variables *)

Inductive AWTermA : ACtx -> AType -> Prop :=
  | AWTermA_Var : forall G x, binds x AC_Var G -> AWTermA G (AT_Expr (AE_FVar x))
  | AWTermA_BVar : forall G x, AWTermA G (AT_Expr (AE_BVar x))
  | AWTermA_TypVar : forall G x t, binds x (AC_Typ t) G -> AWTermA G (AT_Expr (AE_FVar x))
  | AWTermA_TFVar : forall G a, binds a AC_TVar G -> AWTermA G (AT_TFVar a)
  | AWTermA_TBVar : forall G x, AWTermA G (AT_TBVar x)
  | AWTermA_EVar : forall G a, binds a AC_Unsolved_EVar G -> AWTermA G (AT_EVar a)
  | AWTermA_Solved_EVar : forall G a t, binds a (AC_Solved_EVar t) G -> AWTermA G (AT_EVar a)
  | AWTermA_Star: forall G, AWTermA G (AT_Expr AE_Star)
  | AWTermA_App: forall e1 e2 G, AWTermA G (AT_Expr e1) -> AWTermA G (AT_Expr e2) -> AWTermA G (AT_Expr (AE_App e1 e2))
  | AWTermA_Lam: forall e G , AWTermA G (AT_Expr e)  -> AWTermA G (AT_Expr (AE_Lam e))
  | AWTermA_Pi: forall t1 t2 G, AWTermA G t1 -> AWTermA G t2 -> AWTermA G (AT_Expr (AE_Pi t1 t2))
  | AWTermA_CastUp : forall e G, AWTermA G (AT_Expr e) -> AWTermA G (AT_Expr (AE_CastUp e))
  | AWTermA_CastDn : forall e G, AWTermA G (AT_Expr e) -> AWTermA G (AT_Expr (AE_CastDn e))
  | AWTermA_Ann: forall e1 e2 G, AWTermA G (AT_Expr e1) -> AWTermA G e2 -> AWTermA G (AT_Expr (AE_Ann e1 e2))
  | AWTermA_Forall: forall e G, AWTermA G e -> AWTermA G (AT_Expr (AE_Forall e))
.

(* helper lemmas *)
Hint Constructors AWTermA ACpltCtxSubst.
Hint Resolve awf_is_ok AWf_left complete_part_left complete_part_right.
Lemma awterma_open: forall G k u e,
    AWTermA G (AT_Expr (AOpenRec k u e)) ->
    AWTermA G (AT_Expr e)
with awterma_opent: forall G k u e,
    AWTermA G (AOpenTypRec k u e) ->
    AWTermA G e.
Proof.
  introv wt. gen k u. induction e; intros; simpls.
  case_nat*. assumption. assumption.
  inversion wt; subst. apply AWTermA_App. apply* IHe1. apply* IHe2.
  inversion wt; subst. apply AWTermA_Lam. apply* IHe.
  inversion wt; subst. apply AWTermA_Pi. apply* awterma_opent. apply* awterma_opent.
  inversion wt; subst. apply AWTermA_CastUp. apply* IHe.
  inversion wt; subst. apply AWTermA_CastDn. apply* IHe.
  inversion wt; subst. apply AWTermA_Ann. apply* IHe. apply* awterma_opent.
  inversion wt; subst. apply AWTermA_Forall. apply* awterma_opent.
Proof.
  introv wt. gen k u. induction e; intros; simpls.
  assumption. assumption. assumption.
  apply* awterma_open.
Qed.

Lemma awterma_topen: forall G k u e,
    AWTermA G (AT_Expr (ATOpenRec k u e)) ->
    AWTermA G (AT_Expr e)
with awterma_topent: forall G k u e,
    AWTermA G (ATOpenTypRec k u e) ->
    AWTermA G e.
Proof.
  introv wt. gen k u. induction e; intros; simpls.
  assumption. assumption. assumption.
  inversion wt; subst. apply AWTermA_App. apply* IHe1. apply* IHe2.
  inversion wt; subst. apply AWTermA_Lam. apply* IHe.
  inversion wt; subst. apply AWTermA_Pi. apply* awterma_topent. apply* awterma_topent.
  inversion wt; subst. apply AWTermA_CastUp. apply* IHe.
  inversion wt; subst. apply AWTermA_CastDn. apply* IHe.
  inversion wt; subst. apply AWTermA_Ann. apply* IHe. apply* awterma_topent.
  inversion wt; subst. apply AWTermA_Forall. apply* awterma_topent.
Proof.
  introv wt. gen k u. induction e; intros; simpls.
  case_nat*. assumption. assumption.
  apply* awterma_topen.
Qed.

Lemma awterma_remove: forall G H e y v,
    AWTermA (G & y ~ v & H) e ->
    y \notin ATFv e ->
    AWTermA (G & H) e.
Proof.
  introv wt notin. gen_eq I: (G & y ~ v & H).
  gen H. induction wt; introv hh; auto_star.
  simpl in notin. rewrite hh in H. apply AWTermA_Var. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTermA_TypVar. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTermA_TFVar. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTermA_EVar. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTermA_Solved_EVar. apply* binds_subst.

  simpl in notin. apply AWTermA_App. apply* IHwt1. simpls*. apply* IHwt2. simpls*.

  simpl in notin. apply AWTermA_Pi. apply* IHwt1. apply* IHwt2.
  simpl in notin. apply AWTermA_Ann. apply* IHwt1. simpls*. apply* IHwt2.
Qed.

Lemma awterma_remove_empty: forall G e y v,
    AWTermA (G & y ~ v) e ->
    y \notin ATFv e ->
    AWTermA G e.
Proof.
  intros. assert (AWTermA (G & y ~ v & empty) e). rewrite* concat_empty_r.
  assert (AWTermA (G & empty) e). apply* awterma_remove.
  rewrite concat_empty_r in H2. auto.
Qed.

(* one important one, changes from awterm to awterma *)

Theorem awterm_is_awterma: forall G e,
    AWTermT G e ->
    AWTermA G e.
Proof.
  introv wt. induction wt; auto_star.
  pick_fresh y. assert (AWTermA (G & y ~ AC_Var) (AT_Expr (e @ y))).
  apply H0. auto_star. apply awterma_open in H1. apply awterma_remove_empty in H1. constructor*. simpls*.
  constructor*. pick_fresh y. assert (AWTermA (G & y ~ AC_Var) (t2 @' y)).
  apply H0. auto_star. apply awterma_opent in H1. apply awterma_remove_empty in H1. auto_star. auto_star.
  constructor*. pick_fresh y. assert (AWTermA (G & y ~ AC_TVar) (s @#' y)).
  apply H0. auto_star. apply awterma_topent in H1. apply awterma_remove_empty in H1. auto_star. auto_star.
Qed.

(* a definition about length of a expression.
( in order to make all the expression has length,
( there are many meaningless definition,
( which ends with `I` *)

Inductive ALen : ACtx -> AType -> nat -> Prop :=
| ALen_Var: forall G x, binds x AC_Var G -> ALen G (AT_Expr (AE_FVar x)) 1
| ALen_BVar: forall G i, ALen G (AT_Expr (AE_BVar i)) 1
| ALen_TypVar: forall G x t, binds x (AC_Typ t) G -> ALen G (AT_Expr (AE_FVar x)) 1
| ALen_Var_I1 : forall G x, binds x AC_Unsolved_EVar G -> ALen G (AT_Expr (AE_FVar x)) 1
| ALen_Var_I2 : forall G x t, binds x (AC_Solved_EVar t) G -> ALen G (AT_Expr (AE_FVar x)) 1
| ALen_Var_I3 : forall G x, binds x AC_TVar G -> ALen G (AT_Expr (AE_FVar x)) 1
| ALen_Var_I : forall G x, x # G -> ALen G (AT_Expr (AE_FVar x)) 1
| ALen_EVar : forall G a, binds a AC_Unsolved_EVar G -> ALen G (AT_EVar a) 1
| ALen_Solved_EVar: forall G1 G2 a t i,
    ok (G1 & a ~ AC_Solved_EVar t & G2) ->
    ALen G1 t i -> ALen (G1 & a ~ AC_Solved_EVar t & G2) (AT_EVar a) (i + 1)
| ALen_EVar_I1: forall G x, binds x AC_Var G -> ALen G (AT_EVar x) 1
| ALen_EVar_I2: forall G x t, binds x (AC_Typ t) G -> ALen G (AT_EVar x) 1
| ALen_EVar_I3: forall G x, binds x (AC_TVar) G -> ALen G (AT_EVar x) 1
| ALen_EVar_I : forall G a, a # G -> ALen G (AT_EVar a) 1
| ALen_TBVar: forall G i, ALen G (AT_TBVar i) 1
| ALen_TFVar: forall G a, binds a AC_TVar G -> ALen G (AT_TFVar a) 1
| ALen_TFVar_I1: forall G a, binds a AC_Var G -> ALen G (AT_TFVar a) 1
| ALen_TFVar_I2: forall G a t, binds a (AC_Typ t) G -> ALen G (AT_TFVar a) 1
| ALen_TFVar_I3: forall G a, binds a AC_Unsolved_EVar G -> ALen G (AT_TFVar a) 1
| ALen_TFVar_I4: forall G a t, binds a (AC_Solved_EVar t) G -> ALen G (AT_TFVar a) 1
| ALen_TFVar_I: forall G a, a # G -> ALen G (AT_TFVar a) 1
| ALen_Star: forall G, ALen G (AT_Expr AE_Star) 1
| ALen_App: forall e1 e2 G i1 i2, ALen G (AT_Expr e1) i1 -> ALen G (AT_Expr e2) i2 -> ALen G (AT_Expr (AE_App e1 e2)) (i1 + i2 + 1)
| ALen_Lam: forall e G i, ALen G (AT_Expr e) i -> ALen G (AT_Expr (AE_Lam e)) (i + 1)
| ALen_Pi: forall e1 e2 G i1 i2, ALen G e1 i1 -> ALen G e2 i2 -> ALen G (AT_Expr (AE_Pi e1 e2)) (i1 + i2 + 1)
| ALen_CastUp:  forall e G i, ALen G (AT_Expr e) i -> ALen G (AT_Expr (AE_CastUp e)) (i + 1)
| ALen_CastDn:  forall e G i, ALen G (AT_Expr e) i -> ALen G (AT_Expr (AE_CastDn e)) (i + 1)
| ALen_Ann: forall e1 e2 G i1 i2, ALen G (AT_Expr e1) i1 -> ALen G e2 i2 -> ALen G (AT_Expr (AE_Ann e1 e2)) (i1 + i2 + 1)
| ALen_Forall: forall e G i, ALen G e i -> ALen G (AT_Expr (AE_Forall e)) (i + 1).

Hint Constructors ALen.

(* some lemmas about alen *)

Lemma alen_add_var_expr: forall G i y e,
    ALen G (AT_Expr e) i ->
    ok (G & y ~ AC_Var) ->
    ALen (G & y ~ AC_Var) (AT_Expr e) i
with alen_add_var: forall G i y e,
    ALen G e i ->
    ok (G & y ~ AC_Var) ->
    ALen (G & y ~ AC_Var) e i.
Proof.
  introv len okg.
  gen i. induction e; introv len.

  inversion len; subst. apply ALen_BVar.

  inversion len; subst.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_Var. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_TypVar with t. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_Var_I1. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_Var_I2 with t. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_Var_I3. apply* binds_concat_left.
  destruct (eq_var_dec v y). subst.
  apply ALen_Var. apply* binds_push_eq.
  apply ALen_Var_I. auto_star.

  inversion len; subst. apply ALen_Star.
  inversion len; subst. apply ALen_App.
  apply* IHe1.
  apply* IHe2.

  inversion len; subst. apply ALen_Lam.
  apply* IHe.

  inversion len; subst. apply ALen_Pi.
  apply* alen_add_var.
  apply* alen_add_var.

  inversion len; subst. apply ALen_CastUp.
  apply* IHe.

  inversion len; subst. apply ALen_CastDn.
  apply* IHe.

  inversion len; subst. apply ALen_Ann.
  apply* IHe.
  apply* alen_add_var.

  inversion len; subst. apply ALen_Forall.
  apply* alen_add_var.
Proof.
  introv len okg.
  gen i. induction e; introv len.

  inversion len; subst. apply ALen_TBVar.

  inversion len; subst.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_TFVar. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_TFVar_I1. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_TFVar_I2 with t. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_TFVar_I3. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_TFVar_I4 with t. apply* binds_concat_left.
  destruct (eq_var_dec v y). subst.
  apply ALen_TFVar_I1. apply* binds_push_eq.
  apply ALen_TFVar_I. auto_star.

  inversion len; subst.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_EVar. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false okg. simpl_dom. apply union_left.  apply union_right. apply in_singleton_self.
  rewrite <- concat_assoc. apply* ALen_Solved_EVar.
  rewrite* concat_assoc.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_EVar_I1. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_EVar_I2 with t. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_EVar_I3. apply* binds_concat_left.
  destruct (eq_var_dec v y). subst.
  apply ALen_EVar_I1. apply* binds_push_eq.
  apply ALen_EVar_I. auto_star.

  apply* alen_add_var_expr.
Qed.

Lemma alen_add_tvar_expr: forall G i y e,
    ALen G (AT_Expr e) i ->
    ok (G & y ~ AC_TVar) ->
    ALen (G & y ~ AC_TVar) (AT_Expr e) i
with alen_add_tvar: forall G i y e,
    ALen G e i ->
    ok (G & y ~ AC_TVar) ->
    ALen (G & y ~ AC_TVar) e i.
Proof.
  introv len okg.
  gen i. induction e; introv len.

  inversion len; subst. apply ALen_BVar.

  inversion len; subst.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_Var. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_TypVar with t. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_Var_I1. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_Var_I2 with t. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_Var_I3. apply* binds_concat_left.
  destruct (eq_var_dec v y). subst.
  apply ALen_Var_I3. apply* binds_push_eq.
  apply ALen_Var_I. auto_star.

  inversion len; subst. apply ALen_Star.
  inversion len; subst. apply ALen_App.
  apply* IHe1.
  apply* IHe2.

  inversion len; subst. apply ALen_Lam.
  apply* IHe.

  inversion len; subst. apply ALen_Pi.
  apply* alen_add_tvar.
  apply* alen_add_tvar.

  inversion len; subst. apply ALen_CastUp.
  apply* IHe.

  inversion len; subst. apply ALen_CastDn.
  apply* IHe.

  inversion len; subst. apply ALen_Ann.
  apply* IHe.
  apply* alen_add_tvar.

  inversion len; subst. apply ALen_Forall.
  apply* alen_add_tvar.
Proof.
  introv len okg.
  gen i. induction e; introv len.

  inversion len; subst. apply ALen_TBVar.

  inversion len; subst.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_TFVar. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_TFVar_I1. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_TFVar_I2 with t. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_TFVar_I3. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_TFVar_I4 with t. apply* binds_concat_left.
  destruct (eq_var_dec v y). subst.
  apply ALen_TFVar. apply* binds_push_eq.
  apply ALen_TFVar_I. auto_star.

  inversion len; subst.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_EVar. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false okg. simpl_dom. apply union_left.  apply union_right. apply in_singleton_self.
  rewrite <- concat_assoc. apply* ALen_Solved_EVar.
  rewrite* concat_assoc.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_EVar_I1. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_EVar_I2 with t. apply* binds_concat_left.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_EVar_I3. apply* binds_concat_left.
  destruct (eq_var_dec v y). subst.
  apply ALen_EVar_I3. apply* binds_push_eq.
  apply ALen_EVar_I. auto_star.

  apply* alen_add_tvar_expr.
Qed.

Lemma alen_fvar: forall G x,
    ALen G (AT_Expr (AE_FVar x)) 1.
Proof.
  intros.
  assert ({x \in dom G}+{x \notin dom G}). apply* decidable_sumbool. apply indom_decidable.
  destruct H as [hin | hnotin].
  assert (exists vx, binds x vx G) by apply* get_some.
  destruct H as (vx & H). destruct vx; auto_star.
  apply* ALen_Var_I.
Qed.

Lemma alen_tfvar: forall G x,
    ALen G (AT_TFVar x) 1.
Proof.
  intros.
  assert ({x \in dom G}+{x \notin dom G}). apply* decidable_sumbool. apply indom_decidable.
  destruct H as [hin | hnotin].
  assert (exists vx, binds x vx G) by apply* get_some.
  destruct H as (vx & H). destruct vx; auto_star.
  apply* ALen_TFVar_I.
Qed.

Lemma alen_open_expr: forall G e i y n,
    ALen G (AT_Expr e) i ->
    ok G ->
    ALen G (AT_Expr (AOpenRec n (AE_FVar y) e)) i
with alen_open: forall G e i y n,
    ALen G e i ->
    ok G ->
    ALen G (AOpenTypRec n (AE_FVar y) e) i.
Proof.
  introv len okg.
  gen i n. induction e; introv len; intro k; simpls; try(solve[assumption]).

  simpls. auto. case_if*. inversion len; subst. apply alen_fvar.

  inversion len; subst. apply ALen_App.
  apply* IHe1. apply* IHe2.

  inversion len; subst. apply ALen_Lam.
  apply* IHe.

  inversion len; subst. apply ALen_Pi.
  apply* alen_open.
  apply* alen_open.

  inversion len; subst. apply ALen_CastUp.
  apply* IHe.

  inversion len; subst. apply ALen_CastDn.
  apply* IHe.

  inversion len; subst. apply ALen_Ann.
  apply* IHe. apply* alen_open.

  inversion len; subst. apply ALen_Forall.
  apply* alen_open.
Proof.
  introv len okg.
  gen i n. induction e; introv len; intro k; simpls; try(solve[assumption]).

  simpls. auto.
Qed.

Lemma alen_topen_expr: forall G e i y n,
    ALen G (AT_Expr e) i ->
    ok G ->
    ALen G (AT_Expr (ATOpenRec n (AT_TFVar y) e)) i
with alen_topen: forall G e i y n,
    ALen G e i ->
    ok G ->
    ALen G (ATOpenTypRec n (AT_TFVar y) e) i.
Proof.
  introv len okg.
  gen i n. induction e; introv len; intro k; simpls; try(solve[assumption]).

  inversion len; subst. apply ALen_App.
  apply* IHe1. apply* IHe2.

  inversion len; subst. apply ALen_Lam.
  apply* IHe.

  inversion len; subst. apply ALen_Pi.
  apply* alen_topen.
  apply* alen_topen.

  inversion len; subst. apply ALen_CastUp.
  apply* IHe.

  inversion len; subst. apply ALen_CastDn.
  apply* IHe.

  inversion len; subst. apply ALen_Ann.
  apply* IHe. apply* alen_topen.

  inversion len; subst. apply ALen_Forall.
  apply* alen_topen.
Proof.
  introv len okg.
  gen i n. induction e; introv len; intro k; simpls; try(solve[assumption]).

  simpls. auto. case_if*. inversion len; subst. apply* alen_tfvar.

  simpls. auto.
Qed.

Lemma alen_awterm_append: forall G H e n,
    AWf (G & H) ->
    AWTermA G e ->
    ALen G e n ->
    ALen (G & H) e n.
Proof.
  introv wf wt len.
  induction len.
  auto.
  apply ALen_Var. apply* binds_concat_left_ok.
  apply ALen_BVar.
  apply ALen_TypVar with t. apply* binds_concat_left_ok.
  apply* ALen_Var_I1. apply* binds_concat_left_ok.
  apply* ALen_Var_I2. apply* binds_concat_left_ok.
  apply* ALen_Var_I3. apply* binds_concat_left_ok.
  inversion wt; subst; try(solve[false binds_fresh_inv H3 H0]).

  apply* ALen_EVar. apply* binds_concat_left_ok.
  rewrite <- concat_assoc. apply* ALen_Solved_EVar.
  rewrite* concat_assoc.
  apply* ALen_EVar_I1. apply* binds_concat_left_ok.
  apply* ALen_EVar_I2. apply* binds_concat_left_ok.
  apply* ALen_EVar_I3. apply* binds_concat_left_ok.
  inversion wt; subst; try(solve[false binds_fresh_inv H3 H0]).

  apply ALen_TBVar.
  apply* ALen_TFVar. apply* binds_concat_left_ok.
  apply* ALen_TFVar_I1. apply* binds_concat_left_ok.
  apply* ALen_TFVar_I2. apply* binds_concat_left_ok.
  apply* ALen_TFVar_I3. apply* binds_concat_left_ok.
  apply* ALen_TFVar_I4. apply* binds_concat_left_ok.
  inversion wt; subst; try(solve[false binds_fresh_inv H3 H0]).

  apply* ALen_Star.
  inversion wt; subst.
  apply* ALen_App.
  inversion wt; subst. apply* ALen_Lam.
  inversion wt; subst. apply* ALen_Pi.
  inversion wt; subst. apply* ALen_CastUp.
  inversion wt; subst. apply* ALen_CastDn.
  inversion wt; subst. apply* ALen_Ann.
  inversion wt; subst. apply* ALen_Forall.
Qed.

Lemma alen_exists': forall G e n,
    AWf G ->
    LibList.length G < n ->
    AWTermA G e ->
    exists m, ALen G e m.
Proof.
  introv okg len wt. gen G e. induction n as [|n']; introv okg len wt.
  false. inversion len.

  induction wt.
  exists* 1.
  exists* 1.
  assert ({x \in dom G}+{x \notin dom G}). apply* decidable_sumbool. apply indom_decidable.
  destruct H0 as [hin | hnotin].
  (* in *)
  assert (exists vx, binds x vx G) by apply* get_some.
  destruct H0 as (vx & H0). destruct vx; auto_star.

  (* notin *)
  exists* 1.
  exists* 1.
  exists* 1.
  exists* 1.
  assert ({a \in dom G}+{a \notin dom G}). apply* decidable_sumbool. apply indom_decidable.
  destruct H0 as [hin | hnotin].
  (* in *)
  assert (exists vx, binds a vx G) by apply* get_some.
  destruct H0 as (vx & H0). destruct vx; try(solve[exists* 1]).

  destruct (split_bind_context H) as (G1 & G2 & IG).
  assert (exists n, ALen G1 t n). apply~ IHn'.
  rewrite IG in okg. rewrite <- concat_assoc in okg. apply* AWf_left.

  rewrite IG in len.
  rewrite concat_def in len. repeat(rewrite LibList.length_app in len).
  assert(LibList.length (a~ AC_Solved_EVar t) = 1). rewrite single_def. rewrite LibList.length_cons. rewrite LibList.length_nil. Omega.omega.
  Omega.omega.
  apply awterm_is_awterma.
  rewrite IG in okg. apply AWf_left in okg. apply awterm_solved_evar in okg. auto.
  destruct H1 as (ne & H1). exists (ne + 1). rewrite IG in *. apply ALen_Solved_EVar; auto.

  exists* 1.
  exists* 1.

  destruct IHwt1 as (n1 & IHe1); auto. destruct IHwt2 as (n2 & IHe2); auto. exists* (n1 + n2 + 1).
  destruct IHwt as (n & IHe1); auto. exists* (n + 1).
  destruct IHwt1 as (n1 & IHe1); auto. destruct IHwt2 as (n2 & IHe2); auto. exists* (n1 + n2 + 1).
  destruct IHwt as (n & IHe1); auto. exists* (n + 1).
  destruct IHwt as (n & IHe1); auto. exists* (n + 1).
  destruct IHwt1 as (n1 & IHe1); auto. destruct IHwt2 as (n2 & IHe2); auto. exists* (n1 + n2 + 1).
  destruct IHwt as (n & IHe1); auto. exists* (n + 1).
Qed.

Lemma alen_exists: forall G e,
    AWf G ->
    AWTermA G e ->
    exists n, ALen G e n.
Proof.
  intros.
  apply* alen_exists'.
Qed.

Lemma alen_eq: forall G e i1 i2,
    ALen G e i1 ->
    ALen G e i2 ->
    i1 = i2.
Proof.
  introv hy1. gen i2. induction hy1; introv hy2; inversion hy2; subst; auto;
  try(solve[apply (binds_func H) in H1; inversion H1]);
  try(solve[apply (binds_func H) in H2; inversion H2]).
  apply binds_middle_eq_inv in H; auto. inversion H.
  apply binds_middle_eq_inv in H2; auto. inversion H2.
  apply ok_middle_eq2 in H0; auto.
  destruct H0 as [eqg [eqv eqg2]]. inversion eqv. subst. lets: IHhy1 i0 H3. subst*.
  apply binds_middle_eq_inv in H2; auto. inversion H2.
  apply binds_middle_eq_inv in H2; auto. inversion H2.
  apply binds_middle_eq_inv in H2; auto. inversion H2.
  false H2. simpl_dom. apply union_left. apply union_right. apply in_singleton_self.
  apply binds_middle_eq_inv in H; auto. inversion H.
  apply binds_middle_eq_inv in H; auto. inversion H.
  apply binds_middle_eq_inv in H; auto. inversion H.
  false H. simpl_dom. apply union_left. apply union_right. apply in_singleton_self.
Qed.

Lemma alen_evar: forall G1 G2 a t m n,
    ok (G1 & a ~ AC_Solved_EVar t & G2) ->
    ALen (G1 & a ~ AC_Solved_EVar t & G2) (AT_EVar a) n ->
    ALen G1 t m ->
    n = m + 1.
Proof.
  introv okg lena lent.
  inversion lena; subst.
  apply binds_middle_eq_inv in H1; auto. inversion H1.
  apply ok_middle_eq2 in H; auto.
  destruct H as [eqg [eqv eqg2]]. inversion eqv. subst.
  lets: alen_eq H2 lent. subst*.
  apply binds_middle_eq_inv in H1; auto. inversion H1.
  apply binds_middle_eq_inv in H1; auto. inversion H1.
  apply binds_middle_eq_inv in H1; auto. inversion H1.
  false H1. simpl_dom. apply union_left. apply union_right. apply in_singleton_self.
Qed.

Hint Resolve awterm_is_awterma.
Theorem cpltctxsubst_exists': forall G e n m,
    AWf G ->
    AWTermT G e ->
    n < m ->
    ALen G e n ->
    CompleteCtx G ->
    exists t, ACpltCtxSubst G e t
.
Proof.
  intros. gen G e n. induction m; introv wf comp wt less len.
  inversion less.

  gen n. induction wt; introv less len; simpls; auto_star.

  (* APP *)
  destruct(@alen_exists G (AT_Expr e1)) as (ne1 & ex1). auto. auto. assert (exists t1, ACpltCtxSubst G (AT_Expr e1) t1). apply* IHm.
  inversion len; subst. lets: alen_eq H2 ex1. Omega.omega.
  destruct H as (t1 & Ht1).
  destruct(@alen_exists G (AT_Expr e2)) as (ne2 & ex2). auto. auto.
  assert (exists t2, ACpltCtxSubst G (AT_Expr e2) t2). apply* IHm.
  inversion len; subst. lets: alen_eq H4 ex2. Omega.omega.
  destruct H as (t2 & Ht2).
  destruct t1 ; try(solve[inversion Ht1]).
  destruct t2 ; try(solve[inversion Ht2]).
  exists* (DT_Expr (DE_App d d0)).

   (* LAM *)
  inversion len; subst.
  pick_fresh y.
  assert (IH1: y \notin L) by auto_star.
  assert (IH2: AWf (G & y ~ AC_Var)) by apply* AWf_Var.
  assert (IH3: CompleteCtx (G & y ~ AC_Var)). apply* complete_add.
  assert (IH4: ALen (G & y ~ AC_Var) (AT_Expr (e @ y)) i).
    apply alen_add_var with (y:=y) in H3.
    apply* alen_open_expr. apply* awf_is_ok.
  assert (IH5: i < S m). Omega.omega.
  lets: H0 IH1 IH2 IH3 IH5 IH4.
  destruct H1 as (et & H1).
  apply* lam_solve.

  (* Pi *)
  inversion len; subst.
  assert (IT1:  exists t, ACpltCtxSubst G t1 t). apply IHwt with (n:=i1); auto. Omega.omega.
  pick_fresh y.
  assert (IH1: y \notin L) by auto_star.
  assert (IH2: AWf (G & y ~ AC_Var)) by apply* AWf_Var.
  assert (IH3: CompleteCtx (G & y ~ AC_Var)). apply* complete_add.
  assert (IH4: ALen (G & y ~ AC_Var) (t2 @' y) i2).
    apply alen_add_var with (y:=y) in H6.
    apply* alen_open. apply* awf_is_ok.
  assert (IH5: i2 < S m). Omega.omega.
  lets: H0 IH1 IH2 IH3 IH5 IH4.
  destruct IT1 as (et1 & IT1).
  destruct H1 as (et2 & H1).
  apply* pi_solve.

  (* CASTUP *)
  assert (exists t, ACpltCtxSubst G (AT_Expr e) t).
    destruct(@alen_exists G (AT_Expr e)) as (ne & ex). auto. auto. apply IHm with ne; auto.
  inversion len; subst. lets: alen_eq H1 ex. Omega.omega.
  destruct H as (et & H).
  destruct et ; try(solve[inversion H]).
  exists* (DT_Expr (DE_CastUp d)).

  (* CASTDOWN *)
  assert (exists t, ACpltCtxSubst G (AT_Expr e) t).
    destruct(@alen_exists G (AT_Expr e)) as (ne & ex). auto. auto. apply IHm with ne; auto.
  inversion len; subst. lets: alen_eq H1 ex. Omega.omega.
  destruct H as (et & H).
  destruct et ; try(solve[inversion H]).
  exists* (DT_Expr (DE_CastDn d)).

  (* ANN *)
  destruct(@alen_exists G (AT_Expr e1)) as (ne1 & ex1). auto. auto. assert (exists t1, ACpltCtxSubst G (AT_Expr e1) t1). apply* IHm.
  inversion len; subst. lets: alen_eq H2 ex1. Omega.omega.
  destruct H as (t1 & Ht1).
  destruct(@alen_exists G e2) as (ne2 & ex2). auto. auto.
  assert (exists t2, ACpltCtxSubst G e2 t2). apply* IHm.
  inversion len; subst. lets: alen_eq H4 ex2. Omega.omega.
  destruct H as (t2 & Ht2).
  destruct t1 ; try(solve[inversion Ht1]).
  exists* (DT_Expr (DE_Ann d t2)).

  (* Forall *)
  inversion len; subst.
  pick_fresh y.
  assert (IH1: y \notin L) by auto_star.
  assert (IH2: AWf (G & y ~ AC_TVar)) by apply* AWf_TVar.
  assert (IH3: CompleteCtx (G & y ~ AC_TVar)). apply* complete_add_tvar.
  assert (IH4: ALen (G & y ~ AC_TVar) (s @#' y) i).
    apply alen_add_tvar with (y:=y) in H3.
    apply* alen_topen. apply* awf_is_ok.
  assert (IH5: i < S m). Omega.omega.
  lets: H0 IH1 IH2 IH3 IH5 IH4.
  destruct H1 as (et2 & H1).
  apply* forall_solve.

  (* Unsolved_EVar *)
  false (complete_contains_unsolved comp H).

  (* Solved_EVar *)
  destruct (split_bind_context H) as (G1 & G2 & HG). rewrite HG in *.
  assert (exists e, ACpltCtxSubst G1 t e).
     destruct(@alen_exists G1 t) as (nt & ex). do 2 apply* AWf_left.
     apply awterm_is_awterma. apply* awterm_solved_evar.
     apply IHm with nt; auto. do 2 apply* AWf_left. do 2 apply* complete_part_left. apply* awterm_solved_evar.
     assert (ok (G1 & i ~ AC_Solved_EVar t & G2)). auto.
     lets: alen_evar H0 len ex.  Omega.omega.
  destruct H0 as (et & H0).
  exists et. apply~ ACpltCtxSubst_EVar. do 2 apply* complete_part_left. apply* complete_part_right.
Qed.

Theorem cpltctxsubst_exists: cpltctxsubst_exists_def.
Proof.
  introv. intros. destruct(@alen_exists G e) as (n & ex). auto. auto.
  apply* cpltctxsubst_exists'.
Qed.