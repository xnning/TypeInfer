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
    AWTerm G e ->
    CompleteCtx G ->
    exists t, ACpltCtxSubst G e t
.

Definition cpltctxtsubst_exists_def := forall G e,
    AWf G ->
    AWTermT G e ->
    CompleteCtx G ->
    exists t, ACpltCtxTSubst G e t
.

(* admitted lemma with issue about quantification *)

Lemma lam_solve: forall G x e t,
    AWf (G & x ~ AC_Var) ->
    ACpltCtxSubst (G & x ~ AC_Var) (e @ x) t ->
    exists d, ACpltCtxSubst G (AE_Lam e) d.
Admitted.

Lemma pi_solve: forall G x e1 e2 t1 t2,
    AWf (G & x ~ AC_Var) ->
    ACpltCtxSubst G e1 t1 ->
    ACpltCtxSubst (G & x ~ AC_Var) (e2 @ x) t2 ->
    exists d, ACpltCtxSubst G (AE_Pi e1 e2) d.
Admitted.

Lemma let_solve: forall G x e1 e2 t1 t2,
    AWf (G & x ~ AC_Var) ->
    ACpltCtxSubst G e1 t1 ->
    ACpltCtxSubst (G & x ~ AC_Var) (e2 @ x) t2 ->
    exists d, ACpltCtxSubst G (AE_Let e1 e2) d.
Admitted.

Lemma forall_solve: forall G x e t,
    AWf (G & x ~ AC_Var) ->
    ACpltCtxTSubst (G & x ~ AC_Typ AE_Star) (AT_Forall e @' x) t ->
    exists d, ACpltCtxTSubst G (AT_Forall e) d.
Admitted.

(* another form of awterm, which does not care about bound variables *)

Inductive AWTermA : ACtx -> AExpr -> Prop :=
  | AWTermA_Var : forall G x, binds x AC_Var G -> AWTermA G (AE_FVar x)
  | AWTermA_BVar : forall G x, AWTermA G (AE_BVar x)
  | AWTermA_TypVar : forall G x t, binds x (AC_Typ t) G -> AWTermA G (AE_FVar x)
  | AWTermA_LetVar : forall G x t e, binds x (AC_Bnd t e) G -> AWTermA G (AE_FVar x)
  | AWTermA_EVar : forall G a, binds a AC_Unsolved_EVar G -> AWTermA G (AE_EVar a)
  | AWTermA_Solved_EVar : forall G a t, binds a (AC_Solved_EVar t) G -> AWTermA G (AE_EVar a)
  | AWTermA_Star: forall G, AWTermA G AE_Star
  | AWTermA_App: forall e1 e2 G, AWTermA G e1 -> AWTermA G e2 -> AWTermA G (AE_App e1 e2)
  | AWTermA_Lam: forall e G , AWTermA G e  -> AWTermA G (AE_Lam e)
  | AWTermA_Pi: forall t1 t2 G, AWTermA G t1 -> AWTermA G t2 -> AWTermA G (AE_Pi t1 t2)
  | AWTermA_Let: forall e1 e2 G, AWTermA G e1 -> AWTermA G e2 -> AWTermA G (AE_Let e1 e2)
  | AWTermA_CastUp : forall e G, AWTermA G e -> AWTermA G (AE_CastUp e)
  | AWTermA_CastDn : forall e G, AWTermA G e -> AWTermA G (AE_CastDn e)
  | AWTermA_Ann: forall e1 e2 G, AWTermA G e1 -> AWTermA G e2 -> AWTermA G (AE_Ann e1 e2)
.

(* helper lemmas *)
Hint Constructors AWTermA ACpltCtxSubst.
Hint Resolve awf_is_ok AWf_left complete_part_left complete_part_right.
Lemma awterma_open: forall G k u e,
    AWTermA G (AOpenRec k u e) ->
    AWTermA G e.
Proof.
  introv wt. gen k u. induction e; intros; simpls; auto_star;
  try(inversion wt; subst; auto_star).
Qed.

Lemma awterma_remove: forall G H e y v,
    AWTermA (G & y ~ v & H) e ->
    y \notin AFv e ->
    AWTermA (G & H) e.
Proof.
  introv wt notin. gen_eq I: (G & y ~ v & H).
  gen H. induction wt; introv hh; auto_star.
  simpl in notin. rewrite hh in H. apply AWTermA_Var. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTermA_TypVar. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTermA_LetVar. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTermA_EVar. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTermA_Solved_EVar. apply* binds_subst.

  simpl in notin. apply AWTermA_App. apply* IHwt1. apply* IHwt2.

  simpl in notin. apply AWTermA_Pi. apply* IHwt1. apply* IHwt2.
  simpl in notin. apply AWTermA_Let. apply* IHwt1. apply* IHwt2.
  simpl in notin. apply AWTermA_Ann. apply* IHwt1. apply* IHwt2.
Qed.

Lemma awterma_remove_empty: forall G e y v,
    AWTermA (G & y ~ v) e ->
    y \notin AFv e ->
    AWTermA G e.
Proof.
  intros. assert (AWTermA (G & y ~ v & empty) e). rewrite* concat_empty_r.
  assert (AWTermA (G & empty) e). apply* awterma_remove.
  rewrite concat_empty_r in H2. auto.
Qed.

(* one important one, changes from awterm to awterma *)

Theorem awterm_is_awterma: forall G e,
    AWTerm G e ->
    AWTermA G e.
Proof.
  introv wt. induction wt; auto_star.
  pick_fresh y. assert (AWTermA (G & y ~ AC_Var) (e @ y)).
  apply H0. auto_star. apply awterma_open in H1. apply awterma_remove_empty in H1. constructor*. auto_star.
  constructor*. pick_fresh y. assert (AWTermA (G & y ~ AC_Var) (t2 @ y)).
  apply H0. auto_star. apply awterma_open in H1. apply awterma_remove_empty in H1. auto_star. auto_star.
  constructor*. pick_fresh y. assert (AWTermA (G & y ~ AC_Var) (e2 @ y)).
  apply H0. auto_star. apply awterma_open in H1. apply awterma_remove_empty in H1. auto_star. auto_star.
Qed.

(* a definition about length of a expression.
( in order to make all the expression has length,
( there are many meaningless definition,
( which ends with `I` *)

Inductive ALen : ACtx -> AExpr -> nat -> Prop :=
| ALen_BVar: forall G i, ALen G (AE_BVar i) 1
| ALen_Var: forall G x, binds x AC_Var G -> ALen G (AE_FVar x) 1
| ALen_TypVar: forall G x t, binds x (AC_Typ t) G -> ALen G (AE_FVar x) 1
| ALen_LetVar : forall G x t e i, binds x (AC_Bnd t e) G -> ALen G e i -> ALen G (AE_FVar x) (i + 1)
| ALen_Var_I1 : forall G x, binds x AC_Unsolved_EVar G -> ALen G (AE_FVar x) 1
| ALen_Var_I2 : forall G x t, binds x (AC_Solved_EVar t) G -> ALen G (AE_FVar x) 1
| ALen_Var_I : forall G x, x # G -> ALen G (AE_FVar x) 1
| ALen_EVar : forall G a, binds a AC_Unsolved_EVar G -> ALen G (AE_EVar a) 1
| ALen_EVar_I1: forall G x, binds x AC_Var G -> ALen G (AE_EVar x) 1
| ALen_EVar_I2: forall G x t, binds x (AC_Typ t) G -> ALen G (AE_EVar x) 1
| ALen_EVar_I3: forall G x t e, binds x (AC_Bnd t e) G -> ALen G (AE_EVar x) 1
| ALen_Solved_EVar: forall G1 G2 a t i, ok (G1 & a ~ AC_Solved_EVar t & G2) -> ALen G1 t i -> ALen (G1 & a ~ AC_Solved_EVar t & G2) (AE_EVar a) (i + 1)
| ALen_EVar_I : forall G a, a # G -> ALen G (AE_EVar a) 1
| ALen_Star: forall G, ALen G (AE_Star) 1
| ALen_App: forall e1 e2 G i1 i2, ALen G e1 i1 -> ALen G e2 i2 -> ALen G (AE_App e1 e2) (i1 + i2 + 1)
| ALen_Lam: forall e G i, ALen G e i -> ALen G (AE_Lam e) (i + 1)
| ALen_Pi: forall e1 e2 G i1 i2, ALen G e1 i1 -> ALen G e2 i2 -> ALen G (AE_Pi e1 e2) (i1 + i2 + 1)
| ALen_Let: forall e1 e2 G i1 i2, ALen G e1 i1 -> ALen G e2 i2 -> ALen G (AE_Let e1 e2) (i1 + i2 + 1)
| ALen_CastUp:  forall e G i, ALen G e i -> ALen G (AE_CastUp e) (i + 1)
| ALen_CastDn:  forall e G i, ALen G e i -> ALen G (AE_CastDn e) (i + 1)
| ALen_Ann: forall e1 e2 G i1 i2, ALen G e1 i1 -> ALen G e2 i2 -> ALen G (AE_Ann e1 e2) (i1 + i2 + 1).

Hint Constructors ALen.

(* some lemmas about alen *)

Lemma alen_add_var': forall G e i y m,
    ALen G e i ->
    i < m ->
    ok (G & y ~ AC_Var) ->
    ALen (G & y ~ AC_Var) e i.
Proof.
  introv. gen G e i y. induction m.
  introv len less okg.
  inversion less.

  introv len less okg.
  gen i. induction e; introv len less.
  inversion len; subst. apply ALen_BVar.
  inversion len; subst.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_Var. apply* binds_concat_left.

  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_TypVar with t. apply* binds_concat_left.

  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H0 okg.
  apply ALen_LetVar with t e. apply* binds_concat_left.
  apply* IHm. Omega.omega.

  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_Var_I1. apply* binds_concat_left.

  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_Var_I2 with t. apply* binds_concat_left.

  destruct (eq_var_dec v y). subst.
  apply ALen_Var. apply* binds_push_eq.

  apply ALen_Var_I. auto_star.

  inversion len; subst. apply ALen_EVar.
  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply* binds_concat_left.

  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_EVar_I1. apply* binds_concat_left.

  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_EVar_I2 with t. apply* binds_concat_left.

  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false binds_fresh_inv H1 okg.
  apply ALen_EVar_I3 with t e. apply* binds_concat_left.

  assert (v<>y). intros neq. subst. apply ok_push_inv in okg. destruct okg as [_ okg]. false okg. simpl_dom. apply union_left.  apply union_right. apply in_singleton_self.
  rewrite <- concat_assoc. apply* ALen_Solved_EVar.
  rewrite* concat_assoc.

  destruct (eq_var_dec v y). subst.
  apply ALen_EVar_I1. apply* binds_push_eq.

  apply ALen_EVar_I. auto_star.

  inversion len; subst. apply ALen_Star.

  inversion len; subst. apply ALen_App.
  apply* IHe1. Omega.omega.
  apply* IHe2. Omega.omega.

  inversion len; subst. apply ALen_Lam.
  apply* IHe. Omega.omega.

  inversion len; subst. apply ALen_Pi.
  apply* IHe1. Omega.omega.
  apply* IHe2. Omega.omega.

  inversion len; subst. apply ALen_Let.
  apply* IHe1. Omega.omega.
  apply* IHe2. Omega.omega.

  inversion len; subst. apply ALen_CastUp.
  apply* IHe. Omega.omega.

  inversion len; subst. apply ALen_CastDn.
  apply* IHe. Omega.omega.

  inversion len; subst. apply ALen_Ann.
  apply* IHe1. Omega.omega.
  apply* IHe2. Omega.omega.
Qed.

Lemma alen_add_var: forall G e i y,
    ALen G e i ->
    ok (G & y ~ AC_Var) ->
    ALen (G & y ~ AC_Var) e i.
Proof.
  introv len okg. apply* alen_add_var'.
Qed.

Lemma alen_open: forall G e i y,
    ALen G e i ->
    ok G ->
    binds y AC_Var G ->
    ALen G (e @ y) i.
Proof.
  introv len okg bd. unfold AOpen.
  gen i. generalize 0. induction e; introv len; unfold AOpen; simpls; try(solve[assumption]).

  case_if*. inversion len; subst. apply* ALen_Var.

  inversion len; subst. apply ALen_App.
  apply* IHe1. apply* IHe2.

  inversion len; subst. apply ALen_Lam.
  apply* IHe.

  inversion len; subst. apply ALen_Pi.
  apply* IHe1. apply* IHe2.

  inversion len; subst. apply ALen_Let.
  apply* IHe1. apply* IHe2.

  inversion len; subst. apply ALen_CastUp.
  apply* IHe.

  inversion len; subst. apply ALen_CastDn.
  apply* IHe.

  inversion len; subst. apply ALen_Ann.
  apply* IHe1. apply* IHe2.
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
  apply ALen_TypVar with t. apply* binds_concat_left_ok.
  apply* ALen_LetVar. apply* binds_concat_left_ok. apply* IHlen. destruct (split_bind_context H0) as (G1 & G2 & Hg). rewrite Hg in wf.
  assert (AWTerm G1 e).
  rewrite <- concat_assoc in wf. apply AWf_left in wf. apply* awterm_bnd.
  rewrite Hg. rewrite <- concat_assoc. apply* awterm_is_awterma. apply* awterm_weaken_ctx.
  rewrite concat_assoc. apply AWf_left in wf. apply* awf_is_ok.

  apply* ALen_Var_I1. apply* binds_concat_left_ok.
  apply* ALen_Var_I2. apply* binds_concat_left_ok.
  inversion wt; subst; try(solve[false binds_fresh_inv H3 H0]).

  apply* ALen_EVar. apply* binds_concat_left_ok.
  apply* ALen_EVar_I1. apply* binds_concat_left_ok.
  apply* ALen_EVar_I2. apply* binds_concat_left_ok.
  apply* ALen_EVar_I3. apply* binds_concat_left_ok.

  rewrite <- concat_assoc. apply* ALen_Solved_EVar.
  rewrite* concat_assoc.

  inversion wt; subst; try(solve[false binds_fresh_inv H3 H0]).

  apply* ALen_Star.
  inversion wt; subst.
  apply* ALen_App.
  inversion wt; subst. apply* ALen_Lam.
  inversion wt; subst. apply* ALen_Pi.
  inversion wt; subst. apply* ALen_Let.
  inversion wt; subst. apply* ALen_CastUp.
  inversion wt; subst. apply* ALen_CastDn.
  inversion wt; subst. apply* ALen_Ann.
Qed.


Lemma alen_exists': forall n G e,
    AWf G ->
    LibList.length G < n ->
    exists m, ALen G e m.
Proof.
  intro n. induction n as [|n']; introv okg len.
  false. inversion len.

    induction e.
  exists* 1.
  assert ({v \in dom G}+{v \notin dom G}). apply* decidable_sumbool. apply indom_decidable.
  destruct H as [hin | hnotin].
  (* in *)
  assert (exists vx, binds v vx G) by apply* get_some.
  destruct H as (vx & H). destruct vx; auto_star.
  destruct (split_bind_context H) as (G1 & G2 & IG).
  assert (exists n, ALen G1 a0 n). apply~ IHn'.

    rewrite IG in okg. rewrite <- concat_assoc in okg. apply* AWf_left.

  rewrite IG in len.
  rewrite concat_def in len. repeat(rewrite LibList.length_app in len).
    assert(LibList.length (v~ AC_Bnd a a0) = 1). rewrite single_def. rewrite LibList.length_cons. rewrite LibList.length_nil. Omega.omega.

  Omega.omega.

    destruct H0 as (n & H0). exists* (n + 1). apply ALen_LetVar with a a0; auto.

  rewrite <- concat_assoc in IG. rewrite IG. apply* alen_awterm_append. rewrite* <- IG. apply awterm_is_awterma. rewrite IG in okg. rewrite concat_assoc in okg. apply AWf_left in okg. apply* awterm_bnd.

  (* notin *)

  exists* 1.

  assert ({v \in dom G}+{v \notin dom G}). apply* decidable_sumbool. apply indom_decidable.
  destruct H as [hin | hnotin].
  (* in *)
  assert (exists vx, binds v vx G) by apply* get_some.
  destruct H as (vx & H). destruct vx; auto_star.

  destruct (split_bind_context H) as (G1 & G2 & IG).
  assert (exists n, ALen G1 a n). apply~ IHn'.
  rewrite IG in okg. rewrite <- concat_assoc in okg. apply* AWf_left.

  rewrite IG in len.
  rewrite concat_def in len. repeat(rewrite LibList.length_app in len).
  assert(LibList.length (v~ AC_Solved_EVar a) = 1). rewrite single_def. rewrite LibList.length_cons. rewrite LibList.length_nil. Omega.omega.
  Omega.omega.
  destruct H0 as (ne & H0). exists (ne + 1). rewrite IG in *. apply ALen_Solved_EVar; auto.

  (* notin *)
  exists* 1.

  exists* 1.
  destruct IHe1 as (n1 & IHe1). destruct IHe2 as (n2 & IHe2). exists* (n1 + n2 + 1).
  destruct IHe as (n & IHe1). exists* (n + 1).
  destruct IHe1 as (n1 & IHe1). destruct IHe2 as (n2 & IHe2). exists* (n1 + n2 + 1).
  destruct IHe1 as (n1 & IHe1). destruct IHe2 as (n2 & IHe2). exists* (n1 + n2 + 1).
  destruct IHe as (n & IHe1). exists* (n + 1).
  destruct IHe as (n & IHe1). exists* (n + 1).
  destruct IHe1 as (n1 & IHe1). destruct IHe2 as (n2 & IHe2). exists* (n1 + n2 + 1).
Qed.

Lemma alen_exists: forall G e,
    AWf G ->
    exists n, ALen G e n.
Proof.
  introv wf.
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
  lets: binds_func H H1. inversion H0; subst. lets: IHhy1 i0 H3. subst*.
  false binds_fresh_inv H H2.
  false binds_fresh_inv H1 H.
  apply binds_middle_eq_inv in H; auto. inversion H.
  apply binds_middle_eq_inv in H; auto. inversion H.
  apply binds_middle_eq_inv in H; auto. inversion H.
  apply binds_middle_eq_inv in H; auto. inversion H.
  apply binds_middle_eq_inv in H2; auto. inversion H2.
  apply binds_middle_eq_inv in H2; auto. inversion H2.
  apply binds_middle_eq_inv in H2; auto. inversion H2.
  apply binds_middle_eq_inv in H2; auto. inversion H2.
  apply ok_middle_eq2 in H0; auto.
  destruct H0 as [eqg [eqv eqg2]]. inversion eqv. subst. lets: IHhy1 i0 H3. subst*.
  false H2. simpl_dom. apply union_left. apply union_right. apply in_singleton_self.
  false H. simpl_dom. apply union_left. apply union_right. apply in_singleton_self.
Qed.

Lemma alen_evar: forall G1 G2 a t m n,
    ok (G1 & a ~ AC_Solved_EVar t & G2) ->
    ALen (G1 & a ~ AC_Solved_EVar t & G2) (AE_EVar a) n ->
    ALen G1 t m ->
    n = m + 1.
Proof.
  introv okg lena lent.
  inversion lena; subst.
  apply binds_middle_eq_inv in H1; auto. inversion H1.
  apply binds_middle_eq_inv in H1; auto. inversion H1.
  apply binds_middle_eq_inv in H1; auto. inversion H1.
  apply binds_middle_eq_inv in H1; auto. inversion H1.
  apply ok_middle_eq2 in H; auto.
  destruct H as [eqg [eqv eqg2]]. inversion eqv. subst.
  lets: alen_eq H2 lent. subst*.
  false H1. simpl_dom. apply union_left. apply union_right. apply in_singleton_self.
Qed.

Theorem cpltctxsubst_exists': forall G e n m,
    AWf G ->
    AWTerm G e ->
    n < m ->
    ALen G e n ->
    CompleteCtx G ->
    exists t, ACpltCtxSubst G e t
.
Proof.
  intros. gen G e n. induction m; introv wf comp wt less len.
  inversion less.

  gen n. induction wt; introv less len; simpls; auto_star.
  false (complete_contains_unsolved comp H).

  destruct (split_bind_context H) as (G1 & G2 & HG). rewrite HG in *.
  assert (exists e, ACpltCtxSubst G1 t e).
     destruct(@alen_exists G1 t) as (nt & ex). do 2 apply* AWf_left.
     apply IHm with nt; auto. do 2 apply* AWf_left. do 2 apply* complete_part_left. apply* awterm_solved_evar.
     assert (ok (G1 & a ~ AC_Solved_EVar t & G2)). auto.
     lets: alen_evar H0 len ex.  Omega.omega.

  destruct H0 as (et & H0).
  exists et. apply~ ACpltCtxSubst_EVar. do 2 apply* complete_part_left. apply* complete_part_right.

  destruct(@alen_exists G e1) as (ne1 & ex1). auto. auto. assert (exists t1, ACpltCtxSubst G e1 t1). apply* IHm.
  inversion len; subst. lets: alen_eq H2 ex1. Omega.omega.
  destruct H as (t1 & Ht1).
  destruct(@alen_exists G e2) as (ne2 & ex2). auto. auto.
  assert (exists t2, ACpltCtxSubst G e2 t2). apply* IHm.
  inversion len; subst. lets: alen_eq H4 ex2. Omega.omega.
  destruct H as (t2 & Ht2).
  exists* (DE_App t1 t2).

  inversion len; subst.
  pick_fresh y.
  assert (IH1: y \notin L) by auto_star.
  assert (IH2: AWf (G & y ~ AC_Var)) by apply* AWf_Var.
  assert (IH3: CompleteCtx (G & y ~ AC_Var)). unfold CompleteCtx. intros z zv bd eqzv. subst. apply binds_push_inv in bd. destruct bd as [[_ neq] | [_ neq]]. false neq. false complete_contains_unsolved comp neq.
  assert (IH4: ALen (G & y ~ AC_Var) (e @ y) i).
    apply alen_add_var with (y:=y) in H3.
    apply* alen_open. apply* awf_is_ok.
  assert (IH5: i < S m). Omega.omega.
  lets: H0 IH1 IH2 IH3 IH5 IH4.
  destruct H1 as (et & H1).
  apply* lam_solve.

  inversion len; subst.
  assert (IT1:  exists t, ACpltCtxSubst G t1 t). apply IHwt with (n:=i1); auto. Omega.omega.
  pick_fresh y.
  assert (IH1: y \notin L) by auto_star.
  assert (IH2: AWf (G & y ~ AC_Var)) by apply* AWf_Var.
  assert (IH3: CompleteCtx (G & y ~ AC_Var)). unfold CompleteCtx. intros z zv bd eqzv. subst. apply binds_push_inv in bd. destruct bd as [[_ neq] | [_ neq]]. false neq. false complete_contains_unsolved comp neq.
  assert (IH4: ALen (G & y ~ AC_Var) (t2 @ y) i2).
    apply alen_add_var with (y:=y) in H6.
    apply* alen_open. apply* awf_is_ok.
  assert (IH5: i2 < S m). Omega.omega.
  lets: H0 IH1 IH2 IH3 IH5 IH4.
  destruct IT1 as (et1 & IT1).
  destruct H1 as (et2 & H1).
  apply* pi_solve.

  inversion len; subst.
  assert (IT1:  exists t, ACpltCtxSubst G e1 t). apply IHwt with (n:=i1); auto. Omega.omega.
  pick_fresh y.
  assert (IH1: y \notin L) by auto_star.
  assert (IH2: AWf (G & y ~ AC_Var)) by apply* AWf_Var.
  assert (IH3: CompleteCtx (G & y ~ AC_Var)). apply* complete_add.
  assert (IH4: ALen (G & y ~ AC_Var) (e2 @ y) i2).
    apply alen_add_var with (y:=y) in H6.
    apply* alen_open. apply* awf_is_ok.
  assert (IH5: i2 < S m). Omega.omega.
  lets: H0 IH1 IH2 IH3 IH5 IH4.
  destruct IT1 as (et1 & IT1).
  destruct H1 as (et2 & H1).
  apply* let_solve.

  assert (exists t, ACpltCtxSubst G e t).
    destruct(@alen_exists G e) as (ne & ex). auto. auto. apply IHm with ne; auto.
  inversion len; subst. lets: alen_eq H1 ex. Omega.omega.
  destruct H as (et & H).
  exists* (DE_CastUp et).

  assert (exists t, ACpltCtxSubst G e t).
    destruct(@alen_exists G e) as (ne & ex). auto. auto. apply IHm with ne; auto.
  inversion len; subst. lets: alen_eq H1 ex. Omega.omega.
  destruct H as (et & H).
  exists* (DE_CastDn et).

  destruct(@alen_exists G e1) as (ne1 & ex1). auto. auto. assert (exists t1, ACpltCtxSubst G e1 t1). apply* IHm.
  inversion len; subst. lets: alen_eq H2 ex1. Omega.omega.
  destruct H as (t1 & Ht1).
  destruct(@alen_exists G e2) as (ne2 & ex2). auto. auto.
  assert (exists t2, ACpltCtxSubst G e2 t2). apply* IHm.
  inversion len; subst. lets: alen_eq H4 ex2. Omega.omega.
  destruct H as (t2 & Ht2).
  exists* (DE_Ann t1 t2).
Qed.

Theorem cpltctxsubst_exists: cpltctxsubst_exists_def.
Proof.
  introv. intros. destruct(@alen_exists G e) as (n & ex). auto. auto.
  apply* cpltctxsubst_exists'.
Qed.

Lemma complete_add_star: forall G x,
    CompleteCtx G ->
    CompleteCtx (G & x ~ AC_Typ AE_Star).
Proof.
  introv comp.
  unfold CompleteCtx.
  intros z zv bd eqzv. subst.
  apply binds_push_inv in bd. destruct bd as [[_ neq] | [_ neq]].
  false neq.
  false complete_contains_unsolved comp neq.
Qed.

Theorem cpltctxtsubst_exists: cpltctxtsubst_exists_def.
Proof.
  introv wf wt comp.
  induction wt.

  pick_fresh y.
  assert (IH1: y \notin L) by auto_star.
  assert (IH2: AWf (G & y ~ AC_Typ AE_Star)). apply* AWf_TyVar.
  apply AWf_Expr with (H := empty). apply* ATC_Sub.
  rewrite subst_star. rewrite concat_empty_r. apply* AUnify_Star.
  assert (IH3: CompleteCtx (G & y ~ AC_Typ AE_Star)). apply* complete_add_star.
  lets: H0 IH1 IH2 IH3.
  destruct H1 as (nt & H1).
  apply* forall_solve.

  lets: cpltctxsubst_exists wf H comp.
  destruct H0 as (nt & H0).
  exists* (DT_Expr nt).
  apply* ACpltCtxTSubst_Expr.
Qed.
