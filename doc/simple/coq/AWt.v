Require Import LibLN.
Require Import AlgoDef.
Require Import AlgoInfra.
Require Import UtilityEnv.
Require Import Exists.
Require Import LibReflect.

(* well termed context *)

Inductive AWt : ACtx -> Prop :=
     | AWt_Nil : AWt empty
     | AWt_Var : forall G x,
         AWt G -> x # G ->
         AWt (G & x ~ AC_Var)
     | AWt_TVar : forall G a,
         AWt G -> a # G ->
         AWt (G & a ~ AC_TVar)
     | AWt_Marker : forall G a,
         AWt G -> a # G ->
         AWt (G & a ~ AC_Marker)
     | AWt_TyVar : forall G x s,
         AWt G -> x # G ->
         AWTermT G s ->
         AWt (G & x ~ AC_Typ s)
     | AWt_Ctx_Unsolved_EVar : forall G x,
         AWt G -> x # G ->
         AWt (G & x ~ AC_Unsolved_EVar)
     | AWt_Ctx_Solved_EVar : forall G x t,
         AWt G -> x # G ->
         AWTermT G t ->
         AWt (G & x ~ AC_Solved_EVar t)
.

Hint Constructors AWt.
Lemma awt_left: forall (G H: ACtx),
    AWt (G & H) ->
    AWt G.
Proof.
  induction H using env_ind;
  introv wt.
  rewrite concat_empty_r in wt; auto.
  rewrite concat_assoc in wt.
  inversion wt; subst.
  false empty_push_inv H1.
  destruct (eq_push_inv H0) as [? [? ?]]. subst. apply* IHenv.
  destruct (eq_push_inv H0) as [? [? ?]]. subst. apply* IHenv.
  destruct (eq_push_inv H0) as [? [? ?]]. subst. apply* IHenv.
  destruct (eq_push_inv H0) as [? [? ?]]. subst. apply* IHenv.
  destruct (eq_push_inv H0) as [? [? ?]]. subst. apply* IHenv.
  destruct (eq_push_inv H0) as [? [? ?]]. subst. apply* IHenv.
Qed.

Lemma awt_is_ok: forall G,
    AWt G -> ok G.
Proof.
  introv wt. induction wt; auto.
Qed.

Lemma awtermt_awt: forall G x t H,
    AWt (G & x ~ AC_Typ t & H) ->
    AWTermT G t.
Proof.
  introv wt.
  induction H using env_ind.
  rewrite concat_empty_r in wt.
  inversion wt; subst;
    try(solve[destruct (eq_push_inv H) as [? [inv ?]]; subst; false inv]).
  false empty_push_inv H0.
  destruct (eq_push_inv H) as [? [? ?]]; subst.
  inversion H4; subst~.

  rewrite concat_assoc in wt.
  lets: awt_left wt. apply* IHenv.
Qed.

Lemma awtermt_awt': forall G x t,
    AWt (G & x ~ AC_Typ t) ->
    AWTermT G t.
Proof.
  introv wt.
  rewrite <- concat_empty_r in wt.
  lets: awtermt_awt wt. auto.
Qed.

Lemma awtermt_awt_solved_evar: forall G x t H,
    AWt (G & x ~ AC_Solved_EVar t & H) ->
    AWTermT G t.
Proof.
  introv wt.
  induction H using env_ind.
  rewrite concat_empty_r in wt.
  inversion wt; subst;
    try(solve[destruct (eq_push_inv H) as [? [inv ?]]; subst; false inv]).
  false empty_push_inv H0.
  destruct (eq_push_inv H) as [? [? ?]]; subst.
  inversion H4; subst~.

  rewrite concat_assoc in wt.
  lets: awt_left wt. apply* IHenv.
Qed.

Lemma awtermt_awt_solved_evar': forall G x t,
    AWt (G & x ~ AC_Solved_EVar t) ->
    AWTermT G t.
Proof.
  introv wt.
  rewrite <- concat_empty_r in wt.
  lets: awtermt_awt_solved_evar wt. auto.
Qed.

Hint Resolve awt_left.
Lemma awt_insert_var: forall (G H: ACtx) a ,
    AWt (G & H) ->
    a # (G & H) ->
    AWt (G & a ~ AC_Var & H).
Proof.
  introv okg notin.
  induction H using env_ind.
  rewrite concat_empty_r in *. apply~ AWt_Var.
  rewrite concat_assoc in *.
  induction v.
  apply~ AWt_Var. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_TyVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  lets: awtermt_awt' okg.
  apply* awtermt_weaken_middle.
  apply ok_insert; auto.
  lets: awt_left okg. lets: awt_is_ok  H1. auto.
  apply~ AWt_TVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_Ctx_Unsolved_EVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_Ctx_Solved_EVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  lets: awtermt_awt_solved_evar' okg.
  apply* awtermt_weaken_middle.
  apply ok_insert; auto.
  lets: awt_left okg. lets: awt_is_ok  H1. auto.
  apply~ AWt_Marker. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
Qed.

Lemma awt_insert_typvar: forall (G H: ACtx) a t,
    AWt (G & H) ->
    a # (G & H) ->
    AWTermT G t ->
    AWt (G & a ~ AC_Typ t & H).
Proof.
  introv okg notin wt.
  induction H using env_ind.
  rewrite concat_empty_r in *. apply~ AWt_TyVar.
  rewrite concat_assoc in *.
  induction v.
  apply~ AWt_Var. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_TyVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  lets: awtermt_awt' okg.
  apply* awtermt_weaken_middle.
  apply ok_insert; auto.
  lets: awt_left okg. lets: awt_is_ok  H1. auto.
  apply~ AWt_TVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_Ctx_Unsolved_EVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_Ctx_Solved_EVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  lets: awtermt_awt_solved_evar' okg.
  apply* awtermt_weaken_middle.
  apply ok_insert; auto.
  lets: awt_left okg. lets: awt_is_ok  H1. auto.
  apply~ AWt_Marker. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
Qed.

Lemma awt_insert_evar: forall (G H: ACtx) a,
    AWt (G & H) ->
    a # (G & H) ->
    AWt (G & a ~ AC_Unsolved_EVar & H).
Proof.
  introv okg notin.
  induction H using env_ind.
  rewrite concat_empty_r in *. apply~ AWt_Ctx_Unsolved_EVar.
  rewrite concat_assoc in *.
  induction v.
  apply~ AWt_Var. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_TyVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  lets: awtermt_awt' okg.
  apply* awtermt_weaken_middle.
  apply ok_insert; auto.
  lets: awt_left okg. lets: awt_is_ok  H1. auto.
  apply~ AWt_TVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_Ctx_Unsolved_EVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_Ctx_Solved_EVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  lets: awtermt_awt_solved_evar' okg.
  apply* awtermt_weaken_middle.
  apply ok_insert; auto.
  lets: awt_left okg. lets: awt_is_ok  H1. auto.
  apply~ AWt_Marker. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
Qed.

Lemma awt_insert_solved_evar: forall (G H: ACtx) a t,
    AWt (G & H) ->
    a # (G & H) ->
    AWTermT G t ->
    AWt (G & a ~ AC_Solved_EVar t & H).
Proof.
  introv okg notin wt.
  induction H using env_ind.
  rewrite concat_empty_r in *. apply~ AWt_Ctx_Solved_EVar.
  rewrite concat_assoc in *.
  induction v.
  apply~ AWt_Var. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_TyVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  lets: awtermt_awt' okg.
  apply* awtermt_weaken_middle.
  apply ok_insert; auto.
  lets: awt_left okg. lets: awt_is_ok  H1. auto.
  apply~ AWt_TVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_Ctx_Unsolved_EVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_Ctx_Solved_EVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  lets: awtermt_awt_solved_evar' okg.
  apply* awtermt_weaken_middle.
  apply ok_insert; auto.
  lets: awt_left okg. lets: awt_is_ok  H1. auto.
  apply~ AWt_Marker. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
Qed.

Lemma awt_insert_tvar: forall (G H: ACtx) a,
    AWt (G & H) ->
    a # (G & H) ->
    AWt (G & a ~ AC_TVar & H).
Proof.
  introv okg notin.
  induction H using env_ind.
  rewrite concat_empty_r in *. apply~ AWt_TVar.
  rewrite concat_assoc in *.
  induction v.
  apply~ AWt_Var. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_TyVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  lets: awtermt_awt' okg.
  apply* awtermt_weaken_middle.
  apply ok_insert; auto.
  lets: awt_left okg. lets: awt_is_ok  H1. auto.
  apply~ AWt_TVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_Ctx_Unsolved_EVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_Ctx_Solved_EVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  lets: awtermt_awt_solved_evar' okg.
  apply* awtermt_weaken_middle.
  apply ok_insert; auto.
  lets: awt_left okg. lets: awt_is_ok  H1. auto.
  apply~ AWt_Marker. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
Qed.

Lemma awt_insert_marker: forall (G H: ACtx) a,
    AWt (G & H) ->
    a # (G & H) ->
    AWt (G & a ~ AC_Marker & H).
Proof.
  introv okg notin.
  induction H using env_ind.
  rewrite concat_empty_r in *. apply~ AWt_Marker.
  rewrite concat_assoc in *.
  induction v.
  apply~ AWt_Var. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_TyVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  lets: awtermt_awt' okg.
  apply* awtermt_weaken_middle.
  apply ok_insert; auto.
  lets: awt_left okg. lets: awt_is_ok  H1. auto.
  apply~ AWt_TVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_Ctx_Unsolved_EVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  apply~ AWt_Ctx_Solved_EVar. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
  lets: awtermt_awt_solved_evar' okg.
  apply* awtermt_weaken_middle.
  apply ok_insert; auto.
  lets: awt_left okg. lets: awt_is_ok  H1. auto.
  apply~ AWt_Marker. apply* IHenv.
  lets: awt_is_ok okg. destruct (ok_push_inv H0) as [? ?]. auto.
Qed.

Lemma awt_solve_evar: forall (G H: ACtx) a t,
    AWt (G & a ~ AC_Unsolved_EVar & H) ->
    a # (G & H) ->
    AWTermT G t ->
    AWt (G & a ~ AC_Solved_EVar t & H).
Proof.
  introv awt notin wt.
  induction H using env_ind.
  rewrite concat_empty_r in *.
  apply AWt_Ctx_Solved_EVar; auto.
  lets: awt_left awt; auto.
  rewrite concat_assoc in *.
  lets: awt_left awt.
  forwards * : IHenv H0. clear IHenv.
  lets: awt_is_ok awt.
  destruct (ok_push_inv H2) as [? ?].
  induction v.
  apply~ AWt_Var.
  apply~ AWt_TyVar.
  lets: awtermt_awt' awt. apply* awtermt_middle_solve.
  apply~ AWt_TVar.
  apply~ AWt_Ctx_Unsolved_EVar.
  apply AWt_Ctx_Solved_EVar; auto.
  lets: awtermt_awt_solved_evar' awt.
  apply* awtermt_middle_solve.
  apply~ AWt_Marker.
Qed.

Lemma resolve_evar_awt_preservation: forall G s t H a,
    AResolveEVar G a s t H ->
    AWt G ->
    AWt H.
Proof.
  introv res wt.
  induction res; auto.

  apply~ awt_solve_evar.
  do 3 rewrite <- concat_assoc.
  apply~ awt_insert_evar.
  do 3 rewrite~ concat_assoc.
  lets: awt_is_ok wt.
  destruct (ok_middle_inv H0) as [? ? ]. auto.

  lets: IHres wt.
  pick_fresh y.
  assert (AWt (H1 & y ~ AC_Var)). apply~ AWt_Var.
  lets: H2 H4. auto.
  lets: awt_left H5; auto.

  pick_fresh y.
  assert (AWt (G & y ~ AC_Var)). apply~ AWt_Var.
  lets: H1 H2. auto.
  lets: awt_left H3; auto.
Qed.

Lemma resolve_forall_awt_preservation: forall G m s t H a,
    AResolveForall G a m s t H ->
    AWt G ->
    AWt H.
Proof.
  introv res wt.
  induction res; auto.

  apply* IHres.
  rewrite <- concat_assoc in wt.
  lets: awt_insert_evar a1 wt; auto.
  repeat rewrite concat_assoc in H1.
  apply* H1.
Qed.

Lemma unify_awt_preservation: forall G s t H,
    AUnify G s t H ->
    AWt G ->
    AWt H.
Proof.
  introv uni wt.
  induction uni; auto.

  pick_fresh y.
  assert (AWt (G & y ~ AC_Var)). apply~ AWt_Var.
  lets: H1 H2. auto.
  lets: awt_left H3; auto.

  lets: IHuni wt.
  pick_fresh y.
  assert (AWt (H1 & y ~ AC_Var)). apply~ AWt_Var.
  lets: H2 H4. auto.
  lets: awt_left H5; auto.

  pick_fresh y.
  assert (AWt (G & y ~ AC_TVar)). apply~ AWt_TVar.
  lets: H1 H2. auto.
  lets: awt_left H3; auto.

  lets: resolve_evar_awt_preservation H0 wt.
  apply~ awt_solve_evar.
  lets: awt_is_ok H4.
  destruct (ok_middle_inv H5) as [? ?]. auto.

  lets: resolve_evar_awt_preservation H3 wt.
  apply~ awt_solve_evar.
  lets: awt_is_ok H5.
  destruct (ok_middle_inv H6) as [? ?]. auto.
Qed.

(* substitutions *)

Lemma distributivity_ctxsubst_subst_awt : forall H x s e,
    AWt H ->
    x # H ->
    ACtxSubst H (ASubst x s e) =
    ASubst x (ACtxSubst H s) (ACtxSubst H e).
Proof.
  introv. gen s e x.
  induction H using env_ind; introv wf notin.
  repeat(rewrite* subst_empty_env).

  induction v.

  repeat(rewrite subst_add_var).
  apply awt_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_typvar).
  apply awt_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_tvar).
  apply awt_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_evar).
  apply awt_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_solved_evar).
  rewrite substt_subst_distr.
  apply awt_left in wf.
  apply* IHenv.
  simpl_dom. auto.
  assert (x # H).
  lets: awt_is_ok wf. destruct (ok_push_inv H0); auto.
  apply awtermt_awt_solved_evar' in wf. apply notin_tfv_tftv. apply* notin_awtermt.
  apply awtermt_awt_solved_evar' in wf. apply notin_tfv_tfev. apply* notin_awtermt.

  repeat(rewrite subst_add_marker).
  apply awt_left in wf.
  apply* IHenv.
Qed.

Lemma distributivity_ctxsubst_substt_awt : forall H x s e,
    AWt H ->
    x # H ->
    ACtxSubst H (ASubstT x s e) =
    ASubstT x (ACtxTSubst H s) (ACtxSubst H e).
Proof.
  introv. gen s e x.
  induction H using env_ind; introv wf notin.
  repeat(rewrite* subst_empty_env).
  repeat(rewrite* tsubst_empty_env).

  induction v.

  repeat(rewrite subst_add_var).
  repeat(rewrite tsubst_add_var).
  apply awt_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_typvar).
  repeat(rewrite tsubst_add_typvar).
  apply awt_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_tvar).
  repeat(rewrite tsubst_add_tvar).
  apply awt_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_evar).
  repeat(rewrite tsubst_add_evar).
  apply awt_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_solved_evar).
  repeat(rewrite tsubst_add_solved_evar).
  rewrite substt_substt_distr.
  apply awt_left in wf.
  apply* IHenv.
  simpl_dom. auto.
  assert (x # H).
  lets: awt_is_ok wf. destruct (ok_push_inv H0); auto.
  apply awtermt_awt_solved_evar' in wf. apply notin_tfv_tftv. apply* notin_awtermt.
  apply awtermt_awt_solved_evar' in wf. apply notin_tfv_tftv. apply* notin_awtermt.

  repeat(rewrite subst_add_marker).
  repeat(rewrite tsubst_add_marker).
  apply awt_left in wf.
  apply* IHenv.
Qed.

Lemma distributivity_ctxtsubst_tsubst_awt : forall H x s e,
    AWt H ->
    x # H ->
    ACtxTSubst H (ATSubst x s e) =
    ATSubst x (ACtxSubst H s) (ACtxTSubst H e).
Proof.
  introv. gen s e x.
  induction H using env_ind; introv wf notin.
  rewrite* subst_empty_env.
  rewrite* tsubst_empty_env.
  rewrite* tsubst_empty_env.

  induction v.

  rewrite subst_add_var.
  rewrite tsubst_add_var.
  rewrite tsubst_add_var.
  apply awt_left in wf.
  apply* IHenv.

  rewrite subst_add_typvar.
  rewrite tsubst_add_typvar.
  rewrite tsubst_add_typvar.
  apply awt_left in wf.
  apply* IHenv.

  rewrite subst_add_tvar.
  rewrite tsubst_add_tvar.
  rewrite tsubst_add_tvar.
  apply awt_left in wf.
  apply* IHenv.

  rewrite subst_add_evar.
  rewrite tsubst_add_evar.
  rewrite tsubst_add_evar.
  apply awt_left in wf.
  apply* IHenv.

  rewrite subst_add_solved_evar.
  rewrite tsubst_add_solved_evar.
  rewrite tsubst_add_solved_evar.
  rewrite tsubstt_tsubst_distr.
  apply awt_left in wf.
  apply* IHenv.
  simpl_dom. auto.
  assert (x # H).
  lets: awt_is_ok wf. destruct (ok_push_inv H0); auto.
  apply awtermt_awt_solved_evar' in wf. apply notin_tfv_tftv. apply* notin_awtermt.
  apply awtermt_awt_solved_evar' in wf. apply notin_tfv_tfev. apply* notin_awtermt.

  rewrite subst_add_marker.
  rewrite tsubst_add_marker.
  rewrite tsubst_add_marker.
  apply awt_left in wf.
  apply* IHenv.
Qed.

Lemma distributivity_ctxtsubst_substt_awt : forall H x s e,
    AWt H ->
    x # H ->
    ACtxSubst H (ASubstT x s e) =
    ASubstT x (ACtxTSubst H s) (ACtxSubst H e).
Proof.
  introv. gen s e x.
  induction H using env_ind; introv wf notin.
  rewrite* subst_empty_env.
  rewrite* tsubst_empty_env.
  rewrite* subst_empty_env.

  induction v.

  rewrite subst_add_var.
  rewrite tsubst_add_var.
  rewrite subst_add_var.
  apply awt_left in wf.
  apply* IHenv.

  rewrite subst_add_typvar.
  rewrite tsubst_add_typvar.
  rewrite subst_add_typvar.
  apply awt_left in wf.
  apply* IHenv.

  rewrite subst_add_tvar.
  rewrite tsubst_add_tvar.
  rewrite subst_add_tvar.
  apply awt_left in wf.
  apply* IHenv.

  rewrite subst_add_evar.
  rewrite tsubst_add_evar.
  rewrite subst_add_evar.
  apply awt_left in wf.
  apply* IHenv.

  rewrite subst_add_solved_evar.
  rewrite tsubst_add_solved_evar.
  rewrite subst_add_solved_evar.
  rewrite substt_substt_distr.
  apply awt_left in wf.
  apply* IHenv.
  simpl_dom. auto.
  assert (x # H).
  lets: awt_is_ok wf. destruct (ok_push_inv H0); auto.
  apply awtermt_awt_solved_evar' in wf. apply notin_tfv_tftv. apply* notin_awtermt.
  apply awtermt_awt_solved_evar' in wf. apply notin_tfv_tftv. apply* notin_awtermt.

  rewrite subst_add_marker.
  rewrite tsubst_add_marker.
  rewrite subst_add_marker.
  apply awt_left in wf.
  apply* IHenv.
Qed.

Lemma distributivity_ctxtsubst_tsubstt_awt : forall H x s e,
    AWt H ->
    x # H ->
    ACtxTSubst H (ATSubstT x s e) =
    ATSubstT x (ACtxTSubst H s) (ACtxTSubst H e).
Proof.
  introv. gen s e x.
  induction H using env_ind; introv wf notin.
  repeat(rewrite* tsubst_empty_env).

  induction v.

  repeat(rewrite tsubst_add_var).
  apply awt_left in wf.
  apply* IHenv.

  repeat(rewrite tsubst_add_typvar).
  apply awt_left in wf.
  apply* IHenv.

  repeat(rewrite tsubst_add_tvar).
  apply awt_left in wf.
  apply* IHenv.

  repeat(rewrite tsubst_add_evar).
  apply awt_left in wf.
  apply* IHenv.

  repeat(rewrite tsubst_add_solved_evar).
  rewrite tsubstt_tsubstt_distr.
  apply awt_left in wf.
  apply* IHenv.
  simpl_dom. auto.
  assert (x # H).
  lets: awt_is_ok wf. destruct (ok_push_inv H0); auto.
  apply awtermt_awt_solved_evar' in wf. apply notin_tfv_tftv. apply* notin_awtermt.
  apply awtermt_awt_solved_evar' in wf. apply notin_tfv_tftv. apply* notin_awtermt.

  repeat rewrite tsubst_add_marker.
  apply awt_left in wf.
  apply* IHenv.
Qed.

Lemma notin_ctxsubst_fev_awt: forall x H e,
  x \notin AFev e ->
  x # H ->
  AWt H ->
  x \notin AFev (ACtxSubst H e).
Proof.
  introv notine notinh wf. gen e.
  induction H using env_ind; introv notine.
  rewrite* subst_empty_env.
  assert (wf2:=wf). apply awt_left in wf2.
  induction v.
  rewrite subst_add_var. apply* IHenv.
  rewrite subst_add_typvar. apply* IHenv.
  assert (x <> x0). simpl_dom. auto_star.

  rewrite subst_add_tvar. apply* IHenv.
  rewrite subst_add_evar. apply* IHenv.

  rewrite subst_add_solved_evar.
  apply* IHenv. apply* notin_substt_fev.
  apply notin_tfv_tfev. apply notin_awtermt with (G:=H); auto.
  apply* awtermt_awt_solved_evar'.
  rewrite subst_add_marker. apply* IHenv.
Qed.

Lemma notin_ctxsubst_ftv_awt: forall x H e,
  x \notin AFtv e ->
  x # H ->
  AWt H ->
  x \notin AFtv (ACtxSubst H e).
Proof.
  introv notine notinh wf. gen e.
  induction H using env_ind; introv notine.
  rewrite* subst_empty_env.
  assert (wf2:=wf). apply awt_left in wf2.
  induction v.
  rewrite subst_add_var. apply* IHenv.
  rewrite subst_add_typvar. apply* IHenv.
  assert (x <> x0). simpl_dom. auto_star.

  rewrite subst_add_tvar. apply* IHenv.
  rewrite subst_add_evar. apply* IHenv.

  rewrite subst_add_solved_evar.
  apply* IHenv. apply* notin_substt_ftv.
  apply notin_tfv_tftv. apply notin_awtermt with (G:=H); auto.
  apply* awtermt_awt_solved_evar'.
  rewrite subst_add_marker. apply* IHenv.
Qed.

Lemma notin_actxsubst_awt: forall y H e,
    AWt H ->
    y # H ->
    y \notin AFv e ->
    y \notin AFv (ACtxSubst H e).
Proof.
  introv wf notinh notine.
  gen e. induction H using env_ind; introv notine.
  rewrite~ subst_empty_env.
  simpls.
  lets: awt_left wf.
  induction v.
  rewrite~ subst_add_var.
  rewrite~ subst_add_typvar.
  rewrite~ subst_add_tvar.
  rewrite~ subst_add_evar.
  rewrite~ subst_add_solved_evar.
  apply* IHenv. apply* notin_substt. apply notin_awtermt with H; auto.
  apply* awtermt_awt_solved_evar'.
  rewrite~ subst_add_marker.
Qed.

Lemma notin_ctxtsubst_ftv_awt: forall x H e,
  x \notin ATFtv e ->
  x # H ->
  AWt H ->
  x \notin ATFtv (ACtxTSubst H e).
Proof.
  introv notine notinh wf. gen e.
  induction H using env_ind; introv notine.
  rewrite* tsubst_empty_env.
  assert (wf2:=wf). apply awt_left in wf2.
  induction v.
  rewrite tsubst_add_var. apply* IHenv.
  rewrite tsubst_add_typvar. apply* IHenv.
  assert (x <> x0). simpl_dom. auto_star.

  rewrite tsubst_add_tvar. apply* IHenv.
  rewrite tsubst_add_evar. apply* IHenv.

  rewrite tsubst_add_solved_evar.
  apply* IHenv. apply* notin_tsubstt_ftv.
  apply notin_tfv_tftv. apply notin_awtermt with (G:=H); auto.
  apply* awtermt_awt_solved_evar'.
  rewrite tsubst_add_marker. apply* IHenv.
Qed.

Lemma notin_ctxtsubst_fev_awt: forall x H e,
  x \notin ATFev e ->
  x # H ->
  AWt H ->
  x \notin ATFev (ACtxTSubst H e).
Proof.
  introv notine notinh wf. gen e.
  induction H using env_ind; introv notine.
  rewrite* tsubst_empty_env.
  assert (wf2:=wf). apply awt_left in wf2.
  induction v.
  rewrite tsubst_add_var. apply* IHenv.
  rewrite tsubst_add_typvar. apply* IHenv.
  assert (x <> x0). simpl_dom. auto_star.

  rewrite tsubst_add_tvar. apply* IHenv.
  rewrite tsubst_add_evar. apply* IHenv.

  rewrite tsubst_add_solved_evar.
  apply* IHenv. apply* notin_tsubstt_fev.
  apply notin_tfv_tfev. apply notin_awtermt with (G:=H); auto.
  apply* awtermt_awt_solved_evar'.
  rewrite tsubst_add_marker. apply* IHenv.
Qed.

Lemma notin_actxtsubst_awt: forall y H e,
    AWt H ->
    y # H ->
    y \notin ATFv e ->
    y \notin ATFv (ACtxTSubst H e).
Proof.
  introv wf notinh notine.
  gen e. induction H using env_ind; introv notine.
  rewrite~ tsubst_empty_env.
  simpls.
  lets: awt_left wf.
  induction v.
  rewrite~ tsubst_add_var.
  rewrite~ tsubst_add_typvar.
  rewrite~ tsubst_add_tvar.
  rewrite~ tsubst_add_evar.
  rewrite~ tsubst_add_solved_evar.
  apply* IHenv. apply* notin_tsubstt. apply notin_awtermt with H; auto.
  apply* awtermt_awt_solved_evar'.
  rewrite~ tsubst_add_marker.
Qed.

Lemma notin_solved_evar_awt:  forall G x t,
    AWt (G & x ~ AC_Solved_EVar t) ->
    x \notin ATFv t.
Proof.
  introv wf.
  apply notin_awtermt with (G:=G).
  apply* awtermt_awt_solved_evar'.
  lets: awt_is_ok wf.
  apply* ok_push_inv.
Qed.

Lemma actxsubst_open_awt: forall G e u,
    AWt G ->
    ACtxSubst G (e @@ u) = (ACtxSubst G e) @@ (ACtxSubst G u).
Proof.
  introv wf. gen e u.
  induction G using env_ind; introv.
  repeat rewrite~ subst_empty_env.
  assert (AWt G) by apply* awt_left.
  induction v.
  repeat rewrite~ subst_add_var.
  repeat rewrite~ subst_add_typvar.
  repeat rewrite~ subst_add_tvar.
  repeat rewrite~ subst_add_evar.
  repeat rewrite~ subst_add_solved_evar.
  rewrite~ <- IHG. f_equal ~.
  unfold AOpen. rewrite~ asubstt_openrec.
  apply awtermt_is_awtermty with G.
  apply* awtermt_awt_solved_evar'.
  repeat rewrite~ subst_add_marker.
Qed.

Lemma actxtsubst_open_awt: forall G e u,
    AWt G ->
    ACtxTSubst G (e @@' u) = (ACtxTSubst G e) @@' (ACtxSubst G u).
Proof.
  introv wf. gen e u.
  induction G using env_ind; introv.
  repeat rewrite~ subst_empty_env.
  repeat rewrite~ tsubst_empty_env.
  assert (AWt G) by apply* awt_left.
  induction v.
  repeat rewrite~ subst_add_var. repeat rewrite~ tsubst_add_var.
  repeat rewrite~ subst_add_typvar. repeat rewrite~ tsubst_add_typvar.
  repeat rewrite~ subst_add_tvar. repeat rewrite~ tsubst_add_tvar.
  repeat rewrite~ subst_add_evar. repeat rewrite~ tsubst_add_evar.
  repeat rewrite~ subst_add_solved_evar. repeat rewrite~ tsubst_add_solved_evar.
  rewrite~ <- IHG. f_equal ~.
  unfold AOpenT. rewrite~ atsubstt_opentyprec.
  apply awtermt_is_awtermty with G.
  apply* awtermt_awt_solved_evar'.
  repeat rewrite~ subst_add_marker. repeat rewrite~ tsubst_add_marker.
Qed.

Lemma actxtsubst_topen_awt: forall G e u,
    AWt G ->
    ACtxTSubst G (e @@#' u) = (ACtxTSubst G e) @@#' (ACtxTSubst G u).
Proof.
  introv wf. gen e u.
  induction G using env_ind; introv.
  repeat rewrite~ tsubst_empty_env.
  assert (AWt G) by apply* awt_left.
  induction v.
  repeat rewrite~ tsubst_add_var.
  repeat rewrite~ tsubst_add_typvar.
  repeat rewrite~ tsubst_add_tvar.
  repeat rewrite~ tsubst_add_evar.
  repeat rewrite~ tsubst_add_solved_evar.
  rewrite~ <- IHG. f_equal ~.
  unfold ATOpenT. rewrite~ atsubstt_topentyprec.
  apply awtermt_is_awtermty with G.
  apply* awtermt_awt_solved_evar'.
  repeat rewrite~ subst_add_marker. repeat rewrite~ tsubst_add_marker.
Qed.

Lemma ctxsubst_evar_eq : forall G x,
    ok G ->
    (binds x AC_Unsolved_EVar G \/ x # G) ->
    ACtxTSubst G (AT_EVar x) = AT_EVar x.
Proof.
  introv H H1. inductions H.
  rewrite* tsubst_empty_env.
  inductions v.
  rewrite~ tsubst_add_var.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ tsubst_add_typvar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ tsubst_add_tvar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ tsubst_add_evar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

  rewrite~ tsubst_add_solved_evar.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2].
  false. simpl. case_var~.
  rewrite dom_single in NIn.
  false. apply* notin_same.
  simpl. case_var~.
  false. rewrite dom_push in Frh.
  apply* notin_same.

  rewrite~ tsubst_add_marker.
  destruct H1 as [Bnd | Frh].
  destruct (binds_concat_inv Bnd) as [Bnd1 | [NIn Bnd1]].
  destruct (binds_single_inv Bnd1) as [Eq1 Eq2]; subst.
  apply* IHok.
  apply* IHok.
  apply* IHok.

Qed.

Hint Resolve awt_is_ok.
Lemma alen_awterm_append_awt: forall G H e n,
    AWt (G & H) ->
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
  apply* ALen_Var_I4. apply* binds_concat_left_ok.
  inversion wt; subst; try(solve[false binds_fresh_inv H3 H0]).

  apply* ALen_EVar. apply* binds_concat_left_ok.
  rewrite <- concat_assoc. apply* ALen_Solved_EVar.
  rewrite* concat_assoc.
  apply* ALen_EVar_I1. apply* binds_concat_left_ok.
  apply* ALen_EVar_I2. apply* binds_concat_left_ok.
  apply* ALen_EVar_I3. apply* binds_concat_left_ok.
  apply* ALen_EVar_I4. apply* binds_concat_left_ok.
  inversion wt; subst; try(solve[false binds_fresh_inv H3 H0]).

  apply ALen_TBVar.
  apply* ALen_TFVar. apply* binds_concat_left_ok.
  apply* ALen_TFVar_I1. apply* binds_concat_left_ok.
  apply* ALen_TFVar_I2. apply* binds_concat_left_ok.
  apply* ALen_TFVar_I3. apply* binds_concat_left_ok.
  apply* ALen_TFVar_I4. apply* binds_concat_left_ok.
  apply* ALen_TFVar_I5. apply* binds_concat_left_ok.
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

Lemma alen_exists_awt': forall G e n,
    AWt G ->
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
  rewrite IG in okg. rewrite <- concat_assoc in okg. apply* awt_left.

  rewrite IG in len.
  rewrite concat_def in len. repeat(rewrite LibList.length_app in len).
  assert(LibList.length (a~ AC_Solved_EVar t) = 1). rewrite single_def. rewrite LibList.length_cons. rewrite LibList.length_nil. Omega.omega.
  Omega.omega.
  apply awterm_is_awterma.
  rewrite IG in okg. apply awt_left in okg. apply awtermt_awt_solved_evar' in okg. auto.
  destruct H1 as (ne & H1). exists (ne + 1). rewrite IG in *. apply ALen_Solved_EVar; auto.
  lets: awt_is_ok okg. auto.

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

Lemma alen_exists_awt: forall G e,
    AWt G ->
    AWTermA G e ->
    exists n, ALen G e n.
Proof.
  intros.
  apply* alen_exists_awt'.
Qed.

Lemma ctxsubst_awterm_awt' : forall G t n m,
    AWt G ->
    AWTermT G t ->
    n < m ->
    ALen G t n ->
    AWTermT G (ACtxTSubst G t).
Proof.
  intros. gen G t n. induction m; introv wf wt less len.
  inversion less.


  gen n. induction wt; introv less len; simpls; auto.

  (* AE_FVar *)
  assert (ACtxTSubst G (AT_Expr (AE_FVar x)) = AT_Expr (AE_FVar x)).
  rewrite actxtsubst_expr. f_equal.
  rewrite actxsubst_fvar; auto.
  rewrite H0.
  apply* AWTermT_Var.

  (* AE_FVar *)
  assert (ACtxTSubst G (AT_Expr (AE_FVar x)) = AT_Expr (AE_FVar x)).
  rewrite* actxtsubst_expr. f_equal ~.
  rewrite* actxsubst_fvar.
  rewrite H0.
  apply* AWTermT_TypVar.

  (* Star *)
  rewrite tsubst_star.
  apply AWTermT_Star.

  (* APP *)
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_app.
  inversion len; subst.
  apply* AWTermT_App.
  apply IHwt1 with i1; auto. Omega.omega.
  apply IHwt2 with i2; auto. Omega.omega.

  (* Lam *)
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_lam.
  apply AWTermT_Lam with (L \u dom G).
  intros y notiny.
  assert (AWt (G & y ~ AC_Var)). apply* AWt_Var.
  assert (y \notin L) by auto_star.
  lets: H0 H2 H1.
  rewrite actxtsubst_expr in H3.
  rewrite subst_add_var in H3.
  inversion len; subst.
  apply alen_open_expr with (n:=0) (y:=y) in H6; auto.
  apply alen_add_var_expr with (y:=y) in H6; auto.
  lets: H3 H6. Omega.omega.

  rewrite actxsubst_open_awt in H4; auto.
  rewrite actxsubst_fvar in H4; auto.

  (* Pi *)
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_pi.
  inversion len; subst.
  apply AWTermT_Pi with (L \u dom G).
  apply IHwt with (n:=i1); auto. Omega.omega.
  intros y notiny.
  assert (AWt (G & y ~ AC_Var)). apply* AWt_Var.
  assert (y \notin L) by auto_star.
  lets: H0 H2 H1.
  rewrite tsubst_add_var in H3.
  apply alen_open with (n:=0) (y:=y) in H6; auto.
  apply alen_add_var with (y:=y) in H6; auto.
  lets: H3 H6. Omega.omega.

  rewrite actxtsubst_open_awt in H5; auto.
  rewrite actxsubst_fvar in H5; auto.

  (* CASTUP *)
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_castup.
  apply AWTermT_CastUp.
  inversion len; subst.
  apply IHwt with i; auto. Omega.omega.

  (* CASTDOWN *)
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_castdn.
  apply AWTermT_CastDn.
  inversion len; subst.
  apply IHwt with i; auto. Omega.omega.

  (* ANN *)
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_ann.
  inversion len; subst.
  apply AWTermT_Ann.
  apply IHwt1 with i1; auto. Omega.omega.
  apply IHwt2 with i2; auto. Omega.omega.

  (* FORALL *)
  rewrite actxtsubst_expr in *.
  rewrite actxsubst_forall.
  inversion len; subst.
  apply AWTermT_Forall with (L \u dom G).
  intros y notiny.
  assert (AWt (G & y ~ AC_TVar)). apply* AWt_TVar.
  assert (y \notin L) by auto_star.
  lets: H0 H2 H1.
  rewrite tsubst_add_tvar in H4.
  apply alen_topen with (n:=0) (y:=y) in H3; auto.
  apply alen_add_tvar with (y:=y) in H3; auto.
  lets: H4 H3. Omega.omega.

  rewrite actxtsubst_topen_awt in H5.
  rewrite actxtsubst_tfvar_notin in H5; auto.
  lets: awt_is_ok H1. auto.

  (* TVar *)
  rewrite* actxtsubst_tfvar.

  (* Unsolved EVAR *)
  rewrite* ctxsubst_evar_eq.

  (* Solved EVar*)
  destruct (split_bind_context H) as (G1 & G2 & hg).
  assert (AWTermT G t).
  rewrite hg in wf.
  lets: awtermt_awt_solved_evar wf.
  apply awtermt_weaken_ctx with (H:=(i ~ AC_Solved_EVar t & G2)) in H0; auto.
  rewrite concat_assoc in H0. rewrite~ hg.
  lets: awt_is_ok wf; auto.
  rewrite~ concat_assoc.
  assert (exists n1, ALen G1 t n1). apply* alen_exists_awt. rewrite hg in wf. do 2 apply awt_left in wf. auto.
  rewrite hg in wf. apply awt_left in wf. apply awtermt_awt_solved_evar' in wf. apply* awterm_is_awterma.
  destruct H1 as (n1 & len_t).
  assert (n1 < m). rewrite hg in len. apply alen_evar with (G2:=G2) (a:=i) (n:=n) in len_t; auto. Omega.omega. rewrite <- hg. apply* awt_is_ok.
  lets: IHm wf H0 n1 H1.

  assert (ALen (G1 & (i ~ AC_Solved_EVar t & G2)) t n1).
  apply* alen_awterm_append_awt.
  rewrite concat_assoc. rewrite <- hg. auto.
  apply awterm_is_awterma. rewrite hg in wf. apply awt_left in wf. apply awtermt_awt_solved_evar' in wf. auto.
  rewrite concat_assoc in H3. rewrite <- hg in H3.
  lets: H2 H3.

  rewrite hg.
  rewrite tsubst_add_ctx.
  assert (i # G2). rewrite hg in wf. apply awt_is_ok in wf. apply* ok_middle_inv_r.
  rewrite* ctxsubst_evar_eq.
  simpls.
  rewrite tsubst_add_ctx.
  assert (ACtxTSubst (i ~ AC_Solved_EVar t) (AT_EVar i) = t). unfold ACtxTSubst.
  rewrite single_def.
  rewrite LibList.fold_left_cons.
  rewrite LibList.fold_left_nil.
  simpls. case_if*.

  rewrite H6. clear H6.
  rewrite <- actxtsubst_append with (H:=i ~ AC_Solved_EVar t & G2); auto.
  rewrite concat_assoc. rewrite <- hg. auto.

  rewrite concat_assoc. rewrite~ <- hg.
  rewrite hg in wf. apply awt_left in wf. apply awtermt_awt_solved_evar' in wf; auto.
  rewrite hg in wf.
  apply* ok_concat_inv_r.
Qed.

Lemma ctxsubst_awterm_awt : forall G t,
    AWt G ->
    AWTermT G t ->
    AWTermT G (ACtxTSubst G t).
Proof.
  intros.
  assert (exists n, ALen G t n). apply~ alen_exists_awt.
  destruct H1 as (n & len).
  apply* ctxsubst_awterm_awt'.
Qed.

Lemma awf_is_awt: forall G,
    AWf G ->
    AWt G.
Proof.
  introv wf. induction wf; auto.
  apply~ AWt_TyVar. lets: awtermt_awftyp H0. auto.
  apply~ AWt_Ctx_Solved_EVar. lets: awtermt_awftyp H1. auto.
Qed.

Lemma ctxsubst_twice_awt: forall H e,
    AWt H ->
    ACtxSubst H (ACtxSubst H e) = ACtxSubst H e.
Proof.
  introv wf. gen e. induction H using env_ind; introv.
  repeat rewrite~ subst_empty_env.
  lets: awt_left wf.
  destruct (ok_push_inv (awt_is_ok (H & x ~ v) wf)).
  destruct v.
  repeat rewrite~ subst_add_var.
  repeat rewrite~ subst_add_typvar.
  repeat rewrite~ subst_add_tvar.
  repeat rewrite~ subst_add_evar.
  repeat rewrite~ subst_add_solved_evar.
  rewrite~ distributivity_ctxsubst_substt_awt.
  rewrite~ IHenv.
  rewrite~ <- distributivity_ctxsubst_substt_awt.
  rewrite~ substt_twice. apply notin_tfv_tftv.
  apply notin_awtermt with H; auto.
  apply awtermt_awt_solved_evar' in wf; auto.
  repeat rewrite~ subst_add_marker.
Qed.

Lemma ctxtsubst_twice_awt: forall H e,
    AWt H ->
    ACtxTSubst H (ACtxTSubst H e) = ACtxTSubst H e.
Proof.
  introv wf. gen e. induction H using env_ind; introv.
  repeat rewrite~ tsubst_empty_env.
  lets: awt_left wf.
  destruct (ok_push_inv (awt_is_ok  (H & x ~ v) wf)).
  destruct v.
  repeat rewrite~ tsubst_add_var.
  repeat rewrite~ tsubst_add_typvar.
  repeat rewrite~ tsubst_add_tvar.
  repeat rewrite~ tsubst_add_evar.
  repeat rewrite~ tsubst_add_solved_evar.
  rewrite~ distributivity_ctxtsubst_tsubstt_awt.
  rewrite~ IHenv.
  rewrite~ <- distributivity_ctxtsubst_tsubstt_awt.
  rewrite~ tsubstt_twice. apply notin_tfv_tftv.
  apply notin_awtermt with H; auto.
  apply awtermt_awt_solved_evar' in wf; auto.
  repeat rewrite~ tsubst_add_marker.
Qed.
