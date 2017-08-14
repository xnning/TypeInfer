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
Require Import UtilityAlgo.

(* CONTEXT EQUAL UP TO RENAMING *)

Lemma typing_insert_unsolved_evar: forall G1 G2 m e t H a,
    ATyping m (G1 & G2) e t H ->
    a # (G1 & G2) ->
    exists I I1 I2 H2, ATyping m (G1 & a ~ AC_Unsolved_EVar & G2) e t I
                  /\ I = I1 & a ~ AC_Unsolved_EVar & I2
                  /\ H = I1 & H2
                  (*/\ I2 H2 has ....*)

with awf_insert_unsolved_evar: forall G1 G2 a,
    AWf (G1 & G2) ->
    a # (G1 & G2) ->
    AWf (G1 & a ~ AC_Unsolved_EVar & G2).
Proof.
  introv ty notin. gen_eq G:(G1 & G2). gen G1 G2.
  lets: atyping_awf ty.
  induction ty; introv ginfo; subst; auto.

  admit.



  exists~ (G1 & a ~ AC_Unsolved_EVar & G2).
  (* VAR *)
  exists~ (G1 & a ~ AC_Unsolved_EVar & G2). apply ATI_Var. apply* awf_insert_unsolved_evar.
  assert (a <> x). introv neq; subst. false binds_fresh_inv H1 notin0.
  apply~ binds_weaken.

  (* EVAR *)
  exists~ (G1 & a ~ AC_Unsolved_EVar & G2). apply ATI_EVar. apply* awf_insert_unsolved_evar.
  assert (a <> x). introv neq; subst. false binds_fresh_inv H1 notin0.
  apply~ binds_weaken.

  (* EVAR *)
  exists~ (G1 & a ~ AC_Unsolved_EVar & G2). apply ATI_Solved_EVar with t. apply* awf_insert_unsolved_evar.
  assert (a <> x). introv neq; subst. false binds_fresh_inv H1 notin0.
  apply~ binds_weaken.

  (* TVar *)
  exists~ (G1 & a ~ AC_Unsolved_EVar & G2). apply ATI_TVar. apply* awf_insert_unsolved_evar.
  assert (a <> x). introv neq; subst. false binds_fresh_inv H1 notin0.
  apply~ binds_weaken.

  (* ANN *)

(* Lemma unify_same: forall G a, *)
(*     AWf G -> *)
(*     AWTermT G a -> *)
(*     ATMono a -> *)
(*     ACtxTSubst G a = a -> *)
(*     AUnify G a a G. *)
(* Proof. *)
(*   introv wf wt mono sub. induction wt; try(solve[constructor~]). *)
(*   (* Typed Var *) *)
(*   apply AUnify_Typed_Var with t; auto. *)

(*   (* APP *) *)
(*   rewrite actxtsubst_expr in sub. rewrite actxsubst_app in sub. inversion sub. *)
(*   inversion mono. inversion H2. clear H H2 H3 H4. *)
(*   apply AUnify_App with G; auto. *)
(*   rewrite H0. apply~ IHwt1. apply ATrewrite actxtsubst_expr. f_equal~. *)
(*   repeat rewrite H1. apply~ IHwt2. rewrite actxtsubst_expr. f_equal~. *)

(*   (* LAM *) *)
(*   rewrite actxtsubst_expr in sub. rewrite actxsubst_lam in sub. inversion sub. clear sub. *)
(*   apply AUnify_Lam with (L \u dom G); auto. *)
(*   intros y notin. *)
(*   assert (y \notin L) by auto. *)
(*   assert (AWf (G & y ~ AC_Var)) by apply~ AWf_Var. *)
(*   lets: H H1. clear H. *)
(*   lets: H0 H1 H3. clear H0. *)

(*   assert(ACtxTSubst (G & y ~ AC_Var) (AT_Expr (e @@ AE_FVar y)) = *)
(*       AT_Expr (e @@ AE_FVar y)). *)
(*   rewrite tsubst_add_var. *)
(*   rewrite actxtsubst_expr. f_equal. *)
(*   rewrite~ actxsubst_open. *)
(*   rewrite H2. rewrite actxsubst_fvar. auto. *)
(*   lets: H H0. clear H. *)

(*   rewrite tsubst_add_var in H0. *)
(*   rewrite actxtsubst_expr in H0. *)
(*   inversion~ H0. clear H0. *)
(*   rewrite~ actxsubst_open in H6. *)
(*   rewrite actxsubst_fvar in H6. *)

(*   rewrite H6. auto. *)

(*   (* PI *) *)
(*   rewrite actxtsubst_expr in sub. rewrite actxsubst_pi in sub. inversion sub. clear sub. *)
(*   apply AUnify_Pi with G (L \u dom G); auto. *)
(*   rewrite H2. apply~ IHwt. *)

(*   intros y notin. *)
(*   assert (y \notin L) by auto. *)
(*   assert (AWf (G & y ~ AC_Var)) by apply~ AWf_Var. *)
(*   lets: H H1. clear H. *)
(*   lets: H0 H1 H4. clear H0. *)

(*   assert(ACtxTSubst (G & y ~ AC_Var) (t2 @@' AE_FVar y) = t2 @@' AE_FVar y). *)
(*   rewrite tsubst_add_var. *)
(*   rewrite~ actxtsubst_open. *)
(*   rewrite H3. rewrite actxsubst_fvar. auto. *)
(*   lets: H H0. clear H. *)

(*   rewrite tsubst_add_var in H0. *)
(*   rewrite~ actxtsubst_open in H0. *)
(*   rewrite actxsubst_fvar in H0. *)

(*   rewrite H0. *)
(*   rewrite~ actxtsubst_open. *)
(*   rewrite actxsubst_fvar. *)
(*   rewrite H0. auto. *)

(*   (* CASTUP *) *)
(*   apply AUnify_CastUp. *)
(*   apply~ IHwt. *)
(*   rewrite actxtsubst_expr in sub. rewrite actxsubst_castup in sub. inversion~ sub. *)
(*   rewrite actxtsubst_expr. f_equal. *)
(*   repeat rewrite~ H0. *)

(*   (* CASTDOWN *) *)
(*   apply AUnify_CastDn. *)
(*   apply~ IHwt. *)
(*   rewrite actxtsubst_expr in sub. rewrite actxsubst_castdn in sub. inversion~ sub. *)
(*   rewrite actxtsubst_expr. f_equal. *)
(*   repeat rewrite~ H0. *)

(*   (* ANN *) *)
(*   rewrite actxtsubst_expr in sub. rewrite actxsubst_ann in sub. inversion sub. *)
(*   apply AUnify_Ann with G; auto. *)
(*   rewrite H0. apply~ IHwt1. rewrite actxtsubst_expr. f_equal~. *)
(*   repeat rewrite H1. apply~ IHwt2. *)

(*   (* FORALL *) *)
(*   rewrite actxtsubst_expr in sub. rewrite actxsubst_forall in sub. inversion sub. clear sub. *)
(*   apply AUnify_Forall with (L \u dom G); auto. *)
(*   intros y notin. *)
(*   assert (y \notin L) by auto. *)
(*   assert (AWf (G & y ~ AC_Var)) by apply~ AWf_Var. *)
(*   lets: H H1. clear H. *)
(*   lets: H0 H1 H3. clear H0. *)

(*   assert(ACtxTSubst (G & y ~ AC_Var) (AT_Expr (e @@ AE_FVar y)) = *)
(*       AT_Expr (e @@ AE_FVar y)). *)
(*   rewrite tsubst_add_var. *)
(*   rewrite actxtsubst_expr. f_equal. *)
(*   rewrite~ actxsubst_open. *)
(*   rewrite H2. rewrite actxsubst_fvar. auto. *)
(*   lets: H H0. clear H. *)

(*   rewrite tsubst_add_var in H0. *)
(*   rewrite actxtsubst_expr in H0. *)
(*   inversion~ H0. clear H0. *)
(*   rewrite~ actxsubst_open in H6. *)
(*   rewrite actxsubst_fvar in H6. *)

(*   rewrite H6. auto. *)
