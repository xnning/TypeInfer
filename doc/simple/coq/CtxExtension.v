
Require Import DeclDef.
Require Import AlgoDef.
Require Import LibLN.

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

Lemma declaration_preservation : forall G I x v1,
    ExtCtx G I -> binds x v1 G -> exists v2, binds x v2 I.
Proof.
  intros* H0 H1. induction H0; auto;
  try(binds_cases H1; eauto; apply IHExtCtx in B; inversion B as (x1 & HG); exists* x1).
  exists* v1.
  apply IHExtCtx in H1; inversion H1 as (x1 & HG); exists* x1.
  assert (a <> x). unfold not; intros; subst; eapply binds_fresh_inv; eauto.
  apply* binds_push_neq.
  apply IHExtCtx in H1; inversion H1 as (x1 & HG); exists x1.
  assert (a <> x). unfold not; intros; subst; eapply binds_fresh_inv; eauto.
  apply* binds_push_neq.
Qed.

Lemma union_left :forall A (x:A) E F,
    x \in E ->
    x \in (E \u F).
Proof.
  intros* H.
  assert(subset E (E \u F)). apply subset_union_weak_l.
  apply* (H0 x).
Qed.

Lemma union_right :forall A (x:A) E F,
    x \in E ->
    x \in (F \u E).
Proof.
  intros* H.
  assert(subset E (F \u E)). apply subset_union_weak_r.
  apply* (H0 x).
Qed.

Lemma declaration_preservation_dom : forall G I x,
    ExtCtx G I -> x \in (dom G) -> x \in (dom I).
Proof.
  intros* HE HX. induction HE; auto;
  try(
  try(destruct (eq_var_dec x x0); subst);
  try(destruct (eq_var_dec x a); subst);
  try(simpl_dom; apply union_left; apply in_singleton_self);
  try(simpl_dom; apply union_right; apply* IHHE);
  try(rewrite in_union in HX; destruct HX as [HX1 | HX2];auto;
  rewrite in_singleton in HX1; subst; auto_star)).
Qed.

Lemma ok_context : forall G I,
    ExtCtx G I -> ok G.
Proof.
  intros* H. induction H; auto;
  try(apply ok_push; eauto;
  simpl_dom;
  unfold notin; unfold not; intros HV; apply (declaration_preservation_dom H0) in HV; apply* H1).
Qed.

Lemma ok_preservation : forall G I,
    ExtCtx G I -> ok I.
Proof.
  intros* H.
  assert (ok G). apply* ok_context.
  induction H; subst; auto_star.
Qed.

