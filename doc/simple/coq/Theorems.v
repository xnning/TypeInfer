Require Import DeclDef.
Require Import AlgoDef.
Require Import CtxExtension.

(* Soundness *)

Theorem Soundness_Unification : forall G H I t1 t2 H' t1' t2',
    AUnify G t1 t2 H ->
    t1 = ACtxSubst G t1 ->
    t2 = ACtxSubst G t2 ->
    ExtCtx H I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I H H' ->
    ACpltCtxSubst I t1 t1' ->
    ACpltCtxSubst I t2 t2' ->
    (DWfTyp H' (DT_Expr t1') /\ DWfTyp H' (DT_Expr t2') /\ t1' = t2').

Theorem  Soundness_Instantiation : forall G H I s t H' s' t',
    AInst G s t H ->
    AWfTyp G s -> AWfTyp G (AT_Expr t) ->
    ExtCtx H I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I H H' ->
    ACpltCtxTSubst I s s' ->
    ACpltCtxSubst I t t' ->
    DInst H' s' t'.

Theorem Soundness_Generalization : forall G H I e s t H' e' s',
    ATypingI G e t H ->
    AGen H t s ->
    ExtCtx H I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I H H' ->
    ACpltCtxTSubst I s s' ->
    ACpltCtxSubst I e e' ->
    DGen H' e' s'.

Theorem Soundness_Typing : forall G H I e t H' e' t',
    ExtCtx H I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I H H' ->
    ACpltCtxSubst I t t' ->
    ACpltCtxSubst I e e' ->
    (ATypingI G e t H -> DTypingI H' e' t') /\ (ATypingC G e t H -> DTypingC H' e' t').

Theorem Soundness_TypingApp : forall G H1 H I e1 e2 t1 t2 H' e1' e2' t2',
    ExtCtx H I ->
    CompleteCtx I ->
    ATypingI G e1 t1 H1 ->
    ATypingApp H1 (ACtxSubst H1 t1) e2 t2 H ->
    ACpltCtxSubstCtx I H H' ->
    ACpltCtxSubst I e1 e1' ->
    ACpltCtxSubst I e2 e2' ->
    ACpltCtxSubst I t2 t2' ->
    DTypingI H' (DE_App e1' e2') t2'.
