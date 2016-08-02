Require Import DeclDef.
Require Import AlgoDef.
Require Import CtxExtension.

(* Soundness *)

Definition Soundness_Unification := forall G H I t1 t2 H' t1' t2',
    AUnify G t1 t2 H ->
    t1 = ACtxSubst G t1 ->
    t2 = ACtxSubst G t2 ->
    ExtCtx H I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I H H' ->
    ACpltCtxSubst I t1 t1' ->
    ACpltCtxSubst I t2 t2' ->
    (DWfTyp H' (DT_Expr t1') /\ DWfTyp H' (DT_Expr t2') /\ t1' = t2').

Definition  Soundness_Instantiation := forall G H I s t H' s' t',
    AInst G s t H ->
    AWfTyp G s -> AWfTyp G (AT_Expr t) ->
    ExtCtx H I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I H H' ->
    ACpltCtxTSubst I s s' ->
    ACpltCtxSubst I t t' ->
    DInst H' s' t'.

Definition Soundness_Generalization := forall G H I e s t H' e' s',
    ATypingI G e t H ->
    AGen H t s ->
    ExtCtx H I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I H H' ->
    ACpltCtxTSubst I s s' ->
    ACpltCtxSubst I e e' ->
    DGen H' e' s'.

Definition Soundness_Typing := forall G H I e t H' e' t',
    ExtCtx H I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I H H' ->
    ACpltCtxSubst I t t' ->
    ACpltCtxSubst I e e' ->
    (ATypingI G e t H -> DTypingI H' e' t') /\ (ATypingC G e t H -> DTypingC H' e' t').

Definition Soundness_TypingApp := forall G H1 H I e1 e2 t1 t2 H' e1' e2' t2',
    ExtCtx H I ->
    CompleteCtx I ->
    ATypingI G e1 t1 H1 ->
    ATypingApp H1 (AE_App (ACtxSubst H1 t1) e2) t2 H ->
    ACpltCtxSubstCtx I H H' ->
    ACpltCtxSubst I e1 e1' ->
    ACpltCtxSubst I e2 e2' ->
    ACpltCtxSubst I t2 t2' ->
    DTypingI H' (DE_App e1' e2') t2'.

(* Completeness *)

Definition Completeness_Unification := forall G I t1 t2 t1' t2',
    ExtCtx G I ->
    CompleteCtx I ->
    AWfTyp G (AT_Expr t1) ->
    AWfTyp G (AT_Expr t2) ->
    ACpltCtxSubst I t1 t1' ->
    ACpltCtxSubst I t2 t2' ->
    t1' = t2' ->
    (exists H I', CompleteCtx I' /\ ExtCtx H I' /\ ExtCtx I I' /\ AUnify G (ACtxSubst G t1) (ACtxSubst G t2) H).

Definition Completeness_Instantiation := forall G G' I s t s' t',
    ExtCtx G I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I G G' ->
    ACpltCtxTSubst I s s' ->
    ACpltCtxSubst I t t' ->
    DInst G' s' t' ->
    (exists H I', CompleteCtx I' /\ ExtCtx H I' /\ ExtCtx I I' /\ AInst G (ACtxTSubst G s) (ACtxSubst G t) H).

Definition Completeness_Generalization := forall G G' I e e' s s',
    ExtCtx G I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I G G' ->
    ACpltCtxSubst I e e' ->
    ACpltCtxTSubst I s s' ->
    DGen G' e' s' ->
    (exists H I' t, CompleteCtx I' /\ ExtCtx H I' /\ ExtCtx I I' /\ ATypingI G e t H /\ AGen H t s).

Definition Completeness_TypingC := forall G G' I e e' t t',
    ExtCtx G I ->
    CompleteCtx I ->
    AWfTyp G (AT_Expr t) ->
    ACpltCtxSubstCtx I G G' ->
    ACpltCtxSubst I t t' ->
    ACpltCtxSubst I e e' ->
    DTypingC G' e' t' ->
    (exists H I', CompleteCtx I' /\ ExtCtx H I' /\ ExtCtx I I' /\ ATypingC G e (ACtxSubst G t) H).

Definition Completeness_TypingI := forall G G' I e e' t,
    ExtCtx G I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I G G' ->
    ACpltCtxSubst I e e' ->
    DTypingI G' e' t ->
    (exists H I' t', CompleteCtx I' /\ ExtCtx H I' /\ ExtCtx I I' /\ ATypingI G e t' H /\ ACpltCtxSubst I' t' t).

Definition Completeness_TypingApp := forall G G' I e1 e1' e2 e2' t1,
    ExtCtx G I ->
    CompleteCtx I ->
    ACpltCtxSubstCtx I G G' ->
    ACpltCtxSubst I e1 e1' ->
    ACpltCtxSubst I e2 e2' ->
    DTypingI G' (DE_App e1' e2') t1 ->
    (exists H H1 H1' I' t1' t2 t2', ACpltCtxSubstCtx I' H1 H1' -> ACpltCtxSubst I' t2 t2' ->
        CompleteCtx I' /\ ExtCtx H I' /\ ExtCtx I I' /\ DTypingI H1' e1' t2' /\ ATypingI G e1 t2 H1 /\ ATypingApp H1 (AE_App (ACtxSubst H1 t2) e2) t1' H /\ ACpltCtxSubst I' t1' t1).
