(** ** Algorithmic System *)

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.

(** Syntax **)

Inductive AExpr : Set :=
  | AE_BVar : nat -> AExpr
  | AE_FVar : var -> AExpr
  | AE_EVar : var -> AExpr
  | AE_Star : AExpr
  | AE_App : AExpr -> AExpr -> AExpr
  | AE_ILam : AExpr -> AExpr
  | AE_Lam : AExpr -> AExpr -> AExpr
  | AE_Pi : AExpr -> AExpr -> AExpr
  | AE_Let : AExpr -> AExpr -> AExpr
  | AE_CastUp : AExpr -> AExpr
  | AE_CastDn : AExpr -> AExpr
  | AE_Ann : AExpr -> AExpr -> AExpr.

Inductive AType : Set :=
  | AT_Forall : AType -> AType
  | AT_Expr : AExpr -> AType.

(** Open Operation *)


Fixpoint AOpenRec (k : nat) (u : AExpr) (e : AExpr) {struct e} : AExpr :=
  match e with
  | AE_BVar i    => If k = i then u else (AE_BVar i)
  | AE_FVar x    => AE_FVar x
  | AE_EVar x    => AE_EVar x
  | AE_Star      => AE_Star
  | AE_App e1 e2 => AE_App    (AOpenRec k u e1) (AOpenRec k u e2)
  | AE_ILam e    => AE_ILam   (AOpenRec (S k) u e)
  | AE_Lam t e   => AE_Lam    (AOpenRec k u t) (AOpenRec (S k) u e)
  | AE_Pi t1 t2  => AE_Pi     (AOpenRec k u t1) (AOpenRec (S k) u t2)
  | AE_Let e1 e2 => AE_Let    (AOpenRec k u e1) (AOpenRec (S k) u e2)
  | AE_CastUp e  => AE_CastUp (AOpenRec k u e)
  | AE_CastDn e  => AE_CastDn (AOpenRec k u e)
  | AE_Ann e t   => AE_Ann    (AOpenRec k u e) (AOpenRec k u t)
  end.

Fixpoint AOpenTypRec (k : nat) (u : AExpr) (e : AType) {struct e} : AType :=
  match e with
  | AT_Forall s => AT_Forall (AOpenTypRec (S k) u s)
  | AT_Expr t   => AT_Expr (AOpenRec k u t)
  end.

Definition AOpen e u := AOpenRec 0 u e.
Definition AOpenT e u := AOpenTypRec 0 u e.

Notation "e @@ u" := (AOpen e u) (at level 67).
Notation "e @ x" := (AOpen e (AE_FVar x)) (at level 67).

(** Closed Terms *)
Inductive ATerm : AExpr -> Prop :=
  | ATerm_Var : forall x, ATerm (AE_FVar x)
  | ATerm_EVar : forall x, ATerm (AE_EVar x)
  | ATerm_Star : ATerm AE_Star
  | ATerm_App : forall e1 e2,
      ATerm e1 -> ATerm e2 -> ATerm (AE_App e1 e2)
  | ATerm_ILam : forall L e,
      (forall x, x \notin L -> ATerm (e @ x)) ->
      ATerm (AE_ILam e)
  | ATerm_Lam : forall L t e,
      ATerm t ->
      (forall x, x \notin L -> ATerm (e @ x)) ->
      ATerm (AE_Lam t e)
  | ATerm_Pi : forall L t1 t2,
      ATerm t1 ->
      (forall x, x \notin L -> ATerm (t2 @ x)) ->
      ATerm (AE_Pi t1 t2)
  | ATerm_Let : forall L e1 e2,
      ATerm e1 ->
      (forall x, x \notin L -> ATerm (e2 @ x)) ->
      ATerm (AE_Let e1 e2)
  | ATerm_CastUp : forall e,
      ATerm e -> ATerm (AE_CastUp e)
  | ATerm_CastDn : forall e,
      ATerm e -> ATerm (AE_CastDn e)
  | ATerm_Ann : forall t e,
      ATerm t -> ATerm e -> ATerm (AE_Ann t e).

Definition ABody t :=
  exists L, forall x, x \notin L -> ATerm (t @ x).

(** Substitution *)

Fixpoint ASubst (z : var) (u : AExpr) (e : AExpr) {struct e} : AExpr :=
  match e with
  | AE_BVar i    => AE_BVar i
  | AE_FVar x    => If x = z then u else (AE_FVar x)
  | AE_EVar x    => If x = z then u else (AE_EVar x)
  | AE_Star      => AE_Star
  | AE_App e1 e2 => AE_App    (ASubst z u e1) (ASubst z u e2)
  | AE_ILam e    => AE_ILam   (ASubst z u e)
  | AE_Lam t e   => AE_Lam    (ASubst z u t) (ASubst z u e)
  | AE_Pi t1 t2  => AE_Pi     (ASubst z u t1) (ASubst z u t2)
  | AE_Let e1 e2 => AE_Let    (ASubst z u e1) (ASubst z u e2)
  | AE_CastUp e  => AE_CastUp (ASubst z u e)
  | AE_CastDn e  => AE_CastDn (ASubst z u e)
  | AE_Ann e t   => AE_Ann    (ASubst z u e) (ASubst z u t)
  end.

Fixpoint ATSubst (z : var) (u : AExpr) (e : AType) {struct e} : AType :=
  match e with
  | AT_Forall s  => AT_Forall (ATSubst z u s)
  | AT_Expr t    => AT_Expr (ASubst z u t)
  end.

(** Free Varialble *)

Fixpoint AFv (e : AExpr) {struct e} : vars :=
  match e with
  | AE_BVar i    => \{}
  | AE_FVar x    => \{}
  | AE_EVar x    => \{x}
  | AE_Star      => \{}
  | AE_App e1 e2 => (AFv e1) \u (AFv e2)
  | AE_ILam e    => AFv e
  | AE_Lam t e   => (AFv t) \u (AFv e)
  | AE_Pi t1 t2  => (AFv t1) \u (AFv t2)
  | AE_Let e1 e2 => (AFv e1) \u (AFv e2)
  | AE_CastUp e  => AFv e
  | AE_CastDn e  => AFv e
  | AE_Ann e t   => (AFv e) \u (AFv t)
  end.

Fixpoint ATFv (e : AType) {struct e} : vars :=
  match e with
  | AT_Forall s => ATFv s
  | AT_Expr t   => AFv t
  end.

(** Context *)

Inductive ACtxT : Set :=
  | AC_Var : ACtxT
  | AC_Typ : AExpr -> ACtxT
  | AC_Bnd : AType -> AExpr -> ACtxT
  | AC_Unsolved_EVar : ACtxT
  | AC_Solved_EVar : AExpr -> ACtxT.

Definition ACtx := LibEnv.env ACtxT.

Fixpoint ACtxFv (G : ACtx) : vars :=
  match G with
  | nil => \{}
  | cons (x, p) t =>
    match p with
    | AC_Typ ty => (AFv ty) \u (ACtxFv t)
    | AC_Bnd s e => (ATFv s) \u (ACtxFv t)
    | _ => ACtxFv t
    end
  end.

Definition ACtxSubst (G : ACtx) (e : AExpr) : AExpr :=
  LibList.fold_left
    (fun (c : var * ACtxT) v => let (x, p) := c in
        match p with
        | AC_Var => v
        | AC_Typ _ => v
        | AC_Bnd s t => ASubst x t v
        | AC_Unsolved_EVar => v
        | AC_Solved_EVar t => ASubst x t v
        end) e G.

Fixpoint ACtxUV (G : ACtx) {struct G} : ACtx :=
  match G with
  | nil => nil
  | cons (x, p) t =>
    match p with
    | AC_Unsolved_EVar => ACtxUV t & x ~ AC_Unsolved_EVar
    | _ => ACtxUV t
    end
  end.

(** Reduction *)

Inductive ARed : AExpr -> AExpr -> Prop :=
  | AR_Beta : forall t e1 e2,
      ATerm (AE_Lam t e1) ->
      ATerm e2 ->
      ARed (AE_App (AE_Lam t e1) e2) (e1 @@ e2)
  | AR_BetaI : forall e1 e2,
      ATerm (AE_ILam e1) ->
      ATerm e2 ->
      ARed (AE_App (AE_ILam e1) e2) (e1 @@ e2)
  | AR_CastDnUp : forall e,
      ATerm e ->
      ARed (AE_CastDn (AE_CastUp e)) e
  | AR_App : forall e1 e1' e2,
      ATerm e2 -> ARed e1 e1' ->
      ARed (AE_App e1 e2) (AE_App e1' e2)
  | AR_CastDn : forall e e',
      ARed e e' -> ARed (AE_CastDn e) (AE_CastDn e')
  | AR_Ann : forall e t e',
      ATerm t -> ARed e e' ->
      ARed (AE_Ann e t) (AE_Ann e' t)
  | AR_Let : forall e1 e2,
      ATerm (AE_Let e1 e2) ->
      ARed (AE_Let e1 e2) (e2 @@ e1).

Inductive AGen : ACtx -> AExpr -> AType -> Prop :=
  | AGen_Expr : forall G t,
      ((AFv t) \- (ACtxFv G) = \{}) ->
      AGen G t (AT_Expr (ACtxSubst G t))
  | AGen_Poly : forall L G a t s,
      (a \in ((AFv t) \- (ACtxFv G))) ->
      (forall x, x \notin L -> x \notin (ATFv s) ->
                 AGen (G & x ~ AC_Typ AE_Star) (ASubst a (AE_FVar x) t) (AOpenT s (AE_FVar x))) ->
      AGen G t (AT_Forall (ATSubst a (AE_BVar 0) s)).

Inductive AInst : ACtx -> AType -> AExpr -> ACtx -> Prop :=
  | AInst_Expr : forall G t,
      AInst G (AT_Expr t) t G
  | AInst_Poly : forall L G H a s t,
      (forall x, x \notin L ->
                 AInst (G & x ~ AC_Typ AE_Star) (AOpenT (AT_Forall s) (AE_FVar x)) (t @ x) H) ->
      AWf (H & a ~ AC_Unsolved_EVar) ->
      AInst G (AT_Forall s) (t @@ (AE_EVar a)) (H & a ~ AC_Unsolved_EVar)
with

ATypingI : ACtx -> AExpr -> AExpr -> ACtx -> Prop :=
  | ATI_Ax : forall G, AWf G -> ATypingI G AE_Star AE_Star G
  | ATI_Var : forall G x t, AWf G -> binds x (AC_Typ t) G ->
                            ATypingI G (AE_FVar x) t G
  | ATI_LetVar : forall G H x s t t2,
      AWf G -> binds x (AC_Bnd s t) G ->
      AInst G s t2 H ->
      ATypingI G (AE_FVar x) t2 H
  | ATI_Ann : forall G H H1 e t,
      ATypingC G t AE_Star H1 ->
      ATypingC H1 e t H ->
      ATypingI G (AE_Ann e t) t H
  | ATI_Pi : forall L G H1 H I t1 t2,
      ATypingC G t1 AE_Star H1 ->
      (forall x, x \notin L ->
                 ATypingC (H1 & (x ~ AC_Typ t1)) (t2 @ x) AE_Star
                          (H & (x ~ AC_Typ t1) & I)) ->
      ATypingI G (AE_Pi t1 t2) AE_Star H
  | ATI_Lam : forall L G H I e a t2,
      (forall a x, a \notin L -> x \notin L ->
                   ATypingI (G & a ~ AC_Unsolved_EVar & x ~ AC_Typ (AE_EVar a))
                            (e @ x) (t2 @ x)
                            (H & x ~ AC_Typ (AE_EVar a) & I)) ->
      ATypingI G (AE_ILam e) (AE_Pi (AE_EVar a) (ACtxSubst I t2)) (H & ACtxUV I)
  | ATI_LamAnn : forall L G H1 H I e t1 t2,
      ATypingC G t1 AE_Star H1 ->
      (forall x, x \notin L ->
                 ATypingI (H1 & x ~ (AC_Typ t1)) (e @ x) (t2 @ x)
                          (H & x ~ AC_Typ t1 & I)) ->
      ATypingI G (AE_Lam t1 e) (AE_Pi t1 (ACtxSubst I t2)) (H & ACtxUV I)
  | ATI_App : forall G H1 H e1 e2 t1 t2,
      ATypingI G e1 (AE_Pi t1 t2) H1 ->
      ATypingApp H1 (ACtxSubst H1 t1) e2 t2 H ->
      ATypingI G (AE_App e1 e2) t2 H
  | ATI_Let : forall L G H1 H I e1 e2 s t1 t2,
      ATypingI G e1 t1 H1 ->
      AGen H1 t1 s ->
      (forall x, x \notin L ->
                 ATypingI (H1 & x ~ AC_Bnd s e1) (e2 @ x) (t2 @ x)
                          (H & x ~ AC_Bnd s e1 & I)) ->
      ATypingI G (AE_Let e1 e2) (ACtxSubst I (t2 @@ e1)) (H & ACtxUV I)
  | ATI_CastDn : forall G H e t1 t2,
      ATypingI G e t1 H ->
      ARed (ACtxSubst H t1) t2 ->
      ATypingI G (AE_CastDn e) t2 H

with ATypingC : ACtx -> AExpr -> AExpr -> ACtx -> Prop :=
  | ATC_Lam : forall L G H I e t1 t2,
      (forall x, x \notin L ->
                 ATypingC (G & x ~ AC_Typ t1) (e @ x) (t2 @ x)
                          (H & x ~ AC_Typ t1 & I)) ->
      ATypingC G (AE_ILam e) (AE_Pi t1 t2) H
  | ATC_LamAnn : forall L G H1 H2 H I e t1 t2 t3,
      ATypingC G t1 AE_Star H1 ->
      AUnify H1 (ACtxSubst H1 t1) (ACtxSubst H1 t3) H2 ->
      (forall x, x \notin L ->
                 ATypingC (H2 & x ~ (AC_Typ t1)) (e @ x) (t2 @ x)
                          (H & x ~ AC_Typ t1 & I)) ->
      ATypingC G (AE_Lam t1 e) (AE_Pi t3 t2) H
  | ATC_Let : forall L G H1 H I e1 e2 s t1 t2,
      ATypingI G e1 t1 H1 ->
      AGen H1 t1 s ->
      (forall x, x \notin L ->
                 ATypingC (H1 & x ~ (AC_Bnd s e1)) (e2 @ x) (t2 @ x)
                          (H & x ~ AC_Bnd s e1 & I)) ->
      ATypingC G (AE_Let e1 e2) (ACtxSubst I (t2 @@ e1)) (H & ACtxUV I)
  | ATC_CastUp : forall G H e t1 t2,
      ARed (ACtxSubst G t2) t1 ->
      ATypingC G e t1 H ->
      ATypingC G (AE_CastUp e) t2 H
  | ATC_Sub : forall G H1 H e t1 t2,
      ATypingI G e t1 H1 ->
      AUnify H1 (ACtxSubst H1 t1) (ACtxSubst H1 t2) H ->
      ATypingC G e t2 H

with ATypingApp : ACtx -> AExpr -> AExpr -> AExpr -> ACtx -> Prop :=
  | ATA_Pi : forall G H e t1 t2,
      ATypingC G e t1 H ->
      ATypingApp G (AE_Pi t1 t2) e (t2 @@ e) H
  | ATA_EVar : forall G1 G2 H a2 a1 a e,
      ATypingC (G1 & a2 ~ AC_Unsolved_EVar & a1 ~ AC_Unsolved_EVar &
                a ~ AC_Solved_EVar (AE_Pi (AE_EVar a1) (AE_EVar a2)) & G2)
               e (AE_EVar a1) H ->
      ATypingApp (G1 & a ~ AC_Unsolved_EVar & G2) (AE_EVar a) e (AE_EVar a2) H

with AWfTyp : ACtx -> AType -> Prop :=
     | AWf_Unsolve_EVar : forall G x,
         binds x AC_Unsolved_EVar G -> AWfTyp G (AT_Expr (AE_EVar x))
     | AWf_Solved_EVar : forall G x s,
         binds x (AC_Solved_EVar s) G -> AWfTyp G (AT_Expr (AE_EVar x))
     | AWf_Pi : forall L G t1 t2,
         AWfTyp G (AT_Expr t1) ->
         (forall x, x \notin L -> AWfTyp (G & (x ~ AC_Typ t1)) (AT_Expr (t2 @ x))) ->
         AWfTyp G (AT_Expr (AE_Pi t1 t2))
     | AWf_Poly : forall L G s,
         (forall x, x \notin L -> AWfTyp (G & (x ~ AC_Typ AE_Star)) (AOpenT s (AE_FVar x))) ->
         AWfTyp G (AT_Forall s)
     | AWf_Expr : forall G H t,
         ATypingC G t AE_Star H ->
         AWfTyp G (AT_Expr t)

with AWf : ACtx -> Prop :=
     | AWf_Nil : AWf empty
     | AWf_Var : forall G x,
         AWf G -> x # G ->
         AWf (G & x ~ AC_Var)
     | AWf_TyVar : forall G x t,
         AWf G -> x # G ->
         AWfTyp G (AT_Expr t) ->
         AWf (G & x ~ AC_Typ t)
     | AWf_LetVar : forall G H x s t,
         AWf G -> x # G -> AWfTyp G (AT_Expr s) ->
         ATypingC G t s H ->
         AWf (G & x ~ AC_Bnd (AT_Expr s) t)
     | AWf_LetVar2 : forall L G x s t,
         AWf G -> x # G -> AWfTyp G s ->
         (forall y, y \notin L -> AWf (G & y ~ AC_Typ AE_Star & x ~ AC_Bnd (AOpenT s (AE_FVar y)) t)) ->
         AWf (G & x ~ AC_Bnd (AT_Forall s) t)
     | AWf_Ctx_Unsolved_EVar : forall G x,
         AWf G -> x # G ->
         AWf (G & x ~ AC_Unsolved_EVar)
     | AWf_Ctx_Solved_EVar : forall G x t,
         AWf G -> x # G ->
         AWfTyp G (AT_Expr t) ->
         AWf (G & x ~ AC_Solved_EVar t)

with AUnify : ACtx -> AExpr -> AExpr -> ACtx -> Prop :=
  | AUnify_Var : forall x G, binds x AC_Var G -> AUnify G (AE_FVar x) (AE_FVar x) G
  | AUnify_Typed_Var : forall x G t, binds x (AC_Typ t) G -> AUnify G (AE_FVar x) (AE_FVar x) G
  | AUnify_Bnd_Var : forall x t s G, binds x (AC_Bnd s t) G -> AUnify G (AE_FVar x) (AE_FVar x) G
  | AUnify_EVar : forall a G, binds a AC_Unsolved_EVar G -> AUnify G (AE_EVar a) (AE_EVar a) G
  (* no case for solved evar since it is fully applied under context *)
  | AUnify_Star : forall G, AUnify G (AE_Star) (AE_Star) G
  | AUnify_App : forall t1 t2 t3 t4 G H1 H,
      AUnify G t1 t2 H1 ->
      AUnify H1 (ACtxSubst H1 t3) (ACtxSubst H1 t4) H ->
      AUnify G (AE_App t1 t3) (AE_App t2 t3) H
  | AUnify_Let : forall t1 t2 t3 t4 G H1 H L,
      AUnify G t1 t2 H1 ->
      (forall x, x \notin L -> AUnify (H1 & x ~ AC_Var) (ACtxSubst H1 (t3 @ x)) (ACtxSubst H1 (t4 @ x)) (H & x ~ AC_Var)) ->
      AUnify G (AE_Let t1 t3) (AE_Let t2 t4) H
  | AUnify_ILam : forall t1 t2 G H L,
      (forall x, x \notin L -> AUnify (G & x ~ AC_Var) (t1 @ x) (t2 @ x) (H & x ~ AC_Var)) ->
      AUnify G (AE_ILam t1) (AE_ILam t2) H
  | AUnify_Lam : forall t1 t2 t3 t4 G H1 H L,
      AUnify G t1 t3 H1 ->
      (forall x, x \notin L -> AUnify (H1 & x ~ AC_Typ t1) (ACtxSubst H1 (t2 @ x)) (ACtxSubst H1 (t4 @ x)) (H & x ~ AC_Typ t1)) ->
      AUnify G (AE_Lam t1 t2) (AE_Lam t3 t4) H
  | AUnify_CastUp : forall t1 t2 G H,
      AUnify G t1 t2 H ->
      AUnify G (AE_CastUp t1) (AE_CastUp t2) H
  | AUnify_CastDn : forall t1 t2 G H,
      AUnify G t1 t2 H ->
      AUnify G (AE_CastDn t1) (AE_CastDn t2) H
  | AUnify_Pi : forall t1 t2 t3 t4 G H1 H L,
      AUnify G t1 t3 H1 ->
      (forall x, x \notin L -> AUnify (H1 & x ~ AC_Typ t1) (ACtxSubst H1 (t2 @ x)) (ACtxSubst H1 (t4 @ x)) (H & x ~ AC_Typ t1)) ->
      AUnify G (AE_Pi t1 t2) (AE_Pi t3 t4) H
  | AUnify_Ann : forall t1 t2 t3 t4 G H1 H,
      AUnify G t1 t2 H1 ->
      AUnify H1 (ACtxSubst H1 t3) (ACtxSubst H1 t4) H ->
      AUnify G (AE_Ann t1 t3) (AE_Ann t2 t3) H
  | AUnify_EVarTy : forall a t1 t2 G H1 H2,
      a \notin (AFv (t1)) ->
      AResolveEVar G a t1 t2 (H1 & a ~ AC_Unsolved_EVar & H2) ->
      AWfTyp H1 (AT_Expr t2) ->
      AUnify G (AE_EVar a) t1 (H1 & a ~ AC_Solved_EVar t2 & H2)
  | AUnify_TyEVar : forall a t1 t2 G H1 H2,
      a \notin (AFv (t1)) ->
      AResolveEVar G a t1 t2 (H1 & a ~ AC_Unsolved_EVar & H2) ->
      AWfTyp H1 (AT_Expr t2) ->
      AUnify G t1 (AE_EVar a) (H1 & a ~ AC_Solved_EVar t2 & H2)

with

AResolveEVar : ACtx -> var -> AExpr -> AExpr -> ACtx -> Prop :=
  | AResolveEVar_EVar_Before : forall a b G1 G2 G3,
      AResolveEVar (G1 & b ~ AC_Unsolved_EVar & G2 & a ~ AC_Unsolved_EVar & G3) a (AE_EVar b) (AE_EVar b)
                   (G1 & b ~ AC_Unsolved_EVar & G2 & a ~ AC_Unsolved_EVar & G3)
  | AResolveEVar_EVar_After : forall a b G1 G2 G3 a1,
      AResolveEVar (G1 & a ~ AC_Unsolved_EVar & G2 & b ~ AC_Unsolved_EVar & G3) a (AE_EVar b) (AE_EVar a1)
                   (G1 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & G2 & b ~ AC_Solved_EVar (AE_EVar a1) & G3)
  | AResolveEVar_Pi : forall a t1 t2 t3 t4 G H1 H L,
      AResolveEVar G a t1 t3 H1 ->
      (forall x, x \notin L -> AResolveEVar H1 a (ACtxSubst H1 (t2 @ x)) (ACtxSubst H1 (t4 @ x)) H) ->
      AResolveEVar G a (AE_Pi t1 t2) (AE_Pi t3 t4) H
  | AResolveEVar_Var : forall a x G, AResolveEVar G a (AE_FVar x) (AE_FVar x) G
  | AResolveEVar_Star : forall a G, AResolveEVar G a AE_Star AE_Star G
  | AResolveEVar_App : forall a t1 t2 G, AResolveEVar G a (AE_App t1 t2) (AE_App t1 t2) G
  | AResolveEVar_ILam : forall a t1 G, AResolveEVar G a (AE_ILam t1) (AE_ILam t1) G
  | AResolveEVar_Lam: forall a t1 t2 G, AResolveEVar G a (AE_Lam t1 t2) (AE_Lam t1 t2) G
  | AResolveEVar_Let : forall a t1 t2 G, AResolveEVar G a (AE_Let t1 t2) (AE_Let t1 t2) G
  | AResolveEVar_CastUp : forall a t G, AResolveEVar G a (AE_CastUp t) (AE_CastUp t) G
  | AResolveEVar_CastDn : forall a t G, AResolveEVar G a (AE_CastDn t) (AE_CastDn t) G
  | AResolveEVar_Ann : forall a t1 t2 G, AResolveEVar G a (AE_Ann t1 t2) (AE_Ann t1 t2) G
.
