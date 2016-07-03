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

Notation "e ^^ u" := (AOpen e u) (at level 67).
Notation "e ^ x" := (AOpen e (AE_FVar x)).

(** Closed Terms *)
Inductive ATerm : AExpr -> Prop :=
  | ATerm_Var : forall x, ATerm (AE_FVar x)
  | ATerm_EVar : forall x, ATerm (AE_EVar x)
  | ATerm_Star : ATerm AE_Star
  | ATerm_App : forall e1 e2,
      ATerm e1 -> ATerm e2 -> ATerm (AE_App e1 e2)
  | ATerm_ILam : forall L e,
      (forall x, x \notin L -> ATerm (e ^ x)) ->
      ATerm (AE_ILam e)
  | ATerm_Lam : forall L t e,
      ATerm t ->
      (forall x, x \notin L -> ATerm (e ^ x)) ->
      ATerm (AE_Lam t e)
  | ATerm_Pi : forall L t1 t2,
      ATerm t1 ->
      (forall x, x \notin L -> ATerm (t2 ^ x)) ->
      ATerm (AE_Pi t1 t2)
  | ATerm_Let : forall L e1 e2,
      ATerm e1 ->
      (forall x, x \notin L -> ATerm (e2 ^ x)) ->
      ATerm (AE_Let e1 e2)
  | ATerm_CastUp : forall e,
      ATerm e -> ATerm (AE_CastUp e)
  | ATerm_CastDn : forall e,
      ATerm e -> ATerm (AE_CastDn e)
  | ATerm_Ann : forall t e,
      ATerm t -> ATerm e -> ATerm (AE_Ann t e).

Definition ABody t :=
  exists L, forall x, x \notin L -> ATerm (t ^ x).

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

(** Free Varialble *)

Fixpoint AFv (e : AExpr) {struct e} : vars :=
  match e with
  | AE_BVar i    => \{}
  | AE_FVar x    => \{x}
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

(** Context *)

Inductive ACtxT : Set :=
  | AC_Var : ACtxT
  | AC_Typ : AExpr -> ACtxT
  | AC_Bnd : AType -> AExpr -> ACtxT
  | AC_Unsolved_EVar : ACtxT
  | AC_Solved_EVar : AExpr -> ACtxT.

Definition ACtx := LibEnv.env ACtxT.

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

(** Reduction *)

Inductive ARed : AExpr -> AExpr -> Prop :=
  | AR_Beta : forall t e1 e2,
      ATerm (AE_Lam t e1) ->
      ATerm e2 ->
      ARed (AE_App (AE_Lam t e1) e2) (e1 ^^ e2)
  | AR_BetaI : forall e1 e2,
      ATerm (AE_ILam e1) ->
      ATerm e2 ->
      ARed (AE_App (AE_ILam e1) e2) (e1 ^^ e2)
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
      ARed (AE_Let e1 e2) (e2 ^^ e1).

Inductive ATypingI : ACtx -> AExpr -> AExpr -> Prop :=

with ATypingC : ACtx -> AExpr -> AExpr -> Prop :=

with AWfTyp : ACtx -> AType -> Prop :=
     | AWf_Unsolve_EVar : forall G x,
         binds x AC_Unsolved_EVar G -> AWfTyp G (AT_Expr (AE_EVar x))
     | AWf_Solved_EVar : forall G x s,
         binds x (AC_Solved_EVar s) G -> AWfTyp G (AT_Expr (AE_EVar x))
     | AWf_Pi : forall L G t1 t2,
         AWfTyp G (AT_Expr t1) ->
         (forall x, x \notin L -> AWfTyp (G & (x~AC_Typ t1)) (AT_Expr (t2 ^ x))) ->
         AWfTyp G (AT_Expr (AE_Pi t1 t2))
     | AWf_Poly : forall L G s,
         (forall x, x \notin L -> AWfTyp (G & (x ~ AC_Typ AE_Star)) (AOpenT s (AE_FVar x))) ->
         AWfTyp G (AT_Forall s)
     | AWf_Expr : forall G t,
         ATypingC G t AE_Star ->
         AWfTyp G (AT_Expr t)

with AWf : ACtx -> Prop :=
     | AWf_Nil : AWf empty
     | AWf_Var : forall G x,
         AWf G -> x # G ->
         AWf (G & x ~ AC_Var)
     | AWf_TyVar : forall G x t,
         AWf G -> x # G ->
         ATypingC G t AE_Star ->
         AWf (G & x ~ AC_Typ t)
     | AWf_LetVar : forall G x s t,
         AWf G -> x # G -> AWfTyp G (AT_Expr s) ->
         ATypingC G t s ->
         AWf (G & x ~ AC_Bnd (AT_Expr s) t)
     | AWf_LetVar2 : forall L G x s t,
         AWf G -> x # G -> AWfTyp G s ->
         (forall x, x \notin L -> AWf (G & x ~ AC_Bnd (AOpenT s (AE_FVar x)) t)) ->
         AWf (G & x ~ AC_Bnd (AT_Forall s) t)
     | AWf_Ctx_Unsolved_EVar : forall G x,
         AWf G -> x # G ->
         AWf (G & x ~ AC_Unsolved_EVar)
     | AWf_Ctx_Solved_EVar : forall G x t,
         AWf G -> x # G ->
         ATypingC G t AE_Star ->
         AWf (G & x ~ AC_Solved_EVar t).
