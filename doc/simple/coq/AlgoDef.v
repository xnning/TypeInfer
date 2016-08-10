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
  | AE_Lam : AExpr -> AExpr
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
  | AE_Lam e     => AE_Lam   (AOpenRec (S k) u e)
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
Notation "e @@' u" := (AOpenT e u) (at level 67).
Notation "e @' x" := (AOpenT e (AE_FVar x)) (at level 67).

(** Closed Terms *)
Inductive ATerm : AExpr -> Prop :=
  | ATerm_Var : forall x, ATerm (AE_FVar x)
  | ATerm_EVar : forall x, ATerm (AE_EVar x)
  | ATerm_Star : ATerm AE_Star
  | ATerm_App : forall e1 e2,
      ATerm e1 -> ATerm e2 -> ATerm (AE_App e1 e2)
  | ATerm_Lam : forall L e,
      (forall x, x \notin L -> ATerm (e @ x)) ->
      ATerm (AE_Lam e)
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

Inductive ATermTy : AType -> Prop :=
  | ATermTy_Expr : forall e, ATerm e -> ATermTy (AT_Expr e)
  | ATermTy_Forall : forall L t,
      (forall x, x \notin L -> ATermTy (t @' x)) ->
      ATermTy (AT_Forall t).

Definition ABodyTy t :=
  exists L, forall x, x \notin L -> ATermTy (t @' x).

(** Substitution *)

Fixpoint ASubst (z : var) (u : AExpr) (e : AExpr) {struct e} : AExpr :=
  match e with
  | AE_BVar i    => AE_BVar i
  | AE_FVar x    => If x = z then u else (AE_FVar x)
  | AE_EVar x    => If x = z then u else (AE_EVar x)
  | AE_Star      => AE_Star
  | AE_App e1 e2 => AE_App    (ASubst z u e1) (ASubst z u e2)
  | AE_Lam e     => AE_Lam   (ASubst z u e)
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
  | AE_FVar x    => \{x}
  | AE_EVar x    => \{x}
  | AE_Star      => \{}
  | AE_App e1 e2 => (AFv e1) \u (AFv e2)
  | AE_Lam e     => AFv e
  | AE_Pi t1 t2  => (AFv t1) \u (AFv t2)
  | AE_Let e1 e2 => (AFv e1) \u (AFv e2)
  | AE_CastUp e  => AFv e
  | AE_CastDn e  => AFv e
  | AE_Ann e t   => (AFv e) \u (AFv t)
  end.

Fixpoint AEFv (e : AExpr) {struct e} : vars :=
  match e with
  | AE_BVar i    => \{}
  | AE_FVar x    => \{}
  | AE_EVar x    => \{x}
  | AE_Star      => \{}
  | AE_App e1 e2 => (AEFv e1) \u (AEFv e2)
  | AE_Lam e     => AEFv e
  | AE_Pi t1 t2  => (AEFv t1) \u (AEFv t2)
  | AE_Let e1 e2 => (AEFv e1) \u (AEFv e2)
  | AE_CastUp e  => AEFv e
  | AE_CastDn e  => AEFv e
  | AE_Ann e t   => (AEFv e) \u (AEFv t)
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

Definition ACtxTSubst (G : ACtx) (e : AType) : AType :=
  LibList.fold_left
    (fun (c : var * ACtxT) v => let (x, p) := c in
        match p with
        | AC_Var => v
        | AC_Typ _ => v
        | AC_Bnd s t => ATSubst x t v
        | AC_Unsolved_EVar => v
        | AC_Solved_EVar t => ATSubst x t v
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
  | AR_Beta : forall e1 e2,
      ATerm (AE_Lam e1) ->
      ATerm e2 ->
      ARed (AE_App (AE_Lam e1) e2) (e1 @@ e2)
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
      a \notin L ->
      AInst G (AT_Forall s) (t @@ (AE_EVar a)) (H & a ~ AC_Unsolved_EVar).

Inductive AWTerm : ACtx -> AExpr -> Prop :=
  | AWTerm_Var : forall G x, binds x AC_Var G -> AWTerm G (AE_FVar x)
  | AWTerm_TypVar : forall G x t, binds x (AC_Typ t) G -> AWTerm G (AE_FVar x)
  | AWTerm_LetVar : forall G x t e, binds x (AC_Bnd t e) G -> AWTerm G (AE_FVar x)
  | AWTerm_EVar : forall G a, binds a AC_Unsolved_EVar G -> AWTerm G (AE_EVar a)
  | AWTerm_Solved_EVar : forall G a t, binds a (AC_Solved_EVar t) G -> AWTerm G (AE_EVar a)
  | AWTerm_Star: forall G, AWTerm G AE_Star
  | AWTerm_App: forall e1 e2 G, AWTerm G e1 -> AWTerm G e2 -> AWTerm G (AE_App e1 e2)
  | AWTerm_Lam: forall e G L,
      (forall x, x \notin L -> AWTerm (G & x ~ AC_Var) (e @ x)) -> AWTerm G (AE_Lam e)
  | AWTerm_Pi: forall t1 t2 G L,
      AWTerm G t1 ->
      (forall x, x \notin L -> AWTerm (G & x ~ AC_Var) (t2 @ x)) -> AWTerm G (AE_Pi t1 t2)
  | AWTerm_Let: forall e1 e2 G L,
      AWTerm G e1 ->
      (forall x, x \notin L -> AWTerm (G & x ~ AC_Var) (e2 @ x)) -> AWTerm G (AE_Let e1 e2)
  | AWTerm_CastUp : forall e G, AWTerm G e -> AWTerm G (AE_CastUp e)
  | AWTerm_CastDn : forall e G, AWTerm G e -> AWTerm G (AE_CastDn e)
  | AWTerm_Ann: forall e1 e2 G, AWTerm G e1 -> AWTerm G e2 -> AWTerm G (AE_Ann e1 e2)
.

Inductive AWTermT : ACtx -> AType -> Prop :=
  | AWTermT_Forall : forall G s L,
      (forall x, x \notin L -> AWTermT (G & x ~ AC_Var) (s @' x)) -> AWTermT G (AT_Forall s)
  | AWTermT_Expr: forall G e,
      AWTerm G e -> AWTermT G (AT_Expr e).

Inductive AResolveEVar : ACtx -> var -> AExpr -> AExpr -> ACtx -> Prop :=
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
  | AResolveEVar_Lam : forall a t1 G, AResolveEVar G a (AE_Lam t1) (AE_Lam t1) G
  | AResolveEVar_Let : forall a t1 t2 G, AResolveEVar G a (AE_Let t1 t2) (AE_Let t1 t2) G
  | AResolveEVar_CastUp : forall a t G, AResolveEVar G a (AE_CastUp t) (AE_CastUp t) G
  | AResolveEVar_CastDn : forall a t G, AResolveEVar G a (AE_CastDn t) (AE_CastDn t) G
  | AResolveEVar_Ann : forall a t1 t2 G, AResolveEVar G a (AE_Ann t1 t2) (AE_Ann t1 t2) G
.

Inductive AUnify : ACtx -> AExpr -> AExpr -> ACtx -> Prop :=
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
  | AUnify_Lam : forall t1 t2 G H L,
      (forall x, x \notin L -> AUnify (G & x ~ AC_Var) (t1 @ x) (t2 @ x) (H & x ~ AC_Var)) ->
      AUnify G (AE_Lam t1) (AE_Lam t2) H
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
      AWTerm H1 t2 ->
      AUnify G (AE_EVar a) t1 (H1 & a ~ AC_Solved_EVar t2 & H2)
  | AUnify_TyEVar : forall a t1 t2 G H1 H2,
      a \notin (AFv (t1)) ->
      AResolveEVar G a t1 t2 (H1 & a ~ AC_Unsolved_EVar & H2) ->
      AWTerm H1 t2 ->
      AUnify G t1 (AE_EVar a) (H1 & a ~ AC_Solved_EVar t2 & H2).

Inductive AMode := Inf | Chk | App.

Inductive ATyping : AMode -> ACtx -> AExpr -> AExpr -> ACtx -> Prop :=
  | ATI_Ax : forall G H, AWf G H -> ATyping Inf G AE_Star AE_Star H
  | ATI_Var : forall G H x t, AWf G H -> binds x (AC_Typ t) G ->
                            ATyping Inf G (AE_FVar x) t H
  | ATI_LetVar : forall G H1 H x s t t2,
      AWf G H1 -> binds x (AC_Bnd s t) G ->
      AInst H1 s t2 H ->
      ATyping Inf G (AE_FVar x) t2 H
  | ATI_Ann : forall G H H1 e t,
      AWTerm G (AE_Ann e t) ->
      ATyping Chk G t AE_Star H1 ->
      ATyping Chk H1 e t H ->
      ATyping Inf G (AE_Ann e t) t H
  | ATI_Pi : forall G H1 H I t1 t2 x,
      AWTerm G (AE_Pi t1 t2) ->
      x # G ->
      ATyping Chk G t1 AE_Star H1 ->
      ATyping Chk (H1 & (x ~ AC_Typ t1)) (t2 @ x) AE_Star
                  (H & (x ~ AC_Typ t1) & I) ->
      ATyping Inf G (AE_Pi t1 t2) AE_Star H
  | ATI_Lam : forall G H I e a t2 x,
      AWTerm G (AE_Lam e) ->
      x # G ->
      a # G ->
      ATyping Inf (G & a ~ AC_Unsolved_EVar & x ~ AC_Typ (AE_EVar a))
                  (e @ x) (t2 @ x)
                  (H & x ~ AC_Typ (AE_EVar a) & I) ->
      ATyping Inf G (AE_Lam e) (AE_Pi (AE_EVar a) (ACtxSubst I t2)) (H & ACtxUV I)
  | ATI_App : forall G H1 H e1 e2 t1 t2,
      AWTerm G (AE_App e1 e2) ->
      ATyping Inf G e1 (AE_Pi t1 t2) H1 ->
      ATyping App H1 (AE_App (ACtxSubst H1 t1) e2) t2 H ->
      ATyping Inf G (AE_App e1 e2) t2 H
  | ATI_Let : forall G H1 H I e1 e2 s t1 t2 x,
      AWTerm G (AE_Let e1 e2) ->
      x # G -> x \notin AFv t2 ->
      ATyping Inf G e1 t1 H1 ->
      AGen H1 t1 s ->
      ATyping Inf (H1 & x ~ AC_Bnd s e1) (e2 @ x) (t2 @ x)
                  (H & x ~ AC_Bnd s e1 & I) ->
      ATyping Inf G (AE_Let e1 e2) (ACtxSubst I (t2 @@ e1)) (H & ACtxUV I)
  | ATI_CastDn : forall G H e t1 t2,
      AWTerm G (AE_CastDn e) ->
      ATyping Inf G e t1 H ->
      ARed (ACtxSubst H t1) t2 ->
      ATyping Inf G (AE_CastDn e) t2 H

  | ATC_Lam : forall G H I e t1 t2 x,
      AWTerm G (AE_Lam e) -> AWTerm G (AE_Pi t1 t2) ->
      x # G ->
      ATyping Chk (G & x ~ AC_Typ t1) (e @ x) (t2 @ x)
                  (H & x ~ AC_Typ t1 & I) ->
      ATyping Chk G (AE_Lam e) (AE_Pi t1 t2) H
  | ATC_Let : forall G H1 H I e1 e2 s t1 t2 x,
      AWTerm G (AE_Let e1 e2) -> AWTerm G t2 ->
      x # G -> x \notin AFv t2 ->
      ATyping Inf G e1 t1 H1 ->
      AGen H1 t1 s ->
      ATyping Chk (H1 & x ~ (AC_Bnd s e1)) (e2 @ x) (t2 @ x)
                  (H & x ~ AC_Bnd s e1 & I) ->
      ATyping Chk G (AE_Let e1 e2) (ACtxSubst I (t2 @@ e1)) (H & ACtxUV I)
  | ATC_CastUp : forall G H e t1 t2,
      AWTerm G (AE_CastUp e) -> AWTerm G t2 ->
      ARed (ACtxSubst G t2) t1 ->
      ATyping Chk G e t1 H ->
      ATyping Chk G (AE_CastUp e) t2 H
  | ATC_Sub : forall G H1 H e t1 t2,
      AWTerm G e -> AWTerm G t2 ->
      ATyping Inf G e t1 H1 ->
      AUnify H1 (ACtxSubst H1 t1) (ACtxSubst H1 t2) H ->
      ATyping Chk G e t2 H

  | ATA_Pi : forall G H e t1 t2 m H1,
      AWTerm G (AE_App (AE_Pi t1 t2) e) ->
      ATyping m G (AE_Pi t1 t2) AE_Star H1 ->
      ATyping Chk G e t1 H ->
      ATyping App G (AE_App (AE_Pi t1 t2) e) (t2 @@ e) H
  | ATA_EVar : forall G1 G2 H I a e a1 a2,
      AWTerm (G1 & a ~ AC_Unsolved_EVar & G2) (AE_App (AE_EVar a) e) ->
      AWf (G1 & a ~ AC_Unsolved_EVar & G2) I ->
      ATyping Chk (G1 & a2 ~ AC_Unsolved_EVar & a1 ~ AC_Unsolved_EVar &
                    a ~ AC_Solved_EVar (AE_Pi (AE_EVar a1) (AE_EVar a2)) & G2)
                  e (AE_EVar a1) H ->
      ATyping App (G1 & a ~ AC_Unsolved_EVar & G2) (AE_App (AE_EVar a) e) (AE_EVar a2) H

with AWfTyp : ACtx -> AType -> ACtx -> Prop :=
     | AWf_Unsolve_EVar : forall G x,
         binds x AC_Unsolved_EVar G -> AWfTyp G (AT_Expr (AE_EVar x)) G
     | AWf_Solved_EVar : forall G x s,
         binds x (AC_Solved_EVar s) G -> AWfTyp G (AT_Expr (AE_EVar x)) G
     | AWf_Pi : forall L G H1 H t1 t2,
         AWfTyp G (AT_Expr t1) H1 ->
         (forall x I, x \notin L -> AWfTyp (H1 & x ~ AC_Typ t1) (AT_Expr (t2 @ x)) (H & x ~ AC_Typ t1 & I)) ->
         AWfTyp G (AT_Expr (AE_Pi t1 t2)) H
     | AWf_Poly : forall L G H s,
         (forall x I, x \notin L -> AWfTyp (G & x ~ AC_Typ AE_Star) (AOpenT s (AE_FVar x)) (H & x ~ AC_Typ AE_Star & I)) ->
         AWfTyp G (AT_Forall s) H
     | AWf_Expr : forall G H t,
         ATyping Chk G t AE_Star H ->
         AWfTyp G (AT_Expr t) H

with AWf : ACtx -> ACtx -> Prop :=
     | AWf_Nil : AWf empty empty
     | AWf_Var : forall G H x,
         AWf G H -> x # G ->
         AWf (G & x ~ AC_Var) (H & x ~ AC_Var)
     | AWf_TyVar : forall G H H1 x t,
         AWTerm G t ->
         AWf G H1 -> x # G ->
         AWfTyp H1 (AT_Expr t) H ->
         AWf (G & x ~ AC_Typ t) (H & x ~ AC_Typ t)
     | AWf_LetVar : forall G H1 H2 H x s s2 t,
         AWTerm G s ->
         AWTerm G t ->
         AWf G H1 -> x # G -> AWfTyp H1 (AT_Expr s) H2 ->
         ACtxSubst H2 s = s2 ->
         ATyping Chk H2 t s2 H ->
         AWf (G & x ~ AC_Bnd (AT_Expr s) t) (H & x ~ AC_Bnd (AT_Expr s) t)
     | AWf_LetVar2 : forall L G H1 H2 H x s t,
         AWTermT G (AT_Forall s) ->
         AWTerm G t ->
         AWf G H1 -> x # G -> AWfTyp H1 s H2 ->
         (forall y I, y \notin L -> AWf (H2 & y ~ AC_Typ AE_Star & x ~ AC_Bnd (AOpenT (AT_Forall s) (AE_FVar y)) t) (H & y ~ AC_Typ AE_Star & I)) ->
         AWf (G & x ~ AC_Bnd (AT_Forall s) t) (H & x ~ AC_Bnd (AT_Forall s) t)
     | AWf_Ctx_Unsolved_EVar : forall G H x,
         AWf G H -> x # G ->
         AWf (G & x ~ AC_Unsolved_EVar) (H & x ~ AC_Unsolved_EVar)
     | AWf_Ctx_Solved_EVar : forall G H1 H x t,
         AWTerm G t ->
         AWf G H1 -> x # G ->
         AWfTyp H1 (AT_Expr t) H ->
         AWf (G & x ~ AC_Solved_EVar t) (H & x ~ AC_Solved_EVar t)
.

Definition ATypingI := ATyping Inf.
Definition ATypingC := ATyping Chk.
Definition ATypingApp := ATyping App.
