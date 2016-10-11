(** ** Algorithmic System *)

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.

(** Syntax **)

Inductive AExpr : Set :=
  | AE_BVar : nat -> AExpr
  | AE_FVar : var -> AExpr
  | AE_Star : AExpr
  | AE_App : AExpr -> AExpr -> AExpr
  | AE_Lam : AExpr -> AExpr
  | AE_Pi : AType -> AType -> AExpr
  | AE_CastUp : AExpr -> AExpr
  | AE_CastDn : AExpr -> AExpr
  | AE_Ann : AExpr -> AType -> AExpr
  | AE_Forall: AType -> AExpr
with
AType : Set :=
  | AT_TBVar : nat -> AType
  | AT_TFVar : var -> AType
  | AT_EVar : var -> AType
  | AT_Expr : AExpr -> AType.

(** Open Operation *)

Fixpoint AOpenRec (k : nat) (u : AExpr) (e : AExpr) {struct e} : AExpr :=
  match e with
  | AE_BVar i    => If k = i then u else (AE_BVar i)
  | AE_FVar x    => AE_FVar x
  | AE_Star      => AE_Star
  | AE_App e1 e2 => AE_App    (AOpenRec k u e1) (AOpenRec k u e2)
  | AE_Lam e     => AE_Lam   (AOpenRec (S k) u e)
  | AE_Pi t1 t2  => AE_Pi     (AOpenTypRec k u t1) (AOpenTypRec (S k) u t2)
  | AE_CastUp e  => AE_CastUp (AOpenRec k u e)
  | AE_CastDn e  => AE_CastDn (AOpenRec k u e)
  | AE_Ann e t   => AE_Ann    (AOpenRec k u e) (AOpenTypRec k u t)
  | AE_Forall s  => AE_Forall (AOpenTypRec (S k) u s)
  end
with
AOpenTypRec (k : nat) (u : AExpr) (e : AType) {struct e} : AType :=
  match e with
  | AT_TBVar i   => AT_TBVar i
  | AT_TFVar i   => AT_TFVar i
  | AT_Expr t    => AT_Expr (AOpenRec k u t)
  | AT_EVar i    => AT_EVar i
  end.

Fixpoint ATOpenRec (k : nat) (u : AType) (e : AExpr) {struct e} : AExpr :=
  match e with
  | AE_BVar i    => AE_BVar i
  | AE_FVar x    => AE_FVar x
  | AE_Star      => AE_Star
  | AE_App e1 e2 => AE_App    (ATOpenRec k u e1) (ATOpenRec k u e2)
  | AE_Lam e     => AE_Lam   (ATOpenRec (S k) u e)
  | AE_Pi t1 t2  => AE_Pi     (ATOpenTypRec k u t1) (ATOpenTypRec (S k) u t2)
  | AE_CastUp e  => AE_CastUp (ATOpenRec k u e)
  | AE_CastDn e  => AE_CastDn (ATOpenRec k u e)
  | AE_Ann e t   => AE_Ann    (ATOpenRec k u e) (ATOpenTypRec k u t)
  | AE_Forall s  => AE_Forall (ATOpenTypRec (S k) u s)
  end
with
ATOpenTypRec (k : nat) (u : AType) (e : AType) {struct e} : AType :=
  match e with
  | AT_TBVar i   => If i = k then u else (AT_TBVar i)
  | AT_TFVar i   => AT_TFVar i
  | AT_Expr t    => AT_Expr (ATOpenRec k u t)
  | AT_EVar i    => AT_EVar i
  end.

Definition AOpen e u := AOpenRec 0 u e.
Definition AOpenT e u := AOpenTypRec 0 u e.
Definition ATOpen e u := ATOpenRec 0 u e.
Definition ATOpenT e u := ATOpenTypRec 0 u e.

Notation "e @ x" := (AOpen e (AE_FVar x)) (at level 67).
Notation "e @@ u" := (AOpen e u) (at level 67).
Notation "e @# x" := (ATOpen e (AT_TFVar x)) (at level 67).
Notation "e @@# u" := (ATOpen e u) (at level 67).
Notation "e @' x" := (AOpenT e (AE_FVar x)) (at level 67).
Notation "e @@' u" := (AOpenT e u) (at level 67).
Notation "e @#' x" := (ATOpenT e (AT_TFVar x)) (at level 67).
Notation "e @@#' u" := (ATOpenT e u) (at level 67).

(** Closed Terms *)
Inductive ATerm : AExpr -> Prop :=
  | ATerm_Var : forall x, ATerm (AE_FVar x)
  | ATerm_Star : ATerm AE_Star
  | ATerm_App : forall e1 e2,
      ATerm e1 -> ATerm e2 -> ATerm (AE_App e1 e2)
  | ATerm_Lam : forall L e,
      (forall x, x \notin L -> ATerm (e @ x)) ->
      ATerm (AE_Lam e)
  | ATerm_Pi : forall L t1 t2,
      ATermTy t1 ->
      (forall x, x \notin L -> ATermTy (t2 @' x)) ->
      ATerm (AE_Pi t1 t2)
  | ATerm_CastUp : forall e,
      ATerm e -> ATerm (AE_CastUp e)
  | ATerm_CastDn : forall e,
      ATerm e -> ATerm (AE_CastDn e)
  | ATerm_Ann : forall t e,
      ATerm t -> ATermTy e -> ATerm (AE_Ann t e)
  | ATerm_Forall : forall L t,
      (forall x, x \notin L -> ATermTy (t @#' x))->
      ATerm (AE_Forall t)
with
ATermTy : AType -> Prop :=
  | ATermTy_TFVar : forall i, ATermTy (AT_TFVar i)
  | ATermTy_EVar : forall x, ATermTy (AT_EVar x)
  | ATermTy_Expr : forall e, ATerm e -> ATermTy (AT_Expr e)
.

Inductive AMono : AExpr -> Prop :=
| DM_FVar : forall x, AMono (AE_FVar x)
| DM_Star: AMono (AE_Star)
| DM_App: forall e1 e2, AMono e1 -> AMono e2 -> AMono (AE_App e1 e2)
| DM_Lam: forall L e, (forall x, x \notin L -> AMono (e @ x)) -> AMono (AE_Lam e)
| DM_Pi: forall L s1 s2, ATMono s1 -> (forall x, x \notin L -> ATMono (s2 @' x)) -> AMono (AE_Pi s1 s2)
| DM_CastUp: forall e, AMono e -> AMono (AE_CastUp e)
| DM_CastDn: forall e, AMono e -> AMono (AE_CastDn e)
| DM_Ann: forall e s, AMono e -> ATMono s -> AMono (AE_Ann e s)

with
ATMono: AType -> Prop :=
| DM_TFVar : forall x, ATMono (AT_TFVar x)
| DM_EVar : forall x, ATMono (AT_EVar x)
| DM_Expr : forall e, AMono e -> ATMono (AT_Expr e).

Definition ABody t :=
  exists L, forall x, x \notin L -> ATerm (t @ x).

Definition ABodyTy t :=
  exists L, forall x, x \notin L -> ATermTy (t @' x).

Definition ATBody t :=
  exists L, forall x, x \notin L -> ATerm (t @# x).

Definition ATBodyTy t :=
  exists L, forall x, x \notin L -> ATermTy (t @#' x).

(** Substitution *)

Fixpoint ASubst (z : var) (u : AExpr) (e : AExpr) {struct e} : AExpr :=
  match e with
  | AE_BVar i    => AE_BVar i
  | AE_FVar x    => If x = z then u else (AE_FVar x)
  | AE_Star      => AE_Star
  | AE_App e1 e2 => AE_App    (ASubst z u e1) (ASubst z u e2)
  | AE_Lam e     => AE_Lam    (ASubst z u e)
  | AE_Pi t1 t2  => AE_Pi     (ATSubst z u t1) (ATSubst z u t2)
  | AE_CastUp e  => AE_CastUp (ASubst z u e)
  | AE_CastDn e  => AE_CastDn (ASubst z u e)
  | AE_Ann e t   => AE_Ann    (ASubst z u e) (ATSubst z u t)
  | AE_Forall s  => AE_Forall (ATSubst z u s)
  end
with
ATSubst (z : var) (u : AExpr) (e : AType) {struct e} : AType :=
  match e with
  | AT_Expr t    => AT_Expr (ASubst z u t)
  | AT_TBVar x   => AT_TBVar x
  | AT_TFVar x   => AT_TFVar x
  | AT_EVar x    => AT_EVar x
  end.

Fixpoint ASubstT (z : var) (u : AType) (e : AExpr) {struct e} : AExpr :=
  match e with
  | AE_BVar i    => AE_BVar i
  | AE_FVar x    => AE_FVar x
  | AE_Star      => AE_Star
  | AE_App e1 e2 => AE_App    (ASubstT z u e1) (ASubstT z u e2)
  | AE_Lam e     => AE_Lam    (ASubstT z u e)
  | AE_Pi t1 t2  => AE_Pi     (ATSubstT z u t1) (ATSubstT z u t2)
  | AE_CastUp e  => AE_CastUp (ASubstT z u e)
  | AE_CastDn e  => AE_CastDn (ASubstT z u e)
  | AE_Ann e t   => AE_Ann    (ASubstT z u e) (ATSubstT z u t)
  | AE_Forall s  => AE_Forall (ATSubstT z u s)
  end
with
ATSubstT (z : var) (u : AType) (e : AType) {struct e} : AType :=
  match e with
  | AT_TBVar i   => AT_TBVar i
  | AT_TFVar i   => If i = z then u else (AT_TFVar i)
  | AT_EVar i    => If i = z then u else (AT_EVar i)
  | AT_Expr t    => AT_Expr (ASubstT z u t)
  end.

(** Free Varialble *)

Fixpoint AFv (e : AExpr) {struct e} : vars :=
  match e with
  | AE_BVar i    => \{}
  | AE_FVar x    => \{x}
  | AE_Star      => \{}
  | AE_App e1 e2 => (AFv e1) \u (AFv e2)
  | AE_Lam e     => AFv e
  | AE_Pi t1 t2  => (ATFv t1) \u (ATFv t2)
  | AE_CastUp e  => AFv e
  | AE_CastDn e  => AFv e
  | AE_Ann e t   => (AFv e) \u (ATFv t)
  | AE_Forall  t => ATFv t
  end
with
ATFv (e : AType) {struct e} : vars :=
  match e with
  | AT_TBVar x   => \{}
  | AT_TFVar x   => \{x}
  | AT_EVar x    => \{x}
  | AT_Expr e    => AFv e
  end
  .

Fixpoint AFev (e : AExpr) {struct e} : vars :=
  match e with
  | AE_BVar i    => \{}
  | AE_FVar x    => \{x}
  | AE_Star      => \{}
  | AE_App e1 e2 => (AFev e1) \u (AFev e2)
  | AE_Lam e     => AFev e
  | AE_Pi t1 t2  => (ATFev t1) \u (ATFev t2)
  | AE_CastUp e  => AFev e
  | AE_CastDn e  => AFev e
  | AE_Ann e t   => (AFev e) \u (ATFev t)
  | AE_Forall  t => ATFev t
  end
with
ATFev (e : AType) {struct e} : vars :=
  match e with
  | AT_TBVar x   => \{}
  | AT_TFVar x   => \{}
  | AT_EVar x    => \{}
  | AT_Expr e    => AFev e
  end
  .

Fixpoint AFtv (e : AExpr) {struct e} : vars :=
  match e with
  | AE_BVar i    => \{}
  | AE_FVar x    => \{}
  | AE_Star      => \{}
  | AE_App e1 e2 => (AFtv e1) \u (AFtv e2)
  | AE_Lam e     => AFtv e
  | AE_Pi t1 t2  => (ATFtv t1) \u (ATFtv t2)
  | AE_CastUp e  => AFtv e
  | AE_CastDn e  => AFtv e
  | AE_Ann e t   => (AFtv e) \u (ATFtv t)
  | AE_Forall  t => ATFtv t
  end
with
ATFtv (e : AType) {struct e} : vars :=
  match e with
  | AT_TBVar x   => \{}
  | AT_TFVar x   => \{x}
  | AT_EVar x    => \{x}
  | AT_Expr e    => AFtv e
  end
  .

(** Context *)

Inductive ACtxT : Set :=
  | AC_Var : ACtxT
  | AC_Typ : AType -> ACtxT
  | AC_TVar : ACtxT
  | AC_Unsolved_EVar : ACtxT
  | AC_Solved_EVar : AType -> ACtxT.

Definition ACtx := LibEnv.env ACtxT.

Definition ACtxSubst (G : ACtx) (e : AExpr) : AExpr :=
  LibList.fold_left
    (fun (c : var * ACtxT) v => let (x, p) := c in
        match p with
        | AC_Var => v
        | AC_Typ _ => v
        | AC_TVar => v
        | AC_Unsolved_EVar => v
        | AC_Solved_EVar t => ASubstT x t v
        end) e G.

Definition ACtxTSubst (G : ACtx) (e : AType) : AType :=
  LibList.fold_left
    (fun (c : var * ACtxT) v => let (x, p) := c in
        match p with
        | AC_Var => v
        | AC_Typ _ => v
        | AC_TVar => v
        | AC_Unsolved_EVar => v
        | AC_Solved_EVar t => ATSubstT x t v
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
      ATermTy t -> ARed e e' ->
      ARed (AE_Ann e t) (AE_Ann e' t)
.

Inductive AWTermT : ACtx -> AType -> Prop :=
  | AWTermT_Var : forall G x, binds x AC_Var G -> AWTermT G (AT_Expr (AE_FVar x))
  | AWTermT_TypVar : forall G x t, binds x (AC_Typ t) G -> AWTermT G (AT_Expr (AE_FVar x))
  | AWTermT_Star: forall G, AWTermT G (AT_Expr AE_Star)
  | AWTermT_App: forall e1 e2 G, AWTermT G (AT_Expr e1) -> AWTermT G (AT_Expr e2) -> AWTermT G (AT_Expr (AE_App e1 e2))
  | AWTermT_Lam: forall e G L,
      (forall x, x \notin L -> AWTermT (G & x ~ AC_Var) (AT_Expr (e @ x))) -> AWTermT G (AT_Expr (AE_Lam e))
  | AWTermT_Pi: forall t1 t2 G L,
      AWTermT G t1 ->
      (forall x, x \notin L -> AWTermT (G & x ~ AC_Var) (t2 @' x)) -> AWTermT G (AT_Expr (AE_Pi t1 t2))
  | AWTermT_CastUp : forall e G, AWTermT G (AT_Expr e) -> AWTermT G (AT_Expr (AE_CastUp e))
  | AWTermT_CastDn : forall e G, AWTermT G (AT_Expr e) -> AWTermT G (AT_Expr (AE_CastDn e))
  | AWTermT_Ann: forall e1 e2 G, AWTermT G (AT_Expr e1) -> AWTermT G e2 -> AWTermT G (AT_Expr (AE_Ann e1 e2))
  | AWTermT_Forall: forall G L s,
      (forall x, x \notin L -> AWTermT (G & x ~ AC_TVar) (s @#' x))
      -> AWTermT G (AT_Expr (AE_Forall s))
  | AWTermT_TFVar: forall G i, binds i AC_TVar G -> AWTermT G (AT_TFVar i)
  | AWTermT_Unsolved_EVar: forall G i, binds i AC_Unsolved_EVar G -> AWTermT G (AT_EVar i)
  | AWTermT_Solved_EVar: forall G i t, binds i (AC_Solved_EVar t) G -> AWTermT G (AT_EVar i).

Definition AWTerm G e := AWTermT G (AT_Expr e).

Inductive AResolveEVar : ACtx -> var -> AType -> AType -> ACtx -> Prop :=
  | AResolveEVar_EVar_Before : forall a b G1 G2 G3,
      AResolveEVar (G1 & b ~ AC_Unsolved_EVar & G2 & a ~ AC_Unsolved_EVar & G3) a (AT_EVar b) (AT_EVar b)
                   (G1 & b ~ AC_Unsolved_EVar & G2 & a ~ AC_Unsolved_EVar & G3)
  | AResolveEVar_EVar_After : forall a b G1 G2 G3 a1,
      AResolveEVar (G1 & a ~ AC_Unsolved_EVar & G2 & b ~ AC_Unsolved_EVar & G3) a (AT_EVar b) (AT_EVar a1)
                   (G1 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & G2 & b ~ AC_Solved_EVar (AT_EVar a1) & G3)
  | AResolveEVar_Pi : forall a t1 t2 t3 t4 G H1 H L,
      AResolveEVar G a t1 t3 H1 ->
      (forall x, x \notin L -> AResolveEVar H1 a (ACtxTSubst H1 (t2 @' x)) (ACtxTSubst H1 (t4 @' x)) H) ->
      AResolveEVar G a (AT_Expr (AE_Pi t1 t2)) (AT_Expr (AE_Pi t3 t4)) H
  | AResolveEVar_Var : forall a x G, AResolveEVar G a (AT_Expr (AE_FVar x)) (AT_Expr (AE_FVar x)) G
  | AResolveEVar_TBVar : forall (x:nat) a G, AResolveEVar G a (AT_TBVar x) (AT_TBVar x) G
  | AResolveEVar_TFVar : forall a x G, AResolveEVar G a (AT_TFVar x) (AT_TFVar x) G
  | AResolveEVar_Star : forall a G, AResolveEVar G a (AT_Expr AE_Star) (AT_Expr AE_Star) G
  | AResolveEVar_App : forall a t1 t2 G, AResolveEVar G a (AT_Expr (AE_App t1 t2)) (AT_Expr (AE_App t1 t2)) G
  | AResolveEVar_Lam : forall a t1 G, AResolveEVar G a (AT_Expr (AE_Lam t1)) (AT_Expr (AE_Lam t1)) G
  | AResolveEVar_CastUp : forall a t G, AResolveEVar G a (AT_Expr (AE_CastUp t)) (AT_Expr (AE_CastUp t)) G
  | AResolveEVar_CastDn : forall a t G, AResolveEVar G a (AT_Expr (AE_CastDn t)) (AT_Expr (AE_CastDn t)) G
  | AResolveEVar_Ann : forall a t1 t2 G, AResolveEVar G a (AT_Expr (AE_Ann t1 t2)) (AT_Expr (AE_Ann t1 t2)) G
.

Inductive ARFMode := Plus | Minus.

Inductive AResolveForall : ACtx -> var -> ARFMode -> AType -> AType -> ACtx -> Prop :=
  | AResolveForall_Poly: forall a L G1 G2 H s t,
      (forall a1, a1 \notin L ->
             AResolveForall (G1 & a1 ~ AC_Unsolved_EVar & a ~ AC_Unsolved_EVar & G2)
                            a Plus (s @@#' (AT_EVar a1)) t H) ->
      AResolveForall (G1 & a ~ AC_Unsolved_EVar & G2) a Plus (AT_Expr (AE_Forall s)) t H
  | AResolveForall_Pi1: forall G s1 s2 t1 t2 H1 H a,
      AResolveForall G a Plus s1 t1 H1 ->
      AResolveForall H1 a Minus s2 t2 H ->
      AResolveForall G a Minus (AT_Expr (AE_Pi s1 s2)) (AT_Expr (AE_Pi t1 t2)) H
  | AResolveForall_Pi2: forall G s1 s2 t1 t2 H1 H a,
      AResolveForall G a Minus s1 t1 H1 ->
      AResolveForall H1 a Plus s2 t2 H ->
      AResolveForall G a Plus (AT_Expr (AE_Pi s1 s2)) (AT_Expr (AE_Pi t1 t2)) H
  | AResolveForall_Mono : forall G H a m t,
      ATMono t -> AResolveForall G a m t t H.

Inductive AUnify : ACtx -> AType -> AType -> ACtx -> Prop :=
  | AUnify_Var : forall x G, binds x AC_Var G -> AUnify G (AT_Expr (AE_FVar x)) (AT_Expr (AE_FVar x)) G
  | AUnify_Typed_Var : forall x G t, binds x (AC_Typ t) G -> AUnify G (AT_Expr (AE_FVar x)) (AT_Expr (AE_FVar x)) G
  | AUnify_EVar : forall a G, binds a AC_Unsolved_EVar G -> AUnify G (AT_EVar a) (AT_EVar a) G
  | AUnify_TVar : forall a G, binds a AC_TVar G -> AUnify G (AT_TFVar a) (AT_TFVar a) G
  (* no case for solved evar since it is fully applied under context *)
  | AUnify_Star : forall G, AUnify G (AT_Expr (AE_Star)) (AT_Expr (AE_Star)) G
  | AUnify_App : forall t1 t2 t3 t4 G H1 H,
      AUnify G (AT_Expr t1) (AT_Expr t2) H1 ->
      AUnify H1 (AT_Expr (ACtxSubst H1 t3)) (AT_Expr (ACtxSubst H1 t4)) H ->
      AUnify G (AT_Expr (AE_App t1 t3)) (AT_Expr (AE_App t2 t3)) H
  | AUnify_Lam : forall t1 t2 G H L,
      (forall x, x \notin L -> AUnify (G & x ~ AC_Var) (AT_Expr (t1 @ x)) (AT_Expr (t2 @ x)) (H & x ~ AC_Var)) ->
      AUnify G (AT_Expr (AE_Lam t1)) (AT_Expr (AE_Lam t2)) H
  | AUnify_CastUp : forall t1 t2 G H,
      AUnify G (AT_Expr t1) (AT_Expr t2) H ->
      AUnify G (AT_Expr (AE_CastUp t1)) (AT_Expr (AE_CastUp t2)) H
  | AUnify_CastDn : forall t1 t2 G H,
      AUnify G (AT_Expr t1) (AT_Expr t2) H ->
      AUnify G (AT_Expr (AE_CastDn t1)) (AT_Expr (AE_CastDn t2)) H
  | AUnify_Pi : forall t1 t2 t3 t4 G H1 H L,
      AUnify G t1 t3 H1 ->
      (forall x, x \notin L -> AUnify (H1 & x ~ AC_Typ t1) (ACtxTSubst H1 (t2 @' x)) (ACtxTSubst H1 (t4 @' x)) (H & x ~ AC_Typ t1)) ->
      AUnify G (AT_Expr (AE_Pi t1 t2)) (AT_Expr (AE_Pi t3 t4)) H
  | AUnify_Ann : forall t1 t2 t3 t4 G H1 H,
      AUnify G (AT_Expr t1) (AT_Expr t2) H1 ->
      AUnify H1 (ACtxTSubst H1 t3) (ACtxTSubst H1 t4) H ->
      AUnify G (AT_Expr (AE_Ann t1 t3)) (AT_Expr (AE_Ann t2 t3)) H
  | AUnify_EVarTy : forall a t1 t2 G H1 H2,
      a \notin ATFv (t1) ->
      AResolveEVar G a t1 t2 (H1 & a ~ AC_Unsolved_EVar & H2) ->
      AWTermT H1 t2 ->
      AUnify G (AT_EVar a) t1 (H1 & a ~ AC_Solved_EVar t2 & H2)
  | AUnify_TyEVar : forall a t1 t2 G H1 H2,
      a \notin ATFv (t1) ->
      AResolveEVar G a t1 t2 (H1 & a ~ AC_Unsolved_EVar & H2) ->
      AWTermT H1 t2 ->
      AUnify G t1 (AT_EVar a) (H1 & a ~ AC_Solved_EVar t2 & H2).

Inductive AMode := Inf | Chk | App : AType -> AMode.

Inductive ASubtyping : ACtx -> AType -> AType -> ACtx -> Prop :=
  | ASub_PolyR: forall G v s1 s2 H I,
      v # G ->
      ASubtyping (G & v ~ AC_TVar) s1 (s2 @#' v) (H & v ~ AC_TVar & I) ->
      ASubtyping G s1 (AT_Expr (AE_Forall s2)) H
  | ASub_PolyL: forall G s1 s2 H a,
      a # G ->
      ASubtyping (G & a ~ AC_Unsolved_EVar) (s1 @@#' (AT_EVar a)) s2 H ->
      ASubtyping G (AT_Expr (AE_Forall s1)) s2 H
  | ASub_Pi: forall G s1 s2 s3 s4 H I x H1,
      ASubtyping G s3 s1 H1 ->
      ASubtyping (H1 & x ~ AC_Typ s1) (ACtxTSubst H1 (s2 @' x)) (ACtxTSubst H1 (s4 @' x)) (H & x ~ AC_Typ s1 & I) ->
      ASubtyping G (AT_Expr (AE_Pi s1 s2)) (AT_Expr (AE_Pi s3 s4)) H
  | ASub_EVarL: forall a s G1 G2 H1 H t,
      AResolveForall (G1 & a ~ AC_Unsolved_EVar & G2) a Minus s t H1 ->
      AUnify H1 (AT_EVar a) t H ->
      ASubtyping (G1 & a ~ AC_Unsolved_EVar & G2) (AT_EVar a) s H
  | ASub_EVarR: forall a s G1 G2 H1 H t,
      AResolveForall (G1 & a ~ AC_Unsolved_EVar & G2) a Plus s t H1 ->
      AUnify H1 (AT_EVar a) t H ->
      ASubtyping (G1 & a ~ AC_Unsolved_EVar & G2) s (AT_EVar a) H
  | ASub_Unify: forall G H s1 s2,
      AUnify G s1 s2 H ->
      ASubtyping G s1 s2 H.

Inductive ATyping : AMode -> ACtx -> AType -> AType -> ACtx -> Prop :=
  | ATI_Ax : forall G, AWf G -> ATyping Inf G (AT_Expr AE_Star) (AT_Expr AE_Star) G
  | ATI_Var : forall G x t, AWf G -> binds x (AC_Typ t) G ->
                       ATyping Inf G (AT_Expr (AE_FVar x)) t G
  | ATI_EVar : forall G x, AWf G -> binds x AC_Unsolved_EVar G ->
                      ATyping Inf G (AT_EVar x) (AT_Expr AE_Star) G
  | ATI_Solved_EVar : forall G x t, AWf G -> binds x (AC_Solved_EVar t) G ->
                               ATyping Inf G (AT_EVar x) (AT_Expr AE_Star) G
  | ATI_TVar : forall G x, AWf G -> binds x AC_TVar G ->
                      ATyping Inf G (AT_TFVar x) (AT_Expr AE_Star) G
  | ATI_Ann : forall G H H1 e t,
      AWTermT G (AT_Expr (AE_Ann e t)) ->
      ATyping Chk G t (AT_Expr AE_Star) H1 ->
      ATyping Chk H1 (AT_Expr e) t H ->
      ATyping Inf G (AT_Expr (AE_Ann e t)) t H
  | ATI_Pi : forall G H1 H I t1 t2 x,
      AWTermT G (AT_Expr (AE_Pi t1 t2)) ->
      ATyping Chk G t1 (AT_Expr AE_Star) H1 ->
      x # G ->
      ATyping Chk (H1 & x ~ AC_Typ t1) (t2 @' x) (AT_Expr AE_Star)
                  (H & x ~ AC_Typ t1 & I) ->
      ATyping Inf G (AT_Expr (AE_Pi t1 t2)) (AT_Expr AE_Star) H
  | ATI_Lam : forall G H I e a t2 x,
      AWTermT G (AT_Expr (AE_Lam e)) ->
      x # G ->
      a # G ->
      ATyping Inf (G & a ~ AC_Unsolved_EVar & x ~ AC_Typ (AT_EVar a))
                  (AT_Expr (e @ x)) (t2 @' x)
                  (H & x ~ AC_Typ (AT_EVar a) & I) ->
      ATyping Inf G (AT_Expr (AE_Lam e)) (AT_Expr (AE_Pi (AT_EVar a) (ACtxTSubst I t2))) (H & ACtxUV I)
  | ATI_App : forall G H1 H e1 e2 s1 s2,
      AWTermT G (AT_Expr (AE_App e1 e2)) ->
      ATyping Inf G (AT_Expr e1) s1 H1 ->
      ATyping (App (ACtxTSubst H1 s1)) H1 (AT_Expr e2) s2 H ->
      ATyping Inf G (AT_Expr (AE_App e1 e2)) s2 H
  | ATI_CastDn : forall G H e t1 t2,
      AWTermT G (AT_Expr (AE_CastDn e)) ->
      ATyping Inf G (AT_Expr e) (AT_Expr t1) H ->
      ARed (ACtxSubst H t1) t2 ->
      ATyping Inf G (AT_Expr (AE_CastDn e)) (AT_Expr t2) H
  | ATI_Forall: forall G s H a I,
      AWTermT G (AT_Expr (AE_Forall s)) ->
      a # G ->
      ATyping Chk (G & a ~ AC_TVar) (s @#' a) (AT_Expr AE_Star) (H & a ~ AC_TVar & I) ->
      ATyping Inf G (AT_Expr (AE_Forall s)) (AT_Expr AE_Star) H

  | ATC_Lam : forall G H I e s1 s2 x,
      AWTermT G (AT_Expr (AE_Lam e)) ->
      x # G ->
      ATyping Chk (G & x ~ AC_Typ s1) (AT_Expr (e @ x)) (s2 @' x)
                  (H & x ~ AC_Typ s1 & I) ->
      ATyping Chk G (AT_Expr (AE_Lam e)) (AT_Expr (AE_Pi s1 s2)) H
  | ATC_CastUp : forall G H e t1 t2,
      AWTermT G (AT_Expr (AE_CastUp e)) ->
      ARed (ACtxSubst G t2) t1 ->
      ATyping Chk G (AT_Expr e) (AT_Expr t1) H ->
      ATyping Chk G (AT_Expr (AE_CastUp e)) (AT_Expr t2) H
  | ATC_Sub : forall G H1 H e s1 s2,
      ATyping Inf G e s1 H1 ->
      ASubtyping H1 (ACtxTSubst H1 s1) (ACtxTSubst H1 s2) H ->
      ATyping Chk G e s2 H

  | ATA_Pi : forall G H e s1 s2,
      ATyping Chk G (AT_Expr e) s1 H ->
      ATyping (App (AT_Expr (AE_Pi s1 s2))) G (AT_Expr e) (s2 @@' e) H
  | ATA_EVar : forall G1 G2 H a e a1 a2,
      AWf (G1 & a ~ AC_Unsolved_EVar & G2) ->
      AWTermT (G1 & a ~ AC_Unsolved_EVar & G2) (AT_Expr e) ->
      ATyping Chk (G1 & a2 ~ AC_Unsolved_EVar & a1 ~ AC_Unsolved_EVar &
                    a ~ AC_Solved_EVar (AT_Expr (AE_Pi (AT_EVar a1) (AT_EVar a2))) & G2)
                  (AT_Expr e) (AT_EVar a1) H ->
      ATyping (App (AT_EVar a)) (G1 & a ~ AC_Unsolved_EVar & G2) (AT_Expr e) (AT_EVar a2) H
  | ATA_Forall : forall G s e s2 H a,
      AWTermT G e ->
      a # G ->
      ATyping (App (s @@#' (AT_EVar a))) (G & a ~ AC_Unsolved_EVar) e s2 H ->
      ATyping (App (AT_Expr (AE_Forall s))) G e s2 H

with AWfTyp : ACtx -> AType -> Prop :=
     | AWf_Expr : forall G H s,
         ATyping Chk G s (AT_Expr AE_Star) (G & H) ->
         AWfTyp G s

with AWf : ACtx -> Prop :=
     | AWf_Nil : AWf empty
     | AWf_Var : forall G x,
         AWf G -> x # G ->
         AWf (G & x ~ AC_Var)
     | AWf_TVar : forall G a,
         AWf G -> a # G ->
         AWf (G & a ~ AC_TVar)
     | AWf_TyVar : forall G x s,
         AWf G -> x # G ->
         AWfTyp G s ->
         AWf (G & x ~ AC_Typ s)
     | AWf_Ctx_Unsolved_EVar : forall G x,
         AWf G -> x # G ->
         AWf (G & x ~ AC_Unsolved_EVar)
     | AWf_Ctx_Solved_EVar : forall G x t,
         AWf G -> x # G ->
         ATMono t ->
         AWfTyp G t ->
         AWf (G & x ~ AC_Solved_EVar t)
.

Definition ATypingI := ATyping Inf.
Definition ATypingC := ATyping Chk.
