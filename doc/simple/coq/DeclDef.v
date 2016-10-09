(** ** Declarative System *)

Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.

(** Syntax **)

Inductive DExpr : Set :=
  | DE_BVar : nat -> DExpr
  | DE_FVar : var -> DExpr
  | DE_Star : DExpr
  | DE_App : DExpr -> DExpr -> DExpr
  | DE_Lam : DExpr -> DExpr
  | DE_Pi : DType -> DType -> DExpr
  | DE_CastUp : DExpr -> DExpr
  | DE_CastDn : DExpr -> DExpr
  | DE_Ann : DExpr -> DType -> DExpr
  | DE_Forall: DType -> DExpr

with
DType : Set :=
  | DT_TBVar : nat -> DType
  | DT_TFVar : var -> DType
  | DT_Expr : DExpr -> DType.

(** Open Operation *)

Fixpoint DOpenRec (k : nat) (u : DExpr) (e : DExpr) {struct e} : DExpr :=
  match e with
  | DE_BVar i    => If k = i then u else (DE_BVar i)
  | DE_FVar x    => DE_FVar x
  | DE_Star      => DE_Star
  | DE_App e1 e2 => DE_App    (DOpenRec k u e1) (DOpenRec k u e2)
  | DE_Lam e     => DE_Lam    (DOpenRec (S k) u e)
  | DE_Pi t1 t2  => DE_Pi     (DOpenTypRec k u t1) (DOpenTypRec (S k) u t2)
  | DE_CastUp e  => DE_CastUp (DOpenRec k u e)
  | DE_CastDn e  => DE_CastDn (DOpenRec k u e)
  | DE_Ann e t   => DE_Ann    (DOpenRec k u e) (DOpenTypRec k u t)
  | DE_Forall s  => DE_Forall (DOpenTypRec (S k) u s)

  end
with
DOpenTypRec (k : nat) (u : DExpr) (e : DType) {struct e} : DType :=
  match e with
  | DT_TBVar i   => DT_TBVar i
  | DT_TFVar i   => DT_TFVar i
  | DT_Expr t    => DT_Expr (DOpenRec k u t)
  end.

Fixpoint DTOpenRec (k : nat) (u : DType) (e : DExpr) {struct e} : DExpr :=
  match e with
  | DE_BVar i    => DE_BVar i
  | DE_FVar x    => DE_FVar x
  | DE_Star      => DE_Star
  | DE_App e1 e2 => DE_App    (DTOpenRec k u e1) (DTOpenRec k u e2)
  | DE_Lam e     => DE_Lam    (DTOpenRec (S k) u e)
  | DE_Pi t1 t2  => DE_Pi     (DTOpenTypRec k u t1) (DTOpenTypRec (S k) u t2)
  | DE_CastUp e  => DE_CastUp (DTOpenRec k u e)
  | DE_CastDn e  => DE_CastDn (DTOpenRec k u e)
  | DE_Ann e t   => DE_Ann    (DTOpenRec k u e) (DTOpenTypRec k u t)
  | DE_Forall s  => DE_Forall (DTOpenTypRec (S k) u s)
  end
with
DTOpenTypRec (k : nat) (u : DType) (e : DType) {struct e} : DType :=
  match e with
  | DT_TBVar i    => If i = k then u else (DT_TBVar i)
  | DT_TFVar i    => DT_TFVar i
  | DT_Expr t     => DT_Expr (DTOpenRec k u t)
  end.

Definition DOpen e u := DOpenRec 0 u e.
Definition DOpenT e u := DOpenTypRec 0 u e.
Definition DTOpen e u := DTOpenRec 0 u e.
Definition DTOpenT e u := DTOpenTypRec 0 u e.

Notation "e ^ x" := (DOpen e (DE_FVar x)).
Notation "e ^^ u" := (DOpen e u) (at level 67).
Notation "e ^% x" := (DTOpen e (DT_TFVar x)) (at level 67).
Notation "e ^^% u" := (DTOpen e u) (at level 67).
Notation "e ^' x" := (DOpenT e (DE_FVar x)) (at level 67).
Notation "e ^^' u" := (DOpenT e u) (at level 67).
Notation "e ^%' x" := (DTOpenT e (DT_TFVar x)) (at level 67).
Notation "e ^^%' u" := (DTOpenT e u) (at level 67).

(** Closed Terms *)

Inductive DTerm : DExpr -> Prop :=
  | DTerm_Var : forall x, DTerm (DE_FVar x)
  | DTerm_Star : DTerm DE_Star
  | DTerm_App : forall e1 e2,
      DTerm e1 -> DTerm e2 -> DTerm (DE_App e1 e2)
  | DTerm_Lam : forall L e,
      (forall x, x \notin L -> DTerm (e ^ x)) ->
      DTerm (DE_Lam e)
  | DTerm_Pi : forall L t1 t2,
      DTermTy t1 ->
      (forall x, x \notin L -> DTermTy (t2 ^' x)) ->
      DTerm (DE_Pi t1 t2)
  | DTerm_CastUp : forall e,
      DTerm e -> DTerm (DE_CastUp e)
  | DTerm_CastDn : forall e,
      DTerm e -> DTerm (DE_CastDn e)
  | DTerm_Ann : forall t e,
      DTerm t -> DTermTy e -> DTerm (DE_Ann t e)
  | DTerm_Forall : forall L t,
      (forall x, x \notin L -> DTermTy (t ^%' x)) ->
      DTerm (DE_Forall t)
with
DTermTy : DType -> Prop :=
  | DTermTy_TFVar : forall i, DTermTy (DT_TFVar i)
  | DTermTy_Expr : forall e,
      DTerm e -> DTermTy (DT_Expr e).

Inductive DMono : DExpr -> Prop :=
| DM_FVar : forall x, DMono (DE_FVar x)
| DM_Star: DMono (DE_Star)
| DM_App: forall e1 e2, DMono e1 -> DMono e2 -> DMono (DE_App e1 e2)
| DM_Lam: forall L e, (forall x, x \notin L -> DMono (e ^ x)) -> DMono (DE_Lam e)
| DM_Pi: forall L s1 s2, DTMono s1 -> (forall x, x \notin L -> DTMono (s2 ^' x)) -> DMono (DE_Pi s1 s2)
| DM_CastUp: forall e, DMono e -> DMono (DE_CastUp e)
| DM_CastDn: forall e, DMono e -> DMono (DE_CastDn e)
| DM_Ann: forall e s, DMono e -> DTMono s -> DMono (DE_Ann e s)

with
DTMono: DType -> Prop :=
| DM_TFVar : forall x, DTMono (DT_TFVar x)
| DM_Expr : forall e, DMono e -> DTMono (DT_Expr e).

Definition DBody t :=
  exists L, forall x, x \notin L -> DTerm (t ^ x).

Definition DBodyTy t :=
  exists L, forall x, x \notin L -> DTermTy (t ^' x).

(** Substitution *)

Fixpoint DSubst (z : var) (u : DExpr) (e : DExpr) {struct e} : DExpr :=
  match e with
  | DE_BVar i    => DE_BVar i
  | DE_FVar x    => If x = z then u else (DE_FVar x)
  | DE_Star      => DE_Star
  | DE_App e1 e2 => DE_App    (DSubst z u e1) (DSubst z u e2)
  | DE_Lam e     => DE_Lam    (DSubst z u e)
  | DE_Pi t1 t2  => DE_Pi     (DTSubst z u t1) (DTSubst z u t2)
  | DE_CastUp e  => DE_CastUp (DSubst z u e)
  | DE_CastDn e  => DE_CastDn (DSubst z u e)
  | DE_Ann e t   => DE_Ann    (DSubst z u e) (DTSubst z u t)
  | DE_Forall s  => DE_Forall (DTSubst z u s)
  end
with
DTSubst (z : var) (u : DExpr) (e : DType) {struct e} : DType :=
  match e with
  | DT_TBVar i    => DT_TBVar i
  | DT_TFVar i    => DT_TFVar i
  | DT_Expr t    => DT_Expr (DSubst z u t)
  end.

Fixpoint DSubstT (z : var) (u : DType) (e : DExpr) {struct e} : DExpr :=
  match e with
  | DE_BVar i    => DE_BVar i
  | DE_FVar x    => DE_FVar x
  | DE_Star      => DE_Star
  | DE_App e1 e2 => DE_App    (DSubstT z u e1) (DSubstT z u e2)
  | DE_Lam e     => DE_Lam    (DSubstT z u e)
  | DE_Pi t1 t2  => DE_Pi     (DTSubstT z u t1) (DTSubstT z u t2)
  | DE_CastUp e  => DE_CastUp (DSubstT z u e)
  | DE_CastDn e  => DE_CastDn (DSubstT z u e)
  | DE_Ann e t   => DE_Ann    (DSubstT z u e) (DTSubstT z u t)
  | DE_Forall s  => DE_Forall (DTSubstT z u s)
  end
with
DTSubstT (z : var) (u : DType) (e : DType) {struct e} : DType :=
  match e with
  | DT_TBVar i    => DT_TBVar i
  | DT_TFVar i    => If i = z then u else (DT_TFVar i)
  | DT_Expr t     => DT_Expr (DSubstT z u t)
  end.

(** Free Varialble *)

Fixpoint DFv (e : DExpr) {struct e} : vars :=
  match e with
  | DE_BVar i    => \{}
  | DE_FVar x    => \{x}
  | DE_Star      => \{}
  | DE_App e1 e2 => (DFv e1) \u (DFv e2)
  | DE_Lam e     => DFv e
  | DE_Pi t1 t2  => (DTFv t1) \u (DTFv t2)
  | DE_CastUp e  => DFv e
  | DE_CastDn e  => DFv e
  | DE_Ann e t   => (DFv e) \u (DTFv t)
  | DE_Forall s  => DTFv s
  end
with
DTFv (e : DType) {struct e} : vars :=
  match e with
  | DT_TBVar i => \{}
  | DT_TFVar i => \{i}
  | DT_Expr t   => DFv t
  end.

(** Context *)

Inductive DCtxT : Set :=
  | DC_TVar: DCtxT
  | DC_Typ : DType -> DCtxT.

Definition DCtx := LibEnv.env DCtxT.

(** Reduction *)

Inductive DRed : DExpr -> DExpr -> Prop :=
  | DR_Beta : forall e1 e2,
      DTerm (DE_Lam e1) ->
      DTerm e2 ->
      DRed (DE_App (DE_Lam e1) e2) (e1 ^^ e2)
  | DR_CastDnUp : forall e,
      DTerm e ->
      DRed (DE_CastDn (DE_CastUp e)) e
  | DR_App : forall e1 e1' e2,
      DTerm e2 -> DRed e1 e1' ->
      DRed (DE_App e1 e2) (DE_App e1' e2)
  | DR_CastDn : forall e e',
      DRed e e' -> DRed (DE_CastDn e) (DE_CastDn e')
  | DR_Ann : forall e t e',
      DTermTy t -> DRed e e' ->
      DRed (DE_Ann e t) (DE_Ann e' t)
.
(** Typing *)

Inductive DMode := Inf | Chk | App : DType -> DMode.

Inductive DTyping : DMode -> DCtx -> DType -> DType -> Prop :=
  | DTI_TFVar : forall G a, DWf G -> binds a DC_TVar G ->
                      DTyping Inf G (DT_TFVar a) (DT_Expr DE_Star)
  | DTI_Ax : forall G, DWf G -> DTyping Inf G (DT_Expr DE_Star) (DT_Expr DE_Star)
  | DTI_Var : forall G x s, DWf G -> binds x (DC_Typ s) G ->
                       DTyping Inf G (DT_Expr (DE_FVar x)) s
  | DTI_Ann : forall G e t,
      DTyping Chk G t (DT_Expr DE_Star) ->
      DTyping Chk G (DT_Expr e) t ->
      DTyping Inf G (DT_Expr (DE_Ann e t)) t
  | DTI_Lam : forall L G e t1 t2,
      DTMono t1 ->
      DTyping Chk G t1 (DT_Expr DE_Star) ->
      (forall x, x \notin L ->
                 DTyping Inf (G & x ~ DC_Typ t1) (DT_Expr (e ^ x)) (t2 ^' x)) ->
      DTyping Inf G (DT_Expr (DE_Lam e)) (DT_Expr (DE_Pi t1 t2))
  | DTI_Pi : forall L G t1 t2,
      DTyping Chk G t1 (DT_Expr DE_Star) ->
      (forall x, x \notin L ->
                 DTyping Chk (G & (x ~ DC_Typ t1)) (t2 ^' x) (DT_Expr DE_Star)) ->
      DTyping Inf G (DT_Expr (DE_Pi t1 t2)) (DT_Expr DE_Star)
  | DTI_Forall : forall L G s,
      (forall a, a \notin L ->
            DTyping Chk (G & a ~ DC_TVar) (s ^%' a) (DT_Expr DE_Star)) ->
      DTyping Inf G (DT_Expr (DE_Forall s)) (DT_Expr DE_Star)
  | DTI_CastDn : forall G e t1 t2,
      DTyping Inf G (DT_Expr e) (DT_Expr t1) ->
      DRed t1 t2 ->
      DTyping Inf G (DT_Expr (DE_CastDn e)) (DT_Expr t2)
  | DTI_App : forall G e1 e2 s1 s2,
      DTyping Inf G (DT_Expr e1) s1 ->
      DTyping (App s1) G (DT_Expr e2) s2 ->
      DTyping Inf G (DT_Expr (DE_App e1 e2)) s2
  | DTA_Pi : forall G s1 s2 e2,
      DTyping Chk G (DT_Expr e2) s1 ->
      DTyping (App (DT_Expr (DE_Pi s1 s2))) G (DT_Expr e2) (s2 ^^' e2)
  | DTA_Forall : forall G s1 s2 t e2,
      DTMono t ->
      DTyping Chk G t (DT_Expr DE_Star) ->
      DTyping (App (s1 ^^%' t)) G e2 s2 ->
      DTyping (App (DT_Expr (DE_Forall s1))) G e2 s2
  | DTC_Lam : forall L G e t1 t2,
      DTyping Chk G t1 (DT_Expr DE_Star) ->
      (forall x, x \notin L ->
            DTyping Chk (G & x ~ DC_Typ t1) (DT_Expr (e ^ x)) (t2 ^' x)) ->
      DTyping Chk G (DT_Expr (DE_Lam e)) (DT_Expr (DE_Pi t1 t2))
  | DTC_CastUp : forall G e t1 t2,
      DRed t2 t1 ->
      DTyping Chk G (DT_Expr e) (DT_Expr t1) ->
      DTyping Chk G (DT_Expr (DE_CastUp e)) (DT_Expr t2)
  | DTC_Sub : forall G e s1 s2,
      DTyping Inf G e s1 ->
      DSubtyping G s1 s2 ->
      DTyping Chk G e s2
  | DTC_Inst : forall L G e s,
      (forall a, a \notin L -> DTyping Chk (G & a ~ DC_TVar) e (s ^%' a)) ->
      DTyping Chk G e (DT_Expr (DE_Forall s))

with DWf : DCtx -> Prop :=
  | DWf_Nil : DWf empty
  | DWf_TVar : forall G a,
      DWf G -> a # G -> DWf (G & a ~ DC_TVar)
  | DWf_TyVar : forall G x s,
      DWf G -> x # G ->
      DTyping Chk G s (DT_Expr DE_Star) ->
      DWf (G & x ~ DC_Typ s)

with DSubtyping: DCtx -> DType -> DType -> Prop :=
  | DSub_PolyR: forall L G s1 s2,
      (forall a, a \notin L -> DSubtyping (G & a ~ DC_TVar) s1 (s2 ^%' a)) ->
      DSubtyping G s1 (DT_Expr (DE_Forall s2))
  | DSub_PolyL: forall G t s1 s2,
      DTMono t ->
      DTyping Chk G t (DT_Expr DE_Star) ->
      DSubtyping G (s1 ^^%' t) s2 ->
      DSubtyping G (DT_Expr (DE_Forall s1)) s2
  | DSub_Pi: forall L G s1 s2 s3 s4,
      DSubtyping G s3 s1 ->
      (forall x, x \notin L -> DSubtyping (G & x ~ DC_Typ s1) (s2 ^' x) (s4 ^' x)) ->
      DSubtyping G (DT_Expr (DE_Pi s1 s2)) (DT_Expr (DE_Pi s3 s4))
  | DSub_AEq: forall G s,
      DSubtyping G s s
.

Definition DTypingC := DTyping Chk.
Definition DTypingI := DTyping Inf.
