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
  | DE_Pi : DExpr -> DExpr -> DExpr
  | DE_Let : DExpr -> DExpr -> DExpr
  | DE_CastUp : DExpr -> DExpr
  | DE_CastDn : DExpr -> DExpr
  | DE_Ann : DExpr -> DExpr -> DExpr.

Inductive DType : Set :=
  | DT_Forall : DType -> DType
  | DT_Expr : DExpr -> DType.

(** Open Operation *)

Fixpoint DOpenRec (k : nat) (u : DExpr) (e : DExpr) {struct e} : DExpr :=
  match e with
  | DE_BVar i    => If k = i then u else (DE_BVar i)
  | DE_FVar x    => DE_FVar x
  | DE_Star      => DE_Star
  | DE_App e1 e2 => DE_App    (DOpenRec k u e1) (DOpenRec k u e2)
  | DE_Lam e     => DE_Lam    (DOpenRec (S k) u e)
  | DE_Pi t1 t2  => DE_Pi     (DOpenRec k u t1) (DOpenRec (S k) u t2)
  | DE_Let e1 e2 => DE_Let    (DOpenRec k u e1) (DOpenRec (S k) u e2)
  | DE_CastUp e  => DE_CastUp (DOpenRec k u e)
  | DE_CastDn e  => DE_CastDn (DOpenRec k u e)
  | DE_Ann e t   => DE_Ann    (DOpenRec k u e) (DOpenRec k u t)
  end.

Fixpoint DOpenTypRec (k : nat) (u : DExpr) (e : DType) {struct e} : DType :=
  match e with
  | DT_Forall s => DT_Forall (DOpenTypRec (S k) u s)
  | DT_Expr t   => DT_Expr (DOpenRec k u t)
  end.

Definition DOpen e u := DOpenRec 0 u e.
Definition DOpenT e u := DOpenTypRec 0 u e.

Notation "e ^^ u" := (DOpen e u) (at level 67).
Notation "e ^ x" := (DOpen e (DE_FVar x)).
Notation "e ^^' u" := (DOpenT e u) (at level 67).
Notation "e ^' x" := (DOpenT e (DE_FVar x)) (at level 67).

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
      DTerm t1 ->
      (forall x, x \notin L -> DTerm (t2 ^ x)) ->
      DTerm (DE_Pi t1 t2)
  | DTerm_Let : forall L e1 e2,
      DTerm e1 ->
      (forall x, x \notin L -> DTerm (e2 ^ x)) ->
      DTerm (DE_Let e1 e2)
  | DTerm_CastUp : forall e,
      DTerm e -> DTerm (DE_CastUp e)
  | DTerm_CastDn : forall e,
      DTerm e -> DTerm (DE_CastDn e)
  | DTerm_Ann : forall t e,
      DTerm t -> DTerm e -> DTerm (DE_Ann t e).

Definition DBody t :=
  exists L, forall x, x \notin L -> DTerm (t ^ x).

Inductive DTermTy : DType -> Prop :=
  | DTermTy_Expr : forall e, DTerm e -> DTermTy (DT_Expr e)
  | DTermTy_Forall : forall L t,
      (forall x, x \notin L -> DTermTy (t ^' x)) ->
      DTermTy (DT_Forall t).

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
  | DE_Pi t1 t2  => DE_Pi     (DSubst z u t1) (DSubst z u t2)
  | DE_Let e1 e2 => DE_Let    (DSubst z u e1) (DSubst z u e2)
  | DE_CastUp e  => DE_CastUp (DSubst z u e)
  | DE_CastDn e  => DE_CastDn (DSubst z u e)
  | DE_Ann e t   => DE_Ann    (DSubst z u e) (DSubst z u t)
  end.

Fixpoint DTSubst (z : var) (u : DExpr) (e : DType) {struct e} : DType :=
  match e with
  | DT_Forall s  => DT_Forall (DTSubst z u s)
  | DT_Expr t    => DT_Expr (DSubst z u t)
  end.

(** Free Varialble *)

Fixpoint DFv (e : DExpr) {struct e} : vars :=
  match e with
  | DE_BVar i    => \{}
  | DE_FVar x    => \{x}
  | DE_Star      => \{}
  | DE_App e1 e2 => (DFv e1) \u (DFv e2)
  | DE_Lam e     => DFv e
  | DE_Pi t1 t2  => (DFv t1) \u (DFv t2)
  | DE_Let e1 e2 => (DFv e1) \u (DFv e2)
  | DE_CastUp e  => DFv e
  | DE_CastDn e  => DFv e
  | DE_Ann e t   => (DFv e) \u (DFv t)
  end.

Fixpoint DTFv (e : DType) {struct e} : vars :=
  match e with
  | DT_Forall s => DTFv s
  | DT_Expr t   => DFv t
  end.

(** Context *)

Inductive DCtxT : Set :=
  | DC_Typ : DExpr -> DCtxT
  | DC_Bnd : DType -> DExpr -> DCtxT.

Definition DCtx := LibEnv.env DCtxT.

Definition DCtxSubst (G : DCtx) (e : DExpr) : DExpr :=
  LibList.fold_left
    (fun (c : var * DCtxT) v => let (x, p) := c in
        match p with
        | DC_Typ _ => v
        | DC_Bnd s t => DSubst x t v
        end) e G.

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
      DTerm t -> DRed e e' ->
      DRed (DE_Ann e t) (DE_Ann e' t)
  | DR_Let : forall e1 e2,
      DTerm (DE_Let e1 e2) ->
      DRed (DE_Let e1 e2) (e2 ^^ e1).

(** Typing *)

Inductive DTypingI : DCtx -> DExpr -> DExpr -> Prop :=
  | DTI_Ax : forall G, DWf G -> DTypingI G DE_Star DE_Star
  | DTI_Var : forall G x t, DWf G -> binds x (DC_Typ t) G ->
                            DTypingI G (DE_FVar x) t
  | DTI_LetVar : forall G x s t t2,
      DWf G -> binds x (DC_Bnd s t) G ->
      DInst G s t2 ->
      DTypingI G (DE_FVar x) t2
  | DTI_Ann : forall G e t,
      DTypingC G t DE_Star ->
      DTypingC G e t ->
      DTypingI G (DE_Ann e t) t
  | DTI_Lam : forall L G e t1 t2,
      DTypingC G t1 DE_Star ->
      (forall x, x \notin L ->
                 DTypingI (G & x ~ (DC_Typ t1)) (e ^ x) (t2 ^ x)) ->
      DTypingI G (DE_Lam e) (DE_Pi t1 t2)
  | DTI_App : forall G e1 e2 t1 t2,
      DTypingI G e1 (DE_Pi t1 t2) ->
      DTypingC G e2 t1 ->
      DTypingI G (DE_App e1 e2) (t2 ^^ e2)
  | DTI_Let : forall L G e1 e2 s t2,
      DGen G e1 s ->
      (forall x, x \notin L ->
                 DTypingI (G & x ~ (DC_Bnd s e1)) (e2 ^ x) (t2 ^ x)) ->
      DTypingI G (DE_Let e1 e2) (t2 ^^ e1)
  | DTI_Pi : forall L G t1 t2,
      DTypingC G t1 DE_Star ->
      (forall x, x \notin L ->
                 DTypingC (G & (x ~ DC_Typ t1)) (t2 ^ x) DE_Star) ->
      DTypingI G (DE_Pi t1 t2) DE_Star
  | DTI_CastDn : forall G e t1 t2,
      DTypingI G e t1 ->
      DRed t1 t2 ->
      DTypingI G (DE_CastDn e) t2
  | DTI_Conv : forall G e1 t1 t2,
      DTypingI G e1 t2 ->
      DCtxSubst G t1 = DCtxSubst G t2 ->
      DTypingI G e1 t2
      
with DTypingC : DCtx -> DExpr -> DExpr -> Prop :=
  | DTC_Lam : forall L G e t1 t2,
      DTypingC G t1 DE_Star ->
      (forall x, x \notin L ->
                 DTypingC (G & (x ~ DC_Typ t1)) (e ^ x) (t2 ^ x)) ->
      DTypingC G (DE_Lam e) (DE_Pi t1 t2)
  | DTC_Let : forall L G e1 e2 s t2,
      DGen G e1 s ->
      (forall x, x \notin L ->
                 DTypingC (G & x ~ (DC_Bnd s e1)) (e2 ^ x) (t2 ^ x)) ->
      DTypingC G (DE_Let e1 e2) (t2 ^^ e1)
  | DTC_CastUp : forall G e t1 t2,
      DTypingC G e t1 ->
      DRed t2 t1 ->
      DTypingC G (DE_CastUp e) t2
  | DTC_Sub : forall G e t,
      DTypingI G e t ->
      DTypingC G e t

with DWfTyp : DCtx -> DType -> Prop :=
  | DWf_Expr : forall G t,
      DTypingC G t DE_Star ->
      DWfTyp G (DT_Expr t)
  | DWf_Poly : forall L G s,
      (forall x, x \notin L ->
                 DWfTyp (G & x ~ DC_Typ DE_Star) (s ^' x)) ->
      DWfTyp G (DT_Forall s)

with DWf : DCtx -> Prop :=
  | DWf_Nil : DWf empty
  | DWf_TyVar : forall G x t,
      DWf G -> x # G ->
      DTypingC G t DE_Star ->
      DWf (G & x ~ DC_Typ t)
  | DWf_LetVar : forall G x s t,
      DWf G -> x # G -> DWfTyp G (DT_Expr s) ->
      DTypingC G t s ->
      DWf (G & x ~ DC_Bnd (DT_Expr s) t)
  | DWf_LetVar2 : forall L G x s t,
      DWf G -> x # G -> DWfTyp G s ->
      (forall x, x \notin L -> DWf (G & x ~ DC_Bnd (s ^' x) t)) ->
      DWf (G & x ~ DC_Bnd (DT_Forall s) t)

with DInst : DCtx -> DType -> DExpr -> Prop :=
  | DInst_Expr : forall G t1,
      DTypingC G t1 DE_Star ->
      DInst G (DT_Expr t1) t1
  | DInst_Poly : forall L G t s t1,
      DTypingC G t DE_Star ->
      (forall x, x \notin L ->
                 DInst (G & x ~ DC_Typ DE_Star) (s ^' x) (t1 ^ x)) ->
      DInst G (DT_Forall s) (t1 ^^ t)

with DGen : DCtx -> DExpr -> DType -> Prop :=
  | DGen_Expr : forall G e t,
      DTypingI G e t ->
      DGen G e (DT_Expr t)
  | DGen_Poly : forall L G e s,
      (forall x, x \notin L -> x \notin (DFv e) ->
                 DGen (G & x ~ DC_Typ DE_Star) e (s ^' x)) ->
      DGen G e (DT_Forall s).
