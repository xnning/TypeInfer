Set Implicit Arguments.
Require Import LibLN.
Implicit Type x : var.

Inductive trm : Set :=
| trm_bvar : nat -> trm
| trm_fvar : var -> trm
| trm_star : trm
| trm_app : trm -> trm -> trm
| trm_lam : trm -> trm -> trm
| trm_ilam : trm -> trm
| trm_pi : trm -> trm -> trm
| trm_let : trm -> trm -> trm
| trm_castup : trm -> trm
| trm_castdn : trm -> trm
| trm_ann : trm -> trm -> trm.

Fixpoint open_rec (k : nat) (u : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i => If k = i then u else (trm_bvar i)
  | trm_fvar x => trm_fvar x
  | trm_star => trm_star
  | trm_app e1 e2 => trm_app (open_rec k u e1) (open_rec k u e2)
  | trm_lam t e => trm_lam (open_rec k u t) (open_rec (S k) u e)
  | trm_ilam e => trm_ilam (open_rec (S k) u e)
  | trm_pi t1 t2 => trm_pi (open_rec k u t1) (open_rec (S k) u t2) 
  | trm_let e1 e2 => trm_let (open_rec k u e1) (open_rec (S k) u e2) 
  | trm_castup e => trm_castup (open_rec k u e)
  | trm_castdn e => trm_castdn (open_rec k u e)
  | trm_ann e t => trm_ann (open_rec k u e) (open_rec k u t)
  end.

Definition open e u := open_rec 0 u e.

Notation "{ k ~> u } e" := (open_rec k u e) (at level 67).
Notation "e ^^ u" := (open e u) (at level 67).
Notation "e ^ x" := (open e (trm_fvar x)).

Inductive term : trm -> Prop :=
| term_var : forall x, term (trm_fvar x)
| term_star : term trm_star
| term_app : forall e1 e2,
    term e1 -> term e2 -> term (trm_app e1 e2)
| term_lam : forall L t e, 
    term t -> (forall x, x \notin L -> term (e ^ x)) -> term (trm_lam t e)
| term_ilam : forall L e, 
    (forall x, x \notin L -> term (e ^ x)) -> term (trm_ilam e)
| term_pi : forall L t1 t2, 
    term t1 -> (forall x, x \notin L -> term (t2 ^ x)) -> term (trm_pi t1 t2)
| term_let : forall L e1 e2, 
    term e1 -> (forall x, x \notin L -> term (e2 ^ x)) -> term (trm_let e1 e2)
| term_castup : forall e, term e -> term (trm_castup e)
| term_castdn : forall e, term e -> term (trm_castdn e)
| term_ann : forall t e, term e -> term (trm_ann t e).

Definition body t :=
  exists L, forall x, x \notin L -> term (t ^ x).

Definition relation := trm -> trm -> Prop.

Inductive reduct : relation :=
| reduct_beta : forall t e u,
    term (trm_lam t e) -> term u ->
    reduct (trm_app (trm_lam t e) u) (e ^^ u)
| reduct_ibeta : forall e u,
    term (trm_ilam e) -> term u ->
    reduct (trm_app (trm_ilam e) u) (e ^^ u)
| reduct_app : forall e1 e1' e2,
    term e2 -> reduct e1 e1' -> reduct (trm_app e1 e2) (trm_app e1' e2)
| reduct_let : forall e1 e2,
    reduct (trm_let e1 e2) (e2 ^^ e1)
| reduct_castelim : forall e,
    term (trm_castup e) -> reduct (trm_castdn (trm_castup e)) e
| reduct_castup : forall e e',
    reduct e e' -> reduct (trm_castup e) (trm_castup e')
| reduct_castdn : forall e e',
    reduct e e' -> reduct (trm_castdn e) (trm_castdn e').

Inductive env_ty : Set :=
| env_varbnd : trm -> env_ty
| env_var : env_ty
| env_evar : env_ty
| env_evardef : trm -> env_ty.

Definition env := LibEnv.env env_ty.
Section Typing.
Implicit Type E : env.


