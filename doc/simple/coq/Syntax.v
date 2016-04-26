Set Implicit Arguments.
Require Import LibList LibLN.
Implicit Type x : var.

Inductive trm : Set :=
| trm_bvar : nat -> trm
| trm_fvar : var -> trm
| trm_bevar : nat -> trm
| trm_fevar : var -> trm
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
  | trm_bevar i => If k = i then u else (trm_bevar i)
  | trm_fevar x => trm_fevar x
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
| term_evar : forall x, term (trm_fevar x)
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

Fixpoint fv (e : trm) {struct e} : vars :=
  match e with
  | trm_bvar i    => \{}
  | trm_fvar x    => \{x}
  | trm_bevar i   => \{}
  | trm_fevar x   => \{x}
  | trm_star      => \{}
  | trm_app e1 e2 => (fv e1) \u (fv e2)
  | trm_lam t e   => (fv t) \u (fv e)
  | trm_ilam t    => fv t
  | trm_pi t1 t2  => (fv t1) \u (fv t2)
  | trm_let e1 e2 => (fv e1) \u (fv e2)
  | trm_castup e  => fv e
  | trm_castdn e  => fv e
  | trm_ann e t   => (fv e) \u (fv t)
  end.

Fixpoint erase (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => trm_fvar x
  | trm_bevar i   => trm_bvar i
  | trm_fevar x   => trm_fvar x
  | trm_star      => trm_star
  | trm_app e1 e2 => trm_app (erase e1) (erase e1)
  | trm_lam t e   => trm_lam (erase t) (erase e)
  | trm_ilam t    => trm_ilam (erase t)
  | trm_pi t1 t2  => trm_pi (erase t1) (erase t2)
  | trm_let e1 e2 => trm_let (erase e1) (erase e2)
  | trm_castup e  => trm_castup (erase e)
  | trm_castdn e  => trm_castdn (erase e)
  | trm_ann e t   => e
  end.

Fixpoint subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => trm_bvar i 
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_bevar i   => trm_bevar i 
  | trm_fevar x   => If x = z then u else (trm_fevar x)
  | trm_star      => trm_star
  | trm_app t1 t2 => trm_app (subst z u t1) (subst z u t2)
  | trm_lam t1 t2 => trm_lam (subst z u t1) (subst z u t2)
  | trm_ilam t1   => trm_ilam (subst z u t1)
  | trm_pi t1 t2  => trm_pi (subst z u t1) (subst z u t2)
  | trm_let t1 t2 => trm_let (subst z u t1) (subst z u t2)
  | trm_castup t1 => trm_castup (subst z u t1)
  | trm_castdn t1 => trm_castdn (subst z u t1)
  | trm_ann t1 t2 => trm_ann (subst z u t1) (subst z u t2)
  end.

Notation "[ z ~> u ] t" := (subst z u t) (at level 68).

Inductive envbnd : Set :=
| env_var : envbnd
| env_varbnd : trm -> envbnd
| env_evar : envbnd
| env_evardef : trm -> envbnd.

Definition env := LibEnv.env envbnd.
Section Typing.
Implicit Type E : env.

Definition env_subst (E : env) (e : trm) : trm :=
  LibList.fold_left (
      fun b v =>
        match (snd b) with
        | env_var => v
        | env_varbnd _ => v
        | env_evar => v
        | env_evardef e' => [fst b ~> e'] v
        end
    ) e E.

Definition env_inst_env (E : env) (x : var) (E' : env) : env :=
  LibList.fold_right (
      fun b v =>
        If fst b = x then E' ++ v else b :: v
    ) nil E.

Definition env_inst_trm (E : env) (x : var) (t : trm) : env :=
  LibList.fold_right (
      fun b v =>
        If fst b = x then (x, env_evardef t) :: v else b :: v
    ) nil E.

Definition env_inst_pi (E : env) (x : var) (a1 : var) (a2 : var) : env :=
  LibList.fold_right (
      fun b v =>
        If fst b = x then
        (a2, env_evar)
          :: (a1, env_evar)
          :: (x, env_evardef (trm_pi (trm_fevar a1) (trm_fevar a2)))
          :: v
      else b :: v
    ) nil E.

Fixpoint env_varidx (i : nat) (k : var) (E : env) {struct E} : nat :=
  match E with
  | nil => i
  | (x,_) :: E' => If k = x then i else env_varidx (i + 1) k E'
  end.

Definition env_before (E : env) (x : var) (y : var) : Prop :=
  env_varidx 0 x E < env_varidx 0 y E.

Definition env_hasevar (x : var) (E : env) :=
  binds x env_evar E.

Definition env_anyevar (x : var) (E : env) :=
  env_hasevar x E \/ (exists t, binds x (env_evardef t) E).

Definition env_anyvar (x : var) (E : env) :=
  binds x env_var E \/ (exists t, binds x (env_varbnd t) E).

Definition env_hasevars (x : var) (y : var) (E : env) :=
  env_hasevar x E /\ env_hasevar y E /\ env_before E x y.

Inductive typing_infer : env -> trm -> trm -> env -> Prop :=
| typing_star : forall E,
    wf E ->
    typing_infer E trm_star trm_star E
| typing_var : forall E x t,
    wf E ->
    binds x (env_varbnd t) E ->
    typing_infer E (trm_fvar x) t E
| typing_evar : forall E x,
    wf E ->
    binds x env_evar E ->
    typing_infer E (trm_fevar x) trm_star E
| typing_evardef : forall E x,
    wf E ->
    (exists e, binds x (env_evardef e) E) ->
    typing_infer E (trm_fevar x) trm_star E
| typing_app : forall E e1 e2 t1 t2 O1 O,
    typing_infer E e1 t1 O1 ->
    app_typing O1 (env_subst O1 t1) e2 t2 O ->
    typing_infer E (trm_app e1 e2) (t2 ^^ e2) O
| typing_laminfer : forall L E e a b O D,
    a # E -> b # E ->
    (forall x,
        x \notin L ->
        typing_check (E & (a ~ env_evar)
                      & (b ~ env_evar)
                      & (x ~ env_varbnd (trm_fevar a)))
                     e (trm_fevar b)
                     (O & (x ~ env_varbnd (trm_fevar a)) & D)) ->
    typing_infer E (trm_ilam e)
                 (trm_pi (trm_fevar a) (trm_fevar b)) O
| typing_lamann : forall L E e t1 t2 O O1 D,
    typing_check E t1 trm_star O1 ->
    (forall x,
        x \notin L ->
        typing_infer (O1 & x ~ (env_varbnd t1))
                     e t2 (O & (x ~ env_varbnd t1) & D)) ->
    typing_infer E (trm_lam t1 e) (trm_pi t1 t2) O
with typing_check : env -> trm -> trm -> env -> Prop :=
     | typing_lamcheck : forall L E e t1 t2 O1 O D,
         typing_check E (trm_pi t1 t2) trm_star O1 ->
         (forall x, x \notin L ->
                    typing_check (E & x ~ (env_varbnd t1))
                                 (e ^ x)
                                 (t2 ^ x)
                                 (O & (x ~ (env_varbnd t1)) & D)) ->
         typing_check E (trm_ilam e) (trm_pi t1 t2) O

with wf : env -> Prop :=
     | wf_nil : wf empty
     | wf_var : forall E x,
         x # E ->
         wf (E & x ~ env_var)
     | wf_varbnd : forall E x t O,
         x # E ->
         typing_infer E t trm_star O ->
         wf (E & x ~ (env_varbnd t))
     | wf_evar : forall E x,
         x # E ->
         wf (E & x ~ env_evar)
     | wf_evardef : forall E x e t O D,
         x # E ->
         typing_infer E e t O ->
         typing_infer O t trm_star D ->
         wf (E & x ~ (env_evardef e))
            
with app_typing : env -> trm -> trm -> trm -> env -> Prop :=
     | appty_pi : forall E e t1 t2 O,
         typing_check E e t1 O ->
         app_typing E (trm_pi t1 t2) e t2 O
     | appty_evar : forall E a a1 a2 e O,
         env_hasevar a E ->
         a1 # E ->
         a2 # E ->
         typing_check (env_inst_pi
                         E a a1 a2) e (trm_fevar a1) O ->
         app_typing E (trm_fevar a) e (trm_fevar a2) O.

Inductive unify : env -> trm -> trm -> env -> Prop :=
| uni_var : forall E x,
    env_anyvar x E ->
    unify E (trm_fvar x) (trm_fvar x) E
| uni_evarid : forall E a,
    env_anyevar a E ->
    unify E (trm_fevar a) (trm_fevar a) E
| uni_evarlt : forall E a b,
    env_hasevars a b E ->
    unify E (trm_fevar a) (trm_fevar b) (env_inst_trm E b (trm_fevar a))
| uni_evargt : forall E a b,
    env_hasevars a b E ->
    unify E (trm_fevar b) (trm_fevar a) (env_inst_trm E b (trm_fevar a))
| uni_evarty : forall E a t,
    env_hasevar a E ->
    a \notin (fv t) ->
    unify E (trm_fevar a) t (env_inst_trm E a t)
| uni_tyevar : forall E a t,
    env_hasevar a E ->
    a \notin (fv t) ->
    unify E t (trm_fevar a) (env_inst_trm E a t)
| uni_star : forall E,
    unify E trm_star trm_star E
| uni_app : forall E t1 t2 t1' t2' O1 O,
    unify E t2 t2' O1 ->
    unify O1 (env_subst O1 t1) (env_subst O1 t1') O ->
    unify E (trm_app t1 t2) (trm_app t1' t2') O.
(* WIP: cases for ilam, lam, pi, let, castup, castdn, ann *)


