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
| term_ann : forall e t, term e -> term t -> term (trm_ann e t).

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

Fixpoint env_subst (E : env) (e : trm) {struct E} : trm :=
  match E with
  | nil => e
  | (x',t') :: E' =>
    env_subst E' (match t' with
                 | env_var => e
                 | env_varbnd _ => e
                 | env_evar => e
                 | env_evardef e' => [x' ~> e'] e
                 end)
  end.

Inductive wf_term : env -> trm -> Prop :=
| wf_term_var : forall E x,
    binds x env_var E ->
    wf_term E (trm_fvar x)
| wf_term_varbnd : forall E x t,
    binds x (env_varbnd t) E ->
    wf_term E (trm_fvar x)
| wf_term_evar : forall E a,
    binds a env_evar E ->
    wf_term E (trm_fevar a)
| wf_term_star : forall E, wf_term E trm_star
| wf_term_app : forall E e1 e2,
    wf_term E e1 -> wf_term E e2 -> wf_term E (trm_app e1 e2)
| wf_term_lam : forall L E t e, 
    wf_term E t ->
    (forall x, x \notin L -> wf_term E (e ^ x)) ->
    wf_term E (trm_lam t e)
| wf_term_ilam : forall L E e, 
    (forall x, x \notin L -> wf_term E (e ^ x)) ->
    wf_term E (trm_ilam e)
| wf_term_pi : forall L E t1 t2, 
    wf_term E t1 ->
    (forall x, x \notin L -> wf_term E (t2 ^ x)) ->
    wf_term E (trm_pi t1 t2)
| wf_term_let : forall L E e1 e2, 
    wf_term E e1 ->
    (forall x, x \notin L -> wf_term E (e2 ^ x)) ->
    wf_term E (trm_let e1 e2)
| wf_term_castup : forall E e, wf_term E e -> wf_term E (trm_castup e)
| wf_term_castdn : forall E e, wf_term E e -> wf_term E (trm_castdn e)
| wf_term_ann : forall E e t, wf_term E e -> wf_term E t -> wf_term E (trm_ann e t).

Inductive unify : env -> trm -> trm -> env -> Prop :=
| uni_refl : forall E e O,
    unify E e e O
| uni_var : forall E x,
    binds x env_var E ->
    unify E (trm_fvar x) (trm_fvar x) E
| uni_varbnd : forall E x t,
    binds x (env_varbnd t) E ->
    unify E (trm_fvar x) (trm_fvar x) E
| uni_evarid : forall E a,
    binds a env_evar E ->
    unify E (trm_fevar a) (trm_fevar a) E
| uni_evarlt : forall E1 a E2 b E3,
    unify (E1 & a ~ env_evar & E2 & b ~ env_evar & E3)
          (trm_fevar a) (trm_fevar b)
          (E1 & a ~ env_evar & E2 & b ~ env_evardef (trm_fevar a) & E3)
| uni_evargt : forall E1 a E2 b E3,
    unify (E1 & a ~ env_evar & E2 & b ~ env_evar & E3)
          (trm_fevar b) (trm_fevar a)
          (E1 & a ~ env_evar & E2 & b ~ env_evardef (trm_fevar a) & E3)
| uni_evarty : forall E1 a E2 t,
    wf_term E1 t ->
    a \notin (fv t) ->
    unify (E1 & a ~ env_evar & E2)
          (trm_fevar a) t
          (E1 & a ~ env_evardef t & E2)
| uni_tyevar : forall E1 a E2 t,
    wf_term E1 t ->
    a \notin (fv t) ->
    unify (E1 & a ~ env_evar & E2)
          t (trm_fevar a)
          (E1 & a ~ env_evardef t & E2)
| uni_star : forall E,
    unify E trm_star trm_star E
| uni_app : forall E t1 t2 t1' t2' O1 O,
    unify E t2 t2' O1 ->
    unify O1 (env_subst O1 t1) (env_subst O1 t1') O ->
    unify E (trm_app t1 t2) (trm_app t1' t2') O
| uni_lam : forall L E t t' O D,
    (forall x,
        x \notin L ->
        unify (E & x ~ env_var) t t'
              (O & x ~ env_var & D)) ->
    unify E (trm_ilam t) (trm_ilam t') O
| uni_lamann : forall L E t1 t2 t1' t2' O D,
    (forall x,
        x \notin L ->
        unify (E & x ~ env_varbnd t1) t2 t2'
              (O & x ~ env_varbnd t1' & D)) ->
    unify E (trm_lam t1 t2) (trm_lam t1' t2') O
| uni_pi : forall L E t1 t2 t1' t2' O O1 D,
    unify E t1' t1 O1 ->
    (forall x,
        x \notin L ->
        unify (O1 & x ~ env_varbnd t1)
              (env_subst O1 t2) (env_subst O1 t2')
              (O & x ~ env_varbnd t1' & D)) ->
    unify E (trm_pi t1 t2) (trm_pi t1' t2') O
| uni_let : forall L E t1 t2 t1' t2' O O1 D,
    unify E t1 t1' O1 ->
    (forall x,
        x \notin L ->
        unify (O1 & x ~ env_var)
              (env_subst O1 t2) (env_subst O1 t2')
              (O & x ~ env_var & D)) ->
    unify E (trm_let t1 t2) (trm_let t1' t2') O
| uni_castup : forall E t t' O,
    unify E t t' O ->
    unify E (trm_castup t) (trm_castup t') O
| uni_castdn : forall E t t' O,
    unify E t t' O ->
    unify E (trm_castdn t) (trm_castdn t') O
| uni_ann : forall E e t e' t' O O1,
    unify E t t' O1 ->
    unify O1
          (env_subst O1 e) (env_subst O1 e')
          O ->
    unify E (trm_ann e t) (trm_ann e' t') O.

Inductive typing_wf : env -> Prop :=
| wf_nil : typing_wf empty
| wf_var : forall E x,
    x # E ->
    typing_wf (E & x ~ env_var)
| wf_varbnd : forall E x t,
    x # E ->
    typing_wf (E & x ~ (env_varbnd t))
| wf_evar : forall E x,
    x # E ->
    typing_wf (E & x ~ env_evar)
| wf_evardef : forall E x e,
    x # E ->
    typing_wf (E & x ~ (env_evardef e)).

Inductive typing_infer : env -> trm -> trm -> env -> Prop :=
| typing_star : forall E,
    typing_wf E ->
    typing_infer E trm_star trm_star E
| typing_var : forall E x t,
    typing_wf E ->
    binds x (env_varbnd t) E ->
    typing_infer E (trm_fvar x) t E
| typing_evar : forall E x,
    typing_wf E ->
    binds x env_evar E ->
    typing_infer E (trm_fevar x) trm_star E
| typing_evardef : forall E x,
    typing_wf E ->
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
| typing_pi : forall L E t1 t2 O O1 D,
    typing_check E t1 trm_star O1 ->
    (forall x,
        x \notin L ->
        typing_check (O1 & x ~ (env_varbnd t1))
                     t2 trm_star (O & (x ~ env_varbnd t1) & D)) ->
    typing_infer E (trm_pi t1 t2) trm_star O
| typing_letinfer : forall E e1 e2 t1 t2 O O1,
    typing_infer E e1 t1 O1 ->
    typing_infer E (e2 ^^ e1) t2 O ->
    typing_infer E (trm_let e1 e2) t2 O
| typing_castdn : forall E e t1 t2 O,
    typing_infer E e t1 O ->
    reduct (env_subst O t1) t2 ->
    typing_infer E (trm_castdn e) t2 O
| typing_ann : forall E e t O1 O,
    typing_check E t trm_star O1 ->
    typing_check O1 e t O ->
    typing_infer E (trm_ann e t) t O
                 
with typing_check : env -> trm -> trm -> env -> Prop :=
     | typing_lamcheck : forall L E e t1 t2 O1 O D,
         typing_check E (trm_pi t1 t2) trm_star O1 ->
         (forall x, x \notin L ->
                    typing_check (E & x ~ (env_varbnd t1))
                                 (e ^ x)
                                 (t2 ^ x)
                                 (O & (x ~ (env_varbnd t1)) & D)) ->
         typing_check E (trm_ilam e) (trm_pi t1 t2) O
     | typing_letcheck : forall E e1 e2 t1 t2 O O1,
         typing_infer E e1 t1 O1 ->
         typing_check E (e2 ^^ e1) t2 O ->
         typing_check E (trm_let e1 e2) t2 O
     | typing_castup : forall E e t1 t2 O,
         reduct (env_subst E t2) t1 ->
         typing_check E e t1 O ->
         typing_check E (trm_castup e) t2 O
     | typing_sub : forall E e t1 t2 O1 O,
         typing_infer E e t1 O1 ->
         unify O1 (env_subst O1 t1) (env_subst O1 t2) O ->
         typing_check E e t2 O
           
with app_typing : env -> trm -> trm -> trm -> env -> Prop :=
     | appty_pi : forall E e t1 t2 O,
         typing_check E e t1 O ->
         app_typing E (trm_pi t1 t2) e t2 O
     | appty_evar : forall E1 a E2 a1 a2 e O,
         typing_check (E1 & a2 ~ env_evar & a1 ~ env_evar &
                       a ~ env_evardef
                         (trm_pi (trm_fevar a1) (trm_fevar a2)) & E2)
                      e (trm_fevar a1) O ->
         app_typing (E1 & a ~ env_evar & E2)
                    (trm_fevar a) e (trm_fevar a2) O.

Inductive dtyping_wf : env -> Prop :=
| dwf_nil : dtyping_wf empty
| dwf_var : forall E x t,
    x # E ->
    dtyping_wf (E & x ~ (env_varbnd t)).

Inductive dtyping : env -> trm -> trm -> Prop :=
| dtyping_star : forall E,
    dtyping_wf E ->
    dtyping E trm_star trm_star
| dtyping_var : forall E x t,
    dtyping_wf E ->
    binds x (env_varbnd t) E ->
    dtyping E (trm_fvar x) t
| dtyping_app : forall E e1 e2 t1 t2,
    dtyping E e1 (trm_pi t1 t2) ->
    dtyping E e2 t1 ->
    dtyping E (trm_app e1 e2) (t2 ^^ e2)
| dtyping_lam : forall L E e t1 t2,
    (forall x, x \notin L ->
               dtyping (E & x ~ env_varbnd t1) e t2) ->
    dtyping E (trm_ilam e) (trm_pi t1 t2)
| dtyping_lamann : forall L E e t1 t2,
    dtyping E t1 trm_star ->
    (forall x, x \notin L ->
               dtyping (E & x ~ env_varbnd t1) e t2) ->
    dtyping E (trm_lam t1 e) (trm_pi t1 t2)
| dtyping_pi : forall L E t1 t2,
    dtyping E t1 trm_star ->
    (forall x, x \notin L ->
               dtyping (E & x ~ env_varbnd t1) t2 trm_star) ->
    dtyping E (trm_pi t1 t2) trm_star
| dtyping_let : forall E e1 e2 t1 t2,
    dtyping E e1 t1 ->
    dtyping E (e2 ^^ e1) t2 ->
    dtyping E (trm_let e1 e2) t2
| dtyping_castup : forall E e t1 t2,
    dtyping E e t1 ->
    reduct t2 t1 ->
    dtyping E (trm_castup e) t2
| dtyping_castdn : forall E e t1 t2,
    dtyping E e t1 ->
    reduct t1 t2 ->
    dtyping E (trm_castdn e) t2.

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : trm => fv x) in
  let D := gather_vars_with (fun x : env => dom x) in
  constr:(A \u B \u C \u D).

Ltac pick_fresh X :=
  let L := gather_vars in (pick_fresh_gen L X).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.
Lemma dwf_to_wf : forall E,
    dtyping_wf E -> typing_wf E.
Proof.
  intros. induction H.
  exact wf_nil. exact (wf_varbnd t H).
Qed.

Lemma typing_inf_to_chk : forall E e t O,
    typing_infer E e t O ->
    typing_check E e t O.
Proof.
  intros. exact (typing_sub t H (uni_refl O (env_subst O t) O)).
Qed.

Lemma completeness : forall E e t,
    dtyping E e t ->
    exists O t', typing_infer E e t' O /\
                 (t' = t \/ env_subst O t' = t).
Proof.
  intros. induction H.

  (* Case Star *)
  exists E. exists trm_star.
  split. exact (typing_star (dwf_to_wf H)).
  left. trivial.
  
  (* Case Var *)
  exists E. exists t.
  split. exact (typing_var (dwf_to_wf H) H0).
  left. trivial.

  (* Case App *)
  admit.

  (* Case ILam *)
  admit.

  (* Case Lam *)
  exists E. exists (trm_pi t1 t2).
  split. destruct IHdtyping. destruct H2. destruct H2. destruct H3.
  rewrite H3 in H2.
  assert (P1 := typing_inf_to_chk H2).
  pick_fresh_gen L x'.
  assert (H1' := H1 x' Fr).
  destruct H1'.
  destruct H4.
  destruct H4.
  destruct H5.
  rewrite H5 in H4.
  assert (H6 := fun x1 => fun (Fr : x1 \notin L) => H4).
Qed.

Section SubstProperties.

Hint Constructors term.

(** Substitution on indices is identity on well-formed terms. *)

Lemma open_rec_term_core :forall e j v i u, i <> j ->
  {j ~> v}e = {i ~> u}({j ~> v}e) -> e = {i ~> u}e.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.  
  case_nat*. case_nat*. case_nat*. case_nat*.
Qed.

Lemma open_rec_term : forall t u,
  term t -> forall k, t = {k ~> u}t.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds open. pick_fresh x.
  apply* (@open_rec_term_core e 0 (trm_fvar x)).
  unfolds open. pick_fresh x. 
  apply* (@open_rec_term_core e 0 (trm_fvar x)).
  unfolds open. pick_fresh x.
  apply* (@open_rec_term_core t2 0 (trm_fvar x)).
  unfolds open. pick_fresh x.
  apply* (@open_rec_term_core e2 0 (trm_fvar x)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_fresh : forall x t u, 
  x \notin fv t -> [x ~> u] t = t.
Proof.
  intros. induction t; simpls; fequals*.
  case_var*. case_var*. 
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_open : forall x u t1 t2, term u -> 
  [x ~> u] (t1 ^^ t2) = ([x ~> u]t1) ^^ ([x ~> u]t2).
Proof.
  intros. unfold open. generalize 0.
  induction t1; intros; simpl; f_equal*.
  case_nat*. case_var*. apply* open_rec_term.
  case_nat*. case_var*. apply* open_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_open_var : forall x y u e, y <> x -> term u ->
  ([x ~> u]e) ^ y = [x ~> u] (e ^ y).
Proof.
  introv Neq Wu. rewrite* subst_open.
  simpl. case_var*.
Qed.

(** Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_intro : forall x t u, 
  x \notin (fv t) -> term u ->
  t ^^ u = [x ~> u](t ^ x).
Proof.
  introv Fr Wu. rewrite* subst_open.
  rewrite* subst_fresh. simpl. case_var*.
Qed.

End SubstProperties.
