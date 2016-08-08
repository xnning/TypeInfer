Set Implicit Arguments.
Require Import LibLN AlgoDef.

(* Basics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : AExpr => AFv x) in
  let D := gather_vars_with (fun x : AType => ATFv x) in
  let E := gather_vars_with (fun x : ACtx => dom x) in
  constr:(A \u B \u C \u D \u E).

Ltac pick_fresh X :=
  let L := gather_vars in (pick_fresh_gen L X).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.

Ltac exists_fresh := 
  let L := gather_vars_with (fun x : vars => x) in exists L.

Scheme atyping_induct := Induction for ATyping Sort Prop
  with awftyp_induct := Induction for AWfTyp Sort Prop
  with awf_induct := Induction for AWf Sort Prop.

Hint Constructors ARed ATyping AMode AWfTyp AWf AInst AGen
     AUnify AResolveEVar AWTerm.

(** Substitution *)

Hint Constructors ATerm.

(* Substitution on indices is identity on well-formed terms. *)

Lemma aopen_rec_term_core :forall e j v i u, i <> j ->
  AOpenRec j v e = AOpenRec i u (AOpenRec j v e) -> e = AOpenRec i u e.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.  
  case_nat*. case_nat*.
Qed.

Lemma atopen_rec_term_core :forall e j v i u, i <> j ->
  AOpenTypRec j v e = AOpenTypRec i u (AOpenTypRec j v e) -> e = AOpenTypRec i u e.
Proof.
  induction e; introv Neq Equ;
    simpl in *; inversion* Equ; f_equal*.
  apply aopen_rec_term_core with (j := j) (v := v).
  auto. auto.
Qed.

Lemma aopen_rec_term : forall t u,
  ATerm t -> forall k, t = AOpenRec k u t.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds AOpen. pick_fresh x.
   apply* (@aopen_rec_term_core e 0 (AE_FVar x)).
  unfolds AOpen. pick_fresh x.
   apply* (@aopen_rec_term_core t2 0 (AE_FVar x)).
  unfolds AOpen. pick_fresh x.
   apply* (@aopen_rec_term_core e2 0 (AE_FVar x)).
Qed.

Lemma atopen_rec_term : forall t u,
  ATermTy t -> forall k, t = AOpenTypRec k u t.
Proof.
  induction 1; intros; simpl; f_equal*.
  apply* aopen_rec_term.
  unfolds AOpenT. pick_fresh x.
   apply* (@atopen_rec_term_core t 0 (AE_FVar x)).
Qed.

Lemma aopen_var_inj : forall x t1 t2, 
  x \notin (AFv t1) -> x \notin (AFv t2) -> 
  (t1 @ x = t2 @ x) -> (t1 = t2).
Proof.
  intros x t1. unfold AOpen. generalize 0.
  induction t1; intro k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal* 
  | do 2 try case_nat; inversions* H1; try notin_false ].
Qed.

(* Substitution for a fresh name is identity. *)

Lemma asubst_fresh : forall x t u, 
  x \notin AFv t -> ASubst x u t = t.
Proof.
  intros. induction t; simpls; fequals*.
  case_var*. 
Qed.

Lemma atsubst_fresh : forall x t u, 
  x \notin ATFv t -> ATSubst x u t = t.
Proof.
  intros. induction t; simpls; fequals*.
  apply* asubst_fresh.
Qed.

(* Substitution aistributes on the open operation. *)

Lemma asubst_openrec : forall n x u t1 t2, ATerm u -> 
  ASubst x u (AOpenRec n t2 t1) = AOpenRec n (ASubst x u t2) (ASubst x u t1).
Proof.
  intros. gen n.
  induction t1; intros; simpl; f_equal*.
  case_nat*. case_var*. apply* aopen_rec_term.
Qed.

Lemma asubst_open : forall x u t1 t2, ATerm u -> 
  ASubst x u (t1 @@ t2) = (ASubst x u t1) @@ (ASubst x u t2).
Proof.
  intros. apply* asubst_openrec.
Qed.

Lemma atsubst_open : forall x u t1 t2, ATerm u -> 
  ATSubst x u (t1 @@' t2) = (ATSubst x u t1) @@' (ASubst x u t2).
Proof.
  intros. unfold AOpenT. generalize 0.
  induction t1; intros; simpl; f_equal*.
  apply* asubst_openrec.
Qed.

(* Substitution and open_var for aistinct names commute. *)

Lemma asubst_open_var : forall x y u e, y <> x -> ATerm u ->
  (ASubst x u e) @ y = ASubst x u (e @ y).
Proof.
  introv Neq Wu. rewrite* asubst_open.
  simpl. case_var*.
Qed.

Lemma atsubst_open_var : forall x y u e, y <> x -> ATerm u ->
  (ATSubst x u e) @' y = ATSubst x u (e @' y).
Proof.
  introv Neq Wu. rewrite* atsubst_open.
  simpl. case_var*.
Qed.

(* Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma asubst_intro : forall x t u, 
  x \notin (AFv t) -> ATerm u ->
  t @@ u = ASubst x u (t @ x).
Proof.
  introv Fr Wu. rewrite* asubst_open.
  rewrite* asubst_fresh. simpl. case_var*.
Qed.

Lemma atsubst_intro : forall x t u, 
  x \notin (ATFv t) -> ATerm u ->
  t @@' u = ATSubst x u (t @' x).
Proof.
  introv Fr Wu. rewrite* atsubst_open.
  rewrite* atsubst_fresh. simpl. case_var*.
Qed.

(* Tactic to permute subst and open var *)

Ltac cross := 
  rewrite asubst_open_var; try cross.

Tactic Notation "cross" "*" := 
  cross; autos*.

Ltac crosst := 
  rewrite atsubst_open_var; try crosst.

Tactic Notation "crosst" "*" := 
  crosst; autos*.

(** Closedness *)

(* Terms are stable by substitution *)

Lemma asubst_term : forall t z u,
  ATerm u -> ATerm t -> ATerm (ASubst z u t).
Proof.
  induction 2; simple*.
  case_var*.
  apply_fresh* ATerm_Lam as y. rewrite* asubst_open_var.
  apply_fresh* ATerm_Pi as y. rewrite* asubst_open_var.
  apply_fresh* ATerm_Let as y. rewrite* asubst_open_var.
Qed.

Lemma atsubst_term : forall t z u,
  ATerm u -> ATermTy t -> ATermTy (ATSubst z u t).
Proof.
  induction 2; simple*.
  apply* ATermTy_Expr. apply* asubst_term.
  apply_fresh* ATermTy_Forall as y. rewrite* atsubst_open_var.
Qed.

(* Terms are stable by open *)

Lemma aopen_term : forall t u,
  ABody t -> ATerm u -> ATerm (t @@ u).
Proof.
  intros. destruct H. pick_fresh y.
  rewrite* (@asubst_intro y). apply* asubst_term.
Qed.

Lemma aopent_term : forall t u,
  ABodyTy t -> ATerm u -> ATermTy (AOpenT t u).
Proof.
  intros. destruct H. pick_fresh y.
  rewrite* (@atsubst_intro y). apply* atsubst_term.
Qed.

Hint Resolve asubst_term aopen_term atsubst_term aopent_term.

(* Properties of Body *)

Lemma abody_lam : forall e,
  ATerm (AE_Lam e) -> ABody e.
Proof.
  intros. unfold ABody. inversion* H.
Qed.

Lemma abody_pi : forall t1 t2,
  ATerm (AE_Pi t1 t2) -> ABody t2.
Proof.
  intros. unfold ABody. inversion* H.
Qed.

Lemma abody_let : forall e1 e2,
  ATerm (AE_Let e1 e2) -> ABody e2.
Proof.
  intros. unfold ABody. inversion* H.
Qed.

Lemma aterm_pi : forall t1 t2,
  ATerm (AE_Pi t1 t2) -> ATerm t1.
Proof.
  intros. inversion* H.
Qed.

Lemma aterm_let : forall e1 e2,
  ATerm (AE_Let e1 e2) -> ATerm e1.
Proof.
  intros. inversion* H.
Qed.

Lemma atermty_forall : forall e,
  ATermTy (AT_Forall e) -> ABodyTy e.
Proof.
  intros. unfold ABodyTy. inversions* H.
Qed.

Lemma atermty_expr : forall e,
  ATermTy (AT_Expr e) -> ATerm e.
Proof.
  intros. inversions* H.
Qed.

Hint Extern 1 (ATerm ?t) =>
  match goal with
  | H: ATerm (AE_Pi t ?t2) |- _ => apply (@aterm_pi t2)
  | H: ATerm (AE_Let t ?t2) |- _ => apply (@aterm_let t2)
  | H: ATerm (AT_Expr ?t2) |- _ => apply (@atermty_expr t2)
  end.

Hint Extern 3 (ABody ?t) =>
  match goal with 
  | H: context [AE_Lam t] |- _ => apply (@abody_lam)
  | H: context [AE_Pi ?t1 t] |- _ => apply (@abody_pi t1)
  | H: context [AE_Let ?t1 t] |- _ => apply (@abody_let t1)
  end.

Hint Extern 1 (ABody ?t) =>
  match goal with 
  | H: context [t @ _] |- _ =>
      let x := fresh in let Fr := fresh in
      let P := fresh in
      let L := gather_vars in exists L; intros x Fr; 
      lets P: H x __; [ notin_solve 
                      | try destructs P ]
  end.

Hint Extern 3 (ABodyTy ?t) =>
  match goal with 
  | H: context [AT_Forall t] |- _ => apply (@atermty_forall)
  end.

Hint Extern 1 (ABodyTy ?t) =>
  match goal with 
  | H: context [t @' _] |- _ =>
      let x := fresh in let Fr := fresh in
      let P := fresh in
      let L := gather_vars in exists L; intros x Fr; 
      lets P: H x __; [ notin_solve 
                      | try destructs P ]
  end.


Lemma aterm_lam_prove : forall e,
  ABody e -> ATerm (AE_Lam e).
Proof.
  intros. apply_fresh* ATerm_Lam as x.
Qed.

Lemma aterm_pi_prove : forall t1 t2,
  ATerm t1 -> ABody t2 -> ATerm (AE_Pi t1 t2).
Proof.
  intros. apply_fresh* ATerm_Pi as x.
Qed.

Lemma aterm_let_prove : forall e1 e2,
  ATerm e1 -> ABody e2 -> ATerm (AE_Let e1 e2).
Proof.
  intros. apply_fresh* ATerm_Let as x.
Qed.

Lemma atermty_forall_prove : forall s,
  ABodyTy s -> ATermTy (AT_Forall s).
Proof.
  intros. apply_fresh* ATermTy_Forall as x.
Qed.

Lemma atermty_expr_prove : forall e,
    ATerm e -> ATermTy (AT_Expr e).
Proof.
  intros. apply* ATermTy_Expr.
Qed.

Hint Resolve aterm_lam_prove
     aterm_pi_prove aterm_let_prove
     atermty_forall_prove atermty_expr_prove.

Lemma abody_prove : forall L t,
  (forall x, x \notin L -> ATerm (t @ x)) -> ABody t.
Proof.
  intros. exists* L.
Qed.

Hint Extern 1 (ABody ?t) =>
  match goal with 
  | H: forall _, _ \notin ?L -> ATerm (t @ _)  |- _ =>
    apply (@abody_prove L)
  end. 

Lemma abody_subst : forall x t u,
  ATerm u -> ABody t -> ABody (ASubst x u t).
Proof.
  introv. intros Wu [L Bt].
  exists (\{x} \u L). intros y Fr. cross*.
Qed.

Hint Resolve abody_subst.

Lemma abodyty_prove : forall L t,
  (forall x, x \notin L -> ATermTy (t @' x)) -> ABodyTy t.
Proof.
  intros. exists* L.
Qed.

Hint Extern 1 (ABodyTy ?t) =>
  match goal with 
  | H: forall _, _ \notin ?L -> ATermTy (t @' _)  |- _ =>
    apply (@abodyty_prove L)
  end.

Lemma abodyty_subst : forall x t u,
  ATerm u -> ABodyTy t -> ABodyTy (ATSubst x u t).
Proof.
  introv. intros Wu [L Bt].
  exists (\{x} \u L). intros y Fr. crosst*.
Qed.

Hint Resolve abodyty_subst.

(** Regularity *)

Lemma ared_regular : forall t t', ARed t t' -> ATerm t /\ ATerm t'.
Proof.
  intros_all. induction* H.
  split*. apply* aopen_term.
  apply* aterm_let.
Qed.

Hint Extern 1 (ATerm ?t) => match goal with
  | H: ARed t _ |- _ => apply (proj1 (ared_regular H))
  | H: ARed _ t |- _ => apply (proj2 (ared_regular H))
  end.

Hint Extern 1 (ATerm (AE_Lam (ASubst ?x ?u ?t2))) =>
  match goal with H: ATerm (AE_Lam t2) |- _ => 
  unsimpl (ASubst x u (AE_Lam t2)) end.

Hint Extern 1 (ATerm (AE_Pi (ASubst ?x ?u ?t1) (ASubst ?x ?u ?t2))) =>
  match goal with H: ATerm (AE_Pi t1 t2) |- _ => 
  unsimpl (ASubst x u (AE_Pi t1 t2)) end.

Hint Extern 1 (ATerm (AE_Let (ASubst ?x ?u ?t1) (ASubst ?x ?u ?t2))) =>
  match goal with H: ATerm (AE_Let t1 t2) |- _ => 
  unsimpl (ASubst x u (AE_Let t1 t2)) end.

Hint Extern 1 (ATermTy (AT_Forall (ATSubst ?x ?u ?t2))) =>
  match goal with H: ATermTy (AT_Forall t2) |- _ => 
  unsimpl (ATSubst x u (AT_Forall t2)) end.

Definition regular_actx (E : ACtx) :=
  (exists H, AWf E H) /\ ok E /\
  (forall x U, binds x (AC_Typ U) E -> ATerm U) /\
  (forall x T U, binds x (AC_Bnd T U) E -> ATermTy T /\ ATerm U) /\
  (forall x T, binds x (AC_Solved_EVar T) E -> ATerm T).

