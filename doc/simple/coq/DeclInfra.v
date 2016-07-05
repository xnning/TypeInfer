Set Implicit Arguments.
Require Import LibLN DeclDef.

(* Basics *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : DExpr => DFv x) in
  let D := gather_vars_with (fun x : DType => DTFv x) in
  let E := gather_vars_with (fun x : DCtx => dom x) in
  constr:(A \u B \u C \u D \u E).

Ltac pick_fresh X :=
  let L := gather_vars in (pick_fresh_gen L X).

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.

Ltac exists_fresh := 
  let L := gather_vars_with (fun x : vars => x) in exists L.

Scheme dtypingi_induct := Induction for DTypingI Sort Prop
  with dtypingc_induct := Induction for DTypingC Sort Prop
  with dwftyp_induct := Induction for DWfTyp Sort Prop
  with dwf_induct := Induction for DWf Sort Prop
  with dinst_induct := Induction for DInst Sort Prop
  with dgen_induct := Induction for DGen Sort Prop.

Hint Constructors DRed DTypingI DTypingC DWfTyp DWf DInst DGen.

(** Substitution *)

Hint Constructors DTerm.

(* Substitution on indices is identity on well-formed terms. *)

Lemma dopen_rec_term_core :forall e j v i u, i <> j ->
  DOpenRec j v e = DOpenRec i u (DOpenRec j v e) -> e = DOpenRec i u e.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.  
  case_nat*. case_nat*.
Qed.

Lemma dtopen_rec_term_core :forall e j v i u, i <> j ->
  DOpenTypRec j v e = DOpenTypRec i u (DOpenTypRec j v e) -> e = DOpenTypRec i u e.
Proof.
  induction e; introv Neq Equ;
    simpl in *; inversion* Equ; f_equal*.
  apply dopen_rec_term_core with (j := j) (v := v).
  auto. auto.
Qed.

Lemma dopen_rec_term : forall t u,
  DTerm t -> forall k, t = DOpenRec k u t.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds DOpen. pick_fresh x.
   apply* (@dopen_rec_term_core e 0 (DE_FVar x)).
  unfolds DOpen. pick_fresh x.
   apply* (@dopen_rec_term_core t2 0 (DE_FVar x)).
  unfolds DOpen. pick_fresh x.
   apply* (@dopen_rec_term_core e2 0 (DE_FVar x)).
Qed.

Lemma dtopen_rec_term : forall t u,
  DTermTy t -> forall k, t = DOpenTypRec k u t.
Proof.
  induction 1; intros; simpl; f_equal*.
  apply* dopen_rec_term.
  unfolds DOpenT. pick_fresh x.
   apply* (@dtopen_rec_term_core t 0 (DE_FVar x)).
Qed.

Lemma dopen_var_inj : forall x t1 t2, 
  x \notin (DFv t1) -> x \notin (DFv t2) -> 
  (t1 ^ x = t2 ^ x) -> (t1 = t2).
Proof.
  intros x t1. unfold DOpen. generalize 0.
  induction t1; intro k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal* 
  | do 2 try case_nat; inversions* H1; try notin_false ].
Qed.

(* Substitution for a fresh name is identity. *)

Lemma dsubst_fresh : forall x t u, 
  x \notin DFv t -> DSubst x u t = t.
Proof.
  intros. induction t; simpls; fequals*.
  case_var*. 
Qed.

Lemma dtsubst_fresh : forall x t u, 
  x \notin DTFv t -> DTSubst x u t = t.
Proof.
  intros. induction t; simpls; fequals*.
  apply* dsubst_fresh.
Qed.

(* Substitution distributes on the open operation. *)

Lemma dsubst_openrec : forall n x u t1 t2, DTerm u -> 
  DSubst x u (DOpenRec n t2 t1) = DOpenRec n (DSubst x u t2) (DSubst x u t1).
Proof.
  intros. gen n.
  induction t1; intros; simpl; f_equal*.
  case_nat*. case_var*. apply* dopen_rec_term.
Qed.

Lemma dsubst_open : forall x u t1 t2, DTerm u -> 
  DSubst x u (t1 ^^ t2) = (DSubst x u t1) ^^ (DSubst x u t2).
Proof.
  intros. apply* dsubst_openrec.
Qed.

Lemma dtsubst_open : forall x u t1 t2, DTerm u -> 
  DTSubst x u (t1 ^^' t2) = (DTSubst x u t1) ^^' (DSubst x u t2).
Proof.
  intros. unfold DOpenT. generalize 0.
  induction t1; intros; simpl; f_equal*.
  apply* dsubst_openrec.
Qed.

(* Substitution and open_var for distinct names commute. *)

Lemma dsubst_open_var : forall x y u e, y <> x -> DTerm u ->
  (DSubst x u e) ^ y = DSubst x u (e ^ y).
Proof.
  introv Neq Wu. rewrite* dsubst_open.
  simpl. case_var*.
Qed.

Lemma dtsubst_open_var : forall x y u e, y <> x -> DTerm u ->
  (DTSubst x u e) ^' y = DTSubst x u (e ^' y).
Proof.
  introv Neq Wu. rewrite* dtsubst_open.
  simpl. case_var*.
Qed.

(* Opening up an abstraction of body t with a term u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma dsubst_intro : forall x t u, 
  x \notin (DFv t) -> DTerm u ->
  t ^^ u = DSubst x u (t ^ x).
Proof.
  introv Fr Wu. rewrite* dsubst_open.
  rewrite* dsubst_fresh. simpl. case_var*.
Qed.

Lemma dtsubst_intro : forall x t u, 
  x \notin (DTFv t) -> DTerm u ->
  t ^^' u = DTSubst x u (t ^' x).
Proof.
  introv Fr Wu. rewrite* dtsubst_open.
  rewrite* dtsubst_fresh. simpl. case_var*.
Qed.

(* Tactic to permute subst and open var *)

Ltac cross := 
  rewrite dsubst_open_var; try cross.

Tactic Notation "cross" "*" := 
  cross; autos*.

Ltac crosst := 
  rewrite dtsubst_open_var; try crosst.

Tactic Notation "crosst" "*" := 
  crosst; autos*.

(** Closedness *)

(* Terms are stable by substitution *)

Lemma dsubst_term : forall t z u,
  DTerm u -> DTerm t -> DTerm (DSubst z u t).
Proof.
  induction 2; simple*.
  case_var*.
  apply_fresh* DTerm_Lam as y. rewrite* dsubst_open_var.
  apply_fresh* DTerm_Pi as y. rewrite* dsubst_open_var.
  apply_fresh* DTerm_Let as y. rewrite* dsubst_open_var.
Qed.

Lemma dtsubst_term : forall t z u,
  DTerm u -> DTermTy t -> DTermTy (DTSubst z u t).
Proof.
  induction 2; simple*.
  apply* DTermTy_Expr. apply* dsubst_term.
  apply_fresh* DTermTy_Forall as y. rewrite* dtsubst_open_var.
Qed.

(* Terms are stable by open *)

Lemma dopen_term : forall t u,
  DBody t -> DTerm u -> DTerm (t ^^ u).
Proof.
  intros. destruct H. pick_fresh y.
  rewrite* (@dsubst_intro y). apply* dsubst_term.
Qed.

Lemma dopent_term : forall t u,
  DBodyTy t -> DTerm u -> DTermTy (DOpenT t u).
Proof.
  intros. destruct H. pick_fresh y.
  rewrite* (@dtsubst_intro y). apply* dtsubst_term.
Qed.

Hint Resolve dsubst_term dopen_term dtsubst_term dopent_term.

(* Properties of Body *)

Lemma dbody_lam : forall e,
  DTerm (DE_Lam e) -> DBody e.
Proof.
  intros. unfold DBody. inversion* H.
Qed.

Lemma dbody_pi : forall t1 t2,
  DTerm (DE_Pi t1 t2) -> DBody t2.
Proof.
  intros. unfold DBody. inversion* H.
Qed.

Lemma dbody_let : forall e1 e2,
  DTerm (DE_Let e1 e2) -> DBody e2.
Proof.
  intros. unfold DBody. inversion* H.
Qed.

Lemma dterm_pi : forall t1 t2,
  DTerm (DE_Pi t1 t2) -> DTerm t1.
Proof.
  intros. inversion* H.
Qed.

Lemma dterm_let : forall e1 e2,
  DTerm (DE_Let e1 e2) -> DTerm e1.
Proof.
  intros. inversion* H.
Qed.

Lemma dtermty_forall : forall e,
  DTermTy (DT_Forall e) -> DBodyTy e.
Proof.
  intros. unfold DBodyTy. inversions* H.
Qed.

Lemma dtermty_expr : forall e,
  DTermTy (DT_Expr e) -> DTerm e.
Proof.
  intros. inversions* H.
Qed.

Hint Extern 1 (DTerm ?t) =>
  match goal with
  | H: DTerm (DE_Pi t ?t2) |- _ => apply (@dterm_pi t2)
  | H: DTerm (DE_Let t ?t2) |- _ => apply (@dterm_let t2)
  | H: DTerm (DT_Expr ?t2) |- _ => apply (@dtermty_expr t2)
  end.

Hint Extern 3 (DBody ?t) =>
  match goal with 
  | H: context [DE_Lam t] |- _ => apply (@dbody_lam)
  | H: context [DE_Pi ?t1 t] |- _ => apply (@dbody_pi t1)
  | H: context [DE_Let ?t1 t] |- _ => apply (@dbody_let t1)
  end.

Hint Extern 1 (DBody ?t) =>
  match goal with 
  | H: context [t ^ _] |- _ =>
      let x := fresh in let Fr := fresh in
      let P := fresh in
      let L := gather_vars in exists L; intros x Fr; 
      lets P: H x __; [ notin_solve 
                      | try destructs P ]
  end.

Hint Extern 3 (DBodyTy ?t) =>
  match goal with 
  | H: context [DT_Forall t] |- _ => apply (@dtermty_forall)
  end.

Hint Extern 1 (DBodyTy ?t) =>
  match goal with 
  | H: context [t ^' _] |- _ =>
      let x := fresh in let Fr := fresh in
      let P := fresh in
      let L := gather_vars in exists L; intros x Fr; 
      lets P: H x __; [ notin_solve 
                      | try destructs P ]
  end.


Lemma dterm_lam_prove : forall e,
  DBody e -> DTerm (DE_Lam e).
Proof.
  intros. apply_fresh* DTerm_Lam as x.
Qed.

Lemma dterm_pi_prove : forall t1 t2,
  DTerm t1 -> DBody t2 -> DTerm (DE_Pi t1 t2).
Proof.
  intros. apply_fresh* DTerm_Pi as x.
Qed.

Lemma dterm_let_prove : forall e1 e2,
  DTerm e1 -> DBody e2 -> DTerm (DE_Let e1 e2).
Proof.
  intros. apply_fresh* DTerm_Let as x.
Qed.

Lemma dtermty_forall_prove : forall s,
  DBodyTy s -> DTermTy (DT_Forall s).
Proof.
  intros. apply_fresh* DTermTy_Forall as x.
Qed.

Lemma dtermty_expr_prove : forall e,
    DTerm e -> DTermTy (DT_Expr e).
Proof.
  intros. apply* DTermTy_Expr.
Qed.

Hint Resolve dterm_lam_prove
     dterm_pi_prove dterm_let_prove
     dtermty_forall_prove dtermty_expr_prove.

Lemma dbody_prove : forall L t,
  (forall x, x \notin L -> DTerm (t ^ x)) -> DBody t.
Proof.
  intros. exists* L.
Qed.

Hint Extern 1 (DBody ?t) =>
  match goal with 
  | H: forall _, _ \notin ?L -> DTerm (t ^ _)  |- _ =>
    apply (@dbody_prove L)
  end. 

Lemma dbody_subst : forall x t u,
  DTerm u -> DBody t -> DBody (DSubst x u t).
Proof.
  introv. intros Wu [L Bt].
  exists (\{x} \u L). intros y Fr. cross*.
Qed.

Hint Resolve dbody_subst.

Lemma dbodyty_prove : forall L t,
  (forall x, x \notin L -> DTermTy (t ^' x)) -> DBodyTy t.
Proof.
  intros. exists* L.
Qed.

Hint Extern 1 (DBodyTy ?t) =>
  match goal with 
  | H: forall _, _ \notin ?L -> DTermTy (t ^' _)  |- _ =>
    apply (@dbodyty_prove L)
  end.

Lemma dbodyty_subst : forall x t u,
  DTerm u -> DBodyTy t -> DBodyTy (DTSubst x u t).
Proof.
  introv. intros Wu [L Bt].
  exists (\{x} \u L). intros y Fr. crosst*.
Qed.

Hint Resolve dbodyty_subst.

(** Regularity *)

Lemma dred_regular : forall t t', DRed t t' -> DTerm t /\ DTerm t'.
Proof.
  intros_all. induction* H.
  split*. apply* dopen_term.
  apply* dterm_let.
Qed.

Hint Extern 1 (DTerm ?t) => match goal with
  | H: DRed t _ |- _ => apply (proj1 (dred_regular H))
  | H: DRed _ t |- _ => apply (proj2 (dred_regular H))
  end.

Hint Extern 1 (DTerm (DE_Lam (DSubst ?x ?u ?t2))) =>
  match goal with H: DTerm (DE_Lam t2) |- _ => 
  unsimpl (DSubst x u (DE_Lam t2)) end.

Hint Extern 1 (DTerm (DE_Pi (DSubst ?x ?u ?t1) (DSubst ?x ?u ?t2))) =>
  match goal with H: DTerm (DE_Pi t1 t2) |- _ => 
  unsimpl (DSubst x u (DE_Pi t1 t2)) end.

Hint Extern 1 (DTerm (DE_Let (DSubst ?x ?u ?t1) (DSubst ?x ?u ?t2))) =>
  match goal with H: DTerm (DE_Let t1 t2) |- _ => 
  unsimpl (DSubst x u (DE_Let t1 t2)) end.

Hint Extern 1 (DTermTy (DT_Forall (DTSubst ?x ?u ?t2))) =>
  match goal with H: DTermTy (DT_Forall t2) |- _ => 
  unsimpl (DTSubst x u (DT_Forall t2)) end.

Definition contains_terms (E : DCtx) :=
  (forall x U, binds x (DC_Typ U) E -> DTerm U) /\
  (forall x T U, binds x (DC_Bnd T U) E -> DTermTy T /\ DTerm U).

Lemma regular_dtypingi : forall E t T, DTypingI E t T ->
  (DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTerm T)
with regular_dtypingc : forall E t T, DTypingC E t T ->
  (DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTerm T)
with regular_dinst : forall E s t, DInst E s t ->
  (DWf E /\ ok E /\ contains_terms E /\ DTermTy s /\ DTerm t)
with regular_dgen : forall E s t, DGen E t s ->
  (DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTermTy s)
with regular_dwftyp : forall E t, DWfTyp E t ->
  (DWf E /\ ok E /\ contains_terms E /\ DTermTy t).
Proof.
  apply dtypingi_induct with
  (P0 := fun E t T (_ : DTypingC E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTerm T)
  (P1 := fun E t (_ : DWfTyp E t) => DWf E /\ ok E /\ contains_terms E /\ DTermTy t)
  (P2 := fun E (_ : DWf E) => ok E /\ contains_terms E)
  (P3 := fun E t T (_ : DInst E t T) => DWf E /\ ok E /\ contains_terms E /\ DTermTy t /\ DTerm T)
  (P4 := fun E t T(_ : DGen E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTermTy T); 
    unfolds contains_terms; intros; splits*.
  
  pick_fresh x. assert (x \notin L) by auto.
  destruct (H x H0) as [H1 [_ [_ _]]].
  inversion* H1. false* empty_push_inv.
  destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*.

  pick_fresh x. assert (x \notin L) by auto.
  destruct~ (H x H0) as [_ [H1 [_ _]]].
  
  (* WIP *)
Admitted.

