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

Scheme dtyping_induct := Induction for DTyping Sort Prop
  with dwftyp_induct := Induction for DWfTyp Sort Prop
  with dwf_induct := Induction for DWf Sort Prop
  with dinst_induct := Induction for DInst Sort Prop
  with dgen_induct := Induction for DGen Sort Prop.

Hint Constructors DRed DTyping DMode DWfTyp DWf DInst DGen.

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

Lemma notin_dopen_inv : forall x y n e,
    x \notin DFv e ->
    x \notin DFv y ->
    x \notin DFv (DOpenRec n y e).
Proof.
  introv notin neq.
  gen n. induction e; introv; simpls; auto.
  case_if. auto. simpl.  auto.
Qed.

Lemma notin_dopen : forall x y e n,
    x \notin (DFv (DOpenRec n y e)) ->
    x \notin (DFv e).
Proof.
  introv notin. gen n.
  induction e; introv notin; try(simpl in *; auto);
    try(
  apply notin_union in notin;
  destruct notin as [notin1 notin2];
  apply IHe1 in notin1;
  apply IHe2 in notin2;
  auto);
    try(apply IHe in notin; auto).
Qed.

Lemma dopen_reorder: forall e1 e2 i j e,
    DTerm e1 ->
    DTerm e2 ->
    i <> j ->
    DOpenRec i e1 (DOpenRec j e2 e) = DOpenRec j e2 (DOpenRec i e1 e).
Proof.
  introv te1 te2 neq.
  gen i j. induction e; introv neq; simpls; auto; try(solve[f_equal ~]).
  case_nat~. case_nat~. simpls. case_if~. symmetry. apply~ dopen_rec_term.
  case_nat~. simpls. case_if~. apply~ dopen_rec_term.
  simpls. case_if~. case_if~.
Qed.

Lemma dopent_reorder: forall e1 e2 i j e,
    DTerm e1 ->
    DTerm e2 ->
    i <> j ->
    DOpenTypRec i e1 (DOpenTypRec j e2 e) = DOpenTypRec j e2 (DOpenTypRec i e1 e).
Proof.
  introv te1 te2 neq.
  gen i j. induction e; introv neq; simpls; auto; try(solve[f_equal ~]).
  f_equal. apply~ dopen_reorder.
Qed.

Lemma dopen_fv: forall n s y,
    DTerm (DOpenRec n (DE_FVar y) s) ->
    y \notin DFv (DOpenRec n (DE_FVar y) s) ->
    DTerm s.
Proof.
  unfold DOpen.
  introv dt.
  gen_eq s2 : (DOpenRec n (DE_FVar y) s).
  gen s n. induction dt; introv eq notin; simpls.

  induction s; simpls; try(solve[inversion eq]).
  case_nat*. inversion eq;  subst. false notin_same notin0.
  apply DTerm_Var.

  induction s; simpls; try(solve[inversion eq]).
  case_nat*.
  apply DTerm_Star.

  induction s; simpls; try(solve[inversion eq]).
  case_nat*.
  inversion eq; subst.  apply DTerm_App; f_equal *.

  induction s; simpls; try(solve[inversion eq]).
  case_nat*.
  inversion eq; subst.  apply DTerm_Lam with (L \u \{y}).
  intros z notin_z. apply H0 with z (S n); auto. apply~ dopen_reorder.
  apply~ notin_dopen_inv.
  simpls. apply notin_singleton. auto_star.

  induction s; simpls; try(solve[inversion eq]).
  case_nat*.
  inversion eq; subst.  apply DTerm_Pi with (L \u \{y}).
  apply~ IHdt.
  intros z notin_z. apply H0 with z (S n); auto. apply~ dopen_reorder.
  apply~ notin_dopen_inv.
  simpls. apply notin_singleton. auto_star.

  induction s; simpls; try(solve[inversion eq]).
  case_nat*.
  inversion eq; subst.  apply DTerm_Let with (L \u \{y}).
  apply~ IHdt.
  intros z notin_z. apply H0 with z (S n); auto. apply~ dopen_reorder.
  apply~ notin_dopen_inv.
  simpls. apply notin_singleton. auto_star.

  induction s; simpls; try(solve[inversion eq]).
  case_nat*.
  inversion eq; subst.  apply DTerm_CastUp; f_equal *.

  induction s; simpls; try(solve[inversion eq]).
  case_nat*.
  inversion eq; subst.  apply DTerm_CastDn; f_equal *.

  induction s; simpls; try(solve[inversion eq]).
  case_nat*.
  inversion eq; subst.  apply DTerm_Ann; f_equal *.
Qed.

Lemma notin_dopent_inv : forall x y n e,
    x \notin DTFv e ->
    x \notin DFv y ->
    x \notin DTFv (DOpenTypRec n y e).
Proof.
  introv notin neq.
  gen n. induction e; introv; simpls; auto.
  apply~ notin_dopen_inv.
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

Lemma regular_dtyping : forall m E t T, DTyping m E t T ->
  (DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTerm T).
Proof.
  apply dtyping_induct with
  (P0 := fun E t (_ : DWfTyp E t) => DWf E /\ ok E /\ contains_terms E /\ DTermTy t)
  (P1 := fun E (_ : DWf E) => ok E /\ contains_terms E)
  (P2 := fun E t T (_ : DInst E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm T)
  (P3 := fun E t T(_ : DGen E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTermTy T); 
    unfolds contains_terms; intros; splits*.
  
  pick_fresh x. assert (x \notin L) by auto.
  destruct (H x H0) as [H1 [_ [_ _]]].
  inversion* H1. false* empty_push_inv.
  destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*.

  pick_fresh x. assert (x \notin L) by auto.
  destruct~ (H x H0) as [_ [H1 [_ _]]].

  split; intros.
  pick_fresh y. assert (y \notin L) by auto.
  destruct~ (H y H1) as [_ [_ [[H2 _] _]]].
  apply* (H2 x U).
  pick_fresh y. assert (y \notin L) by auto.
  destruct~ (H y H1) as [_ [_ [[_ H2] _]]].
  apply* (H2 x T U).
  
  intros. false* binds_empty_inv.
  intros. false* binds_empty_inv.

  intros. destruct (binds_push_inv H1) as [[? ?]|[? ?]].
  injection H3; intros. subst*.
  destruct H as [_ [H4 _]].
  apply H4 with (x := x0). auto.

  intros. destruct (binds_push_inv H1) as [[? ?]|[? ?]].
  false*. destruct H as [_ [_ H4]].
  apply H4 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  false*. destruct H as [_ [H5 _]].
  apply H5 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  injection H4; intros. subst*.
  destruct H as [_ [_ H5]].
  apply H5 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  false*. destruct H as [_ [H5 _]].
  apply H5 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  injection H4; intros. subst*.
  pick_fresh y. assert (y \notin L) by auto.
  destruct (H1 y H3) as [_ [_ H5]].
  destruct (H5 x (s ^' y) t). auto. split*.
  destruct H as [_ [_ H5]].
  apply H5 with (x := x0). auto.

  pick_fresh x. assert (x \notin L) by auto.
  assert (x \notin DFv e) by auto.
  destruct (H x H0 H1) as [H2 [_ [_ _]]].
  inversion* H2. false* empty_push_inv.
  destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*.

  pick_fresh x. assert (x \notin L) by auto.
  assert (x \notin DFv e) by auto.
  destruct~ (H x H0 H1) as [_ [H2 [_ _]]].

  split; intros.
  pick_fresh y. assert (y \notin L) by auto.
  assert (y \notin DFv e) by auto.
  destruct~ (H y H1 H2) as [_ [_ [[H3 _] _]]].
  apply* (H3 x U).
  pick_fresh y. assert (y \notin L) by auto.
  assert (y \notin DFv e) by auto.
  destruct~ (H y H1 H2) as [_ [_ [[_ H3] _]]].
  apply* (H3 x T U).
  
  pick_fresh x. assert (x \notin L) by auto.
  assert (x \notin DFv e) by auto.
  destruct~ (H x H0 H1) as [_ [_ [_ [H2 _]]]].
Qed.

Lemma open_var_inj : forall x t1 t2,
  x \notin (DFv t1) -> x \notin (DFv t2) ->
  (t1 ^ x = t2 ^ x) -> (t1 = t2).
Proof.
  intros x t1. unfold DOpen. generalize 0.
  induction t1; intro k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal*
  | do 2 try case_nat; inversions* H1; try notin_false ].
Qed.

Lemma openrec_var_inj : forall x t1 k t2,
  x \notin (DFv t1) -> x \notin (DFv t2) ->
  (DOpenRec k (DE_FVar x) t1 = DOpenRec k (DE_FVar x) t2) -> (t1 = t2).
Proof.
  intros x t1. unfold DOpenRec.
  induction t1; intro k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal*
  | do 2 try case_nat; inversions* H1; try notin_false ].
Qed.

Lemma opent_var_inj : forall x t1 t2,
  x \notin (DTFv t1) -> x \notin (DTFv t2) ->
  (t1 ^' x = t2 ^' x) -> (t1 = t2).
Proof.
  intros x t1. unfold DOpenT. generalize 0.
  induction t1; intro k; destruct t2; simpl; intros; inversion H1;
  try solve [ f_equal*
  | do 2 try case_nat; inversions* H1; try notin_false ].

  assert(d = d0). apply* openrec_var_inj.
  subst*.
Qed.

Lemma regular_dinst : forall E s t, DInst E s t ->
  (DWf E /\ ok E /\ contains_terms E /\ DTerm t).
Proof.
  apply dinst_induct with
  (P := fun m E t T (_ : DTyping m E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTerm T)
  (P0 := fun E t (_ : DWfTyp E t) => DWf E /\ ok E /\ contains_terms E /\ DTermTy t)
  (P1 := fun E (_ : DWf E) => ok E /\ contains_terms E)
  (P3 := fun E t T(_ : DGen E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTermTy T); 
    unfolds contains_terms; intros; splits*.
  
  pick_fresh x. assert (x \notin L) by auto.
  destruct (H x H0) as [H1 [_ [_ _]]].
  inversion* H1. false* empty_push_inv.
  destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*.

  pick_fresh x. assert (x \notin L) by auto.
  destruct~ (H x H0) as [_ [H1 [_ _]]].

  split; intros.
  pick_fresh y. assert (y \notin L) by auto.
  destruct~ (H y H1) as [_ [_ [[H2 _] _]]].
  apply* (H2 x U).
  pick_fresh y. assert (y \notin L) by auto.
  destruct~ (H y H1) as [_ [_ [[_ H2] _]]].
  apply* (H2 x T U).
  
  intros. false* binds_empty_inv.
  intros. false* binds_empty_inv.

  intros. destruct (binds_push_inv H1) as [[? ?]|[? ?]].
  injection H3; intros. subst*.
  destruct H as [_ [H4 _]].
  apply H4 with (x := x0). auto.

  intros. destruct (binds_push_inv H1) as [[? ?]|[? ?]].
  false*. destruct H as [_ [_ H4]].
  apply H4 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  false*. destruct H as [_ [H5 _]].
  apply H5 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  injection H4; intros. subst*.
  destruct H as [_ [_ H5]].
  apply H5 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  false*. destruct H as [_ [H5 _]].
  apply H5 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  injection H4; intros. subst*.
  pick_fresh y. assert (y \notin L) by auto.
  destruct (H1 y H3) as [_ [_ H5]].
  destruct (H5 x (s ^' y) t). auto. split*.
  destruct H as [_ [_ H5]].
  apply H5 with (x := x0). auto.

  pick_fresh x. assert (x \notin L) by auto.
  assert (x \notin DFv e) by auto.
  destruct (H x H0 H1) as [H2 [_ [_ _]]].
  inversion* H2. false* empty_push_inv.
  destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*.

  pick_fresh x. assert (x \notin L) by auto.
  assert (x \notin DFv e) by auto.
  destruct~ (H x H0 H1) as [_ [H2 [_ _]]].

  split; intros.
  pick_fresh y. assert (y \notin L) by auto.
  assert (y \notin DFv e) by auto.
  destruct~ (H y H1 H2) as [_ [_ [[H3 _] _]]].
  apply* (H3 x U).
  pick_fresh y. assert (y \notin L) by auto.
  assert (y \notin DFv e) by auto.
  destruct~ (H y H1 H2) as [_ [_ [[_ H3] _]]].
  apply* (H3 x T U).
  
  pick_fresh x. assert (x \notin L) by auto.
  assert (x \notin DFv e) by auto.
  destruct~ (H x H0 H1) as [_ [_ [_ [H2 _]]]].
Qed.

Lemma regular_dgen : forall E t s, DGen E t s ->
  (DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTermTy s).
Proof.
  apply dgen_induct with
  (P := fun m E t T (_ : DTyping m E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTerm T)
  (P0 := fun E t (_ : DWfTyp E t) => DWf E /\ ok E /\ contains_terms E /\ DTermTy t)
  (P1 := fun E (_ : DWf E) => ok E /\ contains_terms E)
  (P2 := fun E t T (_ : DInst E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm T);
    unfolds contains_terms; intros; splits*.
  
  pick_fresh x. assert (x \notin L) by auto.
  destruct (H x H0) as [H1 [_ [_ _]]].
  inversion* H1. false* empty_push_inv.
  destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*.

  pick_fresh x. assert (x \notin L) by auto.
  destruct~ (H x H0) as [_ [H1 [_ _]]].

  split; intros.
  pick_fresh y. assert (y \notin L) by auto.
  destruct~ (H y H1) as [_ [_ [[H2 _] _]]].
  apply* (H2 x U).
  pick_fresh y. assert (y \notin L) by auto.
  destruct~ (H y H1) as [_ [_ [[_ H2] _]]].
  apply* (H2 x T U).
  
  intros. false* binds_empty_inv.
  intros. false* binds_empty_inv.

  intros. destruct (binds_push_inv H1) as [[? ?]|[? ?]].
  injection H3; intros. subst*.
  destruct H as [_ [H4 _]].
  apply H4 with (x := x0). auto.

  intros. destruct (binds_push_inv H1) as [[? ?]|[? ?]].
  false*. destruct H as [_ [_ H4]].
  apply H4 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  false*. destruct H as [_ [H5 _]].
  apply H5 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  injection H4; intros. subst*.
  destruct H as [_ [_ H5]].
  apply H5 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  false*. destruct H as [_ [H5 _]].
  apply H5 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  injection H4; intros. subst*.
  pick_fresh y. assert (y \notin L) by auto.
  destruct (H1 y H3) as [_ [_ H5]].
  destruct (H5 x (s ^' y) t). auto. split*.
  destruct H as [_ [_ H5]].
  apply H5 with (x := x0). auto.

  pick_fresh x. assert (x \notin L) by auto.
  assert (x \notin DFv e) by auto.
  destruct (H x H0 H1) as [H2 [_ [_ _]]].
  inversion* H2. false* empty_push_inv.
  destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*.

  pick_fresh x. assert (x \notin L) by auto.
  assert (x \notin DFv e) by auto.
  destruct~ (H x H0 H1) as [_ [H2 [_ _]]].

  split; intros.
  pick_fresh y. assert (y \notin L) by auto.
  assert (y \notin DFv e) by auto.
  destruct~ (H y H1 H2) as [_ [_ [[H3 _] _]]].
  apply* (H3 x U).
  pick_fresh y. assert (y \notin L) by auto.
  assert (y \notin DFv e) by auto.
  destruct~ (H y H1 H2) as [_ [_ [[_ H3] _]]].
  apply* (H3 x T U).
  
  pick_fresh x. assert (x \notin L) by auto.
  assert (x \notin DFv e) by auto.
  destruct~ (H x H0 H1) as [_ [_ [_ [H2 _]]]].
Qed.

Lemma regular_dwftyp : forall E t, DWfTyp E t ->
  (DWf E /\ ok E /\ contains_terms E).
Proof.
  apply dwftyp_induct with
  (P := fun m E t T (_ : DTyping m E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTerm T)
  (P1 := fun E (_ : DWf E) => ok E /\ contains_terms E)
  (P2 := fun E t T (_ : DInst E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm T)
  (P3 := fun E t T(_ : DGen E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTermTy T); 
    unfolds contains_terms; intros; splits*.
  
  pick_fresh x. assert (x \notin L) by auto.
  destruct (H x H0) as [H1 [_ [_ _]]].
  inversion* H1. false* empty_push_inv.
  destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*.

  pick_fresh x. assert (x \notin L) by auto.
  destruct~ (H x H0) as [_ [H1 [_ _]]].

  intros.
  pick_fresh y. assert (y \notin L) by auto.
  destruct~ (H y H1) as (_ & _ & H2 & _).
  apply* (H2 x U).
  intros.
  pick_fresh y. assert (y \notin L) by auto.
  destruct~ (H y H1) as (_ & _ & _ & H2).
  apply* (H2 x T U). 
  
  intros. false* binds_empty_inv.
  intros. false* binds_empty_inv.

  intros. destruct (binds_push_inv H1) as [[? ?]|[? ?]].
  injection H3; intros. subst*.
  destruct H as [_ [H4 _]].
  apply H4 with (x := x0). auto.

  intros. destruct (binds_push_inv H1) as [[? ?]|[? ?]].
  false*. destruct H as [_ [_ H4]].
  apply H4 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  false*. destruct H as [_ [H5 _]].
  apply H5 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  injection H4; intros. subst*.
  destruct H as [_ [_ H5]].
  apply H5 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  false*. destruct H as [_ [H5 _]].
  apply H5 with (x := x0). auto.

  intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]].
  injection H4; intros. subst*.
  split. apply DTermTy_Forall with (L := L). intros.
  destruct (H1 x0 H3) as [_ [_ H6]].
  destruct (H6 x (s ^' x0) t). auto. auto.
  pick_fresh y. assert (y \notin L) by auto.
  destruct (H1 y H3) as [_ [_ H5]].
  destruct (H5 x (s ^' y) t). auto. auto.
  destruct H as [_ [_ H5]].
  apply H5 with (x := x0). auto.

  pick_fresh x. assert (x \notin L) by auto.
  assert (x \notin DFv e) by auto.
  destruct (H x H0 H1) as [H2 [_ [_ _]]].
  inversion* H2. false* empty_push_inv.
  destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*.

  pick_fresh x. assert (x \notin L) by auto.
  assert (x \notin DFv e) by auto.
  destruct~ (H x H0 H1) as [_ [H2 [_ _]]].

  split; intros.
  pick_fresh y. assert (y \notin L) by auto.
  assert (y \notin DFv e) by auto.
  destruct~ (H y H1 H2) as [_ [_ [[H3 _] _]]].
  apply* (H3 x U).
  pick_fresh y. assert (y \notin L) by auto.
  assert (y \notin DFv e) by auto.
  destruct~ (H y H1 H2) as [_ [_ [[_ H3] _]]].
  apply* (H3 x T U).
  
  pick_fresh x. assert (x \notin L) by auto.
  assert (x \notin DFv e) by auto.
  destruct~ (H x H0 H1) as [_ [_ [_ [H2 _]]]].
Qed.

Hint Extern 1 (DTerm ?t) => match goal with
  | H: DTyping _ _ t _ |- _ => apply (proj32 (proj33 (regular_dtyping H)))
  | H: DTyping _ _ _ t |- _ => apply (proj33 (proj33 (regular_dtyping H)))
  | H: DInst _ _ t    |- _ => apply (proj44 (regular_dinst H))
  | H: DGen _ t _     |- _ => apply (proj32 (proj33 (regular_dgen H)))
  end.

Hint Extern 1 (DTermTy ?s) => match goal with
  | H: DGen _ _ s  |- _ => apply (proj33 (proj33 (regular_dgen H)))
  end.

Lemma dok_from_wf : forall E, DWf E -> ok E.
Proof.
  induction 1. auto. autos* (regular_dtyping H1).
  autos* (regular_dtyping H2).
  autos* (regular_dwftyp H1).
Qed.

Hint Extern 1 (ok ?E) => match goal with
  | H: DWf E |- _ => apply (dok_from_wf H)
  end.

Hint Extern 1 (DWf ?E) => match goal with
  | H: DTyping _ E _ _ |- _ => apply (proj1 (regular_dtyping H))
  | H: DInst E _ _    |- _ => apply (proj1 (regular_dinst H))
  | H: DGen E _ _     |- _ => apply (proj1 (regular_dgen H))
  | H: DWfTyp E _     |- _ => apply (proj1 (regular_dwftyp H))   
  end.

Lemma dwf_push_inv : forall E x U,
  DWf (E & x ~ DC_Typ U) -> DWf E /\ DTerm U.
Proof.
  introv W. inversions W. 
  false (empty_push_inv H0).
  destruct (eq_push_inv H) as [? [? ?]].
  injection H4; intros.
  subst~.
  destruct (eq_push_inv H) as [? [? ?]].
  false*.
  destruct (eq_push_inv H) as [? [? ?]].
  false*.
Qed.

Lemma dterm_from_binds_in_wf : forall x E U,
  DWf E -> binds x (DC_Typ U) E -> DTerm U.
Proof.
  introv W Has. gen E. induction E using env_ind; intros.
  false* binds_empty_inv.
  destruct (binds_push_inv Has) as [[? ?]|[? ?]].
  subst~. destruct~ (dwf_push_inv W).
  apply* IHE.
  inversions* W. false* empty_push_inv.
  destruct (eq_push_inv H1) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H1) as [_ [_ Eq]]. subst*.
  destruct (eq_push_inv H1) as [_ [_ Eq]]. subst*.
Qed.

Hint Extern 1 (DTerm ?t) => match goal with
  H: binds ?x (DC_Typ t) ?E |- _ => apply (@dterm_from_binds_in_wf x E)
  end.

Lemma dwf_left : forall E F : DCtx,
  DWf (E & F) -> DWf E.
Proof.
  intros. induction F using env_ind.
  rewrite~ concat_empty_r in H.
  rewrite concat_assoc in H.
   inversions H. false (empty_push_inv H1).
   destruct (eq_push_inv H0) as [? [? ?]]. subst~. 
   destruct (eq_push_inv H0) as [? [? ?]]. subst~. 
   destruct (eq_push_inv H0) as [? [? ?]]. subst~. 
Qed.

Implicit Arguments dwf_left [E F].

(** Freshness *)

Lemma dfv_open_var : forall y x t,
  x <> y -> x \notin DFv (t ^ y) -> x \notin DFv t.
Proof.
  introv Neq. unfold DOpen. generalize 0. 
  induction t; simpl; intros; try notin_solve.
  specializes IHt1 n. auto. specializes IHt2 n. auto.
  specializes IHt (S n). auto.
  specializes IHt1 n. auto. specializes IHt2 (S n). auto.
  specializes IHt1 n. auto. specializes IHt2 (S n). auto.
  specializes IHt n. auto.
  specializes IHt n. auto.
  specializes IHt1 n. auto. specializes IHt2 n. auto.
Qed.

Lemma dtyping_fresh : forall m x E t T,
    DTyping m E t T -> x # E -> x \notin DFv t
with dgen_fresh : forall x E t s,
    DGen E t s -> x # E -> x \notin DFv t.
Proof.
  introv Typ.
  induction Typ; simpls; intros.
  auto.
  rewrite notin_singleton. intro. subst. applys binds_fresh_inv H0 H1.
  rewrite notin_singleton. intro. subst. applys binds_fresh_inv H0 H2.
  lets: (IHTyp1 H). lets: (IHTyp2 H). auto.
  pick_fresh y. apply* (@dfv_open_var y).
  lets: (IHTyp1 H). lets: (IHTyp2 H). auto.
  pick_fresh y. notin_simpl.
  apply* dgen_fresh.
  apply* (@dfv_open_var y).
  pick_fresh y. notin_simpl. auto. apply* (@dfv_open_var y).
  lets: (IHTyp H0). auto.
  lets: (IHTyp H0). auto.
  pick_fresh y. notin_simpl. auto. apply* (@dfv_open_var y).
  pick_fresh y. notin_simpl.
  apply* dgen_fresh.
  apply* (@dfv_open_var y).
  lets: (IHTyp H0). auto.
  lets: (IHTyp H). auto.
 
  introv Gen.
  induction Gen; simpls; intros.
  apply* dtyping_fresh.
  pick_fresh y. apply* H0.
Qed.

Lemma notin_dfv_from_dwf : forall E F x V,
  DWf (E & x ~ DC_Typ V & F) -> x \notin DFv V.
Proof.
  intros.
  lets W: (dwf_left H). inversions W.
  false (empty_push_inv H1).
  destruct (eq_push_inv H0) as [? [? ?]].
  injection H5. intros.
  subst~.
  apply* dtyping_fresh.
  destruct (eq_push_inv H0) as [? [? ?]].
  false*.
  destruct (eq_push_inv H0) as [? [? ?]].
  false*.
Qed.

Lemma notin_dfv_from_binds : forall x y U E,
  DWf E -> binds y (DC_Typ U) E -> x # E -> x \notin DFv U.
Proof.
  induction E using env_ind; intros.
  false* binds_empty_inv.
  destruct v.
  destruct (dwf_push_inv H).
  destruct (binds_push_inv H0) as [[? ?]|[? ?]]; subst.
  inversions H. false* (empty_push_inv H6).
  injection H5; intros; subst.
  destruct (eq_push_inv H4) as [? [? ?]]. subst~. 
  injection H9; intros; subst.
  apply dtyping_fresh with (m := Chk)(E := E)(T := DE_Star).
  auto. auto.   
  destruct (eq_push_inv H4) as [? [? ?]]. false*.
  destruct (eq_push_inv H4) as [? [? ?]]. false*.
  apply* IHE.
  destruct (binds_push_inv H0) as [[? ?]|[? ?]]; subst.
  false*.
  inversions H. false* (empty_push_inv H5).
  destruct (eq_push_inv H4) as [? [? ?]]. false*. 
  destruct (eq_push_inv H4) as [? [? ?]]; subst~.
  destruct (eq_push_inv H4) as [? [? ?]]; subst~.
Qed.

Lemma notin_dfv_from_binds' : forall E F x V y U,
  DWf (E & x ~ DC_Typ V & F) -> binds y (DC_Typ U) E -> x \notin DFv U.
Proof.
  intros. lets W: (dwf_left H). inversions keep W.
  false (empty_push_inv H2). 
  destruct (eq_push_inv H1) as [? [? ?]]. subst~. 
  lets W': (dwf_left W). apply* notin_dfv_from_binds.
  destruct (eq_push_inv H1) as [? [? ?]]. false*.
  destruct (eq_push_inv H1) as [? [? ?]]. false*.
Qed.

Hint Extern 1 (?x \notin DFv ?V) => 
  match goal with H: DWf (?E & x ~ DC_Typ V & ?F) |- _ =>
    apply (@notin_dfv_from_dwf E F) end.

Hint Extern 1 (?x \notin DFv ?U) => 
  match goal with H: DWf (?E & x ~ DC_Typ ?V & ?F), B: binds ?y U ?E |- _ =>
    apply (@notin_dfv_from_binds' E F x V y) end.

