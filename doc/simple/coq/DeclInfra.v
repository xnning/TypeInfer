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
  with dwf_induct := Induction for DWf Sort Prop
  with dwf_subtyping := Induction for DSubtyping Sort Prop.

Hint Constructors DRed DTyping DMode DWf DSubtyping.

Lemma dnotin_fv_fev: forall x t,
    x \notin DFv t ->
    x \notin DFev t
with dnotin_tfv_tfev: forall x t,
    x \notin DTFv t ->
    x \notin DTFev t.
Proof.
  intros. induction t; simpls; auto.
Proof.
  intros. induction t; simpls; auto.
Qed.

Lemma dnotin_fv_ftv: forall x t,
    x \notin DFv t ->
    x \notin DFtv t
with dnotin_tfv_tftv: forall x t,
    x \notin DTFv t ->
    x \notin DTFtv t.
Proof.
  intros. induction t; simpls; auto.
Proof.
  intros. induction t; simpls; auto.
Qed.

Lemma dnotin_fv_inv: forall x t,
    x \notin DFev t -> x \notin DFtv t ->
    x \notin DFv t
with dnotin_tfv_inv: forall x t,
    x \notin DTFev t -> x \notin DTFtv t ->
    x \notin DTFv t.
Proof.
  intros. induction t; simpls; auto.
Proof.
  intros. induction t; simpls; auto.
Qed.

Hint Resolve dnotin_fv_fev dnotin_tfv_tfev dnotin_fv_ftv dnotin_tfv_tftv dnotin_fv_inv dnotin_tfv_inv.

(** Substitution *)

Hint Constructors DTerm DTermTy.

(* Substitution on indices is identity on well-formed terms. *)

Lemma dopen_rec_term_core :forall e j v i u, i <> j ->
  DOpenRec j v e = DOpenRec i u (DOpenRec j v e) -> e = DOpenRec i u e
with dopent_rec_term_core:forall e j v i u, i <> j ->
  DOpenTypRec j v e = DOpenTypRec i u (DOpenTypRec j v e) -> e = DOpenTypRec i u e.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.  
  case_nat*. case_nat*.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.
Qed.

Lemma dtopen_rec_term_core :forall e j v i u, i <> j ->
  DTOpenRec j v e = DTOpenRec i u (DTOpenRec j v e) -> e = DTOpenRec i u e
with
dtopent_rec_term_core :forall e j v i u, i <> j ->
  DTOpenTypRec j v e = DTOpenTypRec i u (DTOpenTypRec j v e) -> e = DTOpenTypRec i u e.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma dopen_dtopen_rec_term_core :forall e j v i u, i <> j ->
  DTOpenRec j v e = DOpenRec i u (DTOpenRec j v e) -> e = DOpenRec i u e
with
dopent_dtopent_rec_term_core :forall e j v i u, i <> j ->
  DTOpenTypRec j v e = DOpenTypRec i u (DTOpenTypRec j v e) -> e = DOpenTypRec i u e.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.
Qed.

Lemma dtopen_dopen_rec_term_core :forall e j v i u, i <> j ->
  DOpenRec j v e = DTOpenRec i u (DOpenRec j v e) -> e = DTOpenRec i u e
with
dtopent_dopent_rec_term_core :forall e j v i u, i <> j ->
  DOpenTypRec j v e = DTOpenTypRec i u (DOpenTypRec j v e) -> e = DTOpenTypRec i u e.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.
Qed.

Lemma dopen_rec_term : forall t u,
  DTerm t -> forall k, t = DOpenRec k u t
with dopent_rec_term : forall t u,
  DTermTy t -> forall k, t = DOpenTypRec k u t.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds DOpen. pick_fresh x.
   apply* (@dopen_rec_term_core e 0 (DE_FVar x)).
  unfolds DOpen. pick_fresh x.
   apply* (@dopent_rec_term_core t2 0 (DE_FVar x)).
  unfolds DOpen. pick_fresh x.
    apply* (@dopent_dtopent_rec_term_core t 0 (DT_TFVar x)).
Proof.
  induction 1; intros; simpl; f_equal*.
Qed.

Lemma dtopen_rec_term : forall t u,
  DTerm t -> forall k, t = DTOpenRec k u t
with dtopent_rec_term : forall t u,
  DTermTy t -> forall k, t = DTOpenTypRec k u t.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds DOpen. pick_fresh x.
   apply* (@dtopen_dopen_rec_term_core e 0 (DE_FVar x)).
  unfolds DOpen. pick_fresh x.
   apply* (@dtopent_dopent_rec_term_core t2 0 (DE_FVar x)).
  unfolds DOpen. pick_fresh x.
   apply* (@dtopent_rec_term_core t 0 (DT_TFVar x)).
Proof.
  induction 1; intros; simpl; f_equal*.
Qed.

Lemma dopen_var_inj : forall x t1 t2,
  x \notin (DFv t1) -> x \notin (DFv t2) ->
  forall k, (DOpenRec k (DE_FVar x) t1 = DOpenRec k (DE_FVar x) t2) -> (t1 = t2)
with
dopent_var_inj : forall x t1 t2,
  x \notin (DTFv t1) -> x \notin (DTFv t2) ->
  forall k, (DOpenTypRec k (DE_FVar x) t1 = DOpenTypRec k (DE_FVar x) t2) -> (t1 = t2).
Proof.
  intros x t1.
  induction t1; intro t2.
  destruct t2; simpl; intros;try(case_nat~). case_nat~. case_nat~.
  inversion H1; subst. notin_false.
  destruct t2; simpl; intros; try(case_nat~); try(solve[inversion H1]).
  inversion H1; subst. notin_false.
  inversion H1; subst~.
  destruct t2; simpl; intros; try(case_nat~); try(solve[inversion H1]); auto.
  destruct t2; simpl; intros; try(case_nat~); try(solve[inversion H1]); auto.
  inversion H1; subst. f_equal ~. apply* IHt1_1. apply* IHt1_2.
  destruct t2; simpl; intros; try(case_nat~); try(solve[inversion H1]); auto.
  inversion H1; subst. f_equal ~. apply* IHt1.
  destruct t2; simpl; intros; try(case_nat~); try(solve[inversion H1]); auto.
  inversion H1; subst. f_equal ~. apply* dopent_var_inj. apply* dopent_var_inj.
  destruct t2; simpl; intros; try(case_nat~); try(solve[inversion H1]); auto.
  inversion H1; subst. f_equal ~. apply* IHt1.
  destruct t2; simpl; intros; try(case_nat~); try(solve[inversion H1]); auto.
  inversion H1; subst. f_equal ~. apply* IHt1.
  destruct t2; simpl; intros; try(case_nat~); try(solve[inversion H1]); auto.
  inversion H1; subst. f_equal ~. apply* IHt1. apply* dopent_var_inj.
  destruct t2; simpl; intros; try(case_nat~); try(solve[inversion H1]); auto.
  inversion H1; subst. f_equal ~. apply* dopent_var_inj.

  intros x t1.
  destruct t1; intros t2; destruct t2; simpl; intros; inversion H1; auto.
  lets: dopen_var_inj H3; auto.
  subst~.
Qed.

Lemma dtopen_var_inj : forall x t1 t2,
  x \notin (DFv t1) -> x \notin (DFv t2) ->
  forall k, (DTOpenRec k (DT_TFVar x) t1 = DTOpenRec k (DT_TFVar x) t2) -> (t1 = t2)
with
dtopent_var_inj : forall x t1 t2,
  x \notin (DTFv t1) -> x \notin (DTFv t2) ->
  forall k, (DTOpenTypRec k (DT_TFVar x) t1 = DTOpenTypRec k (DT_TFVar x) t2) -> (t1 = t2).
Proof.
  intros x t1.
  induction t1; intro t2.
  destruct t2; simpl; intros; auto; try(false*).
  destruct t2; simpl; intros; auto; try(false*).
  destruct t2; simpl; intros; auto; try(false*).
  destruct t2; simpl; intros; auto; try(solve[false*]).
  inversion H1; subst. f_equal ~. apply* IHt1_1. apply* IHt1_2.
  destruct t2; simpl; intros; auto; try(solve[false*]).
  inversion H1; subst. f_equal ~. apply* IHt1.
  destruct t2; simpl; intros; auto; try(solve[false*]).
  inversion H1; subst. f_equal ~. apply* dtopent_var_inj. apply* dtopent_var_inj.
  destruct t2; simpl; intros; auto; try(solve[false*]).
  inversion H1; subst. f_equal ~. apply* IHt1.
  destruct t2; simpl; intros; auto; try(solve[false*]).
  inversion H1; subst. f_equal ~. apply* IHt1.
  destruct t2; simpl; intros; auto; try(solve[false*]).
  inversion H1; subst. f_equal ~. apply* IHt1. apply* dtopent_var_inj.
  destruct t2; simpl; intros; auto; try(solve[false*]).
  inversion H1; subst. f_equal ~. apply* dtopent_var_inj.
  destruct t2; simpl; intros; auto; try(solve[false*]).
  case_nat~.
  destruct t1;  simpls; inversion H1; auto; try(solve[false*]).
  case_nat~. subst. notin_false.
  destruct t1;  simpls; inversion H1; auto; try(solve[false*]).
  case_nat~.

  destruct t1;  simpls; inversion H1; auto; try(solve[false*]).
  case_nat~. subst. inversion H1. subst. notin_false.
  destruct t1;  simpls; inversion H1; auto; try(solve[false*]).
  case_nat~.

  f_equal *.
Qed.

Lemma dopen_reorder: forall e1 e2 i j e,
    DTerm e1 ->
    DTerm e2 ->
    i <> j ->
    DOpenRec i e1 (DOpenRec j e2 e) = DOpenRec j e2 (DOpenRec i e1 e)
with dopent_reorder: forall e1 e2 i j e,
    DTerm e1 ->
    DTerm e2 ->
    i <> j ->
    DOpenTypRec i e1 (DOpenTypRec j e2 e) = DOpenTypRec j e2 (DOpenTypRec i e1 e).
Proof.
  introv te1 te2 neq.
  gen i j. induction e; introv neq; simpls; auto; try(solve[f_equal ~]).
  case_nat~. case_nat~. simpls. case_if~. symmetry. apply~ dopen_rec_term.
  case_nat~. simpls. case_if~. apply~ dopen_rec_term.
  simpls. case_if~. case_if~.
Proof.
  introv te1 te2 neq.
  gen i j. induction e; introv neq; simpls; auto; try(solve[f_equal ~]).
Qed.

Lemma dtopen_reorder: forall e1 e2 i j e,
    DTermTy e1 ->
    DTermTy e2 ->
    i <> j ->
    DTOpenRec i e1 (DTOpenRec j e2 e) = DTOpenRec j e2 (DTOpenRec i e1 e)
with
dtopent_reorder: forall e1 e2 i j e,
    DTermTy e1 ->
    DTermTy e2 ->
    i <> j ->
    DTOpenTypRec i e1 (DTOpenTypRec j e2 e) = DTOpenTypRec j e2 (DTOpenTypRec i e1 e).
Proof.
  introv te1 te2 neq.
  gen i j. induction e; introv neq; simpls; auto; try(solve[f_equal ~]).
Proof.
  introv te1 te2 neq.
  gen i j. induction e; introv neq; simpls; auto; try(solve[f_equal ~]).
  case_nat~. case_nat~. simpls. case_if~. symmetry. apply~ dtopent_rec_term.
  case_nat~. simpls. case_if~. apply~ dtopent_rec_term.
  simpls. case_if~. case_if~.
Qed.

Lemma notin_dopen_fev_inv : forall x y n e,
    x \notin DFev e ->
    x \notin DFev y ->
    x \notin DFev (DOpenRec n y e)
with notin_dopent_fev_inv : forall x y n e,
    x \notin DTFev e ->
    x \notin DFev y ->
    x \notin DTFev (DOpenTypRec n y e).
Proof.
  introv notin neq.
  gen n. induction e; introv; simpls; auto.
  case_if. auto. simpl.  auto.
Proof.
  introv notin neq.
  gen n. induction e; introv; simpls; auto.
Qed.

Lemma notin_dopen_ftv_inv : forall x y n e,
    x \notin DFtv e ->
    x \notin DFtv y ->
    x \notin DFtv (DOpenRec n y e)
with notin_dopent_ftv_inv : forall x y n e,
    x \notin DTFtv e ->
    x \notin DFtv y ->
    x \notin DTFtv (DOpenTypRec n y e).
Proof.
  introv notin neq.
  gen n. induction e; introv; simpls; auto.
  case_if. auto. simpl.  auto.
Proof.
  introv notin neq.
  gen n. induction e; introv; simpls; auto.
Qed.

Lemma notin_dtopen_inv : forall x y n e,
    x \notin DFv e ->
    x \notin DTFv y ->
    x \notin DFv (DTOpenRec n y e)
with notin_dtopent_inv : forall x y n e,
    x \notin DTFv e ->
    x \notin DTFv y ->
    x \notin DTFv (DTOpenTypRec n y e).
Proof.
  introv notin neq.
  gen n. induction e; introv; simpls; auto.
Proof.
  introv notin neq.
  gen n. induction e; introv; simpls; auto.
  case_if. auto. simpl.  auto.
Qed.

Lemma notin_dopen_fev : forall x y e n,
    x \notin (DFev (DOpenRec n y e)) ->
    x \notin (DFev e)
with
notin_dopent_fev : forall x y e n,
    x \notin (DTFev (DOpenTypRec n y e)) ->
    x \notin (DTFev e).
Proof.
  introv notin. gen n.
  induction e; introv notin; try(simpl in *; auto);
  try(apply notin_union in notin;
      destruct notin as [notin1 notin2];
      apply IHe1 in notin1;
      apply IHe2 in notin2; auto);
  try(apply IHe in notin; auto);
  try(apply notin_union in notin;
      destruct notin as [notin1 notin2];
      try(lets: notin_opent notin1);
      try(lets: notin_opent notin2);
      auto_star).
  apply* notin_dopent_fev.
Proof.
  introv notin. gen n.
  induction e; introv notin.
    simpl in *; auto_star.
    simpl in *. auto.
    simpl in *. auto.
    simpl in *. apply*  notin_dopen_fev.
Qed.

Lemma notin_dopen_ftv : forall x y e n,
    x \notin (DFtv (DOpenRec n y e)) ->
    x \notin (DFtv e)
with
notin_dopent_ftv : forall x y e n,
    x \notin (DTFtv (DOpenTypRec n y e)) ->
    x \notin (DTFtv e).
Proof.
  introv notin. gen n.
  induction e; introv notin; try(simpl in *; auto);
  try(apply notin_union in notin;
      destruct notin as [notin1 notin2];
      apply IHe1 in notin1;
      apply IHe2 in notin2; auto);
  try(apply IHe in notin; auto);
  try(apply notin_union in notin;
      destruct notin as [notin1 notin2];
      try(lets: notin_opent notin1);
      try(lets: notin_opent notin2);
      auto_star).
  apply* notin_dopent_ftv.
Proof.
  introv notin. gen n.
  induction e; introv notin.
    simpl in *; auto_star.
    simpl in *. auto.
    simpl in *. auto.
    simpl in *. apply*  notin_dopen_ftv.
Qed.

Lemma notin_dtopen_ftv : forall x y e n,
    x \notin (DFtv (DTOpenRec n y e)) ->
    x \notin (DFtv e)
with
notin_dtopent_ftv : forall x y e n,
    x \notin (DTFtv (DTOpenTypRec n y e)) ->
    x \notin (DTFtv e).
Proof.
  introv notin. gen n.
  induction e; introv notin; try(simpl in *; auto);
  try(apply notin_union in notin;
      destruct notin as [notin1 notin2];
      apply IHe1 in notin1;
      apply IHe2 in notin2; auto);
  try(apply IHe in notin; auto);
  try(apply notin_union in notin;
      destruct notin as [notin1 notin2];
      try(lets: notin_topen notin1);
      try(lets: notin_topen notin2);
      auto_star).
  apply* notin_dtopent_ftv.
Proof.
  introv notin. gen n.
  induction e; introv notin.
    simpl in *; auto_star.
    simpl in *. auto.
    simpl in *. auto.
    simpl in *. apply*  notin_dtopen_ftv.
Qed.

Lemma notin_dtopen_fev : forall x y e n,
    x \notin (DFev (DTOpenRec n y e)) ->
    x \notin (DFev e)
with
notin_dtopent_fev : forall x y e n,
    x \notin (DTFev (DTOpenTypRec n y e)) ->
    x \notin (DTFev e).
Proof.
  introv notin. gen n.
  induction e; introv notin; try(simpl in *; auto);
  try(apply notin_union in notin;
      destruct notin as [notin1 notin2];
      apply IHe1 in notin1;
      apply IHe2 in notin2; auto);
  try(apply IHe in notin; auto);
  try(apply notin_union in notin;
      destruct notin as [notin1 notin2];
      try(lets: notin_topen notin1);
      try(lets: notin_topen notin2);
      auto_star).
  apply* notin_dtopent_fev.

  introv notin. gen n.
  induction e; introv notin.
    simpl in *; auto_star.
    simpl in *. auto.
    simpl in *. auto.
    simpl in *. apply*  notin_dtopen_fev.
Qed.

Lemma notin_dopen_fv : forall x y e n,
    x \notin (DFv (DOpenRec n y e)) ->
    x \notin (DFv e)
with
notin_dopent_fv : forall x y e n,
    x \notin (DTFv (DOpenTypRec n y e)) ->
    x \notin (DTFv e).
Proof.
  intros. apply dnotin_fv_inv.
  apply dnotin_fv_fev in H. apply* notin_dopen_fev.
  apply dnotin_fv_ftv in H. apply* notin_dopen_ftv.
Proof.
  intros. apply dnotin_tfv_inv.
  apply dnotin_tfv_tfev in H. apply* notin_dopent_fev.
  apply dnotin_tfv_tftv in H. apply* notin_dopent_ftv.
Qed.

Lemma notin_dtopen_fv : forall x y e n,
    x \notin (DFv (DTOpenRec n y e)) ->
    x \notin (DFv e)
with
notin_dtopent_fv : forall x y e n,
    x \notin (DTFv (DTOpenTypRec n y e)) ->
    x \notin (DTFv e).
Proof.
  intros. apply dnotin_fv_inv.
  apply dnotin_fv_fev in H. apply* notin_dtopen_fev.
  apply dnotin_fv_ftv in H. apply* notin_dtopen_ftv.
Proof.
  intros. apply dnotin_tfv_inv.
  apply dnotin_tfv_tfev in H. apply* notin_dtopent_fev.
  apply dnotin_tfv_tftv in H. apply* notin_dtopent_ftv.
Qed.

(* Substitution for a fresh name is identity. *)

Lemma dsubst_fresh : forall x t u, 
  x \notin DFv t -> DSubst x u t = t
with
dtsubst_fresh : forall x t u,
  x \notin DTFv t -> DTSubst x u t = t.
Proof.
  intros. induction t; simpls; fequals*.
  case_var*. 
Proof.
  intros. induction t; simpls; fequals*.
Qed.

Lemma dsubstt_fresh : forall x t u,
  x \notin DFtv t -> DSubstT x u t = t
with dtsubstt_fresh : forall x t u,
  x \notin DTFtv t -> DTSubstT x u t = t.
Proof.
  intros. induction t; simpls; fequals*.
Proof.
  intros. induction t; simpls; fequals*.
  case_var*.
Qed.

(* Substitution distributes on the open operation. *)

Lemma dsubst_openrec : forall n x u t1 t2, DTerm u -> 
  DSubst x u (DOpenRec n t2 t1) = DOpenRec n (DSubst x u t2) (DSubst x u t1)
with
dtsubst_opentyprec : forall n x u t1 t2, DTerm u ->
  DTSubst x u (DOpenTypRec n t2 t1) = DOpenTypRec n (DSubst x u t2) (DTSubst x u t1).
Proof.
  intros. gen n.
  induction t1; intros; simpl; f_equal*.
  case_nat*. case_var*. apply* dopen_rec_term.
Proof.
  intros. induction t1; simpls; fequal *.
Qed.

Lemma dsubst_topenrec : forall n x u t1 t2, DTerm u ->
  DSubst x u (DTOpenRec n t2 t1) = DTOpenRec n (DTSubst x u t2) (DSubst x u t1)
with
dtsubst_topentyprec : forall n x u t1 t2, DTerm u ->
  DTSubst x u (DTOpenTypRec n t2 t1) = DTOpenTypRec n (DTSubst x u t2) (DTSubst x u t1).
Proof.
  intros. gen n.
  induction t1; intros; simpl; f_equal*.
  case_if*. apply* dtopen_rec_term.
Proof.
  intros. induction t1; simpls; fequal *.
  case_nat*.
Qed.

Lemma dsubstt_openrec : forall n x u t1 t2, DTermTy u ->
  DSubstT x u (DOpenRec n t2 t1) = DOpenRec n (DSubstT x u t2) (DSubstT x u t1)
with
dtsubstt_opentyprec : forall n x u t1 t2, DTermTy u ->
  DTSubstT x u (DOpenTypRec n t2 t1) = DOpenTypRec n (DSubstT x u t2) (DTSubstT x u t1).
Proof.
  intros. gen n.
  induction t1; intros; simpl; f_equal*.
  case_nat*.
Proof.
  intros. induction t1; simpls; fequal *.
  case_if*. apply* dopent_rec_term.
Qed.

Lemma dsubstt_topenrec : forall n x u t1 t2, DTermTy u ->
  DSubstT x u (DTOpenRec n t2 t1) = DTOpenRec n (DTSubstT x u t2) (DSubstT x u t1)
with
dtsubstt_topentyprec : forall n x u t1 t2, DTermTy u ->
  DTSubstT x u (DTOpenTypRec n t2 t1) = DTOpenTypRec n (DTSubstT x u t2) (DTSubstT x u t1).
Proof.
  intros. gen n.
  induction t1; intros; simpl; f_equal*.
Proof.
  intros. induction t1; simpls; fequal *.
  case_nat*.
  case_if*. apply* dtopent_rec_term.
Qed.

Lemma dsubst_open : forall x u t1 t2, DTerm u -> 
  DSubst x u (t1 ^^ t2) = (DSubst x u t1) ^^ (DSubst x u t2)
with dtsubst_open : forall x u t1 t2, DTerm u ->
  DTSubst x u (t1 ^^' t2) = (DTSubst x u t1) ^^' (DSubst x u t2).
Proof.
  intros. apply* dsubst_openrec.
Proof.
  intros. unfold DOpenT. generalize 0.
  induction t1; intros; simpl; f_equal*.
  apply* dsubst_openrec.
Qed.

Lemma dsubst_topen : forall x u t1 t2, DTerm u ->
  DSubst x u (t1 ^^% t2) = (DSubst x u t1) ^^% (DTSubst x u t2)
with
  dtsubst_topen : forall x u t1 t2, DTerm u ->
  DTSubst x u (t1 ^^%' t2) = (DTSubst x u t1) ^^%' (DTSubst x u t2).
Proof.
  intros. apply* dsubst_topenrec.
Proof.
  intros. unfold DOpenT. generalize 0.
  induction t1; intros; simpl; f_equal*.
  apply* dtsubst_topentyprec.
  unfold DTOpenT. simpls. f_equal *.
Qed.

Lemma dsubstt_open : forall x u t1 t2, DTermTy u ->
  DSubstT x u (t1 ^^ t2) = (DSubstT x u t1) ^^ (DSubstT x u t2)
with
  dtsubstt_open : forall x u t1 t2, DTermTy u ->
  DTSubstT x u (t1 ^^' t2) = (DTSubstT x u t1) ^^' (DSubstT x u t2).
Proof.
  intros. apply* dsubstt_openrec.
Proof.
  intros. unfold DOpenT. generalize 0.
  induction t1; intros; simpl; f_equal*.
  case_if*. apply* dopent_rec_term.
  apply* dsubstt_openrec.
Qed.

Lemma dsubstt_topen : forall x u t1 t2, DTermTy u ->
  DSubstT x u (t1 ^^% t2) = (DSubstT x u t1) ^^% (DTSubstT x u t2)
with
  dtsubstt_topen : forall x u t1 t2, DTermTy u ->
  DTSubstT x u (t1 ^^%' t2) = (DTSubstT x u t1) ^^%' (DTSubstT x u t2).
Proof.
  intros. apply* dsubstt_topenrec.
Proof.
  intros. unfold DOpenT. generalize 0.
  induction t1; intros; simpl; f_equal*.
  apply* dtsubstt_topentyprec.
  case_if*. apply* dtopent_rec_term.
  unfold DTOpenT. simpls. f_equal *.
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

Lemma dsubst_open_tvar : forall x y u e, y <> x -> DTerm u ->
  (DSubst x u e) ^% y = DSubst x u (e ^% y).
Proof.
  introv Neq Wu. rewrite* dsubst_topen.
Qed.

Lemma dtsubst_open_tvar : forall x y u e, y <> x -> DTerm u ->
  (DTSubst x u e) ^%' y = DTSubst x u (e ^%' y).
Proof.
  introv Neq Wu. rewrite* dtsubst_topen.
Qed.

Lemma dsubstt_open_var : forall x y u e, y <> x -> DTermTy u ->
  (DSubstT x u e) ^ y = DSubstT x u (e ^ y).
Proof.
  introv Neq Wu. rewrite* dsubstt_open.
Qed.

Lemma dtsubstt_open_var : forall x y u e, y <> x -> DTermTy u ->
  (DTSubstT x u e) ^' y = DTSubstT x u (e ^' y).
Proof.
  introv Neq Wu. rewrite* dtsubstt_open.
Qed.

Lemma dsubstt_open_tvar : forall x y u e, y <> x -> DTermTy u ->
  (DSubstT x u e) ^% y = DSubstT x u (e ^% y).
Proof.
  introv Neq Wu. rewrite* dsubstt_topen.
  simpl. case_var*.
Qed.

Lemma dtsubstt_open_tvar : forall x y u e, y <> x -> DTermTy u ->
  (DTSubstT x u e) ^%' y = DTSubstT x u (e ^%' y).
Proof.
  introv Neq Wu. rewrite* dtsubstt_topen.
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

Lemma dsubstt_intro : forall x t u,
  x \notin (DFv t) -> DTermTy u ->
  t ^^% u = DSubstT x u (t ^% x).
Proof.
  introv Fr Wu. rewrite* dsubstt_topen.
  rewrite* dsubstt_fresh. simpl. case_var*.
Qed.

Lemma dtsubstt_intro : forall x t u,
  x \notin (DTFv t) -> DTermTy u ->
  t ^^%' u = DTSubstT x u (t ^%' x).
Proof.
  introv Fr Wu. rewrite* dtsubstt_topen.
  rewrite* dtsubstt_fresh. simpl. case_var*.
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
  DTerm u -> DTerm t -> DTerm (DSubst z u t)
with
dtsubst_term : forall t z u,
  DTerm u -> DTermTy t -> DTermTy (DTSubst z u t)
with
dsubstt_term : forall t z u,
  DTermTy u -> DTerm t -> DTerm (DSubstT z u t)
with
dtsubstt_term : forall t z u,
  DTermTy u -> DTermTy t -> DTermTy (DTSubstT z u t).
Proof.
  induction 2; simple*.
  case_var*.
  apply_fresh* DTerm_Lam as y. rewrite* dsubst_open_var.
  apply_fresh* DTerm_Pi as y. rewrite* dtsubst_open_var.
  apply_fresh* DTerm_Forall as y. rewrite* dtsubst_open_tvar.
Proof.
  induction 2; simple*.
Proof.
  induction 2; simple*.
  apply_fresh* DTerm_Lam as y. rewrite* dsubstt_open_var.
  apply_fresh* DTerm_Pi as y. rewrite* dtsubstt_open_var.
  apply_fresh* DTerm_Forall as y. rewrite* dtsubstt_open_tvar.
Proof.
  induction 2; simple*.
  case_var*.
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
  DTerm (DE_Pi t1 t2) -> DBodyTy t2.
Proof.
  intros. unfold DBodyTy. inversion* H.
Qed.

Lemma dterm_pi : forall t1 t2,
  DTerm (DE_Pi t1 t2) -> DTermTy t1.
Proof.
  intros. inversion* H.
Qed.

Lemma dtermty_expr : forall e,
  DTermTy (DT_Expr e) -> DTerm e.
Proof.
  intros. inversions* H.
Qed.

Hint Extern 1 (DTerm ?t) =>
  match goal with
  | H: DTerm (DE_Pi t ?t2) |- _ => apply (@dterm_pi t2)
  | H: DTerm (DT_Expr ?t2) |- _ => apply (@dtermty_expr t2)
  end.

Hint Extern 3 (DBody ?t) =>
  match goal with 
  | H: context [DE_Lam t] |- _ => apply (@dbody_lam)
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
  | H: context [DE_Pi t] |- _ => apply (@dbody_pi)
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
  DTermTy t1 -> DBodyTy t2 -> DTerm (DE_Pi t1 t2).
Proof.
  intros. apply_fresh* DTerm_Pi as x.
Qed.

Lemma dtermty_forall_prove : forall s,
  DTermTy s -> DTerm (DE_Forall s).
Proof.
  intros. apply_fresh* DTerm_Forall as x.
  inversion H. unfold DTOpenT. simpls. apply* DTermTy_TFVar.
  unfold DTOpenT. simpls. apply DTermTy_Expr. rewrite <- dtopen_rec_term; auto.
Qed.

Lemma dtermty_expr_prove : forall e,
    DTerm e -> DTermTy (DT_Expr e).
Proof.
  intros. apply* DTermTy_Expr.
Qed.

Hint Resolve dterm_lam_prove
     dterm_pi_prove
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

Hint Extern 1 (DTerm (DE_Forall (DTSubst ?x ?u ?t2))) =>
  match goal with H: DTermTy (DE_Forall t2) |- _ =>
  unsimpl (DTSubst x u (DE_Forall t2)) end.

(* Definition contains_terms (E : DCtx) := *)
(*   (forall x U, binds x (DC_Typ U) E -> DTerm U) /\ *)
(*   (forall x T U, binds x (DC_Bnd T U) E -> DTermTy T /\ DTerm U). *)

(* Lemma regular_dtyping : forall m E t T, DTyping m E t T -> *)
(*   (DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTerm T). *)
(* Proof. *)
(*   apply dtyping_induct with *)
(*   (P0 := fun E t (_ : DWfTyp E t) => DWf E /\ ok E /\ contains_terms E /\ DTermTy t) *)
(*   (P1 := fun E (_ : DWf E) => ok E /\ contains_terms E) *)
(*   (P2 := fun E t T (_ : DInst E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm T) *)
(*   (P3 := fun E t T(_ : DGen E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTermTy T);  *)
(*     unfolds contains_terms; intros; splits*. *)
  
(*   pick_fresh x. assert (x \notin L) by auto. *)
(*   destruct (H x H0) as [H1 [_ [_ _]]]. *)
(*   inversion* H1. false* empty_push_inv. *)
(*   destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*. *)
(*   destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*. *)
(*   destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*. *)

(*   pick_fresh x. assert (x \notin L) by auto. *)
(*   destruct~ (H x H0) as [_ [H1 [_ _]]]. *)

(*   split; intros. *)
(*   pick_fresh y. assert (y \notin L) by auto. *)
(*   destruct~ (H y H1) as [_ [_ [[H2 _] _]]]. *)
(*   apply* (H2 x U). *)
(*   pick_fresh y. assert (y \notin L) by auto. *)
(*   destruct~ (H y H1) as [_ [_ [[_ H2] _]]]. *)
(*   apply* (H2 x T U). *)
  
(*   intros. false* binds_empty_inv. *)
(*   intros. false* binds_empty_inv. *)

(*   intros. destruct (binds_push_inv H1) as [[? ?]|[? ?]]. *)
(*   injection H3; intros. subst*. *)
(*   destruct H as [_ [H4 _]]. *)
(*   apply H4 with (x := x0). auto. *)

(*   intros. destruct (binds_push_inv H1) as [[? ?]|[? ?]]. *)
(*   false*. destruct H as [_ [_ H4]]. *)
(*   apply H4 with (x := x0). auto. *)

(*   intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]]. *)
(*   false*. destruct H as [_ [H5 _]]. *)
(*   apply H5 with (x := x0). auto. *)

(*   intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]]. *)
(*   injection H4; intros. subst*. *)
(*   destruct H as [_ [_ H5]]. *)
(*   apply H5 with (x := x0). auto. *)

(*   intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]]. *)
(*   false*. destruct H as [_ [H5 _]]. *)
(*   apply H5 with (x := x0). auto. *)

(*   intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]]. *)
(*   injection H4; intros. subst*. *)
(*   pick_fresh y. assert (y \notin L) by auto. *)
(*   destruct (H1 y H3) as [_ [_ H5]]. *)
(*   destruct (H5 x (s ^' y) t). auto. split*. *)
(*   destruct H as [_ [_ H5]]. *)
(*   apply H5 with (x := x0). auto. *)

(*   pick_fresh x. assert (x \notin L) by auto. *)
(*   assert (x \notin DFv e) by auto. *)
(*   destruct (H x H0 H1) as [H2 [_ [_ _]]]. *)
(*   inversion* H2. false* empty_push_inv. *)
(*   destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*. *)
(*   destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*. *)
(*   destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*. *)

(*   pick_fresh x. assert (x \notin L) by auto. *)
(*   assert (x \notin DFv e) by auto. *)
(*   destruct~ (H x H0 H1) as [_ [H2 [_ _]]]. *)

(*   split; intros. *)
(*   pick_fresh y. assert (y \notin L) by auto. *)
(*   assert (y \notin DFv e) by auto. *)
(*   destruct~ (H y H1 H2) as [_ [_ [[H3 _] _]]]. *)
(*   apply* (H3 x U). *)
(*   pick_fresh y. assert (y \notin L) by auto. *)
(*   assert (y \notin DFv e) by auto. *)
(*   destruct~ (H y H1 H2) as [_ [_ [[_ H3] _]]]. *)
(*   apply* (H3 x T U). *)
  
(*   pick_fresh x. assert (x \notin L) by auto. *)
(*   assert (x \notin DFv e) by auto. *)
(*   destruct~ (H x H0 H1) as [_ [_ [_ [H2 _]]]]. *)
(* Qed. *)


(* Lemma regular_dwftyp : forall E t, DWfTyp E t -> *)
(*   (DWf E /\ ok E /\ contains_terms E /\ DTermTy t). *)
(* Proof. *)
(*   apply dwftyp_induct with *)
(*   (P := fun m E t T (_ : DTyping m E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTerm T) *)
(*   (P1 := fun E (_ : DWf E) => ok E /\ contains_terms E) *)
(*   (P2 := fun E t T (_ : DInst E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm T) *)
(*   (P3 := fun E t T(_ : DGen E t T) => DWf E /\ ok E /\ contains_terms E /\ DTerm t /\ DTermTy T);  *)
(*     unfolds contains_terms; intros; splits*. *)
  
(*   pick_fresh x. assert (x \notin L) by auto. *)
(*   destruct (H x H0) as [H1 [_ [_ _]]]. *)
(*   inversion* H1. false* empty_push_inv. *)
(*   destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*. *)
(*   destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*. *)
(*   destruct (eq_push_inv H2) as [_ [_ Eq]]. subst*. *)

(*   pick_fresh x. assert (x \notin L) by auto. *)
(*   destruct~ (H x H0) as [_ [H1 [_ _]]]. *)

(*   split; intros. *)
(*   pick_fresh y. assert (y \notin L) by auto. *)
(*   destruct~ (H y H1) as (_ & _ & (H2 & _) & _). *)
(*   apply* (H2 x U). *)
(*   pick_fresh y. assert (y \notin L) by auto. *)
(*   destruct~ (H y H1) as (_ & _ & (_ & H2) & _). *)
(*   apply* (H2 x T U).  *)
  
(*   intros. false* binds_empty_inv. *)
(*   intros. false* binds_empty_inv. *)

(*   intros. destruct (binds_push_inv H1) as [[? ?]|[? ?]]. *)
(*   injection H3; intros. subst*. *)
(*   destruct H as [_ [H4 _]]. *)
(*   apply H4 with (x := x0). auto. *)

(*   intros. destruct (binds_push_inv H1) as [[? ?]|[? ?]]. *)
(*   false*. destruct H as [_ [_ H4]]. *)
(*   apply H4 with (x := x0). auto. *)

(*   intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]]. *)
(*   false*. destruct H as [_ [H5 _]]. *)
(*   apply H5 with (x := x0). auto. *)

(*   intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]]. *)
(*   injection H4; intros. subst*. *)
(*   destruct H as [_ [_ H5]]. *)
(*   apply H5 with (x := x0). auto. *)

(*   intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]]. *)
(*   false*. destruct H as [_ [H5 _]]. *)
(*   apply H5 with (x := x0). auto. *)

(*   intros. destruct (binds_push_inv H2) as [[? ?]|[? ?]]. *)
(*   injection H4; intros. subst*. *)
(*   pick_fresh y. assert (y \notin L) by auto. *)
(*   destruct (H1 y H3) as [_ [_ H5]]. *)
(*   destruct (H5 x (s ^' y) t). auto. split*. *)
(*   destruct H as [_ [_ H5]]. *)
(*   apply H5 with (x := x0). auto. *)

(*   pick_fresh x. assert (x \notin L) by auto. *)
(*   assert (x \notin DFv e) by auto. *)
(*   destruct (H x H0 H1) as [H2 [_ [_ _]]]. *)
(*   inversion* H2. false* empty_push_inv. *)
(*   destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*. *)
(*   destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*. *)
(*   destruct (eq_push_inv H3) as [_ [_ Eq]]. subst*. *)

(*   pick_fresh x. assert (x \notin L) by auto. *)
(*   assert (x \notin DFv e) by auto. *)
(*   destruct~ (H x H0 H1) as [_ [H2 [_ _]]]. *)

(*   split; intros. *)
(*   pick_fresh y. assert (y \notin L) by auto. *)
(*   assert (y \notin DFv e) by auto. *)
(*   destruct~ (H y H1 H2) as [_ [_ [[H3 _] _]]]. *)
(*   apply* (H3 x U). *)
(*   pick_fresh y. assert (y \notin L) by auto. *)
(*   assert (y \notin DFv e) by auto. *)
(*   destruct~ (H y H1 H2) as [_ [_ [[_ H3] _]]]. *)
(*   apply* (H3 x T U). *)
  
(*   pick_fresh x. assert (x \notin L) by auto. *)
(*   assert (x \notin DFv e) by auto. *)
(*   destruct~ (H x H0 H1) as [_ [_ [_ [H2 _]]]]. *)
(* Qed. *)

(* Hint Extern 1 (DTerm ?t) => match goal with *)
(*   | H: DTyping _ _ t _ |- _ => apply (proj32 (proj33 (regular_dtyping H))) *)
(*   | H: DTyping _ _ _ t |- _ => apply (proj33 (proj33 (regular_dtyping H))) *)
(*   end. *)

(* Hint Extern 1 (DTermTy ?s) => match goal with *)
(*   | H: DGen _ _ s  |- _ => apply (proj33 (proj33 (regular_dgen H))) *)
(*   | H: DWfTyp _ s  |- _ => apply (proj44 (regular_dwftyp H)) *)
(*   end. *)

(* Lemma dok_from_wf : forall E, DWf E -> ok E. *)
(* Proof. *)
(*   induction 1. auto. autos* (regular_dtyping H1). *)
(*   autos* (regular_dtyping H2). *)
(*   autos* (regular_dwftyp H1). *)
(* Qed. *)

(* Hint Extern 1 (ok ?E) => match goal with *)
(*   | H: DWf E |- _ => apply (dok_from_wf H) *)
(*   end. *)

(* Hint Extern 1 (DWf ?E) => match goal with *)
(*   | H: DTyping _ E _ _ |- _ => apply (proj1 (regular_dtyping H)) *)
(*   | H: DInst E _ _    |- _ => apply (proj1 (regular_dinst H)) *)
(*   | H: DGen E _ _     |- _ => apply (proj1 (regular_dgen H)) *)
(*   | H: DWfTyp E _     |- _ => apply (proj1 (regular_dwftyp H))    *)
(*   end. *)

(* Lemma dwf_push_inv : forall E x U, *)
(*   DWf (E & x ~ DC_Typ U) -> DWf E /\ DTermTy U. *)
(* Proof. *)
(*   introv W. inversions W.  *)
(*   false (empty_push_inv H0). *)
(*   destruct (eq_push_inv H) as [? [? ?]]. *)
(*   false*. *)
(*   destruct (eq_push_inv H) as [? [? ?]]. *)
(*   injection H4; intros. *)
(*   subst~. *)
(*   destruct (eq_push_inv H) as [? [? ?]]. *)
(*   false*. *)
(*   destruct (eq_push_inv H) as [? [? ?]]. *)
(*   false*. *)
(* Qed. *)

(* Lemma dterm_from_binds_in_wf : forall x E U, *)
(*   DWf E -> binds x (DC_Typ U) E -> DTerm U. *)
(* Proof. *)
(*   introv W Has. gen E. induction E using env_ind; intros. *)
(*   false* binds_empty_inv. *)
(*   destruct (binds_push_inv Has) as [[? ?]|[? ?]]. *)
(*   subst~. destruct~ (dwf_push_inv W). *)
(*   apply* IHE. *)
(*   inversions* W. false* empty_push_inv. *)
(*   destruct (eq_push_inv H1) as [_ [_ Eq]]. subst*. *)
(*   destruct (eq_push_inv H1) as [_ [_ Eq]]. subst*. *)
(*   destruct (eq_push_inv H1) as [_ [_ Eq]]. subst*. *)
(* Qed. *)

(* Hint Extern 1 (DTerm ?t) => match goal with *)
(*   H: binds ?x (DC_Typ t) ?E |- _ => apply (@dterm_from_binds_in_wf x E) *)
(*   end. *)

(* Lemma dwf_left : forall E F : DCtx, *)
(*   DWf (E & F) -> DWf E. *)
(* Proof. *)
(*   intros. induction F using env_ind. *)
(*   rewrite~ concat_empty_r in H. *)
(*   rewrite concat_assoc in H. *)
(*    inversions H. false (empty_push_inv H1). *)
(*    destruct (eq_push_inv H0) as [? [? ?]]. subst~.  *)
(*    destruct (eq_push_inv H0) as [? [? ?]]. subst~.  *)
(*    destruct (eq_push_inv H0) as [? [? ?]]. subst~.  *)
(* Qed. *)

(* Implicit Arguments dwf_left [E F]. *)

(** Freshness *)

(* Lemma dfv_open_var : forall y x t, *)
(*   x <> y -> x \notin DFv (t ^ y) -> x \notin DFv t. *)
(* Proof. *)
(*   introv Neq. unfold DOpen. generalize 0.  *)
(*   induction t; simpl; intros; try notin_solve. *)
(*   specializes IHt1 n. auto. specializes IHt2 n. auto. *)
(*   specializes IHt (S n). auto. *)
(*   specializes IHt1 n. auto. specializes IHt2 (S n). auto. *)
(*   specializes IHt1 n. auto. specializes IHt2 (S n). auto. *)
(*   specializes IHt n. auto. *)
(*   specializes IHt n. auto. *)
(*   specializes IHt1 n. auto. specializes IHt2 n. auto. *)
(* Qed. *)

(* Lemma dtyping_fresh : forall m x E t T, *)
(*     DTyping m E t T -> x # E -> x \notin DFv t *)
(* with dgen_fresh : forall x E t s, *)
(*     DGen E t s -> x # E -> x \notin DFv t. *)
(* Proof. *)
(*   introv Typ. *)
(*   induction Typ; simpls; intros. *)
(*   auto. *)
(*   rewrite notin_singleton. intro. subst. applys binds_fresh_inv H0 H1. *)
(*   rewrite notin_singleton. intro. subst. applys binds_fresh_inv H0 H2. *)
(*   lets: (IHTyp1 H). lets: (IHTyp2 H). auto. *)
(*   pick_fresh y. apply* (@dfv_open_var y). *)
(*   lets: (IHTyp1 H). lets: (IHTyp2 H). auto. *)
(*   pick_fresh y. notin_simpl. *)
(*   apply* dgen_fresh. *)
(*   apply* (@dfv_open_var y). *)
(*   pick_fresh y. notin_simpl. auto. apply* (@dfv_open_var y). *)
(*   lets: (IHTyp H0). auto. *)
(*   lets: (IHTyp H0). auto. *)
(*   pick_fresh y. notin_simpl. auto. apply* (@dfv_open_var y). *)
(*   pick_fresh y. notin_simpl. *)
(*   apply* dgen_fresh. *)
(*   apply* (@dfv_open_var y). *)
(*   lets: (IHTyp H0). auto. *)
(*   lets: (IHTyp H). auto. *)
 
(*   introv Gen. *)
(*   induction Gen; simpls; intros. *)
(*   apply* dtyping_fresh. *)
(*   pick_fresh y. apply* H0. *)
(* Qed. *)

(* Lemma notin_dfv_from_dwf : forall E F x V, *)
(*   DWf (E & x ~ DC_Typ V & F) -> x \notin DFv V. *)
(* Proof. *)
(*   intros. *)
(*   lets W: (dwf_left H). inversions W. *)
(*   false (empty_push_inv H1). *)
(*   destruct (eq_push_inv H0) as [? [? ?]]. *)
(*   injection H5. intros. *)
(*   subst~. *)
(*   apply* dtyping_fresh. *)
(*   destruct (eq_push_inv H0) as [? [? ?]]. *)
(*   false*. *)
(*   destruct (eq_push_inv H0) as [? [? ?]]. *)
(*   false*. *)
(* Qed. *)

(* Lemma notin_dfv_from_binds : forall x y U E, *)
(*   DWf E -> binds y (DC_Typ U) E -> x # E -> x \notin DFv U. *)
(* Proof. *)
(*   induction E using env_ind; intros. *)
(*   false* binds_empty_inv. *)
(*   destruct v. *)
(*   destruct (dwf_push_inv H). *)
(*   destruct (binds_push_inv H0) as [[? ?]|[? ?]]; subst. *)
(*   inversions H. false* (empty_push_inv H6). *)
(*   injection H5; intros; subst. *)
(*   destruct (eq_push_inv H4) as [? [? ?]]. subst~.  *)
(*   injection H9; intros; subst. *)
(*   apply dtyping_fresh with (m := Chk)(E := E)(T := DE_Star). *)
(*   auto. auto.    *)
(*   destruct (eq_push_inv H4) as [? [? ?]]. false*. *)
(*   destruct (eq_push_inv H4) as [? [? ?]]. false*. *)
(*   apply* IHE. *)
(*   destruct (binds_push_inv H0) as [[? ?]|[? ?]]; subst. *)
(*   false*. *)
(*   inversions H. false* (empty_push_inv H5). *)
(*   destruct (eq_push_inv H4) as [? [? ?]]. false*.  *)
(*   destruct (eq_push_inv H4) as [? [? ?]]; subst~. *)
(*   destruct (eq_push_inv H4) as [? [? ?]]; subst~. *)
(* Qed. *)

(* Lemma notin_dfv_from_binds' : forall E F x V y U, *)
(*   DWf (E & x ~ DC_Typ V & F) -> binds y (DC_Typ U) E -> x \notin DFv U. *)
(* Proof. *)
(*   intros. lets W: (dwf_left H). inversions keep W. *)
(*   false (empty_push_inv H2).  *)
(*   destruct (eq_push_inv H1) as [? [? ?]]. subst~.  *)
(*   lets W': (dwf_left W). apply* notin_dfv_from_binds. *)
(*   destruct (eq_push_inv H1) as [? [? ?]]. false*. *)
(*   destruct (eq_push_inv H1) as [? [? ?]]. false*. *)
(* Qed. *)

(* Hint Extern 1 (?x \notin DFv ?V) =>  *)
(*   match goal with H: DWf (?E & x ~ DC_Typ V & ?F) |- _ => *)
(*     apply (@notin_dfv_from_dwf E F) end. *)

(* Hint Extern 1 (?x \notin DFv ?U) =>  *)
(*   match goal with H: DWf (?E & x ~ DC_Typ ?V & ?F), B: binds ?y U ?E |- _ => *)
(*     apply (@notin_dfv_from_binds' E F x V y) end. *)
