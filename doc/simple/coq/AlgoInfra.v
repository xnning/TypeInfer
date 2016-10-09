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

Hint Constructors ARed ATyping AMode ARFMode AWfTyp AWf
     AUnify AResolveEVar AResolveForall AWTerm AWTermT.

(** Substitution *)

Hint Constructors ATerm.

(* Substitution on indices is identity on well-formed terms. *)

Lemma aopen_rec_term_core :forall e j v i u, i <> j ->
  AOpenRec j v e = AOpenRec i u (AOpenRec j v e) -> e = AOpenRec i u e
with
aopent_rec_term_core :forall e j v i u, i <> j ->
  AOpenTypRec j v e = AOpenTypRec i u (AOpenTypRec j v e) -> e = AOpenTypRec i u e.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.  
  case_nat*. case_nat*.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.
Qed.

Lemma atopen_rec_term_core :forall e j v i u, i <> j ->
  ATOpenRec j v e = ATOpenRec i u (ATOpenRec j v e) -> e = ATOpenRec i u e
with
atopent_rec_term_core :forall e j v i u, i <> j ->
  ATOpenTypRec j v e = ATOpenTypRec i u (ATOpenTypRec j v e) -> e = ATOpenTypRec i u e.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma aopen_atopen_rec_term_core :forall e j v i u, i <> j ->
  ATOpenRec j v e = AOpenRec i u (ATOpenRec j v e) -> e = AOpenRec i u e
with
aopent_atopent_rec_term_core :forall e j v i u, i <> j ->
  ATOpenTypRec j v e = AOpenTypRec i u (ATOpenTypRec j v e) -> e = AOpenTypRec i u e.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.
Qed.

Lemma atopen_aopen_rec_term_core :forall e j v i u, i <> j ->
  AOpenRec j v e = ATOpenRec i u (AOpenRec j v e) -> e = ATOpenRec i u e
with
atopent_aopent_rec_term_core :forall e j v i u, i <> j ->
  AOpenTypRec j v e = ATOpenTypRec i u (AOpenTypRec j v e) -> e = ATOpenTypRec i u e.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.
Proof.
  induction e; introv Neq Equ;
  simpl in *; inversion* Equ; f_equal*.
Qed.

Lemma aopen_rec_term : forall t u,
  ATerm t -> forall k, t = AOpenRec k u t
with aopent_rec_term : forall t u,
  ATermTy t -> forall k, t = AOpenTypRec k u t.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds AOpen. pick_fresh x.
   apply* (@aopen_rec_term_core e 0 (AE_FVar x)).
  unfolds AOpen. pick_fresh x.
   apply* (@aopent_rec_term_core t2 0 (AE_FVar x)).
  unfolds AOpen. pick_fresh x.
   apply* (@aopent_atopent_rec_term_core t 0 (AT_TFVar x)).
Proof.
  induction 1; intros; simpl; f_equal*.
Qed.

Lemma atopen_rec_term : forall t u,
  ATerm t -> forall k, t = ATOpenRec k u t
with atopent_rec_term : forall t u,
  ATermTy t -> forall k, t = ATOpenTypRec k u t.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds AOpen. pick_fresh x.
   apply* (@atopen_aopen_rec_term_core e 0 (AE_FVar x)).
  unfolds AOpen. pick_fresh x.
   apply* (@atopent_aopent_rec_term_core t2 0 (AE_FVar x)).
  unfolds AOpen. pick_fresh x.
   apply* (@atopent_rec_term_core t 0 (AT_TFVar x)).
Proof.
  induction 1; intros; simpl; f_equal*.
Qed.

Lemma aopen_var_inj : forall x t1 t2,
  x \notin (AFv t1) -> x \notin (AFv t2) ->
  forall k, (AOpenRec k (AE_FVar x) t1 = AOpenRec k (AE_FVar x) t2) -> (t1 = t2)
with
atopen_var_inj : forall x t1 t2,
  x \notin (ATFv t1) -> x \notin (ATFv t2) ->
  forall k, (AOpenTypRec k (AE_FVar x) t1 = AOpenTypRec k (AE_FVar x) t2) -> (t1 = t2).
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
  inversion H1; subst. f_equal ~. apply* atopen_var_inj. apply* atopen_var_inj.
  destruct t2; simpl; intros; try(case_nat~); try(solve[inversion H1]); auto.
  inversion H1; subst. f_equal ~. apply* IHt1.
  destruct t2; simpl; intros; try(case_nat~); try(solve[inversion H1]); auto.
  inversion H1; subst. f_equal ~. apply* IHt1.
  destruct t2; simpl; intros; try(case_nat~); try(solve[inversion H1]); auto.
  inversion H1; subst. f_equal ~. apply* IHt1. apply* atopen_var_inj.
  destruct t2; simpl; intros; try(case_nat~); try(solve[inversion H1]); auto.
  inversion H1; subst. f_equal ~. apply* atopen_var_inj.

  intros x t1.
  destruct t1; intros t2; destruct t2; simpl; intros; inversion H1; auto.
  lets: aopen_var_inj H3; auto.
  subst~.
Qed.

Lemma open_reorder: forall e1 e2 i j e,
    ATerm e1 ->
    ATerm e2 ->
    i <> j ->
    AOpenRec i e1 (AOpenRec j e2 e) = AOpenRec j e2 (AOpenRec i e1 e)
with
 opent_reorder: forall e1 e2 i j e,
    ATerm e1 ->
    ATerm e2 ->
    i <> j ->
    AOpenTypRec i e1 (AOpenTypRec j e2 e) = AOpenTypRec j e2 (AOpenTypRec i e1 e).
Proof.
  introv te1 te2 neq.
  gen i j. induction e; introv neq; simpls; auto; try(solve[f_equal ~]).
  case_nat~. case_nat~. simpls. case_if~. symmetry. apply~ aopen_rec_term.
  case_nat~. simpls. case_if~. apply~ aopen_rec_term.
  simpls. case_if~. case_if~.
Proof.
  introv te1 te2 neq.
  gen i j. induction e; introv neq; simpls; auto; try(solve[f_equal ~]).
Qed.

Lemma topen_reorder: forall e1 e2 i j e,
    ATermTy e1 ->
    ATermTy e2 ->
    i <> j ->
    ATOpenRec i e1 (ATOpenRec j e2 e) = ATOpenRec j e2 (ATOpenRec i e1 e)
with
topent_reorder: forall e1 e2 i j e,
    ATermTy e1 ->
    ATermTy e2 ->
    i <> j ->
    ATOpenTypRec i e1 (ATOpenTypRec j e2 e) = ATOpenTypRec j e2 (ATOpenTypRec i e1 e).
Proof.
  introv te1 te2 neq.
  gen i j. induction e; introv neq; simpls; auto; try(solve[f_equal ~]).
Proof.
  introv te1 te2 neq.
  gen i j. induction e; introv neq; simpls; auto; try(solve[f_equal ~]).
  case_nat~. case_nat~. simpls. case_if~. symmetry. apply~ atopent_rec_term.
  case_nat~. simpls. case_if~. apply~ atopent_rec_term.
  simpls. case_if~. case_if~.
Qed.

Lemma notin_open_inv : forall x y n e,
    x \notin AFv e ->
    x \notin AFv y ->
    x \notin AFv (AOpenRec n y e)
with notin_opent_inv : forall x y n e,
    x \notin ATFv e ->
    x \notin AFv y ->
    x \notin ATFv (AOpenTypRec n y e).
Proof.
  introv notin neq.
  gen n. induction e; introv; simpls; auto.
  case_if. auto. simpl.  auto.
Proof.
  introv notin neq.
  gen n. induction e; introv; simpls; auto.
Qed.

Lemma notin_topen_inv : forall x y n e,
    x \notin AFv e ->
    x \notin ATFv y ->
    x \notin AFv (ATOpenRec n y e)
with notin_topent_inv : forall x y n e,
    x \notin ATFv e ->
    x \notin ATFv y ->
    x \notin ATFv (ATOpenTypRec n y e).
Proof.
  introv notin neq.
  gen n. induction e; introv; simpls; auto.
Proof.
  introv notin neq.
  gen n. induction e; introv; simpls; auto.
  case_if. auto. simpl.  auto.
Qed.

(* Substitution for a fresh name is identity. *)

Lemma asubst_fresh : forall x t u, 
  x \notin AFv t -> ASubst x u t = t
with atsubst_fresh : forall x t u,
  x \notin ATFv t -> ATSubst x u t = t.
Proof.
  intros. induction t; simpls; fequals*.
  case_var*.
Proof.
  intros. induction t; simpls; fequals*.
Qed.

Lemma asubstt_fresh : forall x t u,
  x \notin AFv t -> ASubstT x u t = t
with atsubstt_fresh : forall x t u,
  x \notin ATFv t -> ATSubstT x u t = t.
Proof.
  intros. induction t; simpls; fequals*.
Proof.
  intros. induction t; simpls; fequals*.
  case_var*. case_var*.
Qed.

(* Substitution distributes on the open operation. *)

Lemma asubst_openrec : forall n x u t1 t2, ATerm u -> 
  ASubst x u (AOpenRec n t2 t1) = AOpenRec n (ASubst x u t2) (ASubst x u t1)
with
atsubst_opentyprec : forall n x u t1 t2, ATerm u ->
  ATSubst x u (AOpenTypRec n t2 t1) = AOpenTypRec n (ASubst x u t2) (ATSubst x u t1).
Proof.
  intros. gen n.
  induction t1; intros; simpl; f_equal*.
  case_nat*. case_var*. apply* aopen_rec_term.
Proof.
  intros. induction t1; simpls; fequal *.
Qed.

Lemma asubst_topenrec : forall n x u t1 t2, ATerm u ->
  ASubst x u (ATOpenRec n t2 t1) = ATOpenRec n (ATSubst x u t2) (ASubst x u t1)
with
atsubst_topentyprec : forall n x u t1 t2, ATerm u ->
  ATSubst x u (ATOpenTypRec n t2 t1) = ATOpenTypRec n (ATSubst x u t2) (ATSubst x u t1).
Proof.
  intros. gen n.
  induction t1; intros; simpl; f_equal*.
  case_if*. apply* atopen_rec_term.
Proof.
  intros. induction t1; simpls; fequal *.
  case_nat*.
Qed.

Lemma asubstt_openrec : forall n x u t1 t2, ATermTy u ->
  ASubstT x u (AOpenRec n t2 t1) = AOpenRec n (ASubstT x u t2) (ASubstT x u t1)
with
atsubstt_opentyprec : forall n x u t1 t2, ATermTy u ->
  ATSubstT x u (AOpenTypRec n t2 t1) = AOpenTypRec n (ASubstT x u t2) (ATSubstT x u t1).
Proof.
  intros. gen n.
  induction t1; intros; simpl; f_equal*.
  case_nat*.
Proof.
  intros. induction t1; simpls; fequal *.
  case_if*. apply* aopent_rec_term.
  case_if*. apply* aopent_rec_term.
Qed.

Lemma asubstt_topenrec : forall n x u t1 t2, ATermTy u ->
  ASubstT x u (ATOpenRec n t2 t1) = ATOpenRec n (ATSubstT x u t2) (ASubstT x u t1)
with
atsubstt_topentyprec : forall n x u t1 t2, ATermTy u ->
  ATSubstT x u (ATOpenTypRec n t2 t1) = ATOpenTypRec n (ATSubstT x u t2) (ATSubstT x u t1).
Proof.
  intros. gen n.
  induction t1; intros; simpl; f_equal*.
Proof.
  intros. induction t1; simpls; fequal *.
  case_nat*.
  case_if*. apply* atopent_rec_term.
  case_if*. apply* atopent_rec_term.
Qed.

Lemma asubst_open : forall x u t1 t2, ATerm u -> 
  ASubst x u (t1 @@ t2) = (ASubst x u t1) @@ (ASubst x u t2)
with
  atsubst_open : forall x u t1 t2, ATerm u ->
  ATSubst x u (t1 @@' t2) = (ATSubst x u t1) @@' (ASubst x u t2).
Proof.
  intros. apply* asubst_openrec.
Proof.
  intros. unfold AOpenT. generalize 0.
  induction t1; intros; simpl; f_equal*.
  apply* asubst_openrec.
Qed.

Lemma asubst_topen : forall x u t1 t2, ATerm u ->
  ASubst x u (t1 @@# t2) = (ASubst x u t1) @@# (ATSubst x u t2)
with
  atsubst_topen : forall x u t1 t2, ATerm u ->
  ATSubst x u (t1 @@#' t2) = (ATSubst x u t1) @@#' (ATSubst x u t2).
Proof.
  intros. apply* asubst_topenrec.
Proof.
  intros. unfold AOpenT. generalize 0.
  induction t1; intros; simpl; f_equal*.
  apply* atsubst_topentyprec.
  unfold ATOpenT. simpls. f_equal *.
Qed.

Lemma asubstt_open : forall x u t1 t2, ATermTy u ->
  ASubstT x u (t1 @@ t2) = (ASubstT x u t1) @@ (ASubstT x u t2)
with
  atsubstt_open : forall x u t1 t2, ATermTy u ->
  ATSubstT x u (t1 @@' t2) = (ATSubstT x u t1) @@' (ASubstT x u t2).
Proof.
  intros. apply* asubstt_openrec.
Proof.
  intros. unfold AOpenT. generalize 0.
  induction t1; intros; simpl; f_equal*.
  case_if*. apply* aopent_rec_term.
  case_if*. apply* aopent_rec_term.
  apply* asubstt_openrec.
Qed.

Lemma asubstt_topen : forall x u t1 t2, ATermTy u ->
  ASubstT x u (t1 @@# t2) = (ASubstT x u t1) @@# (ATSubstT x u t2)
with
  atsubstt_topen : forall x u t1 t2, ATermTy u ->
  ATSubstT x u (t1 @@#' t2) = (ATSubstT x u t1) @@#' (ATSubstT x u t2).
Proof.
  intros. apply* asubstt_topenrec.
Proof.
  intros. unfold AOpenT. generalize 0.
  induction t1; intros; simpl; f_equal*.
  apply* atsubstt_topentyprec.
  case_if*. apply* atopent_rec_term.
  case_if*. apply* atopent_rec_term.
  unfold ATOpenT. simpls. f_equal *.
Qed.

(* Substitution and open_var for distinct names commute. *)

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

Lemma asubst_open_tvar : forall x y u e, y <> x -> ATerm u ->
  (ASubst x u e) @# y = ASubst x u (e @# y).
Proof.
  introv Neq Wu. rewrite* asubst_topen.
Qed.

Lemma atsubst_open_tvar : forall x y u e, y <> x -> ATerm u ->
  (ATSubst x u e) @#' y = ATSubst x u (e @#' y).
Proof.
  introv Neq Wu. rewrite* atsubst_topen.
Qed.

Lemma asubstt_open_var : forall x y u e, y <> x -> ATermTy u ->
  (ASubstT x u e) @ y = ASubstT x u (e @ y).
Proof.
  introv Neq Wu. rewrite* asubstt_open.
Qed.

Lemma atsubstt_open_var : forall x y u e, y <> x -> ATermTy u ->
  (ATSubstT x u e) @' y = ATSubstT x u (e @' y).
Proof.
  introv Neq Wu. rewrite* atsubstt_open.
Qed.

Lemma asubstt_open_tvar : forall x y u e, y <> x -> ATermTy u ->
  (ASubstT x u e) @# y = ASubstT x u (e @# y).
Proof.
  introv Neq Wu. rewrite* asubstt_topen.
  simpl. case_var*.
Qed.

Lemma atsubstt_open_tvar : forall x y u e, y <> x -> ATermTy u ->
  (ATSubstT x u e) @#' y = ATSubstT x u (e @#' y).
Proof.
  introv Neq Wu. rewrite* atsubstt_topen.
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

Lemma asubstt_intro : forall x t u,
  x \notin (AFv t) -> ATermTy u ->
  t @@# u = ASubstT x u (t @# x).
Proof.
  introv Fr Wu. rewrite* asubstt_topen.
  rewrite* asubstt_fresh. simpl. case_var*.
Qed.

Lemma atsubstt_intro : forall x t u,
  x \notin (ATFv t) -> ATermTy u ->
  t @@#' u = ATSubstT x u (t @#' x).
Proof.
  introv Fr Wu. rewrite* atsubstt_topen.
  rewrite* atsubstt_fresh. simpl. case_var*.
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
  ATerm u -> ATerm t -> ATerm (ASubst z u t)
with
atsubst_term : forall t z u,
  ATerm u -> ATermTy t -> ATermTy (ATSubst z u t)
with
asubstt_term : forall t z u,
  ATermTy u -> ATerm t -> ATerm (ASubstT z u t)
with
atsubstt_term : forall t z u,
  ATermTy u -> ATermTy t -> ATermTy (ATSubstT z u t).
Proof.
  induction 2; simple*.
  case_var*.
  apply_fresh* ATerm_Lam as y. rewrite* asubst_open_var.
  apply_fresh* ATerm_Pi as y. rewrite* atsubst_open_var.
  apply_fresh* ATerm_Forall as y. rewrite* atsubst_open_tvar.
Proof.
  induction 2; simple*.
  apply~ ATermTy_TFVar.
  apply~ ATermTy_EVar.
  apply* ATermTy_Expr.
Proof.
  induction 2; simple*.
  apply_fresh* ATerm_Lam as y. rewrite* asubstt_open_var.
  apply_fresh* ATerm_Pi as y. rewrite* atsubstt_open_var.
  apply_fresh* ATerm_Forall as y. rewrite* atsubstt_open_tvar.
Proof.
  induction 2; simple*.
  case_var*. apply~ ATermTy_TFVar.
  case_var*. apply~ ATermTy_EVar.
  apply* ATermTy_Expr.
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
  ATerm (AE_Pi t1 t2) -> ABodyTy t2.
Proof.
  intros. unfold ABodyTy. inversion* H.
Qed.

Lemma aterm_pi : forall t1 t2,
  ATerm (AE_Pi t1 t2) -> ATermTy t1.
Proof.
  intros. inversion* H.
Qed.

Lemma atermty_expr : forall e,
  ATermTy (AT_Expr e) -> ATerm e.
Proof.
  intros. inversions* H.
Qed.

Hint Extern 1 (ATerm ?t) =>
  match goal with
  | H: ATerm (AE_Pi t ?t2) |- _ => apply (@aterm_pi t2)
  | H: ATerm (AT_Expr ?t2) |- _ => apply (@atermty_expr t2)
  end.

Hint Extern 3 (ABody ?t) =>
  match goal with 
  | H: context [AE_Lam t] |- _ => apply (@abody_lam)
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
  | H: context [AE_Pi ?t1 t] |- _ => apply (@abody_pi t1)
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
  ATermTy t1 -> ABodyTy t2 -> ATerm (AE_Pi t1 t2).
Proof.
  intros. apply_fresh* ATerm_Pi as x.
Qed.

Lemma atermty_forall_prove : forall s,
  ATermTy s -> ATerm (AE_Forall s).
Proof.
  intros. apply_fresh* ATerm_Forall as x.
  inversion H. unfold ATOpenT. simpls. apply* ATermTy_TFVar.
  unfold ATOpenT. simpls. apply* ATermTy_EVar.
  unfold ATOpenT. simpls. apply* ATermTy_Expr. subst. rewrite <- atopen_rec_term; auto.
Qed.

Lemma atermty_expr_prove : forall e,
    ATerm e -> ATermTy (AT_Expr e).
Proof.
  intros. apply* ATermTy_Expr.
Qed.

Hint Resolve aterm_lam_prove
     aterm_pi_prove
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

Hint Extern 1 (ATerm (AE_Forall ?v (ATSubst ?x ?u ?t2))) =>
  match goal with H: ATerm (AE_Forall v t2) |- _ =>
  unsimpl (ATSubst x u (AE_Forall t2)) end.

Definition regular_actx (E : ACtx) :=
  AWf E /\ ok E /\
  (forall x U, binds x (AC_Typ U) E -> ATermTy U) /\
  (forall x T, binds x (AC_Solved_EVar T) E -> ATermTy T).
