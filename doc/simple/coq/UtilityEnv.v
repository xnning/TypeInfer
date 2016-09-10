Require Import DeclDef.
Require Import AlgoDef.
Require Import LibLN.
Require Import AlgoInfra.

Set Implicit Arguments.

Inductive Softness : ACtx -> Prop :=
  | Softness_Empty: Softness empty
  | Softness_Unsolved: forall G a, Softness G -> a # G -> Softness (G & a ~ AC_Unsolved_EVar)
  | Softness_Solved: forall G a t, Softness G -> a # G -> Softness (G & a ~ AC_Solved_EVar t).

(* properties about \in *)

Lemma union_left :forall {A} (x:A) E F,
    x \in E ->
    x \in (E \u F).
Proof.
  intros* H.
  assert(subset E (E \u F)). apply subset_union_weak_l.
  apply* (H0 x).
Qed.

Lemma union_right :forall {A} (x:A) E F,
    x \in E ->
    x \in (F \u E).
Proof.
  intros* H.
  assert(subset E (F \u E)). apply subset_union_weak_r.
  apply* (H0 x).
Qed.

(* split context into certain form *)

Lemma split_context : forall {A} (G:env A) x,
    x \in (dom G) ->
    exists G1 G2 v, G = G1 & (x ~ v) & G2.
Proof.
  intros* HX.
  induction G using env_ind.
  simpl_dom. rewrite in_empty in HX. inversion HX.
  destruct (eq_var_dec x x0); subst.
  exists* G (empty: env A) v. rewrite concat_empty_r. auto.
  simpl_dom.
  rewrite in_union in HX. destruct HX as [HX1 | HX2].
  rewrite* in_singleton in HX1.
  apply IHG in HX2. destruct HX2 as (G1 & G2 & v0 & HX); subst.
  exists* G1 (G2 & x0 ~ v) v0. rewrite* concat_assoc.
Qed.

Lemma split_bind_context: forall {A} (G : env A) x v,
    binds x v G ->
    exists G1 G2, G = G1 & (x ~ v) & G2.
Proof.
  intros* HX.
  induction G using env_ind.
  apply binds_empty_inv in HX. inversion HX.
  destruct (eq_var_dec x x0). subst.
  apply binds_push_eq_inv in HX. subst.
  exists* G (empty : env A). rewrite concat_empty_r. auto.
  apply binds_push_neq_inv in HX.
  apply IHG in HX.
  destruct HX as (G1 & G2 & HG).
  exists* G1 (G2 & x0 ~ v0).
  rewrite HG. rewrite concat_assoc. auto.
auto.
Qed.

Lemma tail_exists_eq : forall {A} x vx y vy (E F G: env A),
    x <> y ->
    E & x ~ vx = F & y ~ vy & G ->
    exists G1, G = G1 & x ~ vx.
Proof.
  introv Hxy H.
  induction G using env_ind.
  rewrite concat_empty_r in H. apply eq_push_inv in H.
  destruct H as [H1  H2]. apply Hxy in H1. inversion H1.
  rewrite concat_assoc in H.
  apply eq_push_inv in H; subst.
  destruct H as [xeq [veq Eeq]]; subst.
  exists* G.
Qed.

(* if a context is ok *)

Lemma ok_non_eq : forall {A} x vx y vy (E F G: env A),
    ok (E & x ~ vx & F & y ~ vy & G) -> x <> y.
Proof.
  introv H.
  apply ok_middle_inv in H. destruct H as [H _].
  simpl_dom. apply notin_union in H.  destruct H as [H _].
  apply notin_union in H.  destruct H as [_ H].
  apply* notin_singleton.
Qed.

Lemma tail_empty_eq : forall {A} x vx vy (G G1 I I1 I2: env A),
    ok I ->
    I = I1 & x ~ vy & I2 ->
    ok G ->
    G = G1 & x ~ vx ->
    G = I ->
    G1 = I1 /\ vx = vy /\ I2 = empty.
Proof.
  introv HIOK HI HGOK HG HEQ.
  induction I2 using env_ind.
  rewrite concat_empty_r in HI.
  subst. apply eq_push_inv in HEQ.
  auto_star.
  subst.
  rewrite concat_assoc in HEQ.
  apply eq_push_inv in HEQ.
  destruct HEQ as [HEQ _]. rewrite HEQ in *.
  rewrite concat_assoc in HIOK.
  rewrite <- concat_empty_r in HIOK.
  apply ok_non_eq in HIOK.
  assert False. apply* HIOK. inversion H.
Qed.

Lemma ok_middle_eq : forall {A} (I I1 I2 G G1 G2: env A) x v1 v2,
    ok I ->
    I = I1 & x ~ v1 & I2 ->
    ok G ->
    G = G1 & x ~ v2 & G2 ->
    I = G ->
    I1 = G1 /\ v1 = v2 /\ I2 = G2.
Proof.
  introv HIOK HI. gen I I1 G G1 G2 x v1 v2.
  induction I2 using env_ind.
  introv HIOK HI HGOK HG HEQ.
  rewrite concat_empty_r in HI.
  rewrite HI in HEQ. rewrite HG in HEQ.
  assert (I1 = G1 /\ v1 = v2 /\ G2 = empty).
  apply tail_empty_eq with (x0:=x) (G0:=I1 & x ~ v1) (I0 := G1 & x ~ v2 & G2). rewrite HG in HGOK. auto. auto. rewrite HI in HIOK. auto. auto. auto.
  destruct H as [H1 [H2 H3]].
  auto.

  introv HI HGOK HG HEQ. gen I I1 I2 G G1 x v1 v2.
  induction G2 using env_ind.
  introv OKI IHI OKG HI HG HEQ.
  rewrite concat_empty_r in HG.
  rewrite HI in HEQ. rewrite HG in HEQ.
  assert (G1 = I1 /\ v2 = v1 /\ (I2 & x ~ v) = empty). apply tail_empty_eq with (x1:=x0) (G0:=G1 & x0 ~ v2) (I0:= I1 & x0 ~ v1 & (I2 & x ~ v)); auto. rewrite HI in OKI; auto. rewrite HG in OKG; auto.
  destruct H as [_ [_ H]].
  assert (empty = I2 & x ~ v). auto.
  apply  empty_push_inv in H0. inversion H0.

  introv OKI IHI.
  introv OKG HI HG HEQ.

  rewrite concat_assoc in HI.
  rewrite concat_assoc in HG.
  rewrite HI in HEQ. rewrite HG in HEQ.
  assert (x1 = x /\ v = v0). apply eq_push_inv in HEQ. destruct HEQ as [HEQ1 [HEQ2 HEQ3]]. auto.
  destruct H as [HEQX HEQV]. rewrite HEQX in * ; clear HEQX; rewrite HEQV in *; clear HEQV.

  rewrite HI in OKI. apply ok_push_inv in OKI. destruct OKI as [OKI _].
  rewrite HG in OKG. apply ok_push_inv in OKG. destruct OKG as [OKG _].
  assert ( I1 = G1 /\ v1 = v2 /\ I2 = G2). apply IHI with (I := I1 & x0 ~ v1 & I2) (G := G1 & x0 ~ v2 & G2) (x:=x0); auto.
  apply eq_push_inv in HEQ. destruct HEQ as [_ [_ HEQ]]. auto.
  destruct H as [H1 [H2 H3]]. subst. auto.
Qed.

Lemma ok_middle_eq2: forall {A} (I1 I2 G1 G2: env A) x v1 v2,
    ok (I1 & x ~ v1 & I2) ->
    ok (G1 & x ~ v2 & G2) ->
    I1 & x ~ v1 & I2 = G1 & x ~ v2 & G2 ->
    I1 = G1 /\ v1 = v2 /\ I2 = G2.
Proof.
  introv oki okg eqig.
  apply ok_middle_eq with (I:= (I1 & x ~ v1 & I2)) (G:=(G1 & x ~ v2 & G2)) (x0:=x); auto.
Qed.

Lemma reverse_order_inv : forall A (G1 G2 G3 : env A) I1 I2 I3 x vx1 vx2 y vy1 vy2,
    ok (G1 & x ~ vx1 & G2 & y ~ vy1 & G3) ->
    ok (I1 & y ~ vy2 & I2 & x ~ vx2 & I3) ->
    (G1 & x ~ vx1 & G2 & y ~ vy1 & G3) = (I1 & y ~ vy2 & I2 & x ~ vx2 & I3) -> False.
Proof.
  introv OKG OKI HEQ.
  assert (G1 = I1 & y ~ vy2 & I2 /\ vx1 = vx2 /\ G2 & y ~ vy1 & G3 = I3).
  apply ok_middle_eq with (G:=I1 & y ~ vy2 & I2 & x ~ vx2 & I3) (I:=G1 & x ~ vx1 & G2 & y ~ vy1 & G3) (x0:=x); auto_star.
  rewrite* HEQ.
  rewrite* concat_assoc.
  rewrite* concat_assoc.

  assert (y \in dom (I1 & y ~ vy2 & I2)).
  simpl_dom. apply union_left. apply union_right. apply in_singleton_self.
  assert (y \notin dom G1).
  apply ok_middle_inv_l in OKG.
  simpl_dom. apply notin_union in OKG. destruct OKG as [OKG _].
  apply notin_union in OKG. destruct OKG as [OKG _]. auto.
  destruct H as [H _].
  rewrite <- H in H0.
  apply get_some in H0. inversion H0.
  assert (binds y x0 G1); auto.
  apply (binds_fresh_inv H3 H1).
Qed.

(* if a context is awf *)

Lemma awf_is_ok : forall G,
    AWf G ->
    ok G.
Proof.
  introv wf. induction wf; auto.
Qed.

Lemma AWf_left : forall G H,
    AWf (G & H) -> AWf G.
Proof.
  introv IH. gen_eq I: (G & H). gen G H. induction IH; intros IG HH HI;
  try(apply empty_concat_inv in HI; destruct HI as [HIG HIH]; subst; constructor);
  try(
  induction HH using env_ind;
  try(rewrite concat_empty_r in HI;
  rewrite <- HI; constructor; auto);
  try(rewrite concat_assoc in HI;
  apply eq_push_inv in HI; destruct HI as [HIx [HIv HIgh]]; apply* IHIH)).
  rewrite concat_empty_r in HI. rewrite <- HI. apply AWf_LetVar with (H:=H); auto.
  rewrite concat_empty_r in HI. rewrite <- HI. apply AWf_LetVar2 with (L:=L); auto.
Qed.

Lemma AWf_push_inv : forall G x v,
    AWf (G & x ~ v) -> x # G.
Proof.
  introv WF. inversion WF;
  try(apply empty_push_inv in H0; inversion H0);
  try(apply eq_push_inv in H; destruct H as [eqg [eqx eqv]]; subst; simpl_dom; auto).
  try(apply eq_push_inv in H0; destruct H0 as [eqg [eqx eqv]]; subst; simpl_dom; auto).
Qed.

(* atyping *)

Lemma atyping_awterm : forall G m e t H,
  ATyping m G e t H ->
  AWTerm G e.
Proof.
  introv ty.
  induction ty; simpl; auto.
  apply* AWTerm_TypVar.
  apply* AWTerm_LetVar.
Qed.

Lemma notin_open : forall x y e n,
    x \notin (AFv (AOpenRec n y e)) ->
    x \notin (AFv e).
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

Lemma notin_topen : forall x y e n,
    x \notin (ATFv (AOpenTypRec n y e)) ->
    x \notin (ATFv e).
Proof.
  introv notin. gen n.
  induction e; introv notin.
    simpl in *; auto_star.
    simpl in *. apply* notin_open.
Qed.

Lemma notin_awterm : forall G t x,
  AWTerm G t ->
  x # G ->
  x \notin AFv t.
Proof.
  introv wt notin. induction wt; simpl; auto;
      try(apply notin_singleton; unfold not; introv neq; subst; apply (binds_fresh_inv H notin0)).
  pick_fresh y. apply* notin_open. apply H0 with (x0:=y); auto_star.
  pick_fresh y. apply notin_union. split; auto. apply* notin_open. apply H0 with (x0:=y); auto_star.
  pick_fresh y. apply notin_union. split; auto. apply* notin_open. apply H0 with (x0:=y); auto_star.
Qed.

Lemma notin_typing: forall G m e t H x,
  ATyping m G e t H ->
  x # G ->
  x \notin AFv e.
Proof.
  introv ty notin. apply atyping_awterm in ty.
  apply* notin_awterm.
Qed.

Lemma notin_open_inv : forall x y n e,
    x \notin AFv e ->
    x \notin AFv y ->
    x \notin AFv (AOpenRec n y e).
Proof.
  introv notin neq.
  gen n. induction e; introv; simpls; auto.
  case_if. auto. simpl.  auto.
Qed.

Lemma awterm_remove: forall G H x v t,
    AWTerm (G & x ~ v & H) t ->
    x \notin AFv t ->
    AWTerm (G & H) t.
Proof.
  introv wt notin. gen_eq I: (G & x ~ v & H).
  gen H. induction wt; introv hh.
  simpl in notin. rewrite hh in H. apply AWTerm_Var. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTerm_TypVar. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTerm_LetVar. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTerm_EVar. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTerm_Solved_EVar. apply* binds_subst.
  constructor*.

  simpl in notin. apply AWTerm_App. apply* IHwt1. apply* IHwt2.

  apply AWTerm_Lam with (L \u \{x}). intros y notin_y.
  apply notin_union in notin_y. destruct notin_y as [notin_y notin_x]. apply H0 with (H:=H1 & y ~ AC_Var) in notin_y.  rewrite concat_assoc in notin_y. auto.
  simpl in notin. apply* notin_open_inv. simpl. apply* notin_singleton.
  rewrite hh. rewrite* concat_assoc.

  simpl in notin. apply AWTerm_Pi with (L \u \{x}). apply* IHwt. intros y notin_y.
  apply notin_union in notin_y. destruct notin_y as [notin_y notin_x]. apply H0 with (H:=H1 & y ~ AC_Var) in notin_y. rewrite concat_assoc in notin_y. auto.
  apply* notin_open_inv. simpl. apply* notin_singleton.
  rewrite hh. rewrite* concat_assoc.

  simpl in notin. apply AWTerm_Let with (L \u \{x}). apply* IHwt. intros y notin_y.
  apply notin_union in notin_y. destruct notin_y as [notin_y notin_x]. apply H0 with (H:=H1 & y ~ AC_Var) in notin_y.  rewrite concat_assoc in notin_y. auto.
  apply* notin_open_inv. simpl. apply* notin_singleton.
  rewrite hh. rewrite* concat_assoc.

  apply* AWTerm_CastUp.
  apply* AWTerm_CastDn.

  simpl in notin. apply* AWTerm_Ann.
Qed.

Lemma awterm_bnd: forall G x s t,
    AWf (G & x ~ AC_Bnd s t) ->
    AWTerm G t.
Proof.
  introv wf. gen_eq H : (G & x ~ AC_Bnd s t).
  gen G s. induction wf; introv hi; try(
  solve[apply eq_push_inv in hi; destruct hi as [eqx [eqv eqg]]; inversion eqv]); subst; auto.
  apply empty_push_inv in hi. inversion hi.
  apply eq_push_inv in hi; destruct hi as [eqx [eqv eqg]]; inversion eqv. subst. apply* atyping_awterm.

  apply eq_push_inv in hi; destruct hi as [eqx [eqv eqg]]. inversion eqv. subst.
  pick_fresh y.
  assert (AWTerm (G0 & y ~ AC_Typ AE_Star) t). apply* H2.
  rewrite <- concat_empty_r with (E:=G0).
  rewrite <- concat_empty_r with (E:=G0 & y ~ AC_Typ AE_Star) in H3.
  apply* awterm_remove.
Qed.

Lemma awterm_replace: forall G H x t e,
    AWTerm (G & x ~ AC_Typ t & H) e ->
    AWTerm (G & x ~ AC_Var & H) e.
Proof.
  introv wt. gen_eq I: (G & x ~ AC_Typ t & H).
  gen H. induction wt; introv hg; subst.

  destruct (eq_var_dec x x0). subst.
  apply binds_middle_inv in H. destruct H as [h1 | [h2 | h3]]. apply AWTerm_Var. apply binds_concat_right. auto.
  apply AWTerm_Var. apply* binds_middle_eq.
  destruct h3 as [_ [inv _]]. false inv. reflexivity.
  apply binds_subst in H; auto.
  apply AWTerm_Var. apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.

  destruct (eq_var_dec x x0). subst.
  apply binds_middle_inv in H. destruct H as [h1 | [h2 | h3]]. apply AWTerm_TypVar with t0. apply binds_concat_right. auto.
  apply AWTerm_Var. apply* binds_middle_eq.
  destruct h3 as [_ [inv _]]. false inv. reflexivity.
  apply binds_subst in H; auto.
  apply* AWTerm_TypVar. apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.

  destruct (eq_var_dec x x0). subst.
  apply binds_middle_inv in H. destruct H as [h1 | [h2 | h3]]. apply* AWTerm_LetVar.
  apply AWTerm_Var. apply* binds_middle_eq.
  destruct h3 as [_ [inv _]]. false inv. reflexivity.
  apply* AWTerm_LetVar. apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left. destruct h2 as [_ h2]. apply binds_concat_left_inv in h2. apply* binds_concat_left. auto_star.

  destruct (eq_var_dec x a). subst.
  apply binds_middle_inv in H. destruct H as [h1 | [h2 | h3]]. apply AWTerm_EVar. apply binds_concat_right. auto.
  destruct h2 as [_ [_ inv]]. false inv.
  apply AWTerm_EVar.  apply* binds_concat_left.
  apply* AWTerm_EVar. apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left. destruct h2 as [_ h2]. apply binds_concat_left_inv in h2. apply* binds_concat_left. auto_star.

  destruct (eq_var_dec x a). subst.
  apply binds_middle_inv in H. destruct H as [h1 | [h2 | h3]]. apply* AWTerm_Solved_EVar.
  destruct h2 as [_ [_ inv]]. false inv.
  apply AWTerm_Solved_EVar with t0. apply* binds_concat_left.
  apply* AWTerm_Solved_EVar. apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left. destruct h2 as [_ h2]. apply binds_concat_left_inv in h2. apply* binds_concat_left. auto_star.

  constructor.
  apply AWTerm_App. apply* IHwt1. apply* IHwt2.
  apply AWTerm_Lam with L. intros y notin_y. rewrite <- concat_assoc. apply* H0. rewrite* concat_assoc.
  apply AWTerm_Pi with L. apply* IHwt. intros y notin_y. rewrite <- concat_assoc. apply* H0. rewrite* concat_assoc.
  apply AWTerm_Let with L. apply* IHwt. intros y notin_y. rewrite <- concat_assoc. apply* H0. rewrite* concat_assoc.
  apply* AWTerm_CastUp.
  apply* AWTerm_CastDn.
  apply AWTerm_Ann. apply* IHwt1. apply* IHwt2.
Qed.

Lemma awterm_awftyp: forall G t,
    AWfTyp G (AT_Expr t) ->
    AWTerm G t.
Proof.
  introv wt.
  gen_eq s:(AT_Expr t).
  gen t. induction wt; introv hi.
  inversion hi; subst. apply* AWTerm_EVar.
  inversion hi; subst. apply* AWTerm_Solved_EVar.
  inversion hi; subst. clear hi.
  apply AWTerm_Pi with L.
  apply*  IHwt.
  intros y notin_y.
  apply H0 with (t:=t2 @ y) in notin_y; auto.
  rewrite <- concat_empty_r with (E:= G & y ~ AC_Var).
  rewrite <- concat_empty_r with (E:= G & y ~ AC_Typ t1) in notin_y.
  apply* awterm_replace.

  inversion hi.

  inversion hi; subst. apply* atyping_awterm.
Qed.

Lemma binds_swap : forall A (G1 G2 : env A) x v x1 v1 x2 v2,
    x1 <> x2 ->
    binds x v (G1 & x1 ~ v1 & x2 ~ v2 & G2) ->
    binds x v (G1 & x2 ~ v2 & x1 ~ v1 & G2).
Proof.
  intros.
  destruct (binds_concat_inv H0) as [Bnd1 | [Frsh Bnd2]].
  apply* binds_concat_right.
  destruct (binds_push_inv Bnd2) as [[Eq1 Eq2] | [NEeq Bnd]]; subst.
  apply* binds_concat_left.
  destruct (binds_push_inv Bnd) as [[Eq1' Eq2'] | [NEeq' Bnd']]; subst.
  apply* binds_concat_left.
  apply* binds_concat_left.
Qed.

Lemma awterm_reorder : forall G1 G2 x1 x2 v e,
    x1 <> x2 ->
    AWTerm (G1 & x2 ~ AC_Var & x1 ~ v & G2) e ->
    AWTerm (G1 & x1 ~ v & x2 ~ AC_Var & G2) e.
Proof.
  intros. inductions H0.
  apply* AWTerm_Var. apply* binds_swap.
  apply* AWTerm_TypVar. apply* binds_swap.
  apply* AWTerm_LetVar. apply* binds_swap.
  apply* AWTerm_EVar. apply* binds_swap.
  apply* AWTerm_Solved_EVar. apply* binds_swap.
  apply* AWTerm_Star.
  apply* AWTerm_App.

  apply AWTerm_Lam with (L := L); intros.
  assert (JMeq.JMeq (G1 & x2 ~ AC_Var & x1 ~ v & G2 & x ~ AC_Var)
                    (G1 & x2 ~ AC_Var & x1 ~ v & (G2 & x ~ AC_Var))).
  rewrite -> concat_assoc. auto.
  pose (Re := H0 x H2 v x2 x1 H (G2 & x ~ AC_Var) G1 H3).
  rewrite -> concat_assoc in Re.
  auto.

  apply AWTerm_Pi with (L := L). auto. intros.
  assert (JMeq.JMeq (G1 & x2 ~ AC_Var & x1 ~ v & G2 & x ~ AC_Var)
                    (G1 & x2 ~ AC_Var & x1 ~ v & (G2 & x ~ AC_Var))).
  rewrite -> concat_assoc. auto.
  pose (Re := H1 x H3 v x2 x1 H (G2 & x ~ AC_Var) G1 H4).
  rewrite -> concat_assoc in Re.
  auto.

  apply AWTerm_Let with (L := L). auto. intros.
  assert (JMeq.JMeq (G1 & x2 ~ AC_Var & x1 ~ v & G2 & x ~ AC_Var)
                    (G1 & x2 ~ AC_Var & x1 ~ v & (G2 & x ~ AC_Var))).
  rewrite -> concat_assoc. auto.
  pose (Re := H1 x H3 v x2 x1 H (G2 & x ~ AC_Var) G1 H4).
  rewrite -> concat_assoc in Re.
  auto.

  apply* AWTerm_CastUp.
  apply* AWTerm_CastDn.
  apply* AWTerm_Ann.
Qed.

Lemma awterm_reorder_simp : forall G1 x1 x2 v e,
    x1 <> x2 ->
    AWTerm (G1 & x2 ~ AC_Var & x1 ~ v) e ->
    AWTerm (G1 & x1 ~ v & x2 ~ AC_Var) e.
Proof.
  intros.
  assert (G1 & x2 ~ AC_Var & x1 ~ v = G1 & x2 ~ AC_Var & x1 ~ v & empty).
  rewrite* concat_empty_r.
  assert (G1 & x1 ~ v & x2 ~ AC_Var = G1 & x1 ~ v & x2 ~ AC_Var & empty).
  rewrite* concat_empty_r.
  rewrite H1 in H0.
  rewrite H2.
  apply* awterm_reorder.
Qed.

Lemma binds_push_fresh : forall A x v (G : env A) x' v',
    binds x v G -> x' # G ->
    binds x v (G & x' ~ v').
Proof.
  intros. apply* binds_push_neq.
  unfold not; intros. rewrite <- H1 in H0.
  apply binds_fresh_inv with (x := x) (v := v) (E := G).
  auto. auto.
Qed.

Lemma awterm_weaken : forall G x v e,
    AWTerm G e ->
    x # G ->
    AWTerm (G & x ~ v) e.
Proof.
  intros. inductions H.
  apply* AWTerm_Var. apply* binds_push_fresh.
  apply* AWTerm_TypVar. apply* binds_push_fresh.
  apply* AWTerm_LetVar. apply* binds_push_fresh.
  apply* AWTerm_EVar. apply* binds_push_fresh.
  apply* AWTerm_Solved_EVar. apply* binds_push_fresh.
  apply* AWTerm_Star.
  apply* AWTerm_App.
  apply AWTerm_Lam with (L := L \u \{x}); intros. apply* awterm_reorder_simp.
  apply AWTerm_Pi with (L := L \u \{x}); intros. apply* IHAWTerm. apply* awterm_reorder_simp.
  apply AWTerm_Let with (L := L \u \{x}); intros. apply* IHAWTerm. apply* awterm_reorder_simp.
  apply* AWTerm_CastUp.
  apply* AWTerm_CastDn.
  apply* AWTerm_Ann.
Qed.

Lemma awterm_weaken_ctx: forall G H e,
    ok (G & H) ->
    AWTerm G e ->
    AWTerm (G & H) e.
Proof.
  introv. induction H using env_ind; introv okg wf.
  rewrite* concat_empty_r.
  assert (AWTerm (G & H) e). apply* IHenv. rewrite concat_assoc in okg. apply* ok_push_inv_ok.
  rewrite concat_assoc. apply* awterm_weaken.
  rewrite concat_assoc in okg. apply* ok_push_inv.
Qed.

Lemma awterm_solved_evar: forall G x t,
    AWf (G & x ~ AC_Solved_EVar t) ->
    AWTerm G t.
Proof.
  introv wf. gen_eq H : (G & x ~ AC_Solved_EVar t).
  induction wf; introv hi; try(
  apply eq_push_inv in hi; destruct hi as [eqx [eqv eqg]]; inversion eqv); subst; auto.
  apply empty_push_inv in hi. inversion hi.
  apply* awterm_awftyp.
Qed.

Lemma awterm_evar_binds: forall G a t,
    AWf G ->
    binds a (AC_Solved_EVar t) G ->
    AWTerm G t.
Proof.
  introv wf bd. destruct (split_bind_context bd) as (G1 & G2 & HG).
  rewrite HG.
  assert (AWTerm G1 t). rewrite HG in wf. apply* awterm_solved_evar. apply* AWf_left.  auto.
  rewrite HG in wf.
  rewrite <- concat_assoc. apply* awterm_weaken_ctx. apply* awf_is_ok.
  rewrite* concat_assoc.
Qed.

Lemma atyping_awf: forall G m e t H,
    ATyping m G e t H ->
    AWf G.
Proof.
  introv ty.
  induction ty; simpl; auto.
  apply* AWf_left. rewrite* concat_assoc.
  apply* AWf_left.
Qed.

(* substitution *)

Lemma subst_empty_env : forall a,
    ACtxSubst empty a = a.
Proof.
  intro a.
  unfold ACtxSubst.
  rewrite empty_def.
  rewrite LibList.fold_left_nil.
  auto.
Qed.

Lemma tsubst_empty_env : forall a,
    ACtxTSubst empty a = a.
Proof.
  intro a.
  unfold ACtxTSubst.
  rewrite empty_def.
  rewrite LibList.fold_left_nil.
  auto.
Qed.

Lemma subst_star : forall G,
    ACtxSubst G AE_Star = AE_Star.
Proof.
  intro G.
  induction G.
  unfold ACtxSubst. auto.
  unfold ACtxSubst. destruct a. simpl.
  destruct a; auto.
Qed.

Lemma subst_add_var : forall G e x,
    ACtxSubst (G & x ~ AC_Var) e = ACtxSubst G e.
Proof.
  introv. rewrite <- cons_to_push.
  unfold ACtxTSubst. simpl. auto.
Qed.

Lemma tsubst_add_var : forall G e x,
    ACtxTSubst (G & x ~ AC_Var) e = ACtxTSubst G e.
Proof.
  introv. rewrite <- cons_to_push.
  unfold ACtxTSubst. simpl. auto.
Qed.

Lemma subst_add_typvar : forall G e x t,
    ACtxSubst (G & x ~ AC_Typ t) e = ACtxSubst G e.
Proof.
  introv. rewrite <- cons_to_push.
  unfold ACtxTSubst. simpl. auto.
Qed.

Lemma tsubst_add_typvar : forall G e x t,
    ACtxTSubst (G & x ~ AC_Typ t) e = ACtxTSubst G e.
Proof.
  introv. rewrite <- cons_to_push.
  unfold ACtxTSubst. simpl. auto.
Qed.

Lemma subst_add_evar : forall G e x,
     ACtxSubst (G & x ~ AC_Unsolved_EVar) e = ACtxSubst G e.
Proof.
  introv. rewrite <- cons_to_push.
  unfold ACtxTSubst. simpl. auto.
Qed.

Lemma tsubst_add_evar : forall G e x,
     ACtxTSubst (G & x ~ AC_Unsolved_EVar) e = ACtxTSubst G e.
Proof.
  introv. rewrite <- cons_to_push.
  unfold ACtxTSubst. simpl. auto.
Qed.

Lemma tsubst_add_bndvar: forall H x s t e,
    ACtxTSubst (H & x ~ AC_Bnd s t) e = ACtxTSubst H (ATSubst x t e).
Proof.
  introv. rewrite <- cons_to_push in *.
  unfold ACtxTSubst. simpl. auto.
Qed.

Lemma subst_add_bndvar: forall H x s t e,
    ACtxSubst (H & x ~ AC_Bnd s t) e = ACtxSubst H (ASubst x t e).
Proof.
  introv. rewrite <- cons_to_push in *.
  unfold ACtxTSubst. simpl. auto.
Qed.

Lemma tsubst_add_solved_evar: forall H x t e,
    ACtxTSubst (H & x ~ AC_Solved_EVar t) e = ACtxTSubst H (ATSubst x t e).
Proof.
  introv. rewrite <- cons_to_push in *.
  unfold ACtxTSubst. simpl. auto.
Qed.

Lemma subst_add_solved_evar: forall H x t e,
    ACtxSubst (H & x ~ AC_Solved_EVar t) e = ACtxSubst H (ASubst x t e).
Proof.
  introv. rewrite <- cons_to_push in *.
  unfold ACtxTSubst. simpl. auto.
Qed.

Lemma subst_add_ctx: forall G H e,
    ACtxSubst (G & H) e = ACtxSubst G (ACtxSubst H e).
Proof.
  introv.
  gen e. induction H using env_ind; introv.
  rewrite concat_empty_r. rewrite subst_empty_env. auto.
  induction v; rewrite concat_assoc.

  repeat(rewrite subst_add_var). auto.
  repeat(rewrite subst_add_typvar). auto.
  repeat(rewrite subst_add_bndvar). auto.
  repeat(rewrite subst_add_evar). auto.
  repeat(rewrite subst_add_solved_evar). auto.
Qed.

Lemma tsubst_add_ctx: forall G H e,
    ACtxTSubst (G & H) e = ACtxTSubst G (ACtxTSubst H e).
Proof.
  introv.
  gen e. induction H using env_ind; introv.
  rewrite concat_empty_r. rewrite tsubst_empty_env. auto.
  induction v; rewrite concat_assoc.

  repeat(rewrite tsubst_add_var). auto.
  repeat(rewrite tsubst_add_typvar). auto.
  repeat(rewrite tsubst_add_bndvar). auto.
  repeat(rewrite tsubst_add_evar). auto.
  repeat(rewrite tsubst_add_solved_evar). auto.
Qed.

Lemma subst_notin : forall x v e,
    x \notin (AFv e) ->
    ASubst x v e = e.
Proof.
  introv notin.
  induction e; simpls; auto; fequals*.
  case_var*.
  case_var*.
Qed.

Lemma subst_twice : forall x v e,
    x \notin (AFv v) ->
    ASubst x v (ASubst x v e) = ASubst x v e.
Proof.
  introv notin.
  induction e; simpl; auto;
    try(rewrite* IHe1; rewrite* IHe2);
    try(rewrite* IHe).
  destruct (eq_var_dec v0 x).
  case_var*. rewrite* subst_notin.
  case_var*. simpl. case_var*.
  case_var*. rewrite* asubst_fresh. simpl. case_var*.
Qed.

Lemma tsubst_twice: forall x v t,
    x \notin (AFv v) ->
    ATSubst x v (ATSubst x v t) = ATSubst x v t.
Proof.
  introv notin.
  induction t. simpls. rewrite* IHt.
  simpls. rewrite* subst_twice.
Qed.

Lemma tsubst_tsubst: forall x vx y vy e,
    x <> y ->
    x \notin AFv (vx) ->
    ATSubst x vx (ATSubst y vy e) =
    ATSubst x vx (ATSubst y (ASubst x vx vy) e) .
Proof.
 introv.
 induction e; introv neq notin.
 simpl.
 rewrite* IHe.

 induction a; simpl; auto;
   try(simpl in IHa1; inversion IHa1; rewrite H0;
       simpl in IHa2; inversion IHa2; rewrite H1);
   try(simpl in IHa; inversion IHa; rewrite H0); auto.

 destruct (eq_var_dec v y).
  case_var*. rewrite* subst_twice.
  case_var*.
  case_var*. rewrite* subst_twice.
Qed.

Lemma tsubst_tsubst_distr: forall x vx y vy e,
    x <> y ->
    x \notin AFv (vx) ->
    y \notin AFv (vx) ->
    ATSubst x vx (ATSubst y vy e) =
    ATSubst y (ASubst x vx vy) (ATSubst x vx e).
Proof.
  introv.
  induction e; introv neq notinx notiny.
  simpl.
  rewrite* IHe.

  induction a; simpl; auto;
   try(simpl in IHa1; inversion IHa1; rewrite H0;
       simpl in IHa2; inversion IHa2; rewrite H1);
   try(simpl in IHa; inversion IHa; rewrite H0); auto.
  destruct (eq_var_dec v y).
  case_var*.  case_var*. simpl. case_var*.
  destruct (eq_var_dec v x).
  case_var*. case_var*. simpl. case_var*. rewrite* subst_notin.
  case_var*. case_var*. simpl. case_var*. case_var*.
  case_var*. case_var*. simpl. case_var*. case_var*.
  simpl. case_var*. rewrite asubst_fresh with (x:=y); auto.
  simpl. case_var*. case_var*.
Qed.

Lemma subst_subst_distr: forall x vx y vy e,
    x <> y ->
    x \notin AFv (vx) ->
    y \notin AFv (vx) ->
    ASubst x vx (ASubst y vy e) =
    ASubst y (ASubst x vx vy) (ASubst x vx e).
Proof.
  introv.
  induction e; introv neq notinx notiny; simpl; auto;
    try(rewrite <- IHe; auto);
    try(rewrite <- IHe1; auto);
    try(rewrite <- IHe2; auto).
  destruct (eq_var_dec v y).
  case_var*.  case_var*. simpl. case_var*.
  destruct (eq_var_dec v x).
  case_var*. case_var*. simpl. case_var*. rewrite* subst_notin.
  case_var*. case_var*. simpl. case_var*. case_var*.
  case_var*. case_var*. simpl. case_var*. case_var*.
  simpl. case_var*. rewrite asubst_fresh with (x:=y); auto.
  simpl. case_var*. case_var*.
Qed.

(* notin *)


Lemma in_open: forall x y e n,
    x \in AFv e ->
    x \in AFv (AOpenRec n y e).
Proof.
  introv hi. gen n.
  induction e; introv; simpl in *; auto_star;
  try(rewrite in_union in hi; destruct hi as [hi1 | hi2]; [
   apply union_left; apply* IHe1|
   apply union_right; apply* IHe2]).
  rewrite in_empty in hi; inversion hi.
Qed.

Lemma notin_uv : forall G x, x # G -> x # (ACtxUV G).
Proof.
  introv notin.
  induction G using env_ind.
  rewrite empty_def. simpl. rewrite <- empty_def. auto.
  induction v; rewrite <- cons_to_push; simpl; auto.
Qed.


Lemma notin_solved_evar:  forall G x t,
    AWf (G & x ~ AC_Solved_EVar t) ->
    x \notin AFv t.
Proof.
  introv wf.
  apply notin_awterm with (G:=G).
  apply* awterm_solved_evar.
  apply* AWf_push_inv.
Qed.

Lemma notin_subst: forall x t e,
  x \notin AFv t ->
  x \notin AFv (ASubst x t e).
Proof.
  introv notin.
  induction e; simpl; auto.
  case_if * . simpl. apply* notin_singleton.
  case_if * . simpl. apply* notin_singleton.
Qed.

Lemma notin_another_subst: forall x y t e,
  x \notin AFv e ->
  x \notin AFv t ->
  x \notin AFv (ASubst y t e).
Proof.
  introv notine notint.
  destruct (eq_var_dec x y); subst. apply* notin_subst.
  induction e; simpls; auto.
  case_if * .
  case_if * .
Qed.

Lemma notin_ctxsubst: forall x H e,
  x \notin AFv e ->
  x # H ->
  AWf H ->
  x \notin AFv (ACtxSubst H e).
Proof.
  introv notine notinh wf. gen e.
  induction H using env_ind; introv notine.
  rewrite* subst_empty_env.
  assert (wf2:=wf). apply AWf_left in wf2.
  induction v.
  rewrite subst_add_var. apply* IHenv.
  rewrite subst_add_typvar. apply* IHenv.
  assert (x <> x0). simpl_dom. auto_star.

  rewrite subst_add_bndvar.
  apply* IHenv. apply* notin_another_subst.
  apply notin_awterm with (G:=H); auto.
  apply* awterm_bnd.

  rewrite subst_add_evar. apply* IHenv.

  rewrite subst_add_solved_evar.
  apply* IHenv. apply* notin_another_subst.
  apply notin_awterm with (G:=H); auto.
  apply* awterm_solved_evar.
Qed.

Lemma notin_bnd: forall G x s t,
    AWf (G & x ~ AC_Bnd s t) ->
    x \notin AFv t.
Proof.
  introv wf.
  apply notin_awterm with (G:=G).
  apply* awterm_bnd.
  apply* AWf_push_inv.
Qed.

(* uv *)

Lemma empty_uv : ACtxUV empty = empty.
Proof.
  rewrite empty_def. simpl. rewrite <- empty_def. auto.
Qed.

Lemma concat_uv: forall G H,
    ACtxUV (G & H) = (ACtxUV G) & (ACtxUV H).
Proof.
  introv. gen G. induction H using env_ind; introv.
  rewrite empty_uv. rewrite concat_empty_r.  rewrite concat_empty_r. auto.
  rewrite concat_assoc.
  induction v; repeat(rewrite <- cons_to_push);  simpl; auto.
  rewrite IHenv. rewrite concat_assoc. auto.
Qed.

(* distributivity of context substitution *)

Lemma distributivity_ctxsubst_subst : forall H x s e,
    AWf H ->
    x # H ->
    ACtxSubst H (ASubst x s e) =
    ASubst x (ACtxSubst H s) (ACtxSubst H e).
Proof.
  introv. gen s e x.
  induction H using env_ind; introv wf notin.
  repeat(rewrite* subst_empty_env).

  induction v.

  repeat(rewrite subst_add_var).
  apply AWf_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_typvar).
  apply AWf_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_bndvar).
  rewrite subst_subst_distr.
  apply AWf_left in wf.
  apply* IHenv.
  simpl_dom. auto.
  simpl_dom.
  assert (x # H). apply* AWf_push_inv.
  apply awterm_bnd in wf. apply* notin_awterm.
  apply awterm_bnd in wf. apply* notin_awterm.

  repeat(rewrite subst_add_evar).
  apply AWf_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_solved_evar).
  rewrite subst_subst_distr.
  apply AWf_left in wf.
  apply* IHenv.
  simpl_dom. auto.
  assert (x # H). apply* AWf_push_inv.
  apply awterm_solved_evar in wf. apply* notin_awterm.
  apply awterm_solved_evar in wf. apply* notin_awterm.
Qed.

Lemma distributivity_ctxtsubst_tsubst : forall H x s e,
    AWf H ->
    x # H ->
    ACtxTSubst H (ATSubst x s e) =
    ATSubst x (ACtxSubst H s) (ACtxTSubst H e).
Proof.
  introv. gen s e x.
  induction H using env_ind; introv wf notin.
  rewrite* subst_empty_env.
  rewrite* tsubst_empty_env.
  rewrite* tsubst_empty_env.

  induction v.

  rewrite subst_add_var.
  rewrite tsubst_add_var.
  rewrite tsubst_add_var.
  apply AWf_left in wf.
  apply* IHenv.

  rewrite subst_add_typvar.
  rewrite tsubst_add_typvar.
  rewrite tsubst_add_typvar.
  apply AWf_left in wf.
  apply* IHenv.

  rewrite subst_add_bndvar.
  rewrite tsubst_add_bndvar.
  rewrite tsubst_add_bndvar.
  rewrite tsubst_tsubst_distr.
  apply AWf_left in wf.
  apply* IHenv.
  simpl_dom. auto.
  simpl_dom.
  assert (x # H). apply* AWf_push_inv.
  apply awterm_bnd in wf. apply* notin_awterm.
  apply awterm_bnd in wf. apply* notin_awterm.

  rewrite subst_add_evar.
  rewrite tsubst_add_evar.
  rewrite tsubst_add_evar.
  apply AWf_left in wf.
  apply* IHenv.

  rewrite subst_add_solved_evar.
  rewrite tsubst_add_solved_evar.
  rewrite tsubst_add_solved_evar.
  rewrite tsubst_tsubst_distr.
  apply AWf_left in wf.
  apply* IHenv.
  simpl_dom. auto.
  assert (x # H). apply* AWf_push_inv.
  apply awterm_solved_evar in wf. apply* notin_awterm.
  apply awterm_solved_evar in wf. apply* notin_awterm.
Qed.
