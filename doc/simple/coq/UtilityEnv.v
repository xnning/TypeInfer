Require Import DeclDef.
Require Import AlgoDef.
Require Import LibLN.
Require Import AlgoInfra.

Set Implicit Arguments.

Inductive Softness : ACtx -> Prop :=
  | Softness_Empty: Softness empty
  | Softness_Unsolved: forall G a, Softness G -> a # G -> Softness (G & a ~ AC_Unsolved_EVar)
  | Softness_Solved: forall G a t, Softness G -> a # G -> Softness (G & a ~ AC_Solved_EVar t).

Lemma soft_append: forall G H,
    Softness G -> Softness H ->
    ok (G & H) ->
    Softness (G & H).
Proof.
  introv sg sh okg. induction H using env_ind.
  rewrite~ concat_empty_r.
  inversion sh.
  rewrite~ concat_empty_r.

  apply eq_push_inv in H0; destruct H0 as [eqx [eqv eqg2]]. subst.
  rewrite concat_assoc. apply~ Softness_Unsolved.
  apply~ IHenv. rewrite concat_assoc in okg. apply* ok_concat_inv_l.
  rewrite concat_assoc in okg. apply ok_push_inv in okg. destruct okg as [_ okg]. assumption.

  apply eq_push_inv in H0; destruct H0 as [eqx [eqv eqg2]]. subst.
  rewrite concat_assoc. apply~ Softness_Solved.
  apply~ IHenv. rewrite concat_assoc in okg. apply* ok_concat_inv_l.
  rewrite concat_assoc in okg. apply ok_push_inv in okg. destruct okg as [_ okg]. assumption.
Qed.

Lemma soft_single_unsolved: forall a,
    Softness (a ~ AC_Unsolved_EVar).
Proof.
  introv.
  rewrite <- concat_empty_l.
  apply~ Softness_Unsolved.
  apply~ Softness_Empty.
Qed.

Lemma soft_single_solved: forall a t,
    Softness (a ~ AC_Solved_EVar t).
Proof.
  introv.
  rewrite <- concat_empty_l.
  apply~ Softness_Solved.
  apply~ Softness_Empty.
Qed.

Lemma soft_left: forall G H,
    Softness (G & H) ->
    Softness G.
Proof.
  introv sf. induction H using env_ind.
  rewrite concat_empty_r in sf. auto.
  rewrite concat_assoc in sf.
  inversion sf.
  false empty_push_inv H1.
  apply eq_push_inv in H0. destruct H0 as [eqx [eqv eqg]]. subst. apply~ IHenv.
  apply eq_push_inv in H0. destruct H0 as [eqx [eqv eqg]]. subst. apply~ IHenv.
Qed.

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

Lemma ok_insert: forall {A} (G H: env A) a v,
    ok (G & H) ->
    a # (G & H) ->
    ok (G & a ~ v & H).
Proof.
  introv okg notin.
  induction H using env_ind.
  rewrite~ concat_empty_r.
  rewrite concat_assoc. apply ok_push.
  apply~ IHenv. rewrite concat_assoc in okg. apply ok_concat_inv_l in okg. auto.
  assert (x # (G & H)). rewrite concat_assoc in okg. apply ok_push_inv in okg. destruct okg as [_ okg]. auto.
  auto_star.
Qed.

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

Lemma tail_empty_eq2: forall {A} (I1 I2 G1: env A) x vx vy,
    ok (I1 & x ~ vy & I2) ->
    ok (G1 & x ~ vx) ->
    (I1 & x ~ vy & I2) = (G1 & x ~ vx) ->
    G1 = I1 /\ vx = vy /\ I2 = empty.
Proof.
  introv oki okg eq.
  apply tail_empty_eq with (x0:=x) (G:=(G1 & x ~ vx)) (I:=(I1 & x ~ vy & I2)); auto.
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
Qed.

Lemma AWf_push_inv : forall G x v,
    AWf (G & x ~ v) -> x # G.
Proof.
  introv WF. inversion WF;
  try(apply empty_push_inv in H0; inversion H0);
  try(apply eq_push_inv in H; destruct H as [eqg [eqx eqv]]; subst; simpl_dom; auto).
Qed.

(* atyping *)

Lemma atyping_awterm : forall G m e t H,
  ATyping m G e t H ->
  AWTermT G e.
Proof.
  introv ty.
  induction ty; simpl; auto.
  apply* AWTermT_TypVar.
  apply* AWTermT_Solved_EVar.
Qed.

Lemma notin_open_fev : forall x y e n,
    x \notin (AFev (AOpenRec n y e)) ->
    x \notin (AFev e)
with
notin_opent_fev : forall x y e n,
    x \notin (ATFev (AOpenTypRec n y e)) ->
    x \notin (ATFev e).
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
  apply* notin_opent_fev.
Proof.
  introv notin. gen n.
  induction e; introv notin.
    simpl in *; auto_star.
    simpl in *. auto.
    simpl in *. auto.
    simpl in *. apply*  notin_open_fev.
Qed.

Lemma notin_open_ftv : forall x y e n,
    x \notin (AFtv (AOpenRec n y e)) ->
    x \notin (AFtv e)
with
notin_opent_ftv : forall x y e n,
    x \notin (ATFtv (AOpenTypRec n y e)) ->
    x \notin (ATFtv e).
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
  apply* notin_opent_ftv.
Proof.
  introv notin. gen n.
  induction e; introv notin.
    simpl in *; auto_star.
    simpl in *. auto.
    simpl in *. auto.
    simpl in *. apply*  notin_open_ftv.
Qed.

Lemma notin_topen_ftv : forall x y e n,
    x \notin (AFtv (ATOpenRec n y e)) ->
    x \notin (AFtv e)
with
notin_topent_ftv : forall x y e n,
    x \notin (ATFtv (ATOpenTypRec n y e)) ->
    x \notin (ATFtv e).
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
  apply* notin_topent_ftv.

  introv notin. gen n.
  induction e; introv notin.
    simpl in *; auto_star.
    simpl in *. auto.
    simpl in *. auto.
    simpl in *. apply*  notin_topen_ftv.
Qed.

Lemma notin_topen_fev : forall x y e n,
    x \notin (AFev (ATOpenRec n y e)) ->
    x \notin (AFev e)
with
notin_topent_fev : forall x y e n,
    x \notin (ATFev (ATOpenTypRec n y e)) ->
    x \notin (ATFev e).
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
  apply* notin_topent_fev.

  introv notin. gen n.
  induction e; introv notin.
    simpl in *; auto_star.
    simpl in *. auto.
    simpl in *. auto.
    simpl in *. apply*  notin_topen_fev.
Qed.

Lemma notin_open_fv : forall x y e n,
    x \notin (AFv (AOpenRec n y e)) ->
    x \notin (AFv e)
with
notin_opent_fv : forall x y e n,
    x \notin (ATFv (AOpenTypRec n y e)) ->
    x \notin (ATFv e).
Proof.
  intros. apply notin_fv_inv.
  apply notin_fv_fev in H. apply* notin_open_fev.
  apply notin_fv_ftv in H. apply* notin_open_ftv.
Proof.
  intros. apply notin_tfv_inv.
  apply notin_tfv_tfev in H. apply* notin_opent_fev.
  apply notin_tfv_tftv in H. apply* notin_opent_ftv.
Qed.

Lemma notin_topen_fv : forall x y e n,
    x \notin (AFv (ATOpenRec n y e)) ->
    x \notin (AFv e)
with
notin_topent_fv : forall x y e n,
    x \notin (ATFv (ATOpenTypRec n y e)) ->
    x \notin (ATFv e).
Proof.
  intros. apply notin_fv_inv.
  apply notin_fv_fev in H. apply* notin_topen_fev.
  apply notin_fv_ftv in H. apply* notin_topen_ftv.
Proof.
  intros. apply notin_tfv_inv.
  apply notin_tfv_tfev in H. apply* notin_topent_fev.
  apply notin_tfv_tftv in H. apply* notin_topent_ftv.
Qed.

Lemma notin_awtermt : forall G t x,
  AWTermT G t ->
  x # G ->
  x \notin ATFv t.
Proof.
Admitted.

Lemma notin_awterm : forall G t x,
  AWTerm G t ->
  x # G ->
  x \notin AFv t.
Proof.
  intros. unfold AWTerm in H.
  simpls.
  apply notin_awtermt with (x:=x) in H; auto.
Qed.

Lemma notin_typing: forall G m e t H x,
  ATyping m G e t H ->
  x # G ->
  x \notin ATFv e.
Proof.
  introv ty notin. apply atyping_awterm in ty.
  apply* notin_awtermt.
Qed.

Lemma awtermt_remove: forall G H x v t,
    AWTermT (G & x ~ v & H) t ->
    x \notin ATFv t ->
    AWTermT (G & H) t.
Proof.
  introv wt notin. gen_eq I: (G & x ~ v & H).
  gen H. induction wt; introv hh.
  simpl in notin. rewrite hh in H. apply AWTermT_Var. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTermT_TypVar. apply* binds_subst.
  constructor*.

  simpl in notin. apply AWTermT_App. apply* IHwt1. simpls~. apply* IHwt2. simpls~.
  apply AWTermT_Lam with (L \u \{x}). intros y notin_y.
  apply notin_union in notin_y. destruct notin_y as [notin_y notin_x]. apply H0 with (H:=H1 & y ~ AC_Var) in notin_y.  rewrite concat_assoc in notin_y. auto.
  simpl in notin. apply* notin_open_inv. simpl. apply* notin_singleton.
  rewrite hh. rewrite* concat_assoc.

  simpl in notin. apply AWTermT_Pi with (L \u \{x}). subst. apply* IHwt.
  intros y notin_y.
  apply notin_union in notin_y. destruct notin_y as [notin_y notin_x]. subst.
  lets: H0 notin_y. rewrite <- concat_assoc in H2. rewrite <- concat_assoc. apply* H2.
  apply* notin_opent_inv. simpl. apply* notin_singleton.

  apply* AWTermT_CastUp.
  apply* AWTermT_CastDn.

  simpl in notin. apply* AWTermT_Ann.
  subst. apply* IHwt1. simpls~.

  simpl in notin. apply AWTermT_Forall with (L \u \{x}). subst. intros y notin_y.
  apply notin_union in notin_y. destruct notin_y as [notin_y notin_x].
  lets: H notin_y. rewrite <- concat_assoc in H2. rewrite <- concat_assoc. apply* H0.
  apply* notin_topent_inv. simpl. apply* notin_singleton.
  rewrite~ concat_assoc.
  simpl in notin. rewrite hh in H. apply AWTermT_TFVar. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTermT_Unsolved_EVar. apply* binds_subst.
  simpl in notin. rewrite hh in H. apply* AWTermT_Solved_EVar. apply* binds_subst.
Qed.

Lemma awterm_remove: forall G H x v t,
    AWTerm (G & x ~ v & H) t ->
    x \notin AFv t ->
    AWTerm (G & H) t.
Proof.
  intros. unfold AWTerm in H0.
  apply awtermt_remove in H0; auto.
Qed.

Lemma awtermt_replace: forall G H x t e,
    AWTermT (G & x ~ AC_Typ t & H) e ->
    AWTermT (G & x ~ AC_Var & H) e.
Proof.
  introv wt. gen_eq I: (G & x ~ AC_Typ t & H).
  gen H. induction wt; introv hg; subst.

  destruct (eq_var_dec x x0). subst.
  apply binds_middle_inv in H. destruct H as [h1 | [h2 | h3]]. apply AWTermT_Var. apply binds_concat_right. auto.
  apply AWTermT_Var. apply* binds_middle_eq.
  destruct h3 as [_ [inv _]]. false inv. reflexivity.
  apply binds_subst in H; auto.
  apply AWTermT_Var. apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.

  destruct (eq_var_dec x x0). subst.
  apply binds_middle_inv in H. destruct H as [h1 | [h2 | h3]]. apply AWTermT_TypVar with t0. apply binds_concat_right. auto.
  apply AWTermT_Var. apply* binds_middle_eq.
  destruct h3 as [_ [inv _]]. false inv. reflexivity.
  apply binds_subst in H; auto.
  apply* AWTermT_TypVar. apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.

  constructor.
  apply AWTermT_App. apply* IHwt1. apply* IHwt2.
  apply AWTermT_Lam with L. intros y notin_y. rewrite <- concat_assoc. apply* H0. rewrite* concat_assoc.
  apply AWTermT_Pi with L. apply* IHwt. intros y notin_y. rewrite <- concat_assoc. apply* H0. lets: H0 notin_y. rewrite* concat_assoc.
  apply* AWTermT_CastUp.
  apply* AWTermT_CastDn.
  apply AWTermT_Ann. apply* IHwt1. apply* IHwt2.
  apply AWTermT_Forall with L. intros y notin_y. rewrite <- concat_assoc. apply* H0. lets: H notin_y. rewrite* concat_assoc.
  destruct (eq_var_dec x i). subst.
  apply binds_concat_inv in H.
  destruct H as [H1 | [notin H2]].
  apply AWTermT_TFVar. apply* binds_concat_right.
  apply binds_push_eq_inv in H2. inversion H2.
  apply AWTermT_TFVar.
  apply binds_subst in H; auto.
  apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.

  destruct (eq_var_dec x i). subst.
  apply binds_concat_inv in H.
  destruct H as [H1 | [notin H2]].
  apply AWTermT_Unsolved_EVar. apply* binds_concat_right.
  apply binds_push_eq_inv in H2. inversion H2.
  apply AWTermT_Unsolved_EVar.
  apply binds_subst in H; auto.
  apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.

  destruct (eq_var_dec x i). subst.
  apply binds_concat_inv in H.
  destruct H as [H1 | [notin H2]].
  apply AWTermT_Solved_EVar with t0. apply* binds_concat_right.
  apply binds_push_eq_inv in H2. inversion H2.
  apply AWTermT_Solved_EVar with t0.
  apply binds_subst in H; auto.
  apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.
Qed.

Lemma awterm_replace: forall G H x t e,
    AWTerm (G & x ~ AC_Typ t & H) e ->
    AWTerm (G & x ~ AC_Var & H) e.
Proof.
  unfold AWTerm. intros.
  apply awtermt_replace in H0; auto.
Qed.

Lemma awtermt_replace2: forall G H x t e,
    AWTermT (G & x ~ AC_Var & H) e ->
    AWTermT (G & x ~ AC_Typ t & H) e.
Proof.
  introv wt. gen_eq I: (G & x ~ AC_Var & H).
  gen H. induction wt; introv hg; subst.

  destruct (eq_var_dec x x0). subst.
  apply binds_middle_inv in H. destruct H as [h1 | [h2 | h3]]. apply AWTermT_Var. apply binds_concat_right. auto.
  apply AWTermT_TypVar with t. apply* binds_middle_eq.
  destruct h3 as [_ [inv _]]. false inv. reflexivity.
  apply binds_subst in H; auto.
  apply AWTermT_Var. apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.

  destruct (eq_var_dec x x0). subst.
  apply binds_middle_inv in H. destruct H as [h1 | [h2 | h3]]. apply AWTermT_TypVar with t0. apply binds_concat_right. auto.
  apply AWTermT_TypVar with t. apply* binds_middle_eq.
  destruct h3 as [_ [inv _]]. false inv. reflexivity.
  apply binds_subst in H; auto.
  apply* AWTermT_TypVar. apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.

  constructor.
  apply AWTermT_App. apply* IHwt1. apply* IHwt2.
  apply AWTermT_Lam with L. intros y notin_y. rewrite <- concat_assoc. apply* H0. rewrite* concat_assoc.
  apply AWTermT_Pi with L. apply* IHwt. intros y notin_y. rewrite <- concat_assoc. apply* H0. lets: H0 notin_y. rewrite* concat_assoc.
  apply* AWTermT_CastUp.
  apply* AWTermT_CastDn.
  apply AWTermT_Ann. apply* IHwt1. apply* IHwt2.
  apply AWTermT_Forall with L. intros y notin_y. rewrite <- concat_assoc. apply* H0. lets: H notin_y. rewrite* concat_assoc.
  destruct (eq_var_dec x i). subst.
  apply binds_concat_inv in H.
  destruct H as [H1 | [notin H2]].
  apply AWTermT_TFVar. apply* binds_concat_right.
  apply binds_push_eq_inv in H2. inversion H2.
  apply AWTermT_TFVar.
  apply binds_subst in H; auto.
  apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.

  destruct (eq_var_dec x i). subst.
  apply binds_concat_inv in H.
  destruct H as [H1 | [notin H2]].
  apply AWTermT_Unsolved_EVar. apply* binds_concat_right.
  apply binds_push_eq_inv in H2. inversion H2.
  apply AWTermT_Unsolved_EVar.
  apply binds_subst in H; auto.
  apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.

  destruct (eq_var_dec x i). subst.
  apply binds_concat_inv in H.
  destruct H as [H1 | [notin H2]].
  apply AWTermT_Solved_EVar with t0. apply* binds_concat_right.
  apply binds_push_eq_inv in H2. inversion H2.
  apply AWTermT_Solved_EVar with t0.
  apply binds_subst in H; auto.
  apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.
Qed.

Lemma awtermt_middle_solve: forall G H x t e,
    AWTermT (G & x ~ AC_Unsolved_EVar & H) e ->
    AWTermT G t ->
    AWTermT (G & x ~ AC_Solved_EVar t & H) e.
Proof.
  introv wt wf. gen_eq I: (G & x ~ AC_Unsolved_EVar & H).
  gen H. induction wt; introv hg; subst.

  destruct (eq_var_dec x x0). subst.
  apply binds_middle_inv in H. destruct H as [h1 | [h2 | h3]]. apply AWTermT_Var. apply binds_concat_right. auto.
  destruct h2 as [_ [_ inv]]. false inv.
  apply AWTermT_Var.  apply* binds_concat_right.
  apply binds_subst in H; auto.
  apply AWTermT_Var. apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.

  destruct (eq_var_dec x x0). subst.
  apply binds_middle_inv in H. destruct H as [h1 | [h2 | h3]]. apply AWTermT_TypVar with t0. apply binds_concat_right. auto.
  destruct h2 as [_ [_ inv]]. false inv.
  apply AWTermT_Var.  apply* binds_concat_right.
  apply binds_subst in H; auto.
  apply AWTermT_TypVar with t0. apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.

  constructor.
  apply AWTermT_App. apply* IHwt1. apply* IHwt2.
  apply AWTermT_Lam with L. intros y notin_y. rewrite <- concat_assoc. apply* H0. rewrite* concat_assoc.
  apply AWTermT_Pi with L. apply* IHwt. intros y notin_y. rewrite <- concat_assoc. apply* H0. lets: H0 notin_y. rewrite* concat_assoc.
  apply* AWTermT_CastUp.
  apply* AWTermT_CastDn.
  apply AWTermT_Ann. apply* IHwt1. apply* IHwt2.
  apply AWTermT_Forall with L. intros y notin_y. rewrite <- concat_assoc. apply* H0. lets: H notin_y. rewrite* concat_assoc.

  destruct (eq_var_dec x i). subst.
  apply binds_concat_inv in H.
  destruct H as [H1 | [notin H2]].
  apply AWTermT_TFVar. apply* binds_concat_right.
  apply binds_push_eq_inv in H2. inversion H2.
  apply AWTermT_TFVar.
  apply binds_subst in H; auto.
  apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.

  destruct (eq_var_dec x i). subst.
  apply binds_concat_inv in H.
  destruct H as [H1 | [notin H2]].
  apply AWTermT_Unsolved_EVar. apply* binds_concat_right.
  apply AWTermT_Solved_EVar with t.
  apply* binds_concat_left.
  apply binds_subst in H; auto.
  apply AWTermT_Unsolved_EVar.
  apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.

  destruct (eq_var_dec x i). subst.
  apply binds_concat_inv in H.
  destruct H as [H1 | [notin H2]].
  apply AWTermT_Solved_EVar with t0. apply* binds_concat_right.
  apply binds_push_eq_inv in H2. inversion H2.
  apply AWTermT_Solved_EVar with t0.
  apply binds_subst in H; auto.
  apply binds_concat_inv in H. destruct H as [h1 | h2]. apply* binds_concat_right. apply* binds_concat_left.
Qed.


Lemma awtermt_awftyp: forall G t,
    AWfTyp G t ->
    AWTermT G t.
Proof.
  introv wt.
  induction wt.

  apply atyping_awterm in H0. auto.
Qed.

Lemma awtermt_is_atermty  : forall G e,
    AWTermT G e ->
    ATermTy e.
Proof.
  introv wt.
  induction wt; subst; auto; f_equal *; auto.
  apply ATermTy_Expr. apply ATerm_App. inversion IHwt1; subst. auto. inversion IHwt2; subst. auto.
  apply ATermTy_Expr. apply ATerm_Lam with L. intros y notin.
  lets: H0 notin. inversion H1; auto.
  apply ATermTy_Expr. apply ATerm_CastUp. inversion IHwt; auto.
  apply ATermTy_Expr. apply ATerm_CastDn. inversion IHwt; auto.
  apply ATermTy_Expr. apply ATerm_Ann. inversion IHwt1; subst. auto. inversion IHwt2; subst. auto.
  auto. auto. apply ATermTy_TFVar.
  apply ATermTy_EVar.
  apply ATermTy_EVar.
Qed.

Lemma awterm_awftyp: forall G t,
    AWfTyp G (AT_Expr t) ->
    AWTerm G t.
Proof.
  introv wt. unfold AWTerm.
  gen_eq s:(AT_Expr t).
  gen t. induction wt; introv hi.
  inversion hi; subst.

  apply atyping_awterm in H0. auto.
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

Lemma awtermt_reorder : forall G1 G2 x1 x2 v e,
    x1 <> x2 ->
    AWTermT (G1 & x2 ~ AC_Var & x1 ~ v & G2) e ->
    AWTermT (G1 & x1 ~ v & x2 ~ AC_Var & G2) e.
Proof.
  intros. inductions H0.
  apply* AWTermT_Var. apply* binds_swap.
  apply* AWTermT_TypVar. apply* binds_swap.
  apply* AWTermT_Star.
  apply* AWTermT_App.

  apply AWTermT_Lam with (L := L); intros.
  assert (JMeq.JMeq (G1 & x2 ~ AC_Var & x1 ~ v & G2 & x ~ AC_Var)
                    (G1 & x2 ~ AC_Var & x1 ~ v & (G2 & x ~ AC_Var))).
  rewrite -> concat_assoc. auto.
  pose (Re := H0 x H2 v x2 x1 H (G2 & x ~ AC_Var) G1 H3).
  rewrite -> concat_assoc in Re.
  auto.

  apply AWTermT_Pi with (L := L). auto. intros.
  lets: H2 H3.
  rewrite <- concat_assoc in H4.
  rewrite <- concat_assoc.
  apply* H1. rewrite* concat_assoc.

  apply* AWTermT_CastUp.
  apply* AWTermT_CastDn.
  apply* AWTermT_Ann.

  apply AWTermT_Forall with (L := L). intros.
  lets: H1 H2.
  rewrite <- concat_assoc in H3.
  rewrite <- concat_assoc.
  apply* H0. rewrite~ concat_assoc.
  apply* AWTermT_TFVar. apply* binds_swap.
  apply* AWTermT_Unsolved_EVar. apply* binds_swap.
  apply* AWTermT_Solved_EVar. apply* binds_swap.
Qed.

Lemma awterm_reorder : forall G1 G2 x1 x2 v e,
    x1 <> x2 ->
    AWTerm (G1 & x2 ~ AC_Var & x1 ~ v & G2) e ->
    AWTerm (G1 & x1 ~ v & x2 ~ AC_Var & G2) e.
Proof.
  unfold AWTerm. intros.
  apply* awtermt_reorder.
Qed.

Lemma awtermt_reorder_tvar : forall G1 G2 x1 x2 v e,
    x1 <> x2 ->
    AWTermT (G1 & x2 ~ AC_TVar & x1 ~ v & G2) e ->
    AWTermT (G1 & x1 ~ v & x2 ~ AC_TVar & G2) e.
Proof.
  intros. inductions H0.
  apply* AWTermT_Var. apply* binds_swap.
  apply* AWTermT_TypVar. apply* binds_swap.
  apply* AWTermT_Star.
  apply* AWTermT_App.

  apply AWTermT_Lam with (L := L); intros.
  assert (JMeq.JMeq (G1 & x2 ~ AC_TVar & x1 ~ v & G2 & x ~ AC_Var)
                    (G1 & x2 ~ AC_TVar & x1 ~ v & (G2 & x ~ AC_Var))).
  rewrite -> concat_assoc. auto.
  pose (Re := H0 x H2 v x2 x1 H (G2 & x ~ AC_Var) G1 H3).
  rewrite -> concat_assoc in Re.
  auto.

  apply AWTermT_Pi with (L := L). auto. intros.
  lets: H2 H3.
  rewrite <- concat_assoc in H4.
  rewrite <- concat_assoc.
  apply* H1. rewrite~ concat_assoc.

  apply* AWTermT_CastUp.
  apply* AWTermT_CastDn.
  apply* AWTermT_Ann.

  apply AWTermT_Forall with (L := L). intros.
  lets: H1 H2.
  rewrite <- concat_assoc in H3.
  rewrite <- concat_assoc.
  apply* H0. rewrite ~ concat_assoc.
  apply* AWTermT_TFVar. apply* binds_swap.
  apply* AWTermT_Unsolved_EVar. apply* binds_swap.
  apply* AWTermT_Solved_EVar. apply* binds_swap.
Qed.

Lemma awterm_reorder_tvar : forall G1 G2 x1 x2 v e,
    x1 <> x2 ->
    AWTerm (G1 & x2 ~ AC_TVar & x1 ~ v & G2) e ->
    AWTerm (G1 & x1 ~ v & x2 ~ AC_TVar & G2) e.
Proof.
  unfold AWTerm. intros. apply* awtermt_reorder_tvar.
Qed.

Lemma awtermt_reorder_typvar : forall G1 G2 x1 x2 v e t,
    x1 <> x2 ->
    AWTermT (G1 & x2 ~ AC_Typ t & x1 ~ v & G2) e ->
    AWTermT (G1 & x1 ~ v & x2 ~ AC_Typ t & G2) e.
Proof.
  intros. inductions H0.
  apply* AWTermT_Var. apply* binds_swap.
  apply* AWTermT_TypVar. apply* binds_swap.
  apply* AWTermT_Star.
  apply* AWTermT_App.

  apply AWTermT_Lam with (L := L); intros.
  assert (JMeq.JMeq (G1 & x2 ~ AC_Typ t & x1 ~ v & G2 & x ~ AC_Var)
                    (G1 & x2 ~ AC_Typ t & x1 ~ v & (G2 & x ~ AC_Var))).
  rewrite -> concat_assoc. auto.
  pose (Re := H0 x H2 t v x2 x1 H (G2 & x ~ AC_Var) G1 H3).
  rewrite -> concat_assoc in Re.
  auto.

  apply AWTermT_Pi with (L := L). auto. intros.
  lets: H2 H3.
  rewrite <- concat_assoc in H4.
  rewrite <- concat_assoc.
  apply* H1. rewrite* concat_assoc.

  apply* AWTermT_CastUp.
  apply* AWTermT_CastDn.
  apply* AWTermT_Ann.

  apply AWTermT_Forall with (L := L). intros.
  lets: H1 H2.
  rewrite <- concat_assoc in H3.
  rewrite <- concat_assoc.
  apply* H0. rewrite~ concat_assoc.
  apply* AWTermT_TFVar. apply* binds_swap.
  apply* AWTermT_Unsolved_EVar. apply* binds_swap.
  apply* AWTermT_Solved_EVar. apply* binds_swap.
Qed.

Lemma awterm_reorder_typvar : forall G1 G2 x1 x2 v e t,
    x1 <> x2 ->
    AWTerm (G1 & x2 ~ AC_Typ t & x1 ~ v & G2) e ->
    AWTerm (G1 & x1 ~ v & x2 ~ AC_Typ t & G2) e.
Proof.
  unfold AWTerm. intros.
  apply* awtermt_reorder_typvar.
Qed.

Lemma awtermt_reorder_simp : forall G1 x1 x2 v e,
    x1 <> x2 ->
    AWTermT (G1 & x2 ~ AC_Var & x1 ~ v) e ->
    AWTermT (G1 & x1 ~ v & x2 ~ AC_Var) e.
Proof.
  intros.
  assert (G1 & x2 ~ AC_Var & x1 ~ v = G1 & x2 ~ AC_Var & x1 ~ v & empty).
  rewrite* concat_empty_r.
  assert (G1 & x1 ~ v & x2 ~ AC_Var = G1 & x1 ~ v & x2 ~ AC_Var & empty).
  rewrite* concat_empty_r.
  rewrite H1 in H0.
  rewrite H2.
  apply* awtermt_reorder.
Qed.

Lemma awterm_reorder_simp : forall G1 x1 x2 v e,
    x1 <> x2 ->
    AWTerm (G1 & x2 ~ AC_Var & x1 ~ v) e ->
    AWTerm (G1 & x1 ~ v & x2 ~ AC_Var) e.
Proof.
  unfold AWTerm; intros. apply* awtermt_reorder_simp.
Qed.

Lemma awtermt_reorder_tvar_simp : forall G1 x1 x2 v e,
    x1 <> x2 ->
    AWTermT (G1 & x2 ~ AC_TVar & x1 ~ v) e ->
    AWTermT (G1 & x1 ~ v & x2 ~ AC_TVar) e.
Proof.
  intros.
  assert (G1 & x2 ~ AC_TVar & x1 ~ v = G1 & x2 ~ AC_TVar & x1 ~ v & empty).
  rewrite* concat_empty_r.
  assert (G1 & x1 ~ v & x2 ~ AC_TVar = G1 & x1 ~ v & x2 ~ AC_TVar & empty).
  rewrite* concat_empty_r.
  rewrite H1 in H0.
  rewrite H2.
  apply* awtermt_reorder_tvar.
Qed.

Lemma awterm_reorder_tvar_simp : forall G1 x1 x2 v e,
    x1 <> x2 ->
    AWTerm (G1 & x2 ~ AC_TVar & x1 ~ v) e ->
    AWTerm (G1 & x1 ~ v & x2 ~ AC_TVar) e.
Proof.
  unfold AWTerm. intros. apply* awtermt_reorder_tvar_simp.
Qed.

Lemma awtermt_reorder_typvar_simp : forall G1 x1 x2 v e t,
    x1 <> x2 ->
    AWTermT (G1 & x2 ~ AC_Typ t & x1 ~ v) e ->
    AWTermT (G1 & x1 ~ v & x2 ~ AC_Typ t) e.
Proof.
  intros.
  assert (G1 & x2 ~ AC_Typ t & x1 ~ v = G1 & x2 ~ AC_Typ t & x1 ~ v & empty).
  rewrite* concat_empty_r.
  assert (G1 & x1 ~ v & x2 ~ AC_Typ t = G1 & x1 ~ v & x2 ~ AC_Typ t & empty).
  rewrite* concat_empty_r.
  rewrite H1 in H0.
  rewrite H2.
  apply* awtermt_reorder_typvar.
Qed.

Lemma awterm_reorder_typvar_simp : forall G1 x1 x2 v e t,
    x1 <> x2 ->
    AWTerm (G1 & x2 ~ AC_Typ t & x1 ~ v) e ->
    AWTerm (G1 & x1 ~ v & x2 ~ AC_Typ t) e.
Proof.
  unfold AWTerm; intros. apply* awtermt_reorder_typvar_simp.
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

Lemma awtermt_weaken : forall G x v e,
    AWTermT G e ->
    x # G ->
    AWTermT (G & x ~ v) e.
Proof.
  intros. inductions H.
  apply* AWTermT_Var. apply* binds_push_fresh.
  apply* AWTermT_TypVar. apply* binds_push_fresh.
  apply* AWTermT_Star.
  apply* AWTermT_App.
  apply AWTermT_Lam with (L := L \u \{x}); intros. apply* awtermt_reorder_simp.
  apply AWTermT_Pi with (L := L \u \{x}); intros. apply* IHAWTermT. apply* awtermt_reorder_simp.
  apply* AWTermT_CastUp.
  apply* AWTermT_CastDn.
  apply* AWTermT_Ann.
  apply AWTermT_Forall with (L := L \u \{x}); intros. apply* awtermt_reorder_tvar_simp.
  apply* AWTermT_TFVar. apply* binds_push_fresh.
  apply* AWTermT_Unsolved_EVar. apply* binds_push_fresh.
  apply* AWTermT_Solved_EVar. apply* binds_push_fresh.
Qed.

Lemma awterm_weaken : forall G x v e,
    AWTerm G e ->
    x # G ->
    AWTerm (G & x ~ v) e.
Proof.
  unfold AWTerm. intros. apply* awtermt_weaken.
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

Lemma awtermt_weaken_ctx: forall G H e,
    ok (G & H) ->
    AWTermT G e ->
    AWTermT (G & H) e.
Proof.
  introv. induction H using env_ind; introv okg wf.
  rewrite* concat_empty_r.
  assert (AWTermT (G & H) e). apply* IHenv. rewrite concat_assoc in okg. apply* ok_push_inv_ok.
  rewrite concat_assoc. apply* awtermt_weaken.
  rewrite concat_assoc in okg. apply* ok_push_inv.
Qed.

Lemma awtermt_weaken_middle : forall G x v e H,
    AWTermT (G & H) e ->
    x # (G & H) ->
    ok (G & x ~ v & H) ->
    AWTermT (G & x ~ v & H) e.
Proof.
  intros. gen_eq S :(G & H). gen H. inductions H0; introv okg sinfo; subst.
  apply* AWTermT_Var. apply* binds_weaken.
  apply* AWTermT_TypVar.  apply* binds_weaken.
  apply* AWTermT_Star.
  apply* AWTermT_App.
  apply AWTermT_Lam with (L := L \u \{x} \u dom G \u dom H2); intros.
  assert (x0 \notin L) by auto.
  forwards * : H0 H4 (H2 & x0 ~ AC_Var).
  rewrite concat_assoc. apply~ ok_push.
  rewrite~ concat_assoc.
  repeat rewrite~ concat_assoc in H5.
  apply AWTermT_Pi with (L := L \u \{x} \u dom G \u dom H3); intros. apply* IHAWTermT.
  assert (x0 \notin L) by auto.
  forwards * : H1 H5 (H3 & x0 ~ AC_Var).
  rewrite concat_assoc. apply~ ok_push.
  rewrite~ concat_assoc.
  repeat rewrite~ concat_assoc in H6.
  apply* AWTermT_CastUp.
  apply* AWTermT_CastDn.
  apply* AWTermT_Ann.
  apply AWTermT_Forall with (L := L \u \{x} \u dom G \u dom H2); intros.
  assert (x0 \notin L) by auto.
  forwards * : H0 H4 (H2 & x0 ~ AC_TVar).
  rewrite concat_assoc. apply~ ok_push.
  rewrite~ concat_assoc.
  repeat rewrite~ concat_assoc in H5.
  apply* AWTermT_TFVar. apply* binds_weaken.
  apply* AWTermT_Unsolved_EVar.  apply* binds_weaken.
  apply* AWTermT_Solved_EVar.  apply* binds_weaken.
Qed.

Lemma awtermt_weaken_context_middle : forall G e H I,
    AWTermT (G & H) e ->
    ok (G & I & H) ->
    AWTermT (G & I & H) e.
Proof.
  intros. gen_eq S : (G & H). gen H.
  induction H0; introv okg sinfo; subst; auto.

  apply* AWTermT_Var. apply* binds_weaken.
  apply* AWTermT_TypVar.  apply* binds_weaken.
  apply AWTermT_Lam with (L := L \u  dom G \u dom H1 \u dom I); intros.
  assert (x \notin L) by auto.
  forwards * : H0 H3 (H1 & x ~ AC_Var).
  rewrite concat_assoc. apply~ ok_push.
  rewrite~ concat_assoc.
  repeat rewrite~ concat_assoc in H4.
  apply AWTermT_Pi with (L := L \u dom G \u dom H2 \u dom I); intros.
  forwards * : IHAWTermT.
  assert (x \notin L) by auto.
  forwards * : H1 H4 (H2 & x ~ AC_Var).
  rewrite concat_assoc. apply~ ok_push.
  rewrite~ concat_assoc.
  repeat rewrite~ concat_assoc in H5.
  apply AWTermT_Forall with (L := L \u dom G \u dom H1 \u dom I); intros.
  assert (x \notin L) by auto.
  forwards * : H0 H3 (H1 & x ~ AC_TVar).
  rewrite concat_assoc. apply~ ok_push.
  rewrite~ concat_assoc.
  repeat rewrite~ concat_assoc in H4.
  apply* AWTermT_TFVar. apply* binds_weaken.
  apply* AWTermT_Unsolved_EVar.  apply* binds_weaken.
  apply* AWTermT_Solved_EVar.  apply* binds_weaken.
Qed.


Lemma awterm_typ: forall G x a,
    AWf (G & x ~ AC_Typ a) ->
    AWTermT G a.
Proof.
  intros. inductions H.
  false. apply* empty_push_inv.
  destruct (eq_push_inv x) as [? [? ?]]. inversions H2.
  destruct (eq_push_inv x) as [? [? ?]]. inversions H2.
  destruct (eq_push_inv x) as [? [? ?]]. inversions H2.
  destruct (eq_push_inv x) as [? [? ?]]. inversions H3.
  destruct (eq_push_inv x) as [s1 [s2 s3]]. inversion s2. subst.
  apply* awtermt_awftyp.
  destruct (eq_push_inv x) as [? [? ?]]. inversions H2.
  destruct (eq_push_inv x) as [? [? ?]]. inversions H4.
Qed.

Lemma awftyp_typvar: forall G x t,
    AWf (G & x ~ AC_Typ t) ->
    AWfTyp G t.
Proof.
  introv wf. gen_eq H : (G & x ~ AC_Typ t).
  inversion wf; introv hinfo.
  false empty_push_inv hinfo.
  apply eq_push_inv in hinfo. destruct hinfo as [_ [inv _]]. false inv.
  apply eq_push_inv in hinfo. destruct hinfo as [_ [inv _]]. false inv.
  apply eq_push_inv in hinfo. destruct hinfo as [_ [inv _]]. false inv.
  apply eq_push_inv in hinfo. destruct hinfo as [? [? ?]]. inversion H5. subst. auto.
  apply eq_push_inv in hinfo. destruct hinfo as [_ [inv _]]. false inv.
  apply eq_push_inv in hinfo. destruct hinfo as [_ [inv _]]. false inv.
Qed.

Lemma awterm_solved_evar: forall G x t,
    AWf (G & x ~ AC_Solved_EVar t) ->
    AWTermT G t.
Proof.
  introv wf. gen_eq H : (G & x ~ AC_Solved_EVar t).
  induction wf; introv hi; try(
  apply eq_push_inv in hi; destruct hi as [eqx [eqv eqg]]; inversion eqv); subst; auto.
  apply empty_push_inv in hi. inversion hi.
  apply* awtermt_awftyp.
Qed.

Lemma awftyp_solved_evar: forall G x t,
    AWf (G & x ~ AC_Solved_EVar t) ->
    AWfTyp G t.
Proof.
  introv wf. gen_eq H : (G & x ~ AC_Solved_EVar t).
  inversion wf; introv hinfo.
  false empty_push_inv hinfo.
  apply eq_push_inv in hinfo. destruct hinfo as [_ [inv _]]. false inv.
  apply eq_push_inv in hinfo. destruct hinfo as [_ [inv _]]. false inv.
  apply eq_push_inv in hinfo. destruct hinfo as [_ [inv _]]. false inv.
  apply eq_push_inv in hinfo. destruct hinfo as [_ [inv _]]. false inv.
  apply eq_push_inv in hinfo. destruct hinfo as [_ [inv _]]. false inv.
  apply eq_push_inv in hinfo. destruct hinfo as [? [? ?]]. inversion H6. subst. auto.
Qed.

Lemma atmono_solved_evar: forall G x t,
    AWf (G & x ~ AC_Solved_EVar t) ->
    ATMono t.
Proof.
  introv wf. gen_eq H : (G & x ~ AC_Solved_EVar t).
  inversion wf; introv hinfo.
  false empty_push_inv hinfo.
  apply eq_push_inv in hinfo. destruct hinfo as [_ [inv _]]. false inv.
  apply eq_push_inv in hinfo. destruct hinfo as [_ [inv _]]. false inv.
  apply eq_push_inv in hinfo. destruct hinfo as [_ [inv _]]. false inv.
  apply eq_push_inv in hinfo. destruct hinfo as [_ [inv _]]. false inv.
  apply eq_push_inv in hinfo. destruct hinfo as [_ [inv _]]. false inv.
  apply eq_push_inv in hinfo. destruct hinfo as [? [? ?]]. inversion H6. subst. auto.
Qed.


Lemma awterm_evar_binds: forall G a t,
    AWf G ->
    binds a (AC_Solved_EVar t) G ->
    AWTermT G t.
Proof.
  introv wf bd. destruct (split_bind_context bd) as (G1 & G2 & HG).
  rewrite HG.
  assert (AWTermT G1 t). rewrite HG in wf. apply* awterm_solved_evar. apply* AWf_left.  auto.
  rewrite HG in wf.
  rewrite <- concat_assoc. apply* awtermt_weaken_ctx. apply* awf_is_ok.
  rewrite* concat_assoc.
Qed.

Lemma atyping_awf: forall G m e t H,
    ATyping m G e t H ->
    AWf G.
Proof.
  introv ty.
  induction ty; repeat apply AWf_left in IHty; auto.
Qed.

Lemma awftyp_awf: forall G e,
    AWfTyp G e ->
    AWf G.
Proof.
  introv wf. inversion wf; subst.
  lets: atyping_awf H0. auto.
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

Lemma tsubst_star : forall G,
    ACtxTSubst G (AT_Expr AE_Star) = AT_Expr AE_Star.
Proof.
  intro G.
  induction G.
  unfold ACtxSubst. auto.
  unfold ACtxSubst. destruct a. simpl.
  destruct a; auto.
Qed.

Lemma awftyp_star: forall G,
    AWf G ->
    AWfTyp G (AT_Expr AE_Star).
Proof.
  introv wf.
  apply AWf_Expr with G.
  apply~ ATC_Sub.
  rewrite tsubst_star.
  apply ASub_Unify.
  apply AUnify_Star.
  auto.
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

Lemma subst_add_tvar : forall G e x,
     ACtxSubst (G & x ~ AC_TVar) e = ACtxSubst G e.
Proof.
  introv. rewrite <- cons_to_push.
  unfold ACtxTSubst. simpl. auto.
Qed.

Lemma tsubst_add_tvar : forall G e x,
     ACtxTSubst (G & x ~ AC_TVar) e = ACtxTSubst G e.
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

Lemma subst_add_marker : forall G e x,
     ACtxSubst (G & x ~ AC_Marker) e = ACtxSubst G e.
Proof.
  introv. rewrite <- cons_to_push.
  unfold ACtxTSubst. simpl. auto.
Qed.

Lemma tsubst_add_marker : forall G e x,
     ACtxTSubst (G & x ~ AC_Marker) e = ACtxTSubst G e.
Proof.
  introv. rewrite <- cons_to_push.
  unfold ACtxTSubst. simpl. auto.
Qed.

Lemma tsubst_add_solved_evar: forall H x t e,
    ACtxTSubst (H & x ~ AC_Solved_EVar t) e = ACtxTSubst H (ATSubstT x t e).
Proof.
  introv. rewrite <- cons_to_push in *.
  unfold ACtxTSubst. simpl. auto.
Qed.

Lemma subst_add_solved_evar: forall H x t e,
    ACtxSubst (H & x ~ AC_Solved_EVar t) e = ACtxSubst H (ASubstT x t e).
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
  repeat(rewrite subst_add_tvar). auto.
  repeat(rewrite subst_add_evar). auto.
  repeat(rewrite subst_add_solved_evar). auto.
  repeat(rewrite subst_add_marker). auto.
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
  repeat(rewrite tsubst_add_tvar). auto.
  repeat(rewrite tsubst_add_evar). auto.
  repeat(rewrite tsubst_add_solved_evar). auto.
  repeat(rewrite subst_add_marker). auto.
  repeat(rewrite tsubst_add_marker). auto.
Qed.

Lemma actxtsubst_append: forall G H t,
    ok (G & H) ->
    AWTermT G t ->
    ACtxTSubst (G & H) t = ACtxTSubst G t.
Proof.
  introv okg wt.
  induction H using env_ind.
  rewrite~ concat_empty_r.
  rewrite concat_assoc.
  rewrite tsubst_add_ctx.

  assert (ACtxTSubst (x ~ v) t = t).
  rewrite single_def. unfold ACtxTSubst. rewrite LibList.fold_left_cons. rewrite LibList.fold_left_nil.
  destruct v; simpls; auto.
  apply atsubstt_fresh.
  apply notin_tfv_tftv.
  apply notin_awtermt with G; auto.
  rewrite concat_assoc in okg.
  destruct (ok_push_inv okg) as [_ okg2]. auto_star.
  rewrite H0. apply* IHenv.
  rewrite concat_assoc in okg.
  destruct (ok_push_inv okg) as [okg1 _]. auto_star.
Qed.

Lemma actxtsubst_expr: forall G e,
    ACtxTSubst G (AT_Expr e) = AT_Expr (ACtxSubst G e).
Proof.
  intros.
  gen e. induction G using env_ind; intros.
  rewrite tsubst_empty_env.
  rewrite~ subst_empty_env.
  induction v.
  rewrite~ subst_add_var.
  rewrite~ tsubst_add_var.
  rewrite~ subst_add_typvar.
  rewrite~ tsubst_add_typvar.
  rewrite~ subst_add_tvar.
  rewrite~ tsubst_add_tvar.
  rewrite~ subst_add_evar.
  rewrite~ tsubst_add_evar.
  rewrite~ subst_add_solved_evar.
  rewrite~ tsubst_add_solved_evar.
  apply* IHG.
  rewrite~ subst_add_marker.
  rewrite~ tsubst_add_marker.
Qed.

Lemma actxsubst_bvar: forall G e,
    ACtxSubst G (AE_BVar e) = AE_BVar e.
Proof.
  intros.
  induction G using env_ind.
  repeat(rewrite~ subst_empty_env).
  induction v.
  repeat(rewrite~ subst_add_var).
  repeat(rewrite~ subst_add_typvar).
  repeat(rewrite~ subst_add_tvar).
  repeat(rewrite~ subst_add_evar).
  repeat(rewrite~ subst_add_solved_evar).
  repeat rewrite~ subst_add_marker.
Qed.

Lemma actxtsubst_tbvar: forall G e,
    ACtxTSubst G (AT_TBVar e) = AT_TBVar e.
Proof.
  intros.
  induction G using env_ind.
  repeat(rewrite~ tsubst_empty_env).
  induction v.
  repeat(rewrite~ tsubst_add_var).
  repeat(rewrite~ tsubst_add_typvar).
  repeat(rewrite~ tsubst_add_tvar).
  repeat(rewrite~ tsubst_add_evar).
  repeat(rewrite~ tsubst_add_solved_evar).
  repeat rewrite~ tsubst_add_marker.
Qed.

Lemma actxsubst_fvar: forall G e,
    ACtxSubst G (AE_FVar e) = AE_FVar e.
Proof.
  intros.
  induction G using env_ind.
  repeat(rewrite~ subst_empty_env).
  induction v.
  repeat(rewrite~ subst_add_var).
  repeat(rewrite~ subst_add_typvar).
  repeat(rewrite~ subst_add_tvar).
  repeat(rewrite~ subst_add_evar).
  repeat(rewrite~ subst_add_solved_evar).
  repeat rewrite~ subst_add_marker.
Qed.

Lemma actxtsubst_tfvar_notin: forall G e,
   e # G ->
   ACtxTSubst G (AT_TFVar e) = AT_TFVar e.
Proof.
  introv neq.
  induction G using env_ind.
  rewrite~ tsubst_empty_env.
  induction v. rewrite tsubst_add_var. apply* IHG.
  rewrite tsubst_add_typvar. apply* IHG.
  rewrite tsubst_add_tvar. apply* IHG.
  rewrite tsubst_add_evar. apply* IHG.
  rewrite tsubst_add_solved_evar. simpls. simpl_dom. case_var~.
  rewrite tsubst_add_marker. apply* IHG.
Qed.

Lemma actxtsubst_tfvar: forall G e,
    ok G ->
    binds e AC_TVar G ->
    ACtxTSubst G (AT_TFVar e) = AT_TFVar e.
Proof.
  intros.
  induction G using env_ind.
  repeat(rewrite~ tsubst_empty_env).
  destruct (eq_var_dec e x).
  subst. lets: binds_push_eq_inv H0. subst.
  rewrite tsubst_add_tvar.
  apply ok_push_inv in H. destruct H.
  apply* actxtsubst_tfvar_notin.
  lets: ok_push_inv H. destruct H1.
  apply binds_push_neq_inv in H0; auto.
  lets: IHG H1 H0.
  destruct v.
  repeat(rewrite~ tsubst_add_var).
  repeat(rewrite~ tsubst_add_typvar).
  repeat(rewrite~ tsubst_add_tvar).
  repeat(rewrite~ tsubst_add_evar).
  repeat(rewrite~ tsubst_add_solved_evar). simpls. case_var~.
  repeat(rewrite~ tsubst_add_marker).
Qed.

Lemma actxtsubst_evar: forall G1 G2 a t,
   ok (G1 & a ~ AC_Solved_EVar t & G2) ->
   ACtxTSubst (G1 & a ~ AC_Solved_EVar t & G2) (AT_EVar a)
              = ACtxTSubst G1 t.
Proof.
  introv okg.
  rewrite~ actxtsubst_append.
  rewrite~ tsubst_add_solved_evar. simpls. case_var~.
  apply AWTermT_Solved_EVar with t. apply binds_push_eq.
Qed.

Lemma actxtsubst_evar_notin: forall G e,
   e # G ->
   ACtxTSubst G (AT_EVar e) = AT_EVar e.
Proof.
  introv neq.
  induction G using env_ind.
  rewrite~ tsubst_empty_env.
  induction v. rewrite tsubst_add_var. apply* IHG.
  rewrite tsubst_add_typvar. apply* IHG.
  rewrite tsubst_add_tvar. apply* IHG.
  rewrite tsubst_add_evar. apply* IHG.
  rewrite tsubst_add_solved_evar. simpls. simpl_dom. case_var~.
  rewrite tsubst_add_marker. apply* IHG.
Qed.

Lemma actxsubst_app: forall G e1 e2,
    ACtxSubst G (AE_App e1 e2) = AE_App (ACtxSubst G e1) (ACtxSubst G e2).
Proof.
  intros.
  gen e1 e2. induction G using env_ind; intros.
  repeat(rewrite~ subst_empty_env).
  induction v.
  repeat(rewrite~ subst_add_var).
  repeat(rewrite~ subst_add_typvar).
  repeat(rewrite~ subst_add_tvar).
  repeat(rewrite~ subst_add_evar).
  repeat(rewrite~ subst_add_solved_evar).
  simpls. apply* IHG.
  repeat rewrite~ subst_add_marker.
Qed.

Lemma actxsubst_lam: forall G e,
    ACtxSubst G (AE_Lam e) = AE_Lam (ACtxSubst G e).
Proof.
  intros.
  gen e. induction G using env_ind; intros.
  repeat(rewrite~ subst_empty_env).
  induction v.
  repeat(rewrite~ subst_add_var).
  repeat(rewrite~ subst_add_typvar).
  repeat(rewrite~ subst_add_tvar).
  repeat(rewrite~ subst_add_evar).
  repeat(rewrite~ subst_add_solved_evar).
  simpls. apply* IHG.
  repeat rewrite~ subst_add_marker.
Qed.

Lemma actxsubst_castup: forall G e,
    ACtxSubst G (AE_CastUp e) = AE_CastUp (ACtxSubst G e).
Proof.
  intros.
  gen e. induction G using env_ind; intros.
  repeat(rewrite~ subst_empty_env).
  induction v.
  repeat(rewrite~ subst_add_var).
  repeat(rewrite~ subst_add_typvar).
  repeat(rewrite~ subst_add_tvar).
  repeat(rewrite~ subst_add_evar).
  repeat(rewrite~ subst_add_solved_evar).
  simpls. apply* IHG.
  repeat rewrite~ subst_add_marker.
Qed.

Lemma actxsubst_castdn: forall G e,
    ACtxSubst G (AE_CastDn e) = AE_CastDn (ACtxSubst G e).
Proof.
  intros.
  gen e. induction G using env_ind; intros.
  repeat(rewrite~ subst_empty_env).
  induction v.
  repeat(rewrite~ subst_add_var).
  repeat(rewrite~ subst_add_typvar).
  repeat(rewrite~ subst_add_tvar).
  repeat(rewrite~ subst_add_evar).
  repeat(rewrite~ subst_add_solved_evar).
  simpls. apply* IHG.
  repeat rewrite~ subst_add_marker.
Qed.

Lemma actxsubst_pi: forall G e1 e2,
    ACtxSubst G (AE_Pi e1 e2) = AE_Pi (ACtxTSubst G e1) (ACtxTSubst G e2).
Proof.
  intros.
  gen e1 e2. induction G using env_ind; intros.
  repeat(rewrite~ subst_empty_env). repeat(rewrite~ tsubst_empty_env).
  induction v.
  repeat(rewrite~ subst_add_var). repeat(rewrite~ tsubst_add_var).
  repeat(rewrite~ subst_add_typvar). repeat(rewrite~ tsubst_add_typvar).
  repeat(rewrite~ subst_add_tvar). repeat(rewrite~ tsubst_add_tvar).
  repeat(rewrite~ subst_add_evar). repeat(rewrite~ tsubst_add_evar).
  repeat(rewrite~ subst_add_solved_evar). repeat(rewrite~ tsubst_add_solved_evar).
  simpls. apply* IHG.
  repeat rewrite~ subst_add_marker.
  repeat rewrite~ tsubst_add_marker.
Qed.

Lemma actxsubst_ann: forall G e1 e2,
    ACtxSubst G (AE_Ann e1 e2) = AE_Ann (ACtxSubst G e1) (ACtxTSubst G e2).
Proof.
  intros.
  gen e1 e2. induction G using env_ind; intros.
  repeat(rewrite~ subst_empty_env). repeat(rewrite~ tsubst_empty_env).
  induction v.
  repeat(rewrite~ subst_add_var). repeat(rewrite~ tsubst_add_var).
  repeat(rewrite~ subst_add_typvar). repeat(rewrite~ tsubst_add_typvar).
  repeat(rewrite~ subst_add_tvar). repeat(rewrite~ tsubst_add_tvar).
  repeat(rewrite~ subst_add_evar). repeat(rewrite~ tsubst_add_evar).
  repeat(rewrite~ subst_add_solved_evar). repeat(rewrite~ tsubst_add_solved_evar).
  simpls. apply* IHG.
  repeat rewrite~ subst_add_marker. repeat rewrite~ tsubst_add_marker.
Qed.

Lemma actxsubst_forall: forall G e,
    ACtxSubst G (AE_Forall e) = AE_Forall (ACtxTSubst G e).
Proof.
  intros.
  gen e. induction G using env_ind; intros.
  repeat(rewrite~ subst_empty_env). repeat(rewrite~ tsubst_empty_env).
  induction v.
  repeat(rewrite~ subst_add_var). repeat(rewrite~ tsubst_add_var).
  repeat(rewrite~ subst_add_typvar). repeat(rewrite~ tsubst_add_typvar).
  repeat(rewrite~ subst_add_tvar). repeat(rewrite~ tsubst_add_tvar).
  repeat(rewrite~ subst_add_evar). repeat(rewrite~ tsubst_add_evar).
  repeat(rewrite~ subst_add_solved_evar). repeat(rewrite~ tsubst_add_solved_evar).
  simpls. apply* IHG.
  repeat rewrite~ subst_add_marker. repeat rewrite~ tsubst_add_marker.
Qed.

Lemma subst_notin : forall x v e,
    x \notin (AFev e) ->
    ASubst x v e = e
with tsubst_notin : forall x v e,
    x \notin (ATFev e) ->
    ATSubst x v e = e.
Proof.
  introv notin.
  induction e; simpls; auto; fequals*.
  case_var*.
Proof.
  introv notin.
  induction e; simpls; auto; fequals*.
Qed.

Lemma substt_notin : forall x v e,
    x \notin (AFtv e) ->
    ASubstT x v e = e
with tsubstt_notin : forall x v e,
    x \notin (ATFtv e) ->
    ATSubstT x v e = e.
Proof.
  introv notin.
  induction e; simpls; auto; fequals*.
Proof.
  introv notin.
  induction e; simpls; auto; fequals*.
  case_var*. case_var*.
Qed.

Lemma subst_twice : forall x v e,
    x \notin (AFev v) ->
    ASubst x v (ASubst x v e) = ASubst x v e
with tsubst_twice: forall x v t,
    x \notin (AFev v) ->
    ATSubst x v (ATSubst x v t) = ATSubst x v t.
Proof.
  introv notin.
  induction e; simpl; auto; f_equal *.
  case_var*. rewrite* subst_notin.
  simpl. case_var*.
Proof.
  introv notin.
  induction t; simpls; f_equal *.
Qed.

Lemma substt_twice : forall x v e,
    x \notin (ATFtv v) ->
    ASubstT x v (ASubstT x v e) = ASubstT x v e
with tsubstt_twice: forall x v t,
    x \notin (ATFtv v) ->
    ATSubstT x v (ATSubstT x v t) = ATSubstT x v t.
Proof.
  introv notin.
  induction e; simpl; auto; f_equal *.
Proof.
  introv notin.
  induction t; simpls; f_equal *.
  case_var*. rewrite* tsubstt_notin.
  simpl. case_var*. case_var*. rewrite* tsubstt_notin.
  simpl. case_var*.
Qed.

Lemma tsubst_tsubst: forall x vx y vy e,
    x <> y ->
    x \notin AFv (vx) ->
    ATSubst x vx (ATSubst y vy e) =
    ATSubst x vx (ATSubst y (ASubst x vx vy) e)
with tsubstt_tsubstt: forall x vx y vy e,
    x <> y ->
    x \notin ATFv (vx) ->
    ATSubstT x vx (ATSubst y vy e) =
    ATSubstT x vx (ATSubst y (ASubstT x vx vy) e) .
Proof.
 introv.
 induction e; introv neq notin; simpl; auto.

 induction a; simpl; auto;
   try(simpl in IHa1; inversion IHa1; rewrite H0;
       simpl in IHa2; inversion IHa2; rewrite H1);
   try(simpl in IHa; inversion IHa; rewrite H0); f_equal *.

   case_var*. rewrite* subst_twice.
   f_equal *. f_equal *. f_equal *.
Proof.
 introv.
 induction e; introv neq notin; simpl; auto.

 induction a; simpl; auto;
   try(simpl in IHa1; inversion IHa1; rewrite H0;
       simpl in IHa2; inversion IHa2; rewrite H1);
   try(simpl in IHa; inversion IHa; rewrite H0); f_equal *.

   case_var*. rewrite* substt_twice.
   f_equal *. f_equal *. f_equal *.
Qed.

Lemma subst_subst_distr: forall x vx y vy e,
    x <> y ->
    x \notin AFv (vx) ->
    y \notin AFv (vx) ->
    ASubst x vx (ASubst y vy e) =
    ASubst y (ASubst x vx vy) (ASubst x vx e)
with tsubst_tsubst_distr: forall x vx y vy e,
    x <> y ->
    x \notin AFv (vx) ->
    y \notin AFv (vx) ->
    ATSubst x vx (ATSubst y vy e) =
    ATSubst y (ASubst x vx vy) (ATSubst x vx e).
Proof.
  introv.
  induction e; introv neq notinx notiny; simpl; auto; try(solve[f_equal *]).
  destruct (eq_var_dec v y).
  case_var*.  case_var*. simpl. case_var*.
  destruct (eq_var_dec v x).
  case_var*. case_var*. simpl. case_var*. rewrite* subst_notin.
  case_var*. case_var*. simpl. case_var*. case_var*.
Proof.
  introv.
  induction e; introv neq notinx notiny; simpl; auto; try(solve[f_equal *]).
Qed.

Lemma substt_subst_distr: forall x vx y vy e,
    x <> y ->
    x \notin ATFtv (vx) ->
    y \notin ATFev (vx) ->
    ASubstT x vx (ASubst y vy e) =
    ASubst y (ASubstT x vx vy) (ASubstT x vx e)
with tsubstt_tsubst_distr: forall x vx y vy e,
    x <> y ->
    x \notin ATFtv (vx) ->
    y \notin ATFev (vx) ->
    ATSubstT x vx (ATSubst y vy e) =
    ATSubst y (ASubstT x vx vy) (ATSubstT x vx e).
Proof.
  introv.
  induction e; introv neq notinx notiny; simpl; auto; try(solve[f_equal *]).
  destruct (eq_var_dec v y).
  case_var*.  case_var*.
Proof.
  introv.
  induction e; introv neq notinx notiny; simpl; auto; try(solve[f_equal *]).
  case_var*. rewrite* tsubst_notin.
  destruct (eq_var_dec v x).
  case_var*. rewrite* tsubst_notin.
  case_var*.
Qed.

Lemma substt_substt_distr: forall x vx y vy e,
    x <> y ->
    x \notin ATFtv (vx) ->
    y \notin ATFtv (vx) ->
    ASubstT x vx (ASubstT y vy e) =
    ASubstT y (ATSubstT x vx vy) (ASubstT x vx e)
with tsubstt_tsubstt_distr: forall x vx y vy e,
    x <> y ->
    x \notin ATFtv (vx) ->
    y \notin ATFtv (vx) ->
    ATSubstT x vx (ATSubstT y vy e) =
    ATSubstT y (ATSubstT x vx vy) (ATSubstT x vx e).
Proof.
  introv.
  induction e; introv neq notinx notiny; simpl; auto; try(solve[f_equal *]).
Proof.
  introv.
  induction e; introv neq notinx notiny; simpl; auto; try(solve[f_equal *]).
  destruct (eq_var_dec y v).
  case_var*. case_var*. simpls. case_var*.
  case_var*. case_var*. simpls. case_var*. rewrite* tsubstt_notin.
  simpls. case_var*. case_var*.

  destruct (eq_var_dec y v).
  case_var*. case_var*. simpls. case_var*.
  case_var*. case_var*. simpls. case_var*. rewrite* tsubstt_notin.
  simpls. case_var*. case_var*.
Qed.

(* notin *)

Lemma in_open: forall x y e n,
    x \in AFev e ->
    x \in AFev (AOpenRec n y e)
with in_opent: forall x y e n,
    x \in ATFev e ->
    x \in ATFev (AOpenTypRec n y e).
Proof.
  introv hi. gen n.
  induction e; introv; simpl in *; auto_star;
  try(rewrite in_union in hi; destruct hi as [hi1 | hi2]; [
   apply union_left; apply* IHe1|
   apply union_right; apply* IHe2]).
  rewrite in_empty in hi; inversion hi.
  rewrite in_union in hi. destruct hi as [hi1 | hi2].
   apply union_left. apply* in_opent.
   apply union_right; apply* in_opent.
  rewrite in_union in hi. destruct hi as [hi1 | hi2].
   apply union_left. apply* IHe.
   apply union_right; apply* in_opent.
Proof.
  introv hi. gen n.
  induction e; introv; simpl in *; auto_star;
  try(rewrite in_union in hi; destruct hi as [hi1 | hi2]; [
   apply union_left; apply* IHe1|
   apply union_right; apply* IHe2]).
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
    x \notin ATFv t.
Proof.
  introv wf.
  apply notin_awtermt with (G:=G).
  apply* awterm_solved_evar.
  apply* AWf_push_inv.
Qed.

Lemma notin_subst_self: forall x t e,
    x \notin AFev t ->
    x \notin AFev (ASubst x t e)
with notin_tsubst_self: forall x t e,
    x \notin AFev t ->
    x \notin ATFev (ATSubst x t e).
Proof.
  introv notint.
  induction e; simpls; auto.
  case_if * . simpls. apply* notin_singleton.
Proof.
  introv notine.
  induction e; simpls; auto.
Qed.

Lemma notin_substt_self: forall x t e,
    x \notin ATFtv t ->
    x \notin AFtv (ASubstT x t e)
with notin_tsubstt_self: forall x t e,
    x \notin ATFtv t ->
    x \notin ATFtv (ATSubstT x t e).
Proof.
  introv notint.
  induction e; simpls; auto.
Proof.
  introv notint.
  induction e; simpls; auto.
  case_if * . simpls. apply* notin_singleton.
  case_if * . simpls. apply* notin_singleton.
Qed.

Lemma notin_subst: forall x y t e,
  x \notin AFev e ->
  x \notin AFev t ->
  x \notin AFev (ASubst y t e)
with notin_tsubst: forall x y t e,
  x \notin ATFev e ->
  x \notin AFev t ->
  x \notin ATFev (ATSubst y t e).
Proof.
  introv notine notint.
  destruct (eq_var_dec x y); subst. rewrite* subst_notin.
  induction e; simpls; auto.
  case_if * .
Proof.
  introv notine notint.
  destruct (eq_var_dec x y); subst. rewrite* tsubst_notin.
  induction e; simpls; auto.
Qed.

Lemma notin_substt: forall x y t e,
  x \notin AFv e ->
  x \notin ATFv t ->
  x \notin AFv (ASubstT y t e)
with notin_tsubstt: forall x y t e,
  x \notin ATFv e ->
  x \notin ATFv t ->
  x \notin ATFv (ATSubstT y t e).
Proof.
  introv notine notint.
  destruct (eq_var_dec x y); subst. rewrite* substt_notin.
  induction e; simpls; auto.
Proof.
  introv notine notint.
  destruct (eq_var_dec x y); subst. rewrite* tsubstt_notin.
  induction e; simpls; auto.
  case_if * .
  case_if * .
Qed.

Lemma notin_substt_ftv: forall x y t e,
  x \notin AFtv e ->
  x \notin ATFtv t ->
  x \notin AFtv (ASubstT y t e)
with notin_tsubstt_ftv: forall x y t e,
  x \notin ATFtv e ->
  x \notin ATFtv t ->
  x \notin ATFtv (ATSubstT y t e).
Proof.
  introv notine notint.
  destruct (eq_var_dec x y); subst. rewrite* substt_notin.
  induction e; simpls; auto.
Proof.
  introv notine notint.
  destruct (eq_var_dec x y); subst. rewrite* tsubstt_notin.
  induction e; simpls; auto.
  case_if *.
  case_if *.
Qed.

Lemma notin_substt_fev: forall x y t e,
  x \notin AFev e ->
  x \notin ATFev t ->
  x \notin AFev (ASubstT y t e)
with notin_tsubstt_fev: forall x y t e,
  x \notin ATFev e ->
  x \notin ATFev t ->
  x \notin ATFev (ATSubstT y t e).
Proof.
  introv notine notint.
  destruct (eq_var_dec x y); subst. induction e; simpls; auto.
  induction e; simpls; auto.
Proof.
  introv notine notint.
  destruct (eq_var_dec x y); subst. induction e; simpls; auto.
  case_if *. case_if *.
  induction e; simpls; auto.
  case_if *. case_if *.
Qed.

Lemma notin_ctxsubst_fev: forall x H e,
  x \notin AFev e ->
  x # H ->
  AWf H ->
  x \notin AFev (ACtxSubst H e).
Proof.
  introv notine notinh wf. gen e.
  induction H using env_ind; introv notine.
  rewrite* subst_empty_env.
  assert (wf2:=wf). apply AWf_left in wf2.
  induction v.
  rewrite subst_add_var. apply* IHenv.
  rewrite subst_add_typvar. apply* IHenv.
  assert (x <> x0). simpl_dom. auto_star.

  rewrite subst_add_tvar. apply* IHenv.
  rewrite subst_add_evar. apply* IHenv.

  rewrite subst_add_solved_evar.
  apply* IHenv. apply* notin_substt_fev.
  apply notin_tfv_tfev. apply notin_awtermt with (G:=H); auto.
  apply* awterm_solved_evar.
  rewrite subst_add_marker. apply* IHenv.
Qed.

Lemma notin_ctxsubst_ftv: forall x H e,
  x \notin AFtv e ->
  x # H ->
  AWf H ->
  x \notin AFtv (ACtxSubst H e).
Proof.
  introv notine notinh wf. gen e.
  induction H using env_ind; introv notine.
  rewrite* subst_empty_env.
  assert (wf2:=wf). apply AWf_left in wf2.
  induction v.
  rewrite subst_add_var. apply* IHenv.
  rewrite subst_add_typvar. apply* IHenv.
  assert (x <> x0). simpl_dom. auto_star.

  rewrite subst_add_tvar. apply* IHenv.
  rewrite subst_add_evar. apply* IHenv.

  rewrite subst_add_solved_evar.
  apply* IHenv. apply* notin_substt_ftv.
  apply notin_tfv_tftv. apply notin_awtermt with (G:=H); auto.
  apply* awterm_solved_evar.
  rewrite subst_add_marker. apply* IHenv.
Qed.

Lemma notin_actxsubst: forall y H e,
    AWf H ->
    y # H ->
    y \notin AFv e ->
    y \notin AFv (ACtxSubst H e).
Proof.
  introv wf notinh notine.
  gen e. induction H using env_ind; introv notine.
  rewrite~ subst_empty_env.
  simpls.
  lets: AWf_left wf.
  induction v.
  rewrite~ subst_add_var.
  rewrite~ subst_add_typvar.
  rewrite~ subst_add_tvar.
  rewrite~ subst_add_evar.
  rewrite~ subst_add_solved_evar.
  apply* IHenv. apply* notin_substt. apply notin_awtermt with H; auto.
  apply* awterm_solved_evar.
  rewrite~ subst_add_marker.
Qed.

Lemma notin_ctxtsubst_ftv: forall x H e,
  x \notin ATFtv e ->
  x # H ->
  AWf H ->
  x \notin ATFtv (ACtxTSubst H e).
Proof.
  introv notine notinh wf. gen e.
  induction H using env_ind; introv notine.
  rewrite* tsubst_empty_env.
  assert (wf2:=wf). apply AWf_left in wf2.
  induction v.
  rewrite tsubst_add_var. apply* IHenv.
  rewrite tsubst_add_typvar. apply* IHenv.
  assert (x <> x0). simpl_dom. auto_star.

  rewrite tsubst_add_tvar. apply* IHenv.
  rewrite tsubst_add_evar. apply* IHenv.

  rewrite tsubst_add_solved_evar.
  apply* IHenv. apply* notin_tsubstt_ftv.
  apply notin_tfv_tftv. apply notin_awtermt with (G:=H); auto.
  apply* awterm_solved_evar.
  rewrite tsubst_add_marker. apply* IHenv.
Qed.

Lemma notin_ctxtsubst_fev: forall x H e,
  x \notin ATFev e ->
  x # H ->
  AWf H ->
  x \notin ATFev (ACtxTSubst H e).
Proof.
  introv notine notinh wf. gen e.
  induction H using env_ind; introv notine.
  rewrite* tsubst_empty_env.
  assert (wf2:=wf). apply AWf_left in wf2.
  induction v.
  rewrite tsubst_add_var. apply* IHenv.
  rewrite tsubst_add_typvar. apply* IHenv.
  assert (x <> x0). simpl_dom. auto_star.

  rewrite tsubst_add_tvar. apply* IHenv.
  rewrite tsubst_add_evar. apply* IHenv.

  rewrite tsubst_add_solved_evar.
  apply* IHenv. apply* notin_tsubstt_fev.
  apply notin_tfv_tfev. apply notin_awtermt with (G:=H); auto.
  apply* awterm_solved_evar.
  rewrite tsubst_add_marker. apply* IHenv.
Qed.

Lemma notin_actxtsubst: forall y H e,
    AWf H ->
    y # H ->
    y \notin ATFv e ->
    y \notin ATFv (ACtxTSubst H e).
Proof.
  introv wf notinh notine.
  gen e. induction H using env_ind; introv notine.
  rewrite~ tsubst_empty_env.
  simpls.
  lets: AWf_left wf.
  induction v.
  rewrite~ tsubst_add_var.
  rewrite~ tsubst_add_typvar.
  rewrite~ tsubst_add_tvar.
  rewrite~ tsubst_add_evar.
  rewrite~ tsubst_add_solved_evar.
  apply* IHenv. apply* notin_tsubstt. apply notin_awtermt with H; auto.
  apply* awterm_solved_evar.
  rewrite~ tsubst_add_marker.
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

Lemma uv_add_var: forall G x,
    ACtxUV (G & x ~ AC_Var) = ACtxUV G.
Proof.
  introv. rewrite <- cons_to_push. unfold ACtxUV; simpls; auto.
Qed.

Lemma uv_add_typvar: forall G x t,
    ACtxUV (G & x ~ AC_Typ t) = ACtxUV G.
Proof.
  introv. rewrite <- cons_to_push. unfold ACtxUV; simpls; auto.
Qed.

Lemma uv_add_tvar: forall G x,
    ACtxUV (G & x ~ AC_TVar) = ACtxUV G.
Proof.
  introv. rewrite <- cons_to_push. unfold ACtxUV; simpls; auto.
Qed.

Lemma uv_add_evar: forall G x,
    ACtxUV (G & x ~ AC_Unsolved_EVar) = (ACtxUV G) & x ~ AC_Unsolved_EVar.
Proof.
  introv. rewrite <- cons_to_push. unfold ACtxUV; simpls; auto.
Qed.

Lemma uv_add_solved_evar: forall G x t,
    ACtxUV (G & x ~ AC_Solved_EVar t) = (ACtxUV G).
Proof.
  introv. rewrite <- cons_to_push. unfold ACtxUV; simpls; auto.
Qed.

Lemma uv_add_marker: forall G x,
    ACtxUV (G & x ~ AC_Marker) = (ACtxUV G).
Proof.
  introv. rewrite <- cons_to_push. unfold ACtxUV; simpls; auto.
Qed.

Lemma uv_is_soft: forall G,
    ok G ->
    Softness (ACtxUV G).
Proof.
  introv okg. induction G using env_ind.
  rewrite empty_uv. constructor.
  induction v.
  rewrite~ uv_add_var.
  rewrite~ uv_add_typvar.
  rewrite~ uv_add_tvar.
  rewrite~ uv_add_evar. constructor. apply IHG. apply* ok_push_inv. apply notin_uv. apply* ok_push_inv.
  rewrite~ uv_add_solved_evar.
  rewrite~ uv_add_marker.
Qed.

Lemma awf_append_uv: forall G H,
    AWf G ->
    ok (G & H) ->
    AWf (G & ACtxUV H).
Proof.
  introv wf okg.
  induction H using env_ind.
  rewrite empty_uv. rewrite~ concat_empty_r.
  assert (ok (G & H)). rewrite concat_assoc in okg. apply* ok_concat_inv_l.
  lets: IHenv H0.
  destruct v; simpls; auto.
  rewrite~ uv_add_var.
  rewrite~ uv_add_typvar.
  rewrite~ uv_add_tvar.
  rewrite~ uv_add_evar. rewrite concat_assoc. apply~ AWf_Ctx_Unsolved_EVar. simpl_dom. apply notin_union. split.
  rewrite concat_assoc in okg. destruct (ok_push_inv okg) as [_ notin]. auto.
  apply notin_uv. apply ok_concat_inv_r in okg. destruct (ok_push_inv okg) as [_ notin]. auto.
  rewrite~ uv_add_solved_evar.
  rewrite~ uv_add_marker.
Qed.

Lemma uv_ok: forall G H,
    ok (G & H) ->
    ok (G & ACtxUV H).
Proof.
  introv okg.
  induction H using env_ind.
  rewrite~ empty_uv.
  assert (ok (G & H)). rewrite concat_assoc in okg. apply* ok_concat_inv_l.
  lets: IHenv H0.
  destruct v; simpls; auto.
  rewrite~ uv_add_var.
  rewrite~ uv_add_typvar.
  rewrite~ uv_add_tvar.
  rewrite~ uv_add_evar. rewrite concat_assoc. apply~ ok_push. simpl_dom. apply notin_union. split.
  rewrite concat_assoc in okg. destruct (ok_push_inv okg) as [_ notin]. auto.
  apply notin_uv. apply ok_concat_inv_r in okg. destruct (ok_push_inv okg) as [_ notin]. auto.
  rewrite~ uv_add_solved_evar.
  rewrite~ uv_add_marker.
Qed.

Lemma uv_ok2: forall H,
    ok H ->
    ok (ACtxUV H).
Proof.
  introv okg.
  induction H using env_ind.
  rewrite~ empty_uv.
  assert (ok H). apply* ok_concat_inv_l.
  lets: IHenv H0.
  destruct v; simpls; auto.
  rewrite~ uv_add_var.
  rewrite~ uv_add_typvar.
  rewrite~ uv_add_tvar.
  rewrite~ uv_add_evar. apply~ ok_push. apply ok_push_inv in okg. destruct okg. apply notin_uv in H3; auto.
  rewrite~ uv_add_solved_evar.
  rewrite~ uv_add_marker.
Qed.

Lemma uv_var_preservation: forall G a v,
    binds a v (ACtxUV G) ->
    ok G ->
    binds a v G.
Proof.
  intro G.
  induction G using env_ind; introv bd okg.
  rewrite empty_uv in bd.
  false binds_empty_inv bd.
  induction v.
  rewrite~ uv_add_var in bd. destruct (ok_push_inv okg). lets: IHG bd H. apply~ binds_concat_left_ok.
  rewrite~ uv_add_typvar in bd. destruct (ok_push_inv okg). lets: IHG bd H. apply~ binds_concat_left_ok.
  rewrite~ uv_add_tvar in bd. destruct (ok_push_inv okg). lets: IHG bd H. apply~ binds_concat_left_ok.
  rewrite~ uv_add_evar in bd.
  apply binds_push_inv in bd.
  destruct bd as [[eq1 eq2] | [neq1 neq2]]; subst.
  apply~ binds_push_eq. destruct (ok_push_inv okg).
  lets: IHG neq2 H. apply~ binds_concat_left_ok.
  rewrite~ uv_add_solved_evar in bd. destruct (ok_push_inv okg). lets: IHG bd H. apply~ binds_concat_left_ok.
  rewrite~ uv_add_marker in bd. destruct (ok_push_inv okg). lets: IHG bd H. apply~ binds_concat_left_ok.
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

  repeat(rewrite subst_add_tvar).
  apply AWf_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_evar).
  apply AWf_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_solved_evar).
  rewrite substt_subst_distr.
  apply AWf_left in wf.
  apply* IHenv.
  simpl_dom. auto.
  assert (x # H). apply* AWf_push_inv.
  apply awterm_solved_evar in wf. apply notin_tfv_tftv. apply* notin_awtermt.
  apply awterm_solved_evar in wf. apply notin_tfv_tfev. apply* notin_awtermt.

  repeat(rewrite subst_add_marker).
  apply AWf_left in wf.
  apply* IHenv.
Qed.

Lemma distributivity_ctxsubst_substt : forall H x s e,
    AWf H ->
    x # H ->
    ACtxSubst H (ASubstT x s e) =
    ASubstT x (ACtxTSubst H s) (ACtxSubst H e).
Proof.
  introv. gen s e x.
  induction H using env_ind; introv wf notin.
  repeat(rewrite* subst_empty_env).
  repeat(rewrite* tsubst_empty_env).

  induction v.

  repeat(rewrite subst_add_var).
  repeat(rewrite tsubst_add_var).
  apply AWf_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_typvar).
  repeat(rewrite tsubst_add_typvar).
  apply AWf_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_tvar).
  repeat(rewrite tsubst_add_tvar).
  apply AWf_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_evar).
  repeat(rewrite tsubst_add_evar).
  apply AWf_left in wf.
  apply* IHenv.

  repeat(rewrite subst_add_solved_evar).
  repeat(rewrite tsubst_add_solved_evar).
  rewrite substt_substt_distr.
  apply AWf_left in wf.
  apply* IHenv.
  simpl_dom. auto.
  assert (x # H). apply* AWf_push_inv.
  apply awterm_solved_evar in wf. apply notin_tfv_tftv. apply* notin_awtermt.
  apply awterm_solved_evar in wf. apply notin_tfv_tftv. apply* notin_awtermt.

  repeat(rewrite subst_add_marker).
  repeat(rewrite tsubst_add_marker).
  apply AWf_left in wf.
  apply* IHenv.
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

  rewrite subst_add_tvar.
  rewrite tsubst_add_tvar.
  rewrite tsubst_add_tvar.
  apply AWf_left in wf.
  apply* IHenv.

  rewrite subst_add_evar.
  rewrite tsubst_add_evar.
  rewrite tsubst_add_evar.
  apply AWf_left in wf.
  apply* IHenv.

  rewrite subst_add_solved_evar.
  rewrite tsubst_add_solved_evar.
  rewrite tsubst_add_solved_evar.
  rewrite tsubstt_tsubst_distr.
  apply AWf_left in wf.
  apply* IHenv.
  simpl_dom. auto.
  assert (x # H). apply* AWf_push_inv.
  apply awterm_solved_evar in wf. apply notin_tfv_tftv. apply* notin_awtermt.
  apply awterm_solved_evar in wf. apply notin_tfv_tfev. apply* notin_awtermt.

  rewrite subst_add_marker.
  rewrite tsubst_add_marker.
  rewrite tsubst_add_marker.
  apply AWf_left in wf.
  apply* IHenv.
Qed.

Lemma distributivity_ctxtsubst_substt : forall H x s e,
    AWf H ->
    x # H ->
    ACtxSubst H (ASubstT x s e) =
    ASubstT x (ACtxTSubst H s) (ACtxSubst H e).
Proof.
  introv. gen s e x.
  induction H using env_ind; introv wf notin.
  rewrite* subst_empty_env.
  rewrite* tsubst_empty_env.
  rewrite* subst_empty_env.

  induction v.

  rewrite subst_add_var.
  rewrite tsubst_add_var.
  rewrite subst_add_var.
  apply AWf_left in wf.
  apply* IHenv.

  rewrite subst_add_typvar.
  rewrite tsubst_add_typvar.
  rewrite subst_add_typvar.
  apply AWf_left in wf.
  apply* IHenv.

  rewrite subst_add_tvar.
  rewrite tsubst_add_tvar.
  rewrite subst_add_tvar.
  apply AWf_left in wf.
  apply* IHenv.

  rewrite subst_add_evar.
  rewrite tsubst_add_evar.
  rewrite subst_add_evar.
  apply AWf_left in wf.
  apply* IHenv.

  rewrite subst_add_solved_evar.
  rewrite tsubst_add_solved_evar.
  rewrite subst_add_solved_evar.
  rewrite substt_substt_distr.
  apply AWf_left in wf.
  apply* IHenv.
  simpl_dom. auto.
  assert (x # H). apply* AWf_push_inv.
  apply awterm_solved_evar in wf. apply notin_tfv_tftv. apply* notin_awtermt.
  apply awterm_solved_evar in wf. apply notin_tfv_tftv. apply* notin_awtermt.

  rewrite subst_add_marker.
  rewrite tsubst_add_marker.
  rewrite subst_add_marker.
  apply AWf_left in wf.
  apply* IHenv.
Qed.

Lemma distributivity_ctxtsubst_tsubstt : forall H x s e,
    AWf H ->
    x # H ->
    ACtxTSubst H (ATSubstT x s e) =
    ATSubstT x (ACtxTSubst H s) (ACtxTSubst H e).
Proof.
  introv. gen s e x.
  induction H using env_ind; introv wf notin.
  repeat(rewrite* tsubst_empty_env).

  induction v.

  repeat(rewrite tsubst_add_var).
  apply AWf_left in wf.
  apply* IHenv.

  repeat(rewrite tsubst_add_typvar).
  apply AWf_left in wf.
  apply* IHenv.

  repeat(rewrite tsubst_add_tvar).
  apply AWf_left in wf.
  apply* IHenv.

  repeat(rewrite tsubst_add_evar).
  apply AWf_left in wf.
  apply* IHenv.

  repeat(rewrite tsubst_add_solved_evar).
  rewrite tsubstt_tsubstt_distr.
  apply AWf_left in wf.
  apply* IHenv.
  simpl_dom. auto.
  assert (x # H). apply* AWf_push_inv.
  apply awterm_solved_evar in wf. apply notin_tfv_tftv. apply* notin_awtermt.
  apply awterm_solved_evar in wf. apply notin_tfv_tftv. apply* notin_awtermt.

  repeat rewrite tsubst_add_marker.
  apply AWf_left in wf.
  apply* IHenv.
Qed.

Lemma awtermt_is_awtermty: forall G e,
    AWTermT G e -> ATermTy e.
Proof.
  introv wt.
  induction wt; simpls; auto.

  inversion IHwt1; subst.
  inversion IHwt2; subst.
  apply~ ATermTy_Expr.

  apply~ ATermTy_Expr.
  apply ATerm_Lam with L.
  intros y notin_l.
  lets: H0 notin_l.
  inversion H1; subst; auto.

  inversion IHwt; subst.
  apply~ ATermTy_Expr.

  inversion IHwt; subst.
  apply~ ATermTy_Expr.

  inversion IHwt1; subst.
  inversion IHwt2; subst.
  apply~ ATermTy_Expr.

  inversion IHwt1; subst.
  inversion IHwt2; subst.
  apply~ ATermTy_Expr.

  inversion IHwt1; subst.
  inversion IHwt2; subst.
  apply~ ATermTy_Expr.

  apply~ ATermTy_Expr.
  apply ATerm_Forall with L.
  intros y notin_l.
  lets: H0 notin_l. auto.

  apply ATermTy_TFVar.
  apply ATermTy_EVar.
  apply ATermTy_EVar.
Qed.

Lemma ctxsubst_twice: forall H e,
    AWf H ->
    ACtxSubst H (ACtxSubst H e) = ACtxSubst H e.
Proof.
  introv wf. gen e. induction H using env_ind; introv.
  repeat rewrite~ subst_empty_env.
  lets: AWf_left wf.
  destruct (ok_push_inv (awf_is_ok wf)).
  destruct v.
  repeat rewrite~ subst_add_var.
  repeat rewrite~ subst_add_typvar.
  repeat rewrite~ subst_add_tvar.
  repeat rewrite~ subst_add_evar.
  repeat rewrite~ subst_add_solved_evar.
  rewrite~ distributivity_ctxsubst_substt.
  rewrite~ IHenv.
  rewrite~ <- distributivity_ctxsubst_substt.
  rewrite~ substt_twice. apply notin_tfv_tftv.
  apply notin_awtermt with H; auto.
  apply awterm_solved_evar in wf; auto.
  repeat rewrite~ subst_add_marker.
Qed.

Lemma ctxtsubst_twice: forall H e,
    AWf H ->
    ACtxTSubst H (ACtxTSubst H e) = ACtxTSubst H e.
Proof.
  introv wf. gen e. induction H using env_ind; introv.
  repeat rewrite~ tsubst_empty_env.
  lets: AWf_left wf.
  destruct (ok_push_inv (awf_is_ok wf)).
  destruct v.
  repeat rewrite~ tsubst_add_var.
  repeat rewrite~ tsubst_add_typvar.
  repeat rewrite~ tsubst_add_tvar.
  repeat rewrite~ tsubst_add_evar.
  repeat rewrite~ tsubst_add_solved_evar.
  rewrite~ distributivity_ctxtsubst_tsubstt.
  rewrite~ IHenv.
  rewrite~ <- distributivity_ctxtsubst_tsubstt.
  rewrite~ tsubstt_twice. apply notin_tfv_tftv.
  apply notin_awtermt with H; auto.
  apply awterm_solved_evar in wf; auto.
  repeat rewrite~ tsubst_add_marker.
Qed.

(* mono *)

Lemma atmono_subst: forall t e x,
    ATMono t -> ATMono e ->
    ATMono (ATSubstT x t e)
with amono_subst: forall t e x,
    ATMono t -> AMono e ->
    AMono (ASubstT x t e).
Proof.
  introv monot monoe.
  induction e; simpls~.
  case_var~.
  case_var~.
  simpls.
  apply AM_Expr. inversion monoe. subst. apply~ amono_subst.
Proof.
  introv monot monoe.
  induction e; simpls~.
  inversion monoe; subst. apply~ AM_App.
  inversion monoe; subst. apply~ AM_Lam.
  inversion monoe; subst. apply~ AM_Pi.
  inversion monoe; subst. apply~ AM_CastUp.
  inversion monoe; subst. apply~ AM_CastDn.
  inversion monoe; subst. apply~ AM_Ann.
  inversion monoe; subst.
Qed.

Lemma atmono_subst_inv: forall t e x,
    ATMono (ATSubstT x t e) ->
    ATMono e
with amono_subst_inv: forall t e x,
    AMono (ASubstT x t e) ->
    AMono e.
Proof.
  introv mono.
  induction e; simpls~.
  apply~ AM_TFVar.
  apply~ AM_EVar.
  inversion mono; subst.
  apply~ AM_Expr.
  apply* amono_subst_inv.
Proof.
  introv mono.
  induction e; simpls~.
  inversion mono; subst. apply~ AM_App.
  inversion mono; subst. apply~ AM_Lam.
  inversion mono; subst. apply~ AM_Pi.
  apply* atmono_subst_inv.
  apply* atmono_subst_inv.
  inversion mono; subst. apply~ AM_CastUp.
  inversion mono; subst. apply~ AM_CastDn.
  inversion mono; subst. apply~ AM_Ann.
  apply* atmono_subst_inv.
  inversion mono; subst.
Qed.

Lemma atmono_actxtsubst: forall G t,
    AWf G ->
    ATMono t <-> ATMono (ACtxTSubst G t)
with amono_actxsubst: forall G t,
    AWf G ->
    AMono t <-> AMono (ACtxSubst G t).
Proof.
  split. gen t.
  induction G using env_ind; introv mono.
  rewrite~ tsubst_empty_env.
  lets: AWf_left H.
  induction v.
  rewrite~ tsubst_add_var.
  rewrite~ tsubst_add_typvar.
  rewrite~ tsubst_add_tvar.
  rewrite~ tsubst_add_evar.
  rewrite~ tsubst_add_solved_evar.
  apply~ IHG. apply~ atmono_subst.
  lets: atmono_solved_evar H. auto.
  rewrite~ tsubst_add_marker.

  (* right *)
  gen t. induction G using env_ind; introv mono.
  rewrite tsubst_empty_env in mono; auto.
  lets: AWf_left H.
  induction v.
  rewrite tsubst_add_var in mono; auto.
  rewrite tsubst_add_typvar in mono; auto.
  rewrite tsubst_add_tvar in mono; auto.
  rewrite tsubst_add_evar in mono; auto.
  rewrite tsubst_add_solved_evar in mono.
  lets: IHG H0 mono.
  apply atmono_subst_inv in H1. auto.
  rewrite tsubst_add_marker in mono; auto.
Proof.
  split. gen t.
  induction G using env_ind; introv mono.
  rewrite~ subst_empty_env.
  lets: AWf_left H.
  induction v.
  rewrite~ subst_add_var.
  rewrite~ subst_add_typvar.
  rewrite~ subst_add_tvar.
  rewrite~ subst_add_evar.
  rewrite~ subst_add_solved_evar.
  apply~ IHG. apply~ amono_subst.
  lets: atmono_solved_evar H. auto.
  rewrite~ subst_add_marker.

  (* right *)
  gen t. induction G using env_ind; introv mono.
  rewrite subst_empty_env in mono; auto.
  lets: AWf_left H.
  induction v.
  rewrite subst_add_var in mono; auto.
  rewrite subst_add_typvar in mono; auto.
  rewrite subst_add_tvar in mono; auto.
  rewrite subst_add_evar in mono; auto.
  rewrite subst_add_solved_evar in mono.
  lets: IHG H0 mono.
  apply amono_subst_inv in H1. auto.
  rewrite subst_add_marker in mono; auto.
Qed.

Lemma atmono_open: forall t n u,
    ATMono t -> ATMono u ->
    ATMono (ATOpenTypRec n u t)
with amono_open: forall n u t,
    AMono t -> ATMono u ->
    AMono (ATOpenRec n u t).
Proof.
  introv monot monou.
  induction t; simpls~.
  case_nat~.
  apply AM_Expr.
  inversion monot; subst.
  apply* amono_open.
Proof.
  introv monot monou.
  induction t; simpls~.
  inversion monot; subst. apply~ AM_App.
  inversion monot; subst. apply~ AM_Lam.
  inversion monot; subst. apply~ AM_Pi.
  inversion monot; subst. apply~ AM_CastUp.
  inversion monot; subst. apply~ AM_CastDn.
  inversion monot; subst. apply~ AM_Ann.
  inversion monot; subst.
Qed.

Lemma atmono_topen_inv: forall t n u,
    ATMono (ATOpenTypRec n u t) ->
    ATMono t
with amono_topen_inv: forall n u t,
    AMono (ATOpenRec n u t) ->
    AMono t.
Proof.
  introv monot.
  induction t; simpls~.
  case_nat~. apply AM_TBVar.
  apply AM_Expr.
  inversion monot; subst.
  apply* amono_topen_inv.
Proof.
  introv monot. gen n.
  induction t; introv monot; simpls~.
  inversion monot; subst. apply~ AM_App. apply* IHt1. apply* IHt2.
  inversion monot; subst. apply~ AM_Lam. apply* IHt.
  inversion monot; subst. apply~ AM_Pi.
  apply* atmono_topen_inv.
  apply* atmono_topen_inv.
  inversion monot; subst. apply~ AM_CastUp. apply* IHt.
  inversion monot; subst. apply~ AM_CastDn. apply* IHt.
  inversion monot; subst. apply~ AM_Ann. apply* IHt.
  apply* atmono_topen_inv.
  inversion monot; subst.
Qed.

Lemma atmono_open_inv: forall t n u,
    ATMono (AOpenTypRec n u t) ->
    ATMono t
with amono_open_inv: forall n u t,
    AMono (AOpenRec n u t) ->
    AMono t.
Proof.
  introv monot.
  induction t; simpls~.
  apply AM_Expr.
  inversion monot; subst.
  apply* amono_open_inv.
Proof.
  introv monot. gen n.
  induction t; introv monot; simpls~.
  apply AM_BVar.
  inversion monot; subst. apply~ AM_App. apply* IHt1. apply* IHt2.
  inversion monot; subst. apply~ AM_Lam. apply* IHt.
  inversion monot; subst. apply~ AM_Pi.
  apply* atmono_open_inv.
  apply* atmono_open_inv.
  inversion monot; subst. apply~ AM_CastUp. apply* IHt.
  inversion monot; subst. apply~ AM_CastDn. apply* IHt.
  inversion monot; subst. apply~ AM_Ann. apply* IHt.
  apply* atmono_open_inv.
  inversion monot; subst.
Qed.