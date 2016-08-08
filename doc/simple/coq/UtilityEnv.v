Require Import DeclDef.
Require Import AlgoDef.
Require Import LibLN.
Require Import AlgoInfra.

Set Implicit Arguments.

Inductive Softness : ACtx -> Prop :=
  | Softness_Empty: Softness empty
  | Softness_Unsolved: forall G a, Softness G -> a # G -> Softness (G & a ~ AC_Unsolved_EVar)
  | Softness_Solved: forall G a t, Softness G -> a # G -> Softness (G & a ~ AC_Solved_EVar t).

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

Lemma AWf_left : forall G1 G2 H1,
    AWf (G1 & G2) H1 -> (exists H, AWf G1 H).
Proof.
  introv IH. gen_eq I: (G1 & G2). gen G1 G2. induction IH; intros IG HH HI.

  apply empty_concat_inv in HI. destruct HI as [HIG HIH]. subst. exists* (empty:ACtx).
  induction HH using env_ind.
  rewrite concat_empty_r in HI. rewrite <- HI. exists* (H & x ~ AC_Var).
  rewrite concat_assoc in HI. apply eq_push_inv in HI. destruct HI as [HIx [HIv HIgh]]. apply* IHIH.
  induction HH using env_ind.
  rewrite concat_empty_r in HI. rewrite <- HI. exists* (H & x ~ AC_Typ t).
  rewrite concat_assoc in HI. apply eq_push_inv in HI. destruct HI as [HIx [HIv HIgh]]. apply* IHIH.

  induction HH using env_ind.
  rewrite concat_empty_r in HI. rewrite <- HI. exists* (H & x ~ AC_Bnd (AT_Expr s) t).
  rewrite concat_assoc in HI. apply eq_push_inv in HI. destruct HI as [HIx [HIv HIgh]]. apply* IHIH.

  induction HH using env_ind.
  rewrite concat_empty_r in HI. rewrite <- HI. exists* (H & x ~ AC_Bnd (AT_Forall s) t).
  rewrite concat_assoc in HI. apply eq_push_inv in HI. destruct HI as [HIx [HIv HIgh]]. apply* IHIH.

  induction HH using env_ind.
  rewrite concat_empty_r in HI. rewrite <- HI. exists* (H & x ~ AC_Unsolved_EVar).
  rewrite concat_assoc in HI. apply eq_push_inv in HI. destruct HI as [HIx [HIv HIgh]]. apply* IHIH.

  induction HH using env_ind.
  rewrite concat_empty_r in HI. rewrite <- HI. exists* (H & x ~ AC_Solved_EVar t).
  rewrite concat_assoc in HI. apply eq_push_inv in HI. destruct HI as [HIx [HIv HIgh]]. apply* IHIH.
Qed.

Lemma AWf_push_inv : forall G H x v,
    AWf (G & x ~ v) H -> x # G.
Proof.
  introv WF. inversion WF;
  try(apply empty_push_inv in H1; inversion H1);
  try(apply eq_push_inv in H1; destruct H1 as [eqg [eqx eqv]]; subst; simpl_dom; auto);
  try(apply eq_push_inv in H2; destruct H2 as [eqg [eqx eqv]]; subst; simpl_dom; auto);
  try(apply eq_push_inv in H3; destruct H3 as [eqg [eqx eqv]]; subst; simpl_dom; auto).
Qed.

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

Lemma subst_notin : forall x v e,
    x \notin (AFv e) ->
    ASubst x v e = e.
Proof.
  introv notin.
  induction e; simpl; auto;
  try(simpl in notin; rewrite* IHe1; rewrite* IHe2);
  try(rewrite* IHe).

  destruct (eq_var_dec v0 x).
  subst. simpl in notin0. apply notin_same in notin0. inversion notin0.
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
