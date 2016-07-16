Require Import DeclDef.
Require Import AlgoDef.
Require Import LibLN.

Set Implicit Arguments.

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
