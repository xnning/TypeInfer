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