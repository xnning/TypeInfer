Set Implicit Arguments.
Require Import LibLN DeclDef DeclInfra.
Implicit Types x : var.

Lemma dtyping_prod_inv : forall E U T,
  DTypingC E (DE_Pi U T) DE_Star -> 
  DTypingC E U DE_Star
  /\ exists L, forall x, x \notin L ->
                         DTypingC (E & x ~ DC_Typ U) (T ^ x) DE_Star.
Proof.
  introv Typ. gen_eq P1: (DE_Pi U T).
  induction Typ; intros; subst; tryfalse.
  injection H1; intros; subst.
  unfold DTypingC.
  split. auto. exists* L.
  apply* IHTyp.
  apply* IHTyp.
Qed.

Lemma dtyping_abs_inv : forall E t P,
  DTypingC E (DE_Lam t) P -> exists V T m,
      DTypingC E V DE_Star
      /\ P = DE_Pi V T
      /\ exists L, forall x, x \notin L ->
                             DTyping m (E & x ~ DC_Typ V) (t ^ x) (T ^ x).
Proof.
  introv Typ. gen_eq u: (DE_Lam t).
  induction Typ; intros; subst; tryfalse.
  injection H1; intros; subst.
  exists t1 t2 Inf. split*.
  apply* IHTyp.
  injection H1; intros; subst.
  exists t1 t2 Chk. split*.
  apply* IHTyp.
Qed.

Lemma dtyping_prod_type_inv : forall E U T,
  DTypingC E (DE_Pi U T) DE_Star ->
  exists L, forall x, x \notin L ->
      DTypingC (E & x ~ DC_Typ U) (T ^ x) DE_Star.
Proof.
  introv Typ.
  destruct (dtyping_prod_inv Typ) as [TypU [L TypT]].
  exists (L \u dom E). intros. auto.
Qed.

Lemma dtyping_castup_inv : forall E t V,
    DTypingC E (DE_CastUp t) V -> exists U T,
      DTypingC E t T /\ U = V /\ DRed U T.
Proof.
  introv Typ. gen_eq u: (DE_CastUp t).
  induction Typ; intros; subst; tryfalse.
  apply* IHTyp.
  injection H0; intros; subst.
  exists* t2 t1.
  apply* IHTyp.
Qed.

Lemma dtyping_weaken : forall m G E F t T,
  DTyping m (E & G) t T ->
  DWf (E & F & G) -> 
  DTyping m (E & F & G) t T
with dinst_weaken : forall G E F t T,
    DInst (E & G) t T ->
    DWf (E & F & G) ->
    DInst (E & F & G) t T
with dgen_weaken : forall G E F t T,
    DGen (E & G) t T ->
    DWf (E & F & G) ->
    DGen (E & F & G) t T.
Proof.
  introv Typ. gen_eq Env: (E & G). gen G.
  induction Typ; introv EQ W; subst; auto.
  apply* DTI_LetVar. apply* binds_weaken.
  apply_fresh* (@DTI_Lam) as y. apply_ih_bind* H0.
  apply* DTI_App.
  apply_fresh* (@DTI_Let) as y. admit.
  apply_fresh* (@DTI_Pi) as y. apply_ih_bind* H0.
  apply* DTI_CastDn.
  apply_fresh* (@DTC_Lam) as y. apply_ih_bind* H0.
  apply_fresh* (@DTC_Let) as y. admit.
  apply* DTC_CastUp.

  introv Typ. gen_eq Env: (E & G). gen G.
  induction Typ; introv EQ W; subst; auto.
  apply_fresh* (@DInst_Poly) as y. admit.

  introv Typ. gen_eq Env: (E & G). gen G.
  induction Typ; introv EQ W; subst; auto.
  apply_fresh* (@DGen_Poly) as y. intros. admit.
Admitted.
