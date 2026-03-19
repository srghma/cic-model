Require Export basic.
Require Import ZF Zpairs Zrelations Znats.

(** Building a function by compatible union of functions
*)



Section ExtendFamily.

  Variable I : set.

  Variable A F : set -> set.
  Hypothesis extA : ext_fun I A.
  Hypothesis extF : ext_fun I F.

  Hypothesis in_prod : forall x, x ∈ I -> is_cc_fun (A x) (F x).

  Hypothesis fcomp : fdirected I A F.

  Lemma fdir :
    forall x0 x1 x z,
    x0 ∈ I ->
    x1 ∈ I ->
    x ∈ A x0 ->
    z ∈ cc_app (F x1) x ->
    z ∈ cc_app (F x0) x.
intros.
assert (x ∈ A x1).
{rewrite <- couple_in_app in H2.
 specialize in_prod with (1:=H0).
 apply in_prod; rewrite rel_domain_ax; eauto. }
apply eq_elim with (cc_app (F x1) x); trivial.
apply fcomp; trivial.
rewrite inter2_def; auto.
Qed.

Lemma prd_union : is_cc_fun (sup I A) (sup I F).
split; intros.
*red; intros.
 rewrite sup_ax in H; trivial.
 destruct H as (y,?,(_,?)).
 apply in_prod with y; trivial.
*red; intros.
 rewrite rel_domain_ax in H.
 destruct H as (y,inf).
 rewrite sup_ax in inf; trivial.
 destruct inf as (x,?,(_,?)).
 rewrite sup_def;[exists x;trivial|trivial].
 apply in_prod;trivial.
 rewrite rel_domain_ax; eauto.
Qed.

Lemma prd_sup : forall x,
  x ∈ I ->
  fcompat (A x) (F x) (sup I F).
red; intros.
apply eq_intro; intros.
  rewrite <- couple_in_app.
  rewrite sup_def; trivial.
  exists x; trivial.
  rewrite couple_in_app; trivial.

  rewrite <- couple_in_app in H1.
  rewrite sup_def in H1; trivial.
  destruct H1.
  rewrite couple_in_app in H2.
  assert (in_prd := in_prod _ H1).
  apply fdir with x1; trivial.
Qed.


Lemma prd_sup_lub : forall g,
  (forall x, x ∈ I -> fcompat (A x) (F x) g) ->
  fcompat (sup I A) (sup I F) g.
red; intros.
rewrite sup_def in H0; trivial; destruct H0.
rewrite <- (prd_sup x0 H0 _); trivial.
apply H; trivial.
Qed.


End ExtendFamily.
