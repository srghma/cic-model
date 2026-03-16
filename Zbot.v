Require Import Zpairs Zrelations.

(** Extending domains with a set [bot] of "bottom values" *)

Lemma cc_prod_ext_bot bot U V f :
  ext_fun (bot ∪ U) V ->
  (forall x, x ∈ bot -> empty ∈ V x) ->
  (forall x, x ∈ bot -> ~ x ∈ U) ->
  f ∈ (Π x ∈ U, V x) ->
  f ∈ (Π x ∈ bot ∪ U, V x).
intros Vm Vmt Udiscr tyf.
assert (inc : U ⊆ bot ∪ U) by (red; intros;apply union2_intro2; trivial).
rewrite cc_prod_def in tyf|-*; auto.
2:do 2 red; auto.
destruct tyf as ((ff,dom),tyf);
  split; [split;[|rewrite dom]|]; trivial.
intros x tyx.
apply union2_ax in tyx; destruct tyx as [tyx|tyx]; [|auto].
rewrite cc_app_outside_domain; auto.
split; trivial.
Qed.

Definition squ bot f :=
  subset f (fun c => ~ fst c ∈ bot).

#[global]Instance squ_morph : morph2 squ.
do 3 red; intros.
apply subset_morph; trivial.
red; intros.
rewrite H; reflexivity.
Qed.

Lemma squ_ax bot f z :
  z ∈ squ bot f <-> z ∈ f /\ ~ fst z ∈ bot.
unfold squ; rewrite subset_ax.
apply and_iff_morphism; auto with *.
split; intros.
 destruct H.
 rewrite H; trivial.

 exists z; auto with *.
Qed.

Lemma squ_nmt bot f x :
  ~ x ∈ bot ->
  cc_app (squ bot f) x == cc_app f x.
Proof.
intros.
apply eq_set_ax; intros z.
rewrite <- !couple_in_app.
rewrite squ_ax, fst_def.
split; [destruct 1|]; auto.
Qed.

Lemma squ_mt bot f x :
  x ∈ bot ->
  cc_app (squ bot f) x == empty.
Proof.
intros.
apply empty_ext; red; intros.
rewrite <- couple_in_app, squ_ax, fst_def in H0.
destruct H0; contradiction.
Qed.

Lemma squ_cc_fun bot A f :
  is_cc_fun (bot ∪ A) f ->
  is_cc_fun A (squ bot f).
Proof.
destruct 1 as (ff,dom).
split.
*red; intros.
 apply squ_ax in H; destruct H; auto.
*red; intros.
 apply rel_domain_ax in H; destruct H as (y,inf).
 rewrite squ_ax in inf; destruct inf.
 rewrite fst_def in H0.
 assert (tyz : z ∈ bot ∪ A).
 {apply dom; rewrite rel_domain_ax; eauto. }
 rewrite union2_ax in tyz; destruct tyz;[contradiction|trivial].
Qed.


Lemma squ_typ bot A B f :
  ext_fun (bot ∪ A) B ->
  (forall x, x ∈ bot -> ~ x ∈ A) ->
  f ∈ (Π x ∈ bot ∪ A, B x) ->
  squ bot f ∈ (Π x ∈ A, B x).
Proof.
intros Bext nmt tyf.
assert (inc : A ⊆ bot ∪ A) by (intros ?; apply union2_intro2).
rewrite cc_prod_def in tyf|-*; auto.
2:do 2 red; auto.
destruct tyf as (ff,tyf).
split.
*apply squ_cc_fun; trivial.
*intros x tyx.
 rewrite squ_nmt; [auto|intro; eapply nmt; eauto].
Qed.

