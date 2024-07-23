
Require Export basic.
Require Import Sublogic.
Require Export ZFdef.
Require Import Z.
Export CoqSublogicThms.
#[global]Hint Unfold Tnot : core.

(** We assume the existence of a model of IZF (that is actually
    constructed modulo one axiom (ttrepl): *)
Require ZFskolEm.
Module IZF : IZF_R_sig CoqSublogicThms := ZFskolEm.IZF_R.
Include IZF.
(*Print Assumptions repl_ax.*)

Include ZermeloSetTheory CoqSublogicThms IZF.


(*Parameter replf : set -> (set->set) -> set.*)
Definition replf (a:set) (F:set->set) : set :=
  repl a (fun x y => y == F x).


Instance replf_mono_raw :
  Proper (incl_set ==> (eq_set ==> eq_set) ==> incl_set) replf.
unfold replf.
do 4 red; intros.
assert (xm : morph1 x0).
 do 2 red; intros.
 transitivity (y0 y1); auto.
 symmetry; apply H0; reflexivity.
assert (ym : morph1 y0).
 do 2 red; intros.
 transitivity (x0 x1); auto.
 symmetry; apply H0; reflexivity.
rewrite repl_ax in H1.
 rewrite repl_ax.
  destruct H1.
  exists x1; auto.
  rewrite H2; apply H0; reflexivity.

  intros.
  rewrite <- H4; rewrite H5; auto.

  intros.
  rewrite H3; rewrite H4; reflexivity.

 intros.
 rewrite <- H4; rewrite H5; auto.

 intros.
 rewrite H3; rewrite H4; reflexivity.
Qed.

Instance replf_morph_raw :
  Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set) replf.
do 3 red; intros.
apply eq_intro.
 apply replf_mono_raw; auto.
 rewrite H; reflexivity.

 symmetry in H0.
 apply replf_mono_raw; auto.
 rewrite H; reflexivity.
Qed.

Lemma replf_ax : forall a F z,
  ext_fun a F ->
  (z ∈ replf a F <-> exists2 x, x ∈ a & z == F x).
unfold replf; intros.
rewrite repl_ax; intros.
 split; intros.
  destruct H0.
  exists x; trivial.

  destruct H0.
  exists x; trivial.

 rewrite <- H2; rewrite H3; auto.

 rewrite H2; trivial.
Qed.

Lemma replf_intro : forall a F y x,
  ext_fun a F -> x ∈ a -> y == F x -> y ∈ replf a F.
Proof.
intros a F y x Fext H1 H2.
rewrite replf_ax; trivial.
exists x; trivial.
Qed.

Lemma replf_elim : forall a F y,
  ext_fun a F -> y ∈ replf a F -> exists2 x, x ∈ a & y == F x.
Proof.
intros a F y Fext H1.
rewrite replf_ax in H1; trivial.
Qed.

Lemma replf_ext : forall p a F,
  ext_fun a F ->
  (forall x, x ∈ a -> F x ∈ p) ->
  (forall y, y ∈ p -> exists2 x, x ∈ a & y == F x) ->
  p == replf a F.
intros.
apply eq_intro; intros.
 apply H1 in H2; destruct H2.
 apply replf_intro with x; auto.

 apply replf_elim in H2; trivial; destruct H2.
 rewrite H3; auto.
Qed.

Lemma replf_mono2 : forall x y F,
  ext_fun y F ->
  x ⊆ y ->
  replf x F ⊆ replf y F.
red; intros.
assert (ext_fun x F).
 do 2 red; auto.
apply replf_elim in H1; trivial.
destruct H1.
apply replf_intro with x0; auto.
Qed.

Lemma replf_morph_gen : forall x1 x2 F1 F2, 
  ext_fun x1 F1 ->
  ext_fun x2 F2 ->
  eq_index x1 F1 x2 F2 ->
  replf x1 F1 == replf x2 F2.
Proof.
destruct 3.
apply replf_ext; intros; trivial.
 apply H2 in H3; destruct H3.
 apply replf_intro with x0; trivial.
 symmetry; trivial.

 apply replf_elim in H3; trivial; destruct H3.
 apply H1 in H3; destruct H3.
 rewrite H5 in H4.
 exists x0; auto.
Qed.

Lemma replf_morph : forall x1 x2 F1 F2, 
  x1 == x2 ->
  eq_fun x1 F1 F2 ->
  replf x1 F1 == replf x2 F2.
intros.
apply replf_morph_gen; intros.
 apply eq_fun_ext in H0; trivial.
 
 do 2 red; intros.
 rewrite <- H in H1.
 transitivity (F1 x); auto.
 symmetry; apply H0; trivial; reflexivity.

 apply eq_index_eq; trivial.
Qed.

Lemma replf_empty : forall F, replf empty F == empty.
Proof.
intros.
apply empty_ext.
red; intros.
apply replf_elim in H.
 destruct H.
 elim empty_ax with (1:=H).

 do 2 red; intros.
 elim empty_ax with (1:=H0).
Qed.

Lemma compose_replf : forall A F G,
  ext_fun A F ->
  ext_fun (replf A F) G ->
  replf (replf A F) G == replf A (fun x => G (F x)).
intros.
assert (eGF : ext_fun A (fun x => G (F x))).
 red; red; intros.
 apply H0; auto.
 rewrite replf_ax; trivial.
 exists x; auto with *.
apply eq_intro; intros.
 rewrite replf_ax in H1; trivial.
 destruct H1.
 rewrite replf_ax in H1; trivial.
 destruct H1.
 rewrite replf_ax; trivial.
 exists x0; trivial.
 rewrite H2; apply H0; trivial.
 rewrite replf_ax; trivial.
 exists x0; trivial.

 rewrite replf_ax in H1; trivial.
 destruct H1.
 rewrite replf_ax; trivial.
 exists (F x); trivial.
 rewrite replf_ax; trivial.
 exists x; auto with *.
Qed.

(** Upper bound of a family of sets *)

Definition sup x F := union (replf x F).

Lemma sup_ax : forall x F z,
  ext_fun x F ->
  (z ∈ sup x F <-> exists2 y, y ∈ x & z ∈ F y).
intros.
unfold sup.
rewrite union_ax.
split; destruct 1; intros.
 apply replf_elim in H1; auto; destruct H1.
 rewrite H2 in H0; clear H2.
 exists x1; trivial.

 exists (F x0); trivial.
 apply replf_intro with x0; trivial.
 reflexivity.
Qed.

Lemma sup_ext : forall y a F,
  ext_fun a F ->
  (forall x, x ∈ a -> F x ⊆ y) ->
  (forall z, z ∈ y -> exists2 x, x ∈ a & z ∈ F x) ->
  y == sup a F.
intros.
apply eq_intro; intros.
 rewrite sup_ax; auto.

 rewrite sup_ax in H2; trivial; destruct H2.
 apply H0 in H3; trivial.
Qed.

Lemma sup_morph_gen : forall a F b G,
  ext_fun a F ->
  ext_fun b G ->
  eq_index a F b G ->
  sup a F == sup b G.
unfold sup; intros.
apply union_morph; apply replf_morph_gen; trivial.
Qed.

Lemma sup_morph : forall a F b G,
  a == b ->
  eq_fun a F G ->
  sup a F == sup b G.
intros.
apply sup_morph_gen; intros.
 apply eq_fun_ext in H0; trivial.

 do 2 red; intros.
 rewrite <- H in H1.
 transitivity (F x); auto.
 symmetry; apply H0; trivial; reflexivity.

 apply eq_index_eq; trivial.
Qed.

Lemma sup_incl : forall a F x,
  ext_fun a F -> x ∈ a -> F x ⊆ sup a F.
intros.
red; intros.
rewrite sup_ax; trivial.
exists x; trivial.
Qed.
Hint Resolve sup_incl : core.

Lemma sup_lub x f A :
  ext_fun x f ->
  (forall y, y ∈ x -> f y ⊆ A) ->
  sup x f ⊆ A.
red; intros.
apply sup_ax in H1; trivial.
destruct H1 as (y,?,?).
apply H0 with (y:=y); trivial.
Qed.


Lemma replf_is_sup A F :
  ext_fun A F ->
  replf A F == sup A (fun x => singl (F x)).
intros.
assert (fm : ext_fun A (fun x => singl (F x))).
 do 2 red; intros; apply singl_morph; apply H; trivial.
apply eq_intro; intros.
 rewrite sup_ax; trivial.
 rewrite replf_ax in H0; trivial.
 revert H0; apply ex2_morph; red; intros; auto with *.
 split; intros.
  apply singl_elim in H0; trivial.
  rewrite H0; apply singl_intro.

 rewrite replf_ax; trivial.
 rewrite sup_ax in H0; trivial.
 revert H0; apply ex2_morph; red; intros; auto with *.
 split; intros.
  rewrite H0; apply singl_intro.
  apply singl_elim in H0; trivial.
Qed.

Lemma union_is_sup a :
  union a == sup a (fun x => x).
apply eq_intro; intros.
 rewrite sup_ax;[|do 2 red; auto].
 apply union_elim in H; destruct H.
 eauto.

 rewrite sup_ax in H;[|do 2 red; auto].
 destruct H; eauto using union_intro.
Qed.

Lemma inter_wit : forall X F, morph1 F -> 
 forall x, x ∈ inter (replf X F) ->
 exists y, y ∈ X.
intros.
destruct inter_non_empty with (1:=H0).
rewrite replf_ax in H1.
2:red;red;intros; apply H; trivial.
destruct H1; eauto.
Qed.
