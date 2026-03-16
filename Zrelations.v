
Require Import Zpairs Zstable.

(** * Relations *)

Definition isRelation x :=
  forall p, p ∈ x -> isCouple p.

#[global] Instance isRelation_morph : Proper(eq_set==>iff) isRelation.
intros ?? h; apply fa_morph; intros z; rewrite h; reflexivity.
Qed.

Definition rel_domain r :=
  subset (union (union r)) (fun x => exists y, (*y∈union r*) couple x y ∈ r).

#[global]Instance rel_domain_morph : morph1 rel_domain.
do 2 red; intros.
unfold rel_domain in |- *.
apply subset_morph; [rewrite H; reflexivity|].
red; intros.
apply ex_morph; intros z.
rewrite H; reflexivity.
Qed.

Lemma rel_domain_ax r x :
   x ∈ rel_domain r <-> exists y, couple x y ∈ r.
Proof.
unfold rel_domain; rewrite subset_ax.
split.
*intros (_,(x',eqx,(y,inr))).
 rewrite <-eqx in inr; eauto.
*intros (y,inr).
 split.
 +destruct union_elim with x (couple x y) as (z,?,?).
  rewrite union_couple_eq; auto.
  apply union_intro with z; auto.
  apply union_intro with (couple x y); trivial.
 +exists x; [reflexivity|exists y;trivial].
Qed.

Definition rel_image r :=
  subset (union (union r)) (fun y => exists x, (*x∈r*) couple x y ∈ r).

#[global]Instance rel_image_morph : morph1 rel_image.
do 2 red; intros.
unfold rel_image in |- *.
apply subset_morph; [rewrite H; reflexivity|].
red; intros.
apply ex_morph; intros z.
rewrite H; reflexivity.
Qed.

Lemma rel_image_ax r y :
   y ∈ rel_image r <-> exists x, couple x y ∈ r.
Proof.
unfold rel_image; rewrite subset_ax.
split.
*intros (_,(y',eqy,(x,inr))).
 rewrite <-eqy in inr; eauto.
*intros (x,inr).
 split.
 +destruct union_elim with y (couple x y) as (z,?,?).
  rewrite union_couple_eq; auto.
  apply union_intro with z; auto.
  apply union_intro with (couple x y); trivial.
 +exists y; [reflexivity|exists x;trivial].
Qed.

(** Relation typing *)

Definition rel A B := power (prodcart A B).

Lemma rel_mono :
  Proper (incl_set ==> incl_set ==> incl_set) rel.
unfold rel; do 3 red; intros.
apply power_mono.
apply prodcart_mono; trivial.
Qed.

Instance rel_morph : morph2 rel.
Proof.
do 3 red; intros.
unfold rel.
rewrite H; rewrite H0; reflexivity.
Qed.

Lemma rel_isRelation : forall f A B, f ∈ rel A B -> isRelation f.
Proof.
unfold rel in |- *; red in |- *; intros.
specialize power_elim with (1 := H) (2 := H0); apply surj_pair.
Qed.

Lemma app_typ1 : forall r x y A B, r ∈ rel A B -> couple x y ∈ r -> x ∈ A.
Proof.
unfold rel in |- *; intros.
specialize power_elim with (1 := H) (2 := H0); intro.
rewrite <- (fst_def x y).
apply fst_typ with (1 := H1).
Qed.

Lemma app_typ2 : forall r x y A B, r ∈ rel A B -> couple x y ∈ r -> y ∈ B.
Proof.
unfold rel in |- *; intros.
specialize power_elim with (1 := H) (2 := H0); intro.
rewrite <- (snd_def x y).
apply snd_typ with (1 := H1).
Qed.

Lemma rel_domain_incl : forall r A B, r ∈ rel A B -> rel_domain r ⊆ A.
Proof.
unfold rel_domain in |- *; intros.
red in |- *; intros.
elim subset_elim2 with (1 := H0); intros.
destruct H2 as (y, img_z).
rewrite <- H1 in img_z.
apply app_typ1 with (1 := H) (2 := img_z).
Qed.

Lemma rel_image_incl : forall r A B, r ∈ rel A B -> rel_image r ⊆ B.
Proof.
unfold rel_image in |- *; intros.
red in |- *; intros.
elim subset_elim2 with (1 := H0); intros.
destruct H2 as (x0, img_z).
rewrite <- H1 in img_z.
apply app_typ2 with (1 := H) (2 := img_z).
Qed.

Lemma relation_is_rel :
  forall r A B,
  isRelation r ->
  rel_domain r ⊆ A ->
  rel_image r ⊆ B ->
  r ∈ rel A B.
Proof.
unfold rel in |- *; intros.
do 2 red in H.
apply power_intro; intros.
rewrite (H _ H2).
apply couple_intro.
*apply H0.
 apply rel_domain_ax.
 exists (snd z).
 rewrite <- (H _ H2); trivial.
*apply H1.
 apply rel_image_ax.
 exists (fst z).
 rewrite <- (H _ H2); trivial.
Qed.


(* introduces relation R of domain A and codomain B *)
Definition inject_rel R A B :=
  subset (prodcart A B) (fun p => R (fst p) (snd p)).

Lemma inject_rel_is_rel :  forall (R:set->set->Prop) A B,
  inject_rel R A B ∈ rel A B.
Proof.
unfold rel in |- *.
intros.
apply power_intro; intros.
unfold inject_rel in H.
apply subset_elim1 with (1 := H).
Qed.

Lemma inject_rel_intro :
  forall (R:set->set->Prop) A B x y,
  ext_rel A R ->
  x ∈ A ->
  y ∈ B ->
  R x y ->
  couple x y ∈ inject_rel R A B.
Proof.
unfold inject_rel in |- *; intros.
apply subset_intro.
 apply couple_intro; trivial.
 elim (H x (fst (couple x y)) y (snd (couple x y))); intros; auto.
   rewrite fst_def; reflexivity.
   rewrite snd_def; reflexivity.
Qed.

Lemma inject_rel_elim :
  forall (R:set->set->Prop) A B x y,
  ext_rel A R ->
  couple x y ∈ inject_rel R A B ->
  x ∈ A /\ y ∈ B /\ R x y.
Proof.
unfold inject_rel in |- *; intros.
specialize subset_elim1 with (1 := H0); intro.
elim subset_elim2 with (1 := H0); intros.
assert (x ∈ A).
 rewrite <- (fst_def x y).
 apply fst_typ with B; trivial.
split; trivial.
split.
 rewrite <- (snd_def x y).
 apply snd_typ with A; trivial.

elim (H x (fst x0) y (snd x0)); intros; auto.
 rewrite <- H2; symmetry  in |- *; apply fst_def.
 rewrite <- H2; symmetry  in |- *; apply snd_def.
Qed.

(** * Functions *)

Definition isFunction f :=
  isRelation f /\
  forall x y y', couple x y ∈ f -> couple x y' ∈ f -> y == y'.

(*Definition isFun A f :=
  isFunction f /\ rel_domain f == A.*)

#[global]Instance isFunction_morph : Proper(eq_set==>iff) isFunction.
Proof.
do 2 red; intros.
unfold isFunction.
apply and_iff_morphism; [rewrite H;reflexivity|].
apply fa_morph; intros x0.
apply fa_morph; intros y0.
apply fa_morph; intros y'.
rewrite H; reflexivity.
Qed.

Definition lam A F := replf A (fun x => couple x (F x)).

#[local]Lemma fun_elt_is_ext : forall A f,
  ext_fun A f ->
  ext_fun A (fun x => couple x (f x)).
do 2 red; intros.
apply couple_morph; auto.
Qed.
Hint Resolve fun_elt_is_ext : core.

Lemma lam_morph a a' f f':
  a == a' -> eq_fun a f f' -> lam a f == lam a' f'.
intros.
apply replf_morph; trivial.
red; intros.
apply couple_morph; auto.
Qed.

Lemma lam_ax A F z :
  z ∈ lam A F <-> isCouple z /\ fst z ∈ A /\ ext F (fst z) /\ (snd z) == F (fst z).
Proof.
unfold lam.
rewrite replf_ax.
split.
*intros (x,tyx,(e1,eqz)).
 split;[rewrite eqz;trivial|].
 split; [rewrite eqz,fst_def;trivial|].
 assert (ext F (fst z)).
 {rewrite eqz, fst_def.
  red; intros.
  red in e1.
  apply e1 in H.
  apply couple_injection in H; destruct H; trivial. }
 split; [trivial|].
 transitivity (F x).
 +rewrite eqz, snd_def; reflexivity.
 +symmetry; apply H.
  rewrite eqz, fst_def; reflexivity.
*intros (zc & tyx & ? & tyy).
 exists (fst z); [trivial|split].
 +red in H|-*; intros.
  rewrite H with (1:=H0).
  rewrite H0; reflexivity.
 +rewrite <- tyy; trivial.
Qed.

#[global]Opaque lam.

Lemma lam_ax_couple A F x y :
  couple x y ∈ lam A F <-> ext F x /\ x ∈ A /\ y == F x.
Proof.
rewrite lam_ax.
split.
*intros (_ & tyx & Fext & eqy).
 rewrite fst_def in Fext,tyx.
 split; [trivial|].
 split; [trivial|].
 rewrite snd_def in eqy.
 rewrite eqy.
 symmetry; apply Fext; trivial.
 symmetry; apply fst_def.
*intros (Fext & tyx & eqy).
 split;[trivial|].
 split; [rewrite fst_def; trivial|].
 split; [rewrite fst_def; auto with *|].
 rewrite snd_def.
 transitivity (F x);[trivial|].
 apply Fext; trivial.
 symmetry; apply fst_def.
Qed.

Lemma lam_isFunction : forall A f, isFunction (lam A f).
red; intros.
split; intros.
*red; intros.
 rewrite lam_ax in H; apply H.
*rewrite lam_ax_couple in H,H0.
 destruct H as (_ &_&eqy); destruct H0 as (_&_&eqy').
 rewrite eqy,eqy'; reflexivity.
Qed.

Lemma lam_domain A f : ext_fun A f -> rel_domain (lam A f) == A.
Proof.
intros fext.
apply eq_set_ax;intros z.
rewrite rel_domain_ax.
split.
*intros (y,inf).
 rewrite lam_ax_couple in inf; apply inf.
*intros; exists (f z).
 apply lam_ax_couple; auto with *.
Qed.


Definition app f x :=
  union (subset (rel_image f) (fun y => couple x y ∈ f)).


Instance app_morph : morph2 app.
Proof.
do 3 red; intros.
unfold app.
apply union_morph.
apply subset_morph.
 apply rel_image_morph; trivial.

 split; intros.
  rewrite <- H.
  rewrite <- H0; trivial.

  rewrite H.
  rewrite H0; trivial.
Qed.


Lemma app_defined : forall f x y,
  isFunction f -> couple x y ∈ f -> app f x == y.
Proof.
unfold app, isFunction in |- *; intros.
destruct H.
transitivity (union (singl y)).
 apply union_morph.
   apply singl_ext; intros.
  apply subset_intro; trivial.
    apply rel_image_ax; eauto.
  elim subset_elim2 with (1 := H2); intros.
  rewrite <- H3 in H4; eauto.
 apply union_singl_eq.
Qed.

#[global] Opaque app.


Lemma app_elim : forall f x,
  isFunction f -> x ∈ rel_domain f -> couple x (app f x) ∈ f.
Proof.
intros.
apply rel_domain_ax in H0; destruct H0 as (y,inf).
rewrite (app_defined f x y); trivial.
Qed.

Lemma beta_eq f x A :
  ext_fun A f -> x ∈ A -> app (lam A f) x == f x.
Proof.
intros fext tyx.
apply app_defined; [apply lam_isFunction;trivial|].
apply lam_ax_couple; auto with *.
Qed.

Lemma eta_eq A f :
  isFunction f ->
  rel_domain f == A ->
  f == lam A (app f).
intros ff dom.
apply eq_set_ax; intros z.
rewrite lam_ax.
split; intros.
*assert (zc : isCouple z) by (apply ff; trivial).
 red in zc.
 rewrite zc in H.
 split; [trivial|].
 split;[|split].
 +rewrite <- dom; apply rel_domain_ax; eauto.
 +red; intros; apply app_morph; auto with *.
 +rewrite app_defined with (1:=ff)(2:=H); auto with *.
*destruct H as (zc & tyx & _ & eqz).
 red in zc; rewrite zc,eqz.
 rewrite <- dom in tyx.
 apply rel_domain_ax in tyx.
 destruct tyx as (y,inf).
 rewrite app_defined with (1:=ff)(2:=inf); trivial.
Qed.

(** Typing *)

Definition func A B :=
  subset (rel A B) (fun f => isFunction f /\ rel_domain f == A).

Lemma func_bound A B : func A B ⊆ power (power (power (A ∪ B))).
intros f tyf; apply subset_elim1 in tyf.
apply power_intro; intros.
apply power_elim with (1:=tyf) in H.
apply prodcart_bound in H; trivial.
Qed.

Definition func_def A B f :
  f ∈ func A B <-> f ∈ rel A B /\ isFunction f /\  rel_domain f == A.
Proof.
unfold func; rewrite subset_ax.
apply and_iff_morphism;[reflexivity|].
split.
*intros (f',eqf,?); rewrite eqf; trivial.
*intros; exists f; auto with *.
Qed.

#[global]Opaque func.

#[global]Instance func_mono :
  Proper (eq_set ==> incl_set ==> incl_set) func.
intros A A' eqA B B' inclB z inf.
rewrite func_def in inf|-*.
destruct inf as (fr,?).
split; [|rewrite <-eqA;trivial].
revert fr; apply rel_mono; trivial.
rewrite eqA; reflexivity.
Qed.

#[global]Instance func_morph : morph2 func.
do 3 red; intros.
apply incl_eq; apply func_mono; auto with *.
*apply eq_incl; trivial.
*apply eq_incl; auto with *.
Qed.

Lemma func_rel_incl A B : func A B ⊆ rel A B.
Proof.
red; intros.
apply func_def in H; apply H.
Qed.

Lemma func_isFunction f A B : f ∈ func A B -> isFunction f.
Proof.
intros.
apply func_def in H; apply H.
Qed.

Lemma fun_domain_func f A B : f ∈ func A B -> rel_domain f == A.
Proof.
intros.
apply func_def in H; apply H.
Qed.

Lemma lam_is_func A B f :
  ext_fun A f ->
  (forall x, x ∈ A -> f x ∈ B) ->
  lam A f ∈ func A B.
Proof.
intros fext tyf.
apply func_def.
split;[|split].
*apply power_intro; intros.
 rewrite lam_ax in H.
 destruct H as (zc & tyx & _ & eqy).
 red in zc; rewrite zc,eqy.
 apply couple_intro; auto.
*apply lam_isFunction; trivial.
*apply lam_domain; trivial.
Qed.

Lemma app_typ f x A B :
  f ∈ func A B -> x ∈ A -> app f x ∈ B.
Proof.
intros tyf tyx.
rewrite func_def in tyf.
destruct tyf as (fr & ff & dom).
rewrite <- dom in tyx.
apply rel_domain_ax in tyx.
destruct tyx as (y,inf).
rewrite app_defined with (1:=ff)(2:=inf).
apply app_typ2 with (1:=fr)(2:=inf).
Qed.

Lemma func_narrow f A B B' :
  f ∈ func A B ->
  (forall x, x ∈ A -> app f x ∈ B') ->
  f ∈ func A B'.
intros tyf narrow.
rewrite func_def in tyf|-*.
destruct tyf as (fr,(ff,dom)); split;[|auto].
apply power_intro; intros.
rewrite prodcart_ax.
assert (zc := proj1 ff _ H).
red in zc.
rewrite zc in H.
specialize app_typ1 with (1:=fr) (2:=H); intros tyx.
split; [rewrite zc|split];trivial.
rewrite <- app_defined with (1:=ff)(2:=H); auto.
Qed.

Lemma func_eta f A B :
  f ∈ func A B ->
  f == lam A (fun x => app f x).
Proof.
intros.
rewrite func_def in H.
apply eta_eq; apply H.
Qed.

Definition lam_rel (F:set->set) A B := inject_rel (fun x y => F x == y) A B.

#[local]Definition lam_r_ext A f :
  ext_fun A f -> ext_rel A (fun x y => f x == y).
Proof.
intros fext
red; intros.
rewrite <- (fext _ _ H H0), <-H1; reflexivity. 
Qed.
Hint Resolve lam_r_ext : core.

Lemma lam_rel_is_func A B f :
  ext_fun A f ->
  (forall x, x ∈ A -> f x ∈ B) ->
  lam_rel f A B ∈ func A B.
Proof.
intros fext tf.
rewrite func_def.
split;[apply inject_rel_is_rel|].
split;[split|].
*eapply rel_isRelation; apply inject_rel_is_rel.
*intros.
 apply inject_rel_elim in H; [|auto].
 apply inject_rel_elim in H0; [|auto].
 destruct H as (_&_&eqy).
 destruct H0 as (_&_&eqy').
 rewrite <-eqy, <-eqy'; reflexivity.
*apply incl_eq;[eapply rel_domain_incl; apply inject_rel_is_rel|].
 intros x tyx.
 apply rel_domain_ax.
 exists (f x).
 eapply inject_rel_intro; eauto with *.
Qed.

Lemma beta_rel_eq f x A B :
  ext_fun A f ->
  x ∈ A -> (forall x, x ∈ A -> f x ∈ B) -> app (lam_rel f A B) x == f x.
Proof.
intros.
apply app_defined.
*apply func_isFunction with A B.
 apply lam_rel_is_func; auto.
*apply inject_rel_intro; auto with *.
Qed.

Lemma func_is_ext : forall x X F,
  ext_fun x F ->
  ext_fun x (fun x => func X (F x)).
do 2 red; intros.
apply func_morph; auto.
reflexivity.
Qed.
Hint Resolve func_is_ext : core.

Lemma func_stable_set A K :
  stable_set K (func A).
red; red; intros.
destruct inter_wit with (1:=H0).
assert (forall x, x ∈ X -> z ∈ func A x).
 intros.
 apply inter_elim with (1:=H0).
 rewrite replf_def.
  exists x0; auto with *.

  red; red; intros.
  rewrite H4; reflexivity.
clear H0.
assert (z ∈ func A x) by auto.
apply func_narrow with x; trivial.
intros.
apply inter_intro; eauto.
intros.
apply app_typ with A; auto.
Qed.

(** Dependent typing *)

Definition dep_image (A:set) (B:set->set) := replf A B.

Lemma dep_image_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  dep_image x1 f1 == dep_image x2 f2.
Proof.
intros.
unfold dep_image.
apply replf_morph; trivial.
Qed.

Definition dep_func (A:set) (B:set->set) :=
  subset (func A (union (dep_image A B)))
    (fun f => forall x, x ∈ A -> app f x ∈ B x).

Lemma dep_func_bound A B :
  dep_func A B ⊆ power (power (power (A ∪ sup A B))).
Proof.
intros f tyf; apply subset_elim1 in tyf.
apply func_bound in tyf; trivial.
Qed.

Lemma dep_func_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  dep_func x1 f1 == dep_func x2 f2.
Proof.
intros.
unfold dep_func.
apply subset_morph; trivial.
 apply func_morph; trivial.
 apply union_morph.
 apply dep_image_ext; trivial.

 split; intros.
  rewrite <- H in H3.
  rewrite <- (H0 x0 x0); auto; reflexivity.

  rewrite (H0 x0 x0); trivial; try reflexivity.
  rewrite H in H3; auto.
Qed.

Lemma dep_func_mono : forall A A' F F',
  ext_fun A F ->
  ext_fun A' F' ->
  A == A' ->  
  (forall x, x ∈ A -> F x ⊆ F' x) ->
  dep_func A F ⊆ dep_func A' F'.
unfold dep_func; red; intros A A' F F' eF eF' eqA H z H0.
rewrite subset_ax in H0|-*.
destruct H0; split.
 clear H1; revert z H0; apply func_mono; auto with *.
 red; intros.
 unfold dep_image in H0|-*.
 rewrite union_ax in H0|-*.
 destruct H0.
 rewrite replf_def in H1; trivial.
 destruct H1.
 exists (F' x0).
  rewrite H2 in H0. 
  apply H; auto.

  rewrite eqA in H1. 
  rewrite replf_ax; auto.
  exists x0; auto with *.

 destruct H1.
 exists x; trivial.
 intros.
 rewrite <- eqA in H3.
 apply H; auto.
Qed.

Lemma dep_func_intro : forall f dom F,
  ext_fun dom f ->
  ext_fun dom F ->
  (forall x, x ∈ dom -> f x ∈ F x) ->
  lam dom f ∈ dep_func dom F.
Proof.
intros.
assert (forall x, x ∈ dom -> f x ∈ union (dep_image dom F)).
 intros.
 apply union_intro with (F x); auto.
 unfold dep_image.
 apply replf_intro with x; trivial.
 reflexivity.
unfold dep_func.
apply subset_intro.
 apply lam_is_func; trivial.

 intros.
 rewrite beta_eq; auto.
Qed.

Lemma dep_func_eta : forall f dom F,
  f ∈ dep_func dom F ->
  f == lam dom (fun x => app f x).
intros.
apply subset_elim1 in H.
apply func_eta with (1:=H).
Qed.

Lemma dep_func_incl_func : forall A B,
  dep_func A B ⊆ func A (union (dep_image A B)).
Proof.
unfold dep_func in |- *; red in |- *; intros.
apply subset_elim1 with (1 := H).
Qed.

Lemma dep_func_elim :
  forall f x A B, f ∈ dep_func A B -> x ∈ A -> app f x ∈ B x.
Proof.
unfold dep_func in |- *; intros.
elim subset_elim2 with (1 := H); intros.
rewrite H1.
auto.
Qed.
#[global]Opaque dep_func.

(** * Aczel's encoding of functions *)

(** Characterizing functions *)

Definition is_cc_fun A f :=
  isRelation f /\ rel_domain f ⊆ A.

Instance is_cc_fun_morph : Proper (eq_set ==> eq_set ==> iff) is_cc_fun.
Proof.
intros ?? h ?? h'; unfold is_cc_fun.
rewrite h,h'; reflexivity.
Qed.


(** Function constructor *)

Definition cc_lam (x:set) (y:set->set) : set :=
  sup x (fun x' => replf (extf y x') (fun y' => couple x' y')).

Notation "'λ'  x ∈ A , B" :=
  (cc_lam A (fun x => B)) (x ident, at level 200, right associativity).

Instance cc_lam_morph : Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set) cc_lam.
unfold cc_lam; do 3 red; intros.
apply sup_morph; trivial.
red; intros.
apply replf_morph.
*apply extf_morph; trivial.
*red; intros; apply couple_morph; trivial.
Qed.

Lemma cc_lam_ax dom f z :
  (z ∈ cc_lam dom f <->
   exists2 x, x ∈ dom & ext f x /\ exists2 y, y ∈ f x & z == couple x y).
unfold cc_lam; intros.
rewrite sup_ax.
apply ex2_morph; red; intros; auto with *.
rewrite replf_ax; auto with *.
split; intros.
 +destruct H as (e1,(x,ex,(e2,eqz))).
  apply extf_def in ex.
  destruct ex; eauto.
 +destruct H as (ea,(y,?,?)).
  split.
  {red; intros.
   apply replf_morph; [rewrite H1; reflexivity|].
   red;intros.
   apply couple_morph; trivial. }
  exists y;[apply extf_def|split]; auto.
  red; intros; apply couple_morph; auto with *.
Qed.
#[global]Opaque cc_lam.
Lemma cc_lam_def dom f z :
  ext_fun dom f ->
  (z ∈ cc_lam dom f <->
   exists2 x, x ∈ dom & exists2 y, y ∈ f x & z == couple x y).
intros.
rewrite cc_lam_ax.
apply ex2_morph'; red; intros; auto with *.
split; [destruct 1|split]; auto with *.
Qed.

Lemma cc_lam_def_couple dom f x y :
  ext_fun dom f ->
  (couple x y ∈ cc_lam dom f <-> x ∈ dom /\ y ∈ f x).
Proof.
intros.
rewrite cc_lam_def; trivial.
split.
*intros (x',tyx',(y',tyy',e)).
 apply couple_injection in e; destruct e as (eqx,eqy).
 rewrite <-(H _ _ tyx' (symmetry eqx)).
 rewrite eqx, eqy; auto.
*intros (tyx,tyy).
 exists x; trivial.
 exists y; auto with *.
Qed.

Lemma cc_lam_rel A F :
  isRelation (cc_lam A F).
Proof.
red; intros.
rewrite cc_lam_ax in H; trivial.
destruct H as (x,_,(_,(y,_,eqp))).
rewrite eqp; trivial.
Qed.

Lemma is_cc_fun_lam' A A' F :
  A ⊆ A' -> 
  is_cc_fun A' (cc_lam A F).
Proof.
split; [apply cc_lam_rel; trivial|].
red; intros.
rewrite rel_domain_ax in H0.
destruct H0 as (y,inf).
rewrite cc_lam_ax in inf; auto.
destruct inf as (x,tyx,(_,(y',_,eqc))).
apply couple_injection in eqc; destruct eqc as (eqz,_).
rewrite eqz; auto.
Qed.


Lemma is_cc_fun_lam A F :
  is_cc_fun A (cc_lam A F).
Proof.
intros.
apply is_cc_fun_lam'; trivial.
reflexivity.
Qed.

Lemma cc_lam_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  cc_lam x1 f1 == cc_lam x2 f2.
intros.
assert (ext_fun x1 f1).
 apply eq_fun_ext in H0; trivial.
assert (ext_fun x2 f2).
 do 2 red; intros.
 rewrite <-H in H2.
 rewrite <- (H0 x x'); trivial.
 symmetry; apply H0; trivial; try reflexivity.
rewrite eq_set_ax; intros z.
do 2 (rewrite cc_lam_def; trivial).
split; (destruct 1 as (x,?,h); destruct h as (y,?,?); exists x;[|exists y]); trivial.
 rewrite <- H; trivial.
 revert H4; apply eq_elim; apply H0; auto with *.
 rewrite H; auto.
 revert H4; apply eq_elim; symmetry; apply H0; auto with *.
 rewrite H; trivial.
Qed.

Lemma cc_impredicative_lam : forall dom F,
  (forall x, x ∈ dom -> F x == empty) ->
  cc_lam dom F == empty.
Proof.
intros.
apply empty_ext; red in |- *; intros.
rewrite cc_lam_ax in H0; trivial; destruct H0 as (z,?,(_,(y,?,?))).
rewrite H in H1; trivial.
apply empty_ax with y; trivial.
Qed.

(** Application *)

Definition cc_app (x y:set) : set :=
  rel_image (subset x (fun p => fst p == y)).

Instance cc_app_morph : morph2 cc_app.
do 3 red; unfold cc_app in |- *; intros.
apply rel_image_morph.
apply subset_morph; trivial.
red; intros.
rewrite H0.
reflexivity.
Qed.

Lemma couple_in_app : forall x z f,
  couple x z ∈ f <-> z ∈ cc_app f x.
unfold cc_app, rel_image; split; intros.
 apply subset_intro.
 destruct union_elim with z (couple x z) as (y,?,?).
  rewrite union_couple_eq; trivial.

  apply union_intro with y; trivial.
  apply union_intro with (couple x z); trivial.
  apply subset_intro; trivial.
  apply fst_def.

 exists x.
 apply subset_intro; trivial.
 apply fst_def.

 rewrite subset_ax in H; destruct H.
 destruct H0.
 destruct H1.
 rewrite subset_ax in H1; destruct H1.
 destruct H2.
 rewrite <- H0 in H1.
 rewrite <- H2 in H3; rewrite fst_def in H3.
 rewrite H3 in H1; trivial.
Qed.

#[global]Opaque cc_app.


Lemma cc_app_empty : forall x, cc_app empty x == empty.
intro.
apply empty_ext; red; intros.
rewrite <- couple_in_app in H.
apply empty_ax in H; trivial.
Qed.

Lemma cc_app_outside_domain dom f x :
  is_cc_fun dom f ->
  ~ x ∈ dom ->
  cc_app f x == empty.
intros.
apply empty_ext; red; intros.
apply H0.
apply H.
apply rel_domain_ax.
exists x0.
apply couple_in_app; trivial.
Qed.

(** Beta reduction *)

Lemma cc_beta_eq0 : forall dom F x,
  ext F x ->
  x ∈ dom ->
  cc_app (cc_lam dom F) x == F x.
Proof.
intros.
apply eq_intro; intros.
*rewrite <- couple_in_app in H1.
 rewrite cc_lam_ax in H1; trivial.
 destruct H1 as (x',?,(ex,(y,?,?))).
 apply couple_injection in H3; destruct H3.
 rewrite H4; revert H2; apply eq_elim.
 apply ex; symmetry; trivial.
*rewrite <- couple_in_app.
 rewrite cc_lam_ax; eauto with *.
Qed.

Lemma cc_beta_eq : forall dom F x,
  ext_fun dom F ->
  x ∈ dom ->
  cc_app (cc_lam dom F) x == F x.
Proof.
intros.
apply cc_beta_eq0; trivial.
apply ext_ext with (1:=H); trivial.
Qed.

(** Eta reduction *)

Lemma cc_eta_eq' : forall dom f,
  is_cc_fun dom f ->
  f == λ x ∈ dom, cc_app f x.
unfold is_cc_fun.
intros.
assert (am : ext_fun dom (fun x => cc_app f x)).
 do 2 red; intros; apply cc_app_morph; auto with *.
apply eq_intro; intros.
*assert (zc := proj1 H _ H0); red in zc.
 rewrite zc in H0|-*.
 rewrite cc_lam_def_couple;[|trivial].
 split.
 +apply H.
  rewrite rel_domain_ax; eauto.
 +apply couple_in_app in H0; trivial.
*apply cc_lam_def in H0; trivial.
 destruct H0 as (x,tyx,(y,tyy,eqz)); rewrite eqz.
 apply couple_in_app; auto.
Qed.

(** Typing: dependent products *)

Definition cc_prod (x:set) (y:set->set) : set :=
  replf (dep_func x y)
    (fun f => cc_lam x (fun x' => app f x')).

Notation "'Π'  x ∈ A , B" :=
  (cc_prod A (fun x => B)) (x ident, at level 200, right associativity).

Lemma cc_prod_ext :
  forall x1 x2 f1 f2,
  x1 == x2 ->
  eq_fun x1 f1 f2 ->
  cc_prod x1 f1 == cc_prod x2 f2.
Proof.
unfold cc_prod in |- *; intros.
apply replf_morph; intros; trivial.
 apply dep_func_ext; trivial.

 red; intros.
 apply cc_lam_ext; auto.
 red; intros.
 apply app_morph; trivial.
Qed.

Instance cc_prod_morph : Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set) cc_prod.
do 3 red; intros; apply cc_prod_ext; trivial.
red; intros; apply H0; trivial.
Qed.

Lemma cc_prod_fun1 : forall A x,
  ext_fun A (fun f => cc_lam x (fun x' => app f x')).
Proof.
do 2 red; intros.
apply cc_lam_ext; try reflexivity; red; intros.
apply app_morph; trivial.
Qed.
#[local]Hint Resolve cc_prod_fun1 : core.

Lemma cc_prod_is_cc_fun : forall A B f,
  f ∈ cc_prod A B -> is_cc_fun A f.
intros.
unfold cc_prod in H.
rewrite replf_ax in H; auto.
destruct H.
destruct H0.
rewrite H1.
apply is_cc_fun_lam; auto.
Qed.
Hint Resolve cc_prod_is_cc_fun : core.

Lemma cc_prod_elim : forall dom f x F,
  f ∈ cc_prod dom F ->
  x ∈ dom ->
  cc_app f x ∈ F x.
intros.
unfold cc_prod in H.
elim replf_elim with (1 := H); clear H; intros; auto.
rewrite H1; clear H1.
rewrite cc_beta_eq; auto.
 apply dep_func_elim with dom; trivial.

 do 2 red; intros.
 rewrite H2; reflexivity.
Qed.

Lemma cc_app_typ f v A B B' :
  f ∈ cc_prod A B ->
  B' == B v ->
  v ∈ A ->
  cc_app f v ∈ B'.
intros.
rewrite H0; apply cc_prod_elim with (1:=H); trivial.
Qed.

Lemma cc_prod_def_intro A B f :
  ext_fun A B ->
  is_cc_fun A f ->
  (forall x, x ∈ A -> cc_app f x ∈ B x) ->
  f ∈ cc_prod A B.
Proof.
intros Bext ff tyf.
unfold cc_prod.
rewrite replf_def; trivial.
exists (lam A (cc_app f)).
*apply dep_func_intro; trivial.
 intros ??? h; rewrite h; reflexivity.
*rewrite cc_eta_eq' with (1:=ff).
 apply cc_lam_ext; [reflexivity|].
 red; intros.
 rewrite beta_eq.
 +rewrite H0; reflexivity.
 +intros ??? h; rewrite h; reflexivity.
 +rewrite <- H0; trivial.
Qed.

Lemma cc_prod_def A B f :
  ext_fun A B ->
  (f ∈ cc_prod A B <->
   is_cc_fun A f /\ (forall x, x ∈ A -> cc_app f x ∈ B x)).
Proof.
split; intros.
*split.
 +apply cc_prod_is_cc_fun in H0; trivial.
 +intros; apply cc_prod_elim with (1:=H0); trivial.
*destruct H0.
 apply cc_prod_def_intro; trivial.
Qed.
#[global]Opaque cc_prod.

Lemma cc_prod_rel A B :
  ext_fun A B ->
  cc_prod A B ⊆ rel A (union (sup A B)).
Proof.
intros Bext f tyf.
rewrite cc_prod_def in tyf;[destruct tyf as (ff,tyf)|trivial].
apply power_intro; intros.
rewrite prodcart_ax.
assert (zc := proj1 ff _ H).
red in zc; rewrite zc in H.
split; [trivial|].
assert (tyx : fst z ∈ A).
{apply ff.
 rewrite rel_domain_ax; eauto. }
split; [trivial|].
apply couple_in_app in H.
apply union_intro with (cc_app f (fst z)); trivial.
rewrite sup_def; eauto.
Qed.

Lemma cc_prod_bound A B :
  ext_fun A B ->
  cc_prod A B ⊆ power (power (power (A ∪ union (sup A B)))).
Proof.
intros Bext f tyf.
apply power_intro; intros z tyz.
apply cc_prod_rel in tyf; [|trivial].
apply power_elim with (1:=tyf) in tyz.
apply prodcart_bound in tyz; trivial.
Qed.

Definition cc_arr A B := cc_prod A (fun _ => B).

Instance cc_arr_morph : morph2 cc_arr.
do 3 red; intros.
apply cc_prod_morph; trivial.
red; trivial.
Qed.

(*
Lemma cc_prod_intro_imp (dom dom': set) (f F : set -> set) :
  ext_fun dom f ->
  ext_fun dom' F ->
  dom ⊆ dom' ->
  (forall x : set, x ∈ dom -> f x ∈ F x) ->
  (forall x, x ∈ dom' -> x ∈ dom \/ F x ⊆ singl empty) ->
  cc_lam dom f ∈ cc_prod dom' F.
intros.
apply cc_prod_def;[trivial|].
split; intros.
*apply is_cc_fun_lam'; trivial.
*destruct H3 with (1:=H4).
 +rewrite cc_beta_eq; auto.
 +rewrite 

unfold cc_prod.
rewrite replf_ax.
exists (lam dom' (fun x=>cond_f).
apply dep_func_intro.



cut (cc_lam dom f ∈ cc_prod dom F).
 apply cc_prod_covariant; auto with *.
apply cc_prod_intro; intros; auto.
do 2 red; intros.
apply H0; trivial.
rewrite <- H1; trivial.
Qed.
*)


Lemma cc_prod_intro : forall dom f F,
  ext_fun dom f ->
  ext_fun dom F ->
  (forall x, x ∈ dom -> f x ∈ F x) ->
  cc_lam dom f ∈ cc_prod dom F.
Proof.
intros.
rewrite cc_prod_def; trivial.
split; intros.
*apply is_cc_fun_lam'; auto with *.
*rewrite cc_beta_eq; auto.
Qed.

Lemma cc_arr_intro : forall A B F,
  ext_fun A F ->
  (forall x, x ∈ A -> F x ∈ B) ->
  cc_lam A F ∈ cc_arr A B.
unfold cc_arr; intros.
apply cc_prod_intro; auto.
Qed.

Lemma cc_arr_elim : forall f x A B,
  f ∈ cc_arr A B -> 
  x ∈ A ->
  cc_app f x ∈ B.
intros.
apply cc_prod_elim with (1:=H); trivial.
Qed.


(* Eta reduction : *)
Lemma cc_eta_eq: forall dom F f,
  f ∈ cc_prod dom F ->
  f == λ x ∈ dom, cc_app f x.
intros.
apply cc_eta_eq'; eauto.
Qed.

Lemma cc_prod_covariant : forall dom dom' F G,
  ext_fun dom' G ->
  dom == dom' ->
  (forall x, x ∈ dom -> F x ⊆ G x) ->
  cc_prod dom F ⊆ cc_prod dom' G.
red; intros.
setoid_replace (cc_prod dom' G) with (cc_prod dom G).
 specialize cc_eta_eq with (1:=H2); intro.
 rewrite H3.
 apply cc_prod_intro; trivial.
  red; red; intros.
  rewrite H5; auto with *.

  red; red; intros.
  rewrite H0 in H4; apply H; trivial.

  intros.
  apply H1; trivial.
  apply cc_prod_elim with (1:=H2); trivial.

 apply cc_prod_ext; trivial.
 symmetry; trivial.
Qed.

Lemma cc_prod_intro' : forall (dom dom': set) (f F : set -> set),
       ext_fun dom f ->
       ext_fun dom' F ->
       dom == dom' ->
       (forall x : set, x ∈ dom -> f x ∈ F x) ->
       cc_lam dom f ∈ cc_prod dom' F.
intros.
cut (cc_lam dom f ∈ cc_prod dom F).
 apply cc_prod_covariant; auto with *.
apply cc_prod_intro; intros; auto.
do 2 red; intros.
apply H0; trivial.
rewrite <- H1; trivial.
Qed.

Lemma subset_cc_prod A B B' P :
  ext_fun A B ->
  (forall x x', x ∈ A -> x==x' -> B' x == subset (B x') (P x')) ->
  subset (cc_prod A B) (fun f => forall x, x ∈ A -> exists2 y, cc_app f x == y & P x y) ==
    cc_prod A B'.
intros Bm eqB.
assert (B'm : ext_fun A B').
{do 2 red; intros.
 rewrite eqB with (x:=x)(x':=x); auto with *.
 rewrite eqB with (x:=x')(x':=x); auto with *.
 rewrite <- H0; trivial. }
apply eq_set_ax; intros z.
rewrite subset_ax.
split; intros.
+destruct H as (tyz,(z',eqz,?)).
 rewrite cc_eta_eq with (1:=tyz).
 apply cc_prod_intro; trivial. 
  do 2 red; intros; apply cc_app_morph; auto with *.
  intros.
  destruct H with (1:=H0) as (y,eqy,?).  
  rewrite eqB with (x':=x); auto with *.
  rewrite eqz,eqy.
  apply subset_intro; trivial.
  rewrite <-eqy,<-eqz.
  apply cc_prod_elim with (1:=tyz); trivial.
+split.
 {revert H; apply cc_prod_covariant; auto with *.
  intros.  
  rewrite eqB with (x':=x); auto with *.
  intros w; apply subset_elim1. }
 {exists z;[reflexivity|].
  intros.
  specialize cc_prod_elim with (1:=H)(2:=H0).
  rewrite eqB with (x':=x); auto with *.
  intros.
  apply subset_elim2 in H1; trivial.  }
Qed.

Lemma cc_prod_stable_set : forall K dom F,
  (forall y y' x x', y == y' -> x ∈ dom -> x == x' -> F y x == F y' x') ->
  (forall x, x ∈ dom -> stable_set K (fun y => F y x)) ->
  stable_set K (fun y => cc_prod dom (F y)).
intros K dom F Fm Fs.
assert (Hm : morph1 (fun y => cc_prod dom (F y))).
 do 2 red; intros.
 apply cc_prod_ext; auto with *.
 red; intros; apply Fm; auto.
red; red ;intros.
destruct inter_wit with (1:=H0) as (w,winX).
assert (forall x, x ∈ X -> z ∈ cc_prod dom (F x)).
 intros.
 apply inter_elim with (1:=H0).
 rewrite replf_ax; auto.
 exists x; auto with *.
clear H0.
assert (z ∈ cc_prod dom (F w)) by auto.
rewrite (cc_eta_eq _ _ _ H0).
apply cc_prod_intro.
 red; red; intros; apply cc_app_morph; auto with *.

 red; red; intros; apply Fm; auto with *.

 intros.
 apply Fs; trivial.
 apply inter_intro.
  intros.
  rewrite replf_def in H3; auto.
  2:red;red;intros;apply Fm; auto with *.
  destruct H3.
  rewrite H4; apply H1 in H3.
  apply cc_prod_elim with (1:=H3); trivial.

  exists (F w x); rewrite replf_def.
  2:red;red;intros; apply Fm; auto with *.
  eauto with *.
Qed.
