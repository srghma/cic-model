
Require Export ZF.
Require Import Zstable.

(** Only using bounded quantifications.
    replf allowed since it is derivable in Zermelo.
    WFR not allowed.
*)
(** ordered pairs *)

(** 1- untyped operations *)

Definition couple x y := pair (singl x) (pair x y).

Instance couple_morph : morph2 couple.
unfold couple; do 3 red; intros.
rewrite H; rewrite H0; reflexivity.
Qed.

Lemma couple_bound a b : couple a b ⊆ (power (power (a ∪ b))).
red; intros.
apply power_intro; intros.
apply power_intro; intros.
apply union2_ax.
apply pair_elim in H; destruct H as [H|H]; rewrite H in H0;
  apply pair_elim in H0; destruct H0 as [H0|H0]; rewrite H0 in H1; auto.
Qed.

Lemma union_couple_eq : forall a b, union (couple a b) == pair a b. 
Proof.
intros; unfold couple in |- *; symmetry  in |- *.
apply union_ext; intros.
 elim pair_elim with (1 := H0); intro y_eq;  rewrite y_eq in H.
   rewrite (singl_elim _ _ H); auto.
  trivial.
 elim pair_elim with (1 := H); intro.
  exists (singl a); auto.
    apply singl_intro_eq; auto.
  exists (pair a b); auto.
Qed.

Lemma discr_mt_couple a b : ~ empty == couple a b.
apply discr_mt_pair.  
Qed.

Definition fst p := union (subset (union p) (fun x => singl x ∈ p)).

Instance fst_morph : morph1 fst.
unfold fst; do 2 red; intros.
apply union_morph.
apply subset_morph; intros.
 apply union_morph; trivial.
 split; intro.
   rewrite <- H; trivial.
   rewrite H; trivial.
Qed.

Lemma fst_def : forall x y, fst (couple x y) == x.
Proof.
unfold fst, couple in |- *; intros.
transitivity (union (singl x)).
 apply union_morph.
   apply singl_ext; intros.
  apply subset_intro.
   apply union_intro with (singl x).
    apply singl_intro.
    auto.
   auto.
  elim subset_elim2 with (1 := H); intros.
    rewrite <- H0 in H1.
    clear H0 x0.
    elim pair_elim with (1 := H1); intros.
   apply singl_inj; trivial.
   assert (x ∈ singl z).
    rewrite H0; auto.
     rewrite (singl_elim _ _ H2); reflexivity.
 apply union_singl_eq.
Qed.

Lemma fst_mt : fst empty == empty.
unfold fst.
apply empty_ext; red; intros.
apply union_elim in H; destruct H.
apply subset_elim1 in H0.
apply union_elim in H0; destruct H0.
apply empty_ax in H1; trivial.
Qed.  

Definition snd p :=
  union (subset (union p) (fun z => pair (fst p) z == union p)).

Instance snd_morph : morph1 snd.
Proof.
unfold snd; do 2 red; intros.
apply union_morph.
apply subset_morph; intros.
 apply union_morph; trivial.

 red; intros.
 rewrite H; reflexivity.
Qed.

Lemma snd_def : forall x y, snd (couple x y) == y.
Proof.
intros; unfold snd in |- *.
transitivity (union (singl y)).
 apply union_morph.
   apply singl_ext; intros.
  apply subset_intro.
    rewrite union_couple_eq.
     auto.
    rewrite fst_def.
     symmetry  in |- *.
     apply union_couple_eq.
  elim subset_elim2 with (1 := H); intros.
  rewrite H0.   
  rewrite fst_def in H1.
  rewrite union_couple_eq in H1.
  apply pair_inv in H1; destruct H1.
   destruct H1; auto.

   destruct H1.
   rewrite H2; trivial.
 apply union_singl_eq.
Qed.

Lemma couple_mt_discr a b :
  ~ couple a b == empty.
intro.
apply empty_ax with (x:=singl a).
rewrite <- H; apply pair_intro1.
Qed.

#[global]Opaque couple fst snd.

Lemma couple_injection : forall x y x' y',
  couple x y == couple x' y' -> x == x' /\ y == y'.
intros.
split.
 rewrite <- (fst_def x y);rewrite H; rewrite fst_def; reflexivity.
 rewrite <- (snd_def x y);rewrite H; rewrite snd_def; reflexivity.
Qed.

Definition isCouple c := c == couple (fst c) (snd c).

Global Instance isCouple_morph : Proper (eq_set==>iff) isCouple.
do 2 red; intros; unfold isCouple.
rewrite H; reflexivity.
Qed.

Lemma isCouple_couple a b : isCouple (couple a b).
red.
rewrite fst_def, snd_def; reflexivity.
Qed.
Hint Resolve isCouple_couple : core.

(** 2- typing *)

Definition prodcart A B :=
  subset (power (power (A ∪ B)))
    (fun x => exists2 a, a ∈ A & exists2 b, b ∈ B & x == couple a b).

Lemma prodcart_bound A B : prodcart A B ⊆ power (power (A ∪ B)).
intro; apply subset_elim1.
Qed.

Lemma prodcart_ax A B z :
  z ∈ prodcart A B <-> isCouple z /\ fst z ∈ A /\ snd z ∈ B.
Proof.
unfold prodcart.
rewrite subset_ax.
split.
*intros (tyz, (z', eqz, (a, tya, (b, tyb, eqz')))).
 rewrite eqz, eqz', fst_def, snd_def; auto.
*intros (zc & tya & tyb).
 split.
 +apply power_intro; intros.
  apply power_intro; intros.
  red in zc; rewrite zc in H.
  assert (tyz1: z1 ∈ union(couple (fst z)(snd z))).
  {apply union_intro with z0; trivial. }
  rewrite union_couple_eq in tyz1.
  apply pair_elim in tyz1.
  destruct tyz1 as [tyz1|tyz1]; rewrite tyz1.
  apply union2_intro1; trivial.
  apply union2_intro2; trivial.
 +exists z;[reflexivity|].
  exists (fst z);[trivial|].
  exists (snd z);trivial.
Qed.

#[global]Opaque prodcart.


Instance prodcart_mono :
  Proper (incl_set ==> incl_set ==> incl_set) prodcart.
Proof.
intros A A' H B B' H0 z H1.
rewrite prodcart_ax in H1|-*.
destruct H1 as (?&?&?); auto.
Qed.

Instance prodcart_morph : morph2 prodcart.
Proof.
intros A A' H B B' H0.
apply eq_set_ax; intros z.
rewrite !prodcart_ax.
rewrite H,H0; reflexivity.
Qed.

Lemma couple_intro x y A B :
  x ∈ A -> y ∈ B -> couple x y ∈ prodcart A B.
Proof.
intros.
apply prodcart_ax; rewrite fst_def,snd_def; auto.
Qed.

Lemma surj_pair p A B :
  p ∈ prodcart A B -> p == couple (fst p) (snd p).
Proof.
intros.
rewrite prodcart_ax in H; apply H.
Qed.

Lemma fst_typ p A B : p ∈ prodcart A B -> fst p ∈ A.
Proof.
intros typ.
rewrite prodcart_ax in typ; destruct typ as (_&?&_); trivial.
Qed.

Lemma snd_typ p A B : p ∈ prodcart A B -> snd p ∈ B.
Proof.
intros typ.
rewrite prodcart_ax in typ; destruct typ as (_&_&?); trivial.
Qed.

Lemma subset_prodcart A B P Q :
  prodcart (subset A P) (subset B Q) ==
    subset (prodcart A B)
      (fun p => (exists2 x', fst p == x' & (exists2 y', snd p == y' & P x' /\ Q y'))).
apply eq_set_ax; intros z.
rewrite subset_ax.
split; intros.
+split.
 {revert z H; apply prodcart_mono.
   intro; apply subset_elim1. 
   intro; apply subset_elim1. }
 {exists z; [reflexivity|].
  specialize fst_typ with (1:=H) as tyx.
  specialize snd_typ with (1:=H) as tyy.
  destruct subset_elim2 with (1:=tyx) as (x',?,?).
  destruct subset_elim2 with (1:=tyy) as (y',?,?).
  eauto. }
+destruct H as (tyz,(z',eqz,(x',eqx,(y',eqy,(?,?))))).
 rewrite <- eqz in eqx,eqy.
 rewrite surj_pair with (1:=tyz).
 apply couple_intro.
 rewrite eqx; apply subset_intro; trivial.
 apply fst_typ in tyz.
 rewrite <- eqx; trivial.
 rewrite eqy; apply subset_intro; trivial.
 apply snd_typ in tyz.
 rewrite <- eqy; trivial.
Qed.

(* dependent pairs *)

Definition sigma A B :=
  subset (prodcart A (sup A B)) (fun p => ext B (fst p) /\ snd p ∈ B (fst p)).

Notation "'Σ'  x ∈ A , B" :=
   (sigma A (fun x => B)) (x ident, at level 200, right associativity).

Instance sigma_morph : Proper (eq_set ==> (eq_set ==> eq_set) ==> eq_set) sigma.
unfold sigma; do 3 red; intros.
apply subset_morph.
 apply prodcart_morph; trivial.
 apply sup_morph; trivial.
 red; intros; auto.

 red; intros.
 apply and_iff_morphism; [rewrite H0;reflexivity|].
 apply in_set_morph; auto with *.
Qed.

Lemma sigma_ax A B z :
  z ∈ sigma A B <-> isCouple z /\ fst z ∈ A /\ ext B (fst z) /\ snd z ∈ B (fst z).
Proof.
unfold sigma.
rewrite subset_ax.
rewrite prodcart_ax.
split.
*intros ((zc & tyx & _), (z',eqz,(ef,tyy))).
 rewrite <- eqz in ef.
 do 3 (split;[trivial|]).
 revert tyy; apply in_set_morph; [rewrite eqz;reflexivity|].
 apply ef; rewrite eqz; reflexivity.
*intros (zc & tyx & ef & tyy).
 split; [split;[|split]|exists z;[reflexivity|split]]; trivial.
 rewrite sup_ax;exists (fst z);[|split];trivial.
Qed.
#[global]Opaque sigma.

Lemma sigma_def A B z :
  ext_fun A B ->
  (z ∈ sigma A B <-> isCouple z /\ fst z ∈ A /\ snd z ∈ B (fst z)).
Proof.
intros.
rewrite sigma_ax.
apply and_iff_morphism; [reflexivity|].
apply and_iff_morphisml; [reflexivity|].
split; [destruct 1|split]; auto with *.
Qed.

Lemma sigma_ax_couple A B x y :
  ext_fun A B ->
  (couple x y ∈ sigma A B <-> x ∈ A /\ y ∈ B x).
Proof.
intros.
rewrite sigma_def;[|trivial].
split.
*intros (_ & tyx & tyy).
 rewrite fst_def in tyx.
 rewrite snd_def in tyy.
 rewrite <- (H _) with (1:=tyx) (2:=symmetry (fst_def _ _)) in tyy.
 auto.
*intros (tyx,tyy).
 split;[trivial|split].
 +rewrite fst_def; trivial.
 +rewrite snd_def.
  rewrite <- (H _) with (1:=tyx) (2:=symmetry (fst_def _ _)); trivial.
Qed.

Lemma sigma_ext A A' B B' :
  A == A' ->
  (forall x x', x ∈ A -> x == x' -> B x == B' x') ->
  sigma A B == sigma A' B'.
Proof.
intros eqA eqB.
apply eq_set_ax; intros z.
rewrite !sigma_def.
*apply and_iff_morphism;[reflexivity|].
 apply and_iff_morphisml;[rewrite eqA;reflexivity|intros tyx _].
 apply in_set_morph; [reflexivity|].
 auto with *.
*apply eq_fun_ext with (G:=B).
 red; intros; symmetry; apply eqB.
 rewrite <-H0,eqA; trivial.
 symmetry; trivial.
*apply eq_fun_ext with B'; trivial.
Qed.

Lemma sigma_nodep A B :
  prodcart A B == Σ __∈A, B.
Proof.
apply eq_set_ax; intros z.
rewrite prodcart_ax, sigma_def;[|auto with *].
reflexivity.
Qed.

Lemma couple_intro_sigma x y A B :
  ext_fun A B ->
  x ∈ A -> y ∈ B x -> couple x y ∈ sigma A B.
Proof.
intros; apply sigma_ax_couple; auto.
Qed.

Lemma fst_typ_sigma p A B : p ∈ sigma A B -> fst p ∈ A.
Proof.
rewrite sigma_ax; intros h;apply h.
Qed.

Lemma snd_typ_sigma p y A B :
  p ∈ sigma A B -> y == fst p -> snd p ∈ B y.
intros typ eqy.
rewrite sigma_ax in typ.
destruct typ as (? & tyx & ef & tyy).
symmetry in eqy.
rewrite <- (ef _ eqy); trivial.
Qed.

Lemma sigma_mono A A' B B' :
  ext_fun A' B' ->
  A ⊆ A' ->
  (forall x, x ∈ A -> B x ⊆ B' x) ->
  sigma A B ⊆ sigma A' B'.
Proof.
intros Be incA incB z; rewrite !sigma_ax.
intros (zc & ty1 & eB & ty2).
repeat split; auto.
apply (incB (fst z)); auto with *.
Qed.

Lemma currify_sigma A B P :
  ext_fun A B -> 
  (forall x x', x ∈ sigma A B -> x==x' -> P x -> P x') ->
  (forall i, i ∈ sigma A B -> P i) <->
  (forall x, x ∈ A -> forall y, y ∈ B x -> P (couple x y)).
split; intros.
+apply H1.
 apply couple_intro_sigma; trivial.
+assert (h:=H2); apply sigma_ax in h; destruct h as (?&?&?&?); trivial.
 apply H0 with (2:=symmetry H3); auto.
 red in H3; rewrite <- H3; trivial.
Qed.

Lemma subset_sigma A B P :
  ext_fun A B ->
  subset (sigma A B) P ==
    sigma A (fun x => subset (B x) (fun y => exists2 p, couple x y == p & P p)).
intros Bm.
assert (B'm : ext_fun A (fun x => subset (B x) (fun y => exists2 p, couple x y == p & P p))).
{do 2 red; intros.
 apply subset_morph; auto with *. 
 red; intros.
 split; intros (p,?,?); exists p; trivial.
  rewrite <- H0; trivial.
  rewrite H0; trivial. }
apply eq_set_ax; intros z.
rewrite subset_ax.
split; intros.
+destruct H as (tyz,(z',eqz,?)).
 apply sigma_ax in tyz; trivial.
 destruct tyz as (eqc&tyx&_&tyy).
 red in eqc; rewrite eqc.
 apply couple_intro_sigma; trivial. 
 apply subset_intro; trivial.
 exists z'; trivial.
 rewrite <- eqc; trivial.
+apply sigma_ax in H.
 destruct H as (eqz & tyx & ? & tyy).
 rewrite subset_ax in tyy. 
 destruct tyy as (tyy,(y',eqy,(z',eqc,?))).
 red in eqz; rewrite <- eqy, <-eqz in eqc.
 split;[|eauto].
 rewrite eqz; apply couple_intro_sigma; trivial.
Qed.

Definition sigma_case b c :=
  cond_set (isCouple c) (b (fst c) (snd c)).

Instance sigma_case_morph :
  Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) sigma_case.
do 3 red; intros.
apply cond_set_morph.
 rewrite H0; reflexivity.

 apply H; rewrite H0; reflexivity.
Qed.

Lemma sigma_case_couple f a b c :
  morph2 f ->
  c == couple a b ->
  sigma_case f c == f a b.
intros.
unfold sigma_case.
rewrite cond_set_ok.
 rewrite H0; rewrite fst_def, snd_def; reflexivity.

 red; rewrite H0; rewrite fst_def, snd_def; reflexivity.
Qed.
(*
Lemma sigma_case_mt f c :
  c == empty -> 
  sigma_case f c == empty.
intros.
unfold sigma_case.
apply empty_ext; red; intros.
rewrite cond_set_ax in H0.
destruct H0.
rewrite H1 in H.
assert (singl (fst c) ∈ couple (fst c) (snd c)).
 apply pair_intro1.
rewrite H in H2.
apply empty_ax in H2; trivial.
*)
(*Lemma fst_mt : fst empty == empty.
apply empty_ext; red; intros.
unfold fst in H.
apply union_elim in H; destruct H.
apply subset_elim1 in H0.
apply union_elim in H0; destruct H0.
apply empty_ax in H1; trivial.
Qed.
Lemma snd_mt : snd empty == empty.
apply empty_ext; red; intros.
unfold snd in H.
apply union_elim in H; destruct H.
apply subset_elim1 in H0.
apply union_elim in H0; destruct H0.
apply empty_ax in H1; trivial.
Qed.
*)

Lemma prodcart_stable_set : forall K F G,
  morph1 F ->
  morph1 G ->
  stable_set K F ->
  stable_set K G ->
  stable_set K (fun y => prodcart (F y) (G y)).
intros K F G Fm Gm Fs Gs.
red; red; intros X Xcls z zint.
destruct inter_wit with (1:=zint) as (w,winX).
assert (zall : forall x, x ∈ X -> z ∈ prodcart (F x) (G x)).
{intros.
 apply inter_elim with (1:=zint).
 rewrite replf_ax.
  exists x; [|split]; auto with *.
  red; intros.
  rewrite H0; reflexivity. }
clear zint.
assert (z ∈ prodcart (F w) (G w)) by auto.
rewrite (surj_pair _ _ _ H).
apply couple_intro.
 apply Fs; trivial.
 apply inter_intro.
  intros.
  rewrite replf_ax in H0; trivial.
  destruct H0 as (x,tyx,(_,eqy)).
  rewrite eqy; apply zall in tyx; apply fst_typ in tyx; trivial.

  exists (F w); rewrite replf_ax; auto.
  eauto with *.

 apply Gs; trivial.
 apply inter_intro.
  intros.
  rewrite replf_ax in H0.
  destruct H0 as (x,tyx,(_,eqy)).
  rewrite eqy; apply zall in tyx; apply snd_typ in tyx; trivial.

  exists (G w); rewrite replf_ax; auto.
  eauto with *.
Qed.

Lemma sigma2_stable_set K A F :
  (forall y y' x x', y == y' -> x ∈ A -> x == x' -> F y x == F y' x') ->
  (forall x, x ∈ A -> stable_set K (fun y => F y x)) ->
  stable_set K (fun y => sigma A (F y)).
intros Fm Fs.
assert (Hm : morph1 (fun y => sigma A (F y))).
{do 2 red; intros.
 apply sigma_ext; auto with *. }
red; red ;intros.
destruct inter_wit with (1:=H0) as (w,winX).
assert (forall x, x ∈ X -> z ∈ sigma A (F x)).
 intros.
 apply inter_elim with (1:=H0).
 rewrite replf_ax; auto.
 exists x; auto with *.
clear H0.
assert (z ∈ sigma A (F w)) by auto.
rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H0)).
apply couple_intro_sigma.
 red;red;intros;apply Fm; auto with *.

 apply fst_typ_sigma in H0; trivial.

 apply Fs; trivial.
  apply fst_typ_sigma in H0; trivial.
 apply inter_intro.
  intros.
  rewrite replf_def in H2.
   destruct H2.
   rewrite H3; apply H1 in H2; apply snd_typ_sigma with (y:=fst z) in H2;
   auto with *.
   red; red; intros; apply Fm; auto with *.
   apply fst_typ_sigma in H0; trivial.

  exists (F w (fst z)); rewrite replf_def.
   eauto with *.

   red;red;intros; apply Fm; auto with *.
   apply fst_typ_sigma in H0; trivial.
Qed.

Lemma sigma_stable_set K F G :
  morph1 F ->
  morph2 G ->
  stable_set K F ->
  (forall x, x ∈ sup K F -> stable_set K (fun y => G y x)) ->
  stable_set K (fun y => sigma (F y) (G y)).
intros Fm Gm Fs Gs.
red; red; intros.
assert (Hm : morph1 (fun y => sigma (F y) (G y))).
{do 2 red; intros.
 apply sigma_ext; intros; auto.
 apply Gm; trivial. }
destruct inter_wit with (1:=H0) as (w,winX).
assert (forall x, x ∈ X -> z ∈ sigma (F x) (G x)).
 intros.
 apply inter_elim with (1:=H0).
 rewrite replf_def; auto.
 exists x; auto with *.
clear H0.
assert (z ∈ sigma (F w) (G w)) by auto.
rewrite (surj_pair _ _ _ (subset_elim1 _ _ _ H0)).
apply couple_intro_sigma.
 do 2 red;intros;apply Gm; auto with *.

 apply Fs; trivial.
 apply inter_intro.
  intros.
  rewrite replf_def in H2; auto.
  destruct H2.
  rewrite H3; apply H1 in H2; apply fst_typ_sigma in H2; trivial.

  exists (F w); rewrite replf_ax; auto.
  eauto with *.

  apply Gs; trivial.
  {rewrite sup_ax; auto.
   exists w; [auto|].
   apply fst_typ_sigma in H0; auto. }
  apply inter_intro.
  intros.
  rewrite replf_def in H2.
   destruct H2.
   rewrite H3; apply H1 in H2; apply snd_typ_sigma with (y:=fst z) in H2;
   auto with *.
   red; red; intros; apply Gm; auto with *.

  exists (G w (fst z)); rewrite replf_def.
  2:red;red;intros; apply Gm; auto with *.
  eauto with *.
Qed.
