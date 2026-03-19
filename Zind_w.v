Require Import ZF Zpairs Zrelations Zstable.
Require Import ZFgrothendieck.
Require Import Zw.
Require Import Ziso.

(** In this file we develop the theory of W-types:
    - typing
    - existence of a fixpoint
    - recursor
 *)

Section W_theory.

(** * Definition and properties of the W-type operator *)

Variable A : set.
Variable B : set -> set.
Hypothesis Bm : morph1 B.

(* The intended type operator *)
Definition W_F X := Σ x ∈ A, cc_arr (B x) X.

Lemma wfm1 : forall X, ext_fun A (fun x => cc_arr (B x) X).
do 2 red; intros.
apply cc_arr_morph; auto with *.
Qed.
Hint Resolve wfm1 : core.

Lemma W_F_intro X a f :
  ext_fun (B a) f ->
  a ∈ A ->
  (forall i, i ∈ B a -> f i ∈ X) ->
  couple a (cc_lam (B a) f) ∈ W_F X.
intros.
apply couple_intro_sigma; auto with *.
apply cc_arr_intro; intros; auto with *.
Qed.

Lemma W_F_elim X x :
  x ∈ W_F X ->
  fst x ∈ A /\
  (forall i, i ∈ B (fst x) -> cc_app (snd x) i ∈ X) /\
  x ==couple (fst x) (cc_lam (B (fst x)) (cc_app (snd x))). 
intros.
assert (ty1 := fst_typ_sigma _ _ _ H).
assert (eq1 := surj_pair _ _ _ (subset_elim1 _ _ _ H)).
apply snd_typ_sigma with (y:=fst x) in H; auto with *.
split; trivial.
split; intros.
 apply cc_arr_elim with (1:=H); trivial.

 rewrite cc_eta_eq with (1:=H) in eq1; trivial.
Qed.

Instance W_F_mono : Proper (incl_set ==> incl_set) W_F.
do 3 red; intros.
apply W_F_elim in H0; destruct H0 as (?,(?,?)).
rewrite H2.
apply W_F_intro; auto.
do 2 red; intros; apply cc_app_morph; auto with *.
Qed.

Instance W_F_morph : morph1 W_F.
apply Fmono_morph; auto with *.
Qed.

Lemma W_F_stable X : stable_set X W_F.
unfold W_F.
apply sigma2_stable_set; auto with *.
 intros; apply cc_prod_ext; auto with *.
 red; trivial.

 intros.
 apply cc_prod_stable_set; intros; auto.
 apply id_stable_set.
Qed.

Lemma WFi_ext a a' f f' :
  a ∈ A ->
  a == a' ->
  (a == a' -> eq_fun (B a) f f') ->
  couple a (cc_lam (B a) f) == couple a' (cc_lam (B a') f').
intros.
apply couple_morph; trivial.
apply cc_lam_ext; auto.
Qed.

Lemma WFi_inv a a' Y Y' f f' :
  couple a (cc_lam Y f) == couple a' (cc_lam Y' f') ->
  ext_fun Y f ->
  ext_fun Y' f' ->
  (a == a' -> Y == Y') ->
  a == a' /\ eq_fun Y f f'.
intros.
apply couple_injection in H; destruct H; split; trivial.
red; intros.
assert (eqr := cc_app_morph _ _ H3 _ _ H5).
rewrite cc_beta_eq in eqr; trivial.
rewrite cc_beta_eq in eqr; trivial.
rewrite <- H2; trivial; rewrite <- H5; trivial.
Qed.

  (** Applying [f] to the recursive subterms of [x] *)
  Definition WFmap f x :=
    couple (fst x) (λ i ∈ B (fst x), f (cc_app (snd x) i)).

  Lemma WFmap_ext : forall f f' x x',
    fst x ∈ A ->
    fst x == fst x' ->
    (forall i i', i ∈ B (fst x) -> i == i' ->
     f (cc_app (snd x) i) == f' (cc_app (snd x') i')) ->
    WFmap f x == WFmap f' x'.
intros.
apply WFi_ext; auto.
Qed.

  Instance WFmap_morph : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) WFmap.
do 3 red; intros.
apply couple_morph.
 apply fst_morph; trivial.

 apply cc_lam_ext; intros.
  rewrite H0; reflexivity.

  red; intros.
  apply H.
  rewrite H0; rewrite H2; reflexivity.
Qed.

Lemma WFmap_comp : forall f g X Y x,
  morph1 g ->
  morph1 f ->
  (forall x, x ∈ X -> g x ∈ Y) ->
  x ∈ W_F X ->
  WFmap f (WFmap g x) == WFmap (fun x => f (g x)) x.
intros.
unfold WFmap.
apply W_F_elim in H2; destruct H2 as (?,(?,_)).
symmetry; apply WFi_ext; intros; auto.
 rewrite fst_def; reflexivity.

 red; intros.
 apply H0; auto.
 rewrite snd_def.
 rewrite <- H6.
 rewrite cc_beta_eq; auto with *.
 do 2 red; intros; apply H; auto.
 rewrite H8; reflexivity.
Qed.

Lemma WF_eta : forall X x,
  x ∈ W_F X ->
  x == WFmap (fun x => x) x.
intros.
apply W_F_elim in H; destruct H as (_,(_,?)); assumption.
Qed.

  Lemma WFmap_inj : forall X Y g g' x x',
    x ∈ W_F X -> x' ∈ W_F Y ->
    ext_fun X g -> ext_fun Y g' ->
    (forall a a', a ∈ X -> a' ∈ Y -> g a == g' a' -> a == a') ->
    WFmap g x == WFmap g' x' -> x == x'.
unfold WFmap; intros.
apply W_F_elim in H; destruct H as (?,(?,?)).
apply W_F_elim in H0; destruct H0 as (?,(?,?)).
apply WFi_inv in H4; auto.
 destruct H4.
 red in H9.
 rewrite H6; rewrite H8; apply WFi_ext; intros; auto.
 red; intros.
 apply H3; auto.
 apply H7.
 rewrite <- H12; revert H11; apply eq_elim; apply Bm; trivial.

 do 2 red; intros; apply H1; auto.
 rewrite H10; reflexivity.

 do 2 red; intros; apply H2; auto.
 rewrite H10; reflexivity.
Qed.

  Lemma WFmap_typ : forall X Y f x,
    ext_fun X f ->
    x ∈ W_F X ->
    (forall a, a ∈ X -> f a ∈ Y) ->
    WFmap f x ∈ W_F Y.
intros.
apply W_F_elim in H0; destruct H0 as (?,(?,_)).
apply W_F_intro; auto.
do 2 red; intros.
apply H; auto.
rewrite H4; reflexivity.
Qed.

(** If [f] is as iso between [X] and [Y},
    then [WFmap f] is an iso between [W_F X] and [W_F Y] *)
Lemma WFmap_iso X Y f :
  iso_fun X Y f ->
  iso_fun (W_F X) (W_F Y) (WFmap f).
intros isof.
assert (fm := iso_funm isof).
assert (fext : ext_fun X f).
 apply morph_is_ext; trivial.
constructor; intros.
 apply WFmap_morph; trivial.

 red; intros.
 eapply WFmap_typ with (2:=H); intros; trivial.
 apply (iso_typ isof); trivial.

 apply WFmap_inj with (1:=H)(2:=H0) in H1; intros; trivial.
 apply (iso_inj isof) in H4; trivial.

 exists (WFmap (iso_inv X f) y).
  apply WFmap_typ with (2:=H); intros; trivial.
   apply morph_is_ext; apply (iso_funm (iso_fun_sym isof)).

   apply iso_inv_typ with (1:=isof); trivial.

  rewrite WFmap_comp with (1:=iso_funm (iso_fun_sym isof)) (2:=fm) (4:=H); intros; trivial.
   transitivity (WFmap (fun x => x) y).
   2:symmetry; apply WF_eta with (1:=H); trivial.
   apply WFmap_ext; intros; auto with *.
    apply W_F_elim with (1:=H).

    rewrite <- H1.
    apply iso_inv_eq with (1:=isof); trivial.
    apply W_F_elim with (1:=H); trivial.

   apply iso_inv_typ with (1:=isof); trivial.
Qed.

(** The iso between [W_F X] and [Wf X]. *)

Section WfIso. Import Zwdom.
  
Definition Wintro x := Wsup (fst x) (snd x).
Instance Wintro_morph : morph1 Wintro.
do 2 red; intros.
apply Wsup_morph; [apply fst_morph|apply snd_morph]; trivial.
Qed.

Lemma Wintro_ext : forall X, ext_fun (W_F X) Wintro.
do 2 red; intros; apply Wintro_morph; trivial.
Qed.

Hint Resolve Wintro_morph : core.

Lemma Wf_intro : forall x X,
  x ∈ W_F X ->
  Wintro x ∈ Wf A B X.
intros.
apply W_F_elim in H.
destruct H as (tyx,(tyy,eqx)).
apply snd_morph in eqx.
rewrite snd_def in eqx.
apply Wf_intro; trivial.
rewrite eqx.
apply cc_prod_intro; auto.
do 2 red; intros; apply cc_app_morph; auto with *.
Qed.

Lemma Wf_elim a X :
  a ∈ Wf A B X ->
  exists2 x, x ∈ W_F X &
  a == Wintro x.
intros.
apply Wf_elim in H.
destruct H as (x,tyx,(f,tyf,eqa)).
exists (couple x f).
+rewrite cc_eta_eq with (1:=tyf).
 apply W_F_intro; intros; trivial.
  do 2 red; intros; apply cc_app_morph; auto with *.
 apply cc_prod_elim with (1:=tyf); trivial.
+unfold Wintro; rewrite fst_def, snd_def; trivial.
Qed.

(*Hint Resolve Wf_mono Wf_morph : core.*)

Lemma Wintro_inj X X' x x' :
  X ⊆ Wdom A B ->
  X' ⊆ Wdom A B ->
  x ∈ W_F X ->
  x' ∈ W_F X' ->
  Wintro x == Wintro x' ->
  x==x'.
intros tyX tyX' tyx tyx' eqWi.
assert (isc := proj1 (proj1 (sigma_ax _ _ _) tyx)).
assert (isc' := proj1 (proj1 (sigma_ax _ _ _) tyx')).
red in isc,isc'; rewrite isc,isc'.
apply W_F_elim in tyx.
destruct tyx as (tyx1,(tyx2,eqx)).
apply W_F_elim in tyx'.
destruct tyx' as (tyx'1,(tyx'2,eqx')).
eapply Wsup_inj_typ with (A:=A)(B:=B)(1:=tyX)(2:=tyX') in eqWi.
*destruct eqWi as (eq1,eq2).
 apply couple_morph; trivial.
*rewrite eqx,snd_def.
 apply cc_arr_intro;[|trivial].
 intros ????; apply cc_app_morph; auto with *.
*rewrite eqx',snd_def.
 apply cc_arr_intro;[|trivial].
 intros ????; apply cc_app_morph; auto with *.
Qed.
 
 Lemma W_F_Wf_iso X :
  X ⊆ Wdom A B ->
  iso_fun (W_F X) (Wf A B X) Wintro.
split; intros.
 apply Wintro_morph.

 red; intros.
 apply Wf_intro; trivial.

 apply Wintro_inj with X X; auto.

 destruct Wf_elim with (1:=H0); eauto with *.
Qed.

 Lemma W_iso : iso_fun (W_F (W A B)) (W A B) Wintro.
unfold W at 1.
rewrite W_eqn; [|trivial].
apply W_F_Wf_iso.   
apply W_typ; trivial.
Qed.
 
End WfIso.
 
(** The iso between [W_F X] and [Wf Y], given an iso [f] between [X] and [Y]. *)
Definition wiso f := comp_iso (WFmap f) Wintro.

Lemma W_F_Wf_mapiso X Y f :
  Y ⊆ Zwdom.Wdom A B ->
  iso_fun X Y f ->
  iso_fun (W_F X) (Zwdom.Wf A B Y) (wiso f).
intros.
apply iso_fun_trans with (W_F Y).
 apply WFmap_iso; trivial.

 apply W_F_Wf_iso; trivial.
Qed.

Instance wisom  : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) wiso.
do 3 red; intros.
unfold wiso.
apply comp_iso_morph; trivial.
 apply WFmap_morph; trivial.

 apply Wintro_morph.
Qed.

Lemma wiso_ext : forall X f f',
  eq_fun X f f' -> eq_fun (W_F X) (wiso f) (wiso f').
red; intros.
apply Wintro_morph.
apply WFmap_ext.
 apply W_F_elim with (1:=H0).

 rewrite H1; reflexivity.

 intros.
 apply H.
  apply W_F_elim with (1:=H0); trivial.

  rewrite H1; rewrite H3; reflexivity.
Qed.
Hint Resolve wiso_ext : core.

 (** * Universe facts: when A and B belong to a given (infinite) universe, then so does W(A,B). *)
(*
Section W_Univ.

(* Universe facts *)
  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : Znats.N ∈ U.  

  Hypothesis aU : A ∈ U.
  Hypothesis bU : forall a, a ∈ A -> B a ∈ U.

  Lemma G_W_F X : X ∈ U -> W_F X ∈ U.
intros.
unfold W_F.
apply G_sigma; intros; trivial.
apply G_cc_prod; auto.
Qed.
  Lemma G_W_ord : W_ord ∈ U.
unfold W_ord.
apply G_clos_ord; auto.
apply ZFwdom.G_Wdom; trivial.
Qed.

  Lemma G_W : W ∈ U.
apply G_TI; intros; trivial.
 apply W_F_morph.

 apply G_W_ord.

 apply G_W_F; trivial.
Qed.

  Lemma G_Wi o : isOrd o -> TI W_F o ∈ U.
intros.
apply G_incl with W; trivial.
 apply G_W.

 apply W_post; trivial.
Qed.

End W_Univ.
*)
End W_theory.

#[global]Hint Resolve W_F_mono : core.

(* Discharged morphism results *)

Instance W_F_morph_gen :
  Proper (eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) W_F.
do 4 red; intros.
unfold W_F.
apply sigma_ext; trivial.
intros.
rewrite (H0 _ _ H3),H1; reflexivity.
Qed.

Lemma W_F_ext : forall A A' B B' X X',
  A == A' ->
  eq_fun A B B' ->
  X == X' ->
  W_F A B X == W_F A' B' X'.
unfold W_F; intros.
apply sigma_ext; trivial.
intros.
apply cc_prod_ext; auto with *.
red; auto.
Qed.

(** A specific instance of W-type: the type of sets (cf Ens.set) *)

Section Sets.

Hypothesis U : set.
Hypothesis Ugrot : grot_univ U.

  Definition sets := W U (fun X =>X).

  Let sm : morph1 (fun X => X).
do 2 red; trivial.
Qed.
  
  Lemma sets_ind :
    forall P : set -> Prop,
    Proper (eq_set==>iff) P ->
    (forall y X f, morph1 f ->
     (* y ∈ sigma X:U. U->Ens.set *)
     y == Zwdom.Wsup X (cc_lam X f) ->
     X ∈ U ->
     (forall x, x ∈ X -> f x ∈ sets) ->
     (* induction hypothesis *)
     (forall x, x ∈ X -> P (f x)) ->
     P y) ->
    forall x, x ∈ sets -> P x.
unfold sets;intros P Pm Hrec w tyw.
elim tyw using W_ind; auto.
intros X f tyX tyf Hsub.
apply Hrec with X (cc_app f); auto with *.
*rewrite <- cc_eta_eq with (1:=tyf).
 reflexivity.
*intros.
 apply cc_prod_elim with (1:=tyf); trivial. 
Qed.


  

Lemma G_prodcart_bound A B:
    A ⊆ U ->
    B ⊆ U ->
    prodcart A B ⊆ U.
red; intros.
rewrite prodcart_ax in H1.
destruct H1 as (?&?&?).
red in H1; rewrite H1.
apply G_couple; auto.
Qed.

Lemma G_fst x : x ∈ U -> fst x ∈ U.
intros.
Transparent fst.
unfold fst.
apply G_union; trivial.
apply G_subset; trivial.
apply G_union; trivial.
Qed.
Lemma G_snd x : x ∈ U -> snd x ∈ U.
intros.
Transparent snd.
unfold snd.
apply G_union; trivial.
apply G_subset; trivial.
apply G_union; trivial.
Qed.
Lemma G_Nil : empty ∈ U -> Zlist.Nil ∈ U.
intros.
apply G_trans with (func empty empty); auto.
*apply lam_is_func; auto with *.
 intros.
 apply empty_ax in H0; contradiction.
*apply G_func; trivial.
Qed.
Lemma G_lam a f :
  ext_fun a f -> a ∈ U -> (forall x, x ∈ a -> f x ∈ U) -> lam a f ∈ U.
intros.
Transparent lam.
unfold lam.
apply G_replf; auto.
intros.
apply G_couple; auto.
apply G_trans with a; auto.
Qed.

Lemma G_Cons x l : x ∈ U -> l ∈ U -> Zlist.Cons x l ∈ U.
intros.
unfold Zlist.Cons.  
assert (Gn : Zlist.next (rel_domain l) ∈ U).
{unfold Zlist.next.
 apply G_union2; trivial.
 apply G_singl; auto.
 apply G_incl with x; auto.
 apply G_replf; trivial.
 do 2 red; intros; apply Znats.succ_morph; trivial.
 unfold rel_domain.
 apply G_subset; trivial.
 apply G_union; trivial.
 apply G_union; trivial.
 intros.
 assert (x0 ∈ U).
 {apply rel_domain_ax in H1.
  destruct H1.
  rewrite <- (fst_def x0 x1).
  apply G_fst; auto.
  apply G_trans with l; trivial. }
 unfold Znats.succ.
 apply G_union2; trivial.
 apply G_singl; auto. }
apply G_lam; trivial.
*do 2 red ;intros.
 rewrite H2; reflexivity.
*intros.
 unfold Znats.natcase.
 apply G_union2; trivial.
 apply G_subset; trivial.
 apply G_subset; trivial.
 apply G_app; trivial.
 apply G_union; trivial.
 apply G_trans with (2:=H1); trivial.
Qed.

Lemma sets_incl_U : sets ⊆ U.
red; intros.
apply sets_ind with (3:=H); intros.
*do 2 red; intros.
 rewrite H0; reflexivity.
*rewrite H1.
 Transparent Zwdom.Wsup.
 unfold Zwdom.Wsup. 
 apply G_union2; trivial.
 +apply G_singl; auto.
  apply G_couple; trivial.
  apply G_Nil.
  apply G_incl with (y:=empty) in H2; trivial.
 +assert (Gl : (λ x ∈ X, f x) ∈ U) by (apply G_cc_lam; auto). 
  apply G_replf; auto.
  ++do 2 red; intros.
    rewrite H6; reflexivity.
  ++intros.
    rewrite cc_lam_ax in H5.
    destruct H5 as (a,?,(_,(b,?,?))).
    rewrite H7, fst_def, snd_def.
    assert (a ∈ U) by (apply G_trans with X; auto).
    assert (b ∈ U) by (apply G_trans with (f a); auto).
    apply G_couple; auto.
    apply G_Cons;trivial.
    apply G_fst; trivial.
    apply G_snd; trivial.
Qed.

End Sets.
