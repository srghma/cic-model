Require Import Zpairs Zsum Znats Zrelations Zlist.
Import ZF Zrelations.


Record Zuniv (U:set) : Prop := {
  Zu_trans : forall x y, y ∈ x -> x ∈ U -> y ∈ U;
  Zu_pair : forall x y, x ∈ U -> y ∈ U -> pair x y ∈ U;
  Zu_power : forall x, x ∈ U -> power x ∈ U;
  Zu_union : forall x, x ∈ U -> union x ∈ U }.

Instance Zuniv_morph : Proper (eq_set==>iff) Zuniv.
apply morph_impl_iff1; auto with *.
do 3 red; intros.
destruct H0 as (Gtr,G2,Gpow,Gun).
split; intros.
*rewrite <- H in H1|-*; eauto.
*rewrite <- H in H0,H1|-*; auto.
*rewrite <- H in H0|-*; auto.
*rewrite <- H in H0|-*; auto.
Qed.

Lemma Zuniv_empty : Zuniv empty.
split; intros.
*elim empty_ax with (1:=H0).
*elim empty_ax with (1:=H0).
*elim empty_ax with (1:=H).
*elim empty_ax with (1:=H).
Qed.

Section ZermeloUniverse.

Variable U : set.
Hypothesis univ : Zuniv U.

Lemma Zu_incl : forall x y, x ∈ U -> y ⊆ x -> y ∈ U.
intros.
apply Zu_trans with (power x); trivial.
 rewrite power_ax; auto.

 apply Zu_power; trivial.
Qed.

Lemma Zu_subset : forall x P, x ∈ U -> subset x P ∈ U.
intros.
apply Zu_incl with x; trivial.
red; intros.
apply subset_elim1 in H0; trivial.
Qed.

Lemma Zu_singl : forall x, x ∈ U -> singl x ∈ U.
unfold singl; intros; apply Zu_pair; auto.
Qed.


Lemma replf_bound : forall A F F',
  ext_fun A F ->
  (forall x, x ∈ A -> F x ⊆ F') ->
  replf A F ⊆ power F'.
red; intros.
red in H0.
apply power_intro; intros.
rewrite replf_ax in H1.
destruct H1 as (x,?,(_,eqz)).
rewrite eqz in H2; eauto.
Qed.
(*
Lemma Zu_replf A B :
  ext_fun A B ->
  A ∈ U ->
  (exists2 Y' : set, Y' ∈ U & forall x : set, x ∈ X -> Y x ⊆ Y') ->
  replf A B ∈ U.
intros.
apply Zu_union; trivial.
apply Zu_replf; trivial.
Qed.*)

Lemma Zu_union2 : forall x y, x ∈ U -> y ∈ U -> x ∪ y ∈ U.
intros.
unfold union2.
apply Zu_union; trivial.
apply Zu_pair; trivial.
Qed.

Definition unif_bound A B :=
  exists2 B', B' ∈ U & forall x, x ∈ A -> B x ⊆ B'.

Lemma unif_bound_cst A x :
  x ∈ U ->
  unif_bound A (fun _ => x).
exists x; [trivial| reflexivity].
Qed.
Lemma unif_bound_id A :
  A ∈ U ->
  unif_bound A (fun x => x).
exists (union A); [apply Zu_union; trivial|].
red;intros; apply union_intro with x; trivial.
Qed.
  
(*Lemma unif_bound_replf  :
  F' ∈ U ->
  (forall x, x ∈ A -> F x ⊆ F') ->
  unif_bound (prodcart A F') (fun x => G (fst

  unif_bound A (fun x => replf (F x) (G x)).
*)
Lemma Zu_sup A B :
  ext_fun A B ->
  A ∈ U ->
  unif_bound A B ->
  sup A B ∈ U.
intros.
destruct H1 as (B',?,inB').
apply Zu_union; trivial.
eapply Zu_incl;[|apply replf_bound with (2:=inB'); trivial]. 
apply Zu_power; trivial.
Qed.

Lemma Zu_nat x : x ∈ U -> N ⊆ U.
red; intros.
elim H0 using N_ind; intros.
 rewrite <- H2; trivial.

 apply Zu_incl with x; trivial.

 apply Zu_union2; trivial.
 apply Zu_singl; trivial.
Qed.

Lemma Zu_prodcart : forall A B, A ∈ U -> B ∈ U -> prodcart A B ∈ U.
intros.
eapply Zu_incl;[|apply prodcart_bound].
apply Zu_power; trivial.
apply Zu_power; trivial.
apply Zu_union2; trivial.
Qed.

Lemma Zu_sigma A B :
  ext_fun A B ->
  A ∈ U ->
  unif_bound A B ->
  sigma A B ∈ U.
intros Bext Au (B', Bu, inB').
apply Zu_incl with (prodcart A B'); [apply Zu_prodcart; trivial|].
red; intros.
rewrite sigma_ax in H.
destruct H as (zc & ty1 & (_,ty2)); red in zc.
rewrite zc; apply couple_intro; trivial.
revert ty2; apply inB'; trivial.
Qed.

Lemma Zu_couple : forall x y, x ∈ U -> y ∈ U -> couple x y ∈ U.
intros.
eapply Zu_incl;[|apply couple_bound].
apply Zu_power; trivial.
apply Zu_power; trivial.
apply Zu_union2; trivial.
Qed.

  Lemma Zu_sum X Y : X ∈ U -> Y ∈ U -> sum X Y ∈ U.
unfold sum; intros.
apply Zu_union2; apply Zu_prodcart; trivial.
 apply Zu_singl; apply Zu_nat with X; trivial.
 apply zero_typ.

 apply Zu_singl; apply Zu_nat with X; trivial.
 apply succ_typ;  apply zero_typ.
Qed.

Lemma Zu_sumcase A B f g a :
  morph1 f ->
  morph1 g ->
  a ∈ sum A B ->
  (forall a, a ∈ A -> f a ∈ U) ->
  (forall a, a ∈ B -> g a ∈ U) ->
  sum_case f g a ∈ U.
intros.
apply sum_case_ind with (6:=H1); intros; auto.
apply morph_impl_iff1; auto with *.
do 3 red; intros.
rewrite <- H4; trivial.
Qed.

Lemma Zu_rel : forall A B, A ∈ U -> B ∈ U -> rel A B ∈ U.
intros.
unfold rel.
apply Zu_power; trivial.
apply Zu_prodcart; trivial.
Qed.

Lemma Zu_func : forall A B, A ∈ U -> B ∈ U -> func A B ∈ U.
Proof.
intros.
eapply Zu_incl;[|apply func_bound; trivial].
do 3 (apply Zu_power;trivial).
apply Zu_union2; trivial.
Qed.

Lemma Zu_dep_func : forall X Y,
  ext_fun X Y ->
  X ∈ U ->
  unif_bound X Y ->
  dep_func X Y ∈ U.
Proof.
intros.
eapply Zu_incl;[|apply dep_func_bound; trivial].
do 3 (apply Zu_power;trivial).
apply Zu_union2; trivial.
apply Zu_sup; trivial.
Qed.

Local Transparent lam app cc_lam cc_app.
Lemma Zu_app f x :
  f ∈ U -> x ∈ U -> app f x ∈ U.
unfold app; intros.
apply Zu_union; trivial.
apply Zu_subset.
unfold rel_image.
apply Zu_subset.
apply Zu_union; trivial.
apply Zu_union; trivial.
Qed.

  Lemma Zu_cc_lam A F :
    A ∈ U ->
    unif_bound A F ->
    cc_lam A F ∈ U.
intros.
unfold cc_lam.
apply Zu_sup; intros; trivial.
{do 2 red; intros; apply replf_morph; auto.
 rewrite H2; reflexivity.
 red; intros; apply couple_morph; trivial. }
destruct H0 as (F',?,?).
exists (prodcart A F'); [apply Zu_prodcart; trivial|].
red; intros.
rewrite replf_ax in H3.
destruct H3 as (p,?,(_,eqz)); rewrite eqz.
apply couple_intro; auto.
rewrite extf_def in H3; destruct H3.
apply H1 with(x:=x); trivial.
Qed.


  Lemma Zu_cc_app f x :
    f ∈ U -> x ∈ U -> cc_app f x ∈ U.
unfold cc_app; intros.
unfold rel_image.
apply Zu_subset.
apply Zu_union; trivial.
apply Zu_union; trivial.
apply Zu_subset; trivial.
Qed.
Opaque lam app cc_lam cc_app.

  Lemma Zu_cc_prod A B :
    ext_fun A B ->
    A ∈ U ->
    unif_bound A B ->
    cc_prod A B ∈ U.
intros.
eapply Zu_incl;[|apply cc_prod_bound; trivial].
do 3 (apply Zu_power;trivial).
apply Zu_union; trivial.
apply Zu_pair; trivial.
apply Zu_union; trivial.
apply Zu_sup; trivial.
Qed.

Section NonTrivial.

  Hypothesis Unontriv : empty ∈ U.

End NonTrivial.


Section Infinite.

  Hypothesis Uinf : N ∈ U.

  Lemma Zu_inf_nontriv : empty ∈ U.
apply Zu_trans with N; trivial.
apply zero_typ.
Qed.
  Hint Resolve Zu_inf_nontriv : core.

  Lemma Zu_List A : A ∈ U -> List A ∈ U.
intros.
unfold List.
apply Zu_sup;[intros ??? e; rewrite e; reflexivity|trivial|].
exists (rel N A); [apply Zu_rel; trivial|].
intros.
transitivity (rel x A); [apply func_rel_incl|apply rel_mono; auto with *].
red; intros.
apply N_trans with x; trivial.
Qed.

End Infinite.

End ZermeloUniverse.

(** Intersection *)

Lemma Zuniv_inter : forall UU,
  (exists x, x ∈ UU) ->
  (forall x, x ∈ UU -> Zuniv x) ->
  Zuniv (inter UU).
destruct 1.
split; intros.
*apply inter_intro; intros; eauto.
 destruct (H0 _ H3) as (trans,_,_,_).
 apply trans with x0; trivial.
 apply inter_elim with (1:=H2); trivial.

*apply inter_intro; intros; eauto.
 destruct (H0 _ H3) as (_,clos_pair,_,_).
 apply clos_pair; eapply inter_elim; eauto.

*apply inter_intro; intros; eauto.
 destruct (H0 _ H2) as (_,_,clos_pow,_).
 apply clos_pow; eapply inter_elim; eauto.

*apply inter_intro; intros; eauto.
 destruct (H0 _ H2) as (_,_,_,clos_un).
 apply clos_un; eapply inter_elim; eauto.
Qed.

(* The intersection of all Grothendieck universes satisfying P given
   an superset UU (containing at least one universe satisfying P) *)
Definition Zuniv_inf (UU:set) (P:set->Prop) :=
  subset UU (fun y => forall V, Zuniv V -> P V -> y ∈ V).

Lemma Zuniv_inf_univ (P:set->Prop) UU :
  (exists U, Zuniv U /\ P U /\ U ⊆ UU) ->
  Zuniv (Zuniv_inf UU P).
intros (U & gU & pU & Uincl).
assert (Vdef : forall z, z ∈ Zuniv_inf UU P <-> forall V, Zuniv V -> P V -> z ∈ V).
{unfold Zuniv_inf; intros.
 split; intros. 
 *destruct subset_elim2 with (1:=H) as (z',eqz,?); clear H.
  rewrite eqz; auto.
 *apply subset_intro; [|auto].
  apply Uincl; auto. }
split; intros.
*rewrite Vdef in H0|-*; intros.
 apply Zu_trans with x; auto.
*rewrite Vdef in H,H0|-*; intros.
 apply Zu_pair; auto.
*rewrite Vdef in H|-*; intros.
 apply Zu_power; auto.
*rewrite Vdef in H|-*; intros.
 apply Zu_union; auto.
Qed.


(** Successor *)

(** [y] is the the successor of [x]
    if it the least Grothendieck universe of which [x] is an element *)
Definition Zuniv_succ_pred x y :=
  Zuniv y /\ x ∈ y /\ forall U, Zuniv U -> x ∈ U -> y ⊆ U.

Instance Zuniv_succ_pred_morph : Proper (eq_set==>eq_set==>iff) Zuniv_succ_pred.
do 3 red; intros.
apply and_iff_morphism.
 apply Zuniv_morph; trivial.
apply and_iff_morphism.
 apply in_set_morph; trivial.
apply fa_morph; intros U.
rewrite H; rewrite H0; reflexivity.
Qed.

(** Build the successor given an upper bound *)
Definition Zuniv_succ_ub UU x := Zuniv_inf UU (fun U => x ∈ U).

Instance Zuniv_succ_ub_morph : morph2 Zuniv_succ_ub.
do 3 red; intros; apply subset_morph; trivial.
red; intros.
apply fa_morph; intros z.
rewrite H0; reflexivity.
Qed.

Lemma grot_succ_ub_sound UU x :
  (exists U, Zuniv U /\ x ∈ U /\ U ⊆ UU) ->
  Zuniv_succ_pred x (Zuniv_succ_ub UU x).
intros has_ub.
destruct (has_ub) as (U&gU&xin&ub).
split;[|split]; intros.
*apply Zuniv_inf_univ; trivial.

*apply subset_intro; auto.

*red; intros.
 unfold Zuniv_succ_ub, Zuniv_inf in H1;
   rewrite subset_ax in H1; destruct H1 as (_,(z',eqz,?)).
 rewrite eqz; auto.
Qed.

