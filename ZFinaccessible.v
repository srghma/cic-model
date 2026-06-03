
Require Import Znats ZFord ZFrank ZFgrothendieck.

(* An inaccesible cardinal yields a Grothendieck universe *)
Section VN_Inaccessible.

Variable mu : set.
Hypothesis mu_inacc : VN_inaccessible mu.

Let mu_ord : isOrd mu.
destruct mu_inacc as ((?,_),_); trivial.
Qed.

Let mu_lim : forall x, lt x mu -> lt (osucc x) mu.
destruct mu_inacc as ((_,?),_); trivial.
Qed.

Let mu_reg : VN_regular mu.
destruct mu_inacc as ((_,_),?); trivial.
Qed.

Lemma VN_grot : grot_univ (VN mu).
split; intros.
*apply VN_trans with x; trivial.

*apply VNlim_pair; trivial.
 split; auto.
 
*apply VNlim_power; trivial.
 split; trivial.

*rewrite <- (replf_id x).
 apply mu_reg; intros; auto with *.
 apply VN_trans with x; trivial.
 
*revert I f H H0 H1; apply G_replf_fsup.
 {intros.
  apply VN_incl with x; trivial. }
 intros.
 assert (replf A F ⊆ power (sup A F)).
 {apply union_power; reflexivity. }
 apply VN_incl with (2:=H2); trivial.
 apply VNlim_power; [apply mu_inacc|].
 apply mu_reg; trivial.
Qed.
                
End VN_Inaccessible.

(* Conversely, the set of ordinals of a Grothendieck universe form
   an inaccessible cardinal *)

Section Grothendieck_Universe.

  Variable U : set.
  Hypothesis Ug : grot_univ U.
  Hypothesis Uinf : N ∈ U.

  Definition grot_ord := subset U isOrd.

  Lemma grot_ord_intro : forall x, lt x grot_ord -> x ∈ U.
intros.
apply subset_elim1 in H; trivial.
Qed.

  Lemma isOrd_grot : forall x, lt x grot_ord -> isOrd x.
intros.
apply subset_elim2 in H; destruct H.
rewrite H; trivial.
Qed.
Hint Resolve isOrd_grot : core.

  Lemma grot_ord_inv : forall x, isOrd x -> x ∈ U -> lt x grot_ord.
intros.
apply subset_intro; trivial.
Qed.

  Lemma isOrd_grot_ord : isOrd grot_ord.
apply isOrd_intro; intros.
 apply subset_intro; trivial.
 apply G_incl with b; trivial.
 apply grot_ord_intro; trivial.

 red; intros.
 assert (isOrd x) by eauto using isOrd_grot.
 assert (isOrd y) by eauto using isOrd_grot.
 assert (x ∈ U) by (apply grot_ord_intro; trivial).
 assert (y ∈ U) by (apply grot_ord_intro; trivial).
 exists (x ⊔ y). 
  apply subset_intro.
   apply G_osup2; auto.
   
   apply isOrd_osup2; trivial.

  split; [apply osup2_incl1|apply osup2_incl2]; auto.

 apply isOrd_grot; trivial.
Qed.
Hint Resolve isOrd_grot_ord : core.

 Lemma G_limit : forall x, lt x grot_ord -> lt (osucc x) grot_ord.
intros.
apply grot_ord_inv; auto.
apply G_subset; trivial.
apply G_power; trivial.
apply grot_ord_intro; trivial.
Qed.

(* *)

  Lemma VN_in_grot :
    forall o, lt o grot_ord -> VN o ∈ U.
unfold VN; intros.
apply G_TI; auto with *.
 apply grot_ord_intro; trivial.

 intros.
 apply G_power; trivial.
Qed.


  Lemma VN_incl_grot : VN grot_ord ⊆ U.
red; intros.
rewrite VN_def in H; auto.
destruct H.
apply G_trans with (power (VN x)); trivial.
 rewrite power_ax; trivial.

 apply G_power; trivial.
 apply VN_in_grot; trivial.
Qed.


  Lemma G_ord_sup : forall x F,
  ext_fun x F ->
  x ∈ U ->
  (forall y, y ∈ x -> lt (F y) grot_ord) ->
  lt (osup x F) grot_ord.
intros.
assert (osup x F ∈ U).
 apply G_osup; intros; auto.
 apply grot_ord_intro; auto.
assert (isOrd (osup x F)).
 apply isOrd_osup; trivial.
 intros.
 apply isOrd_inv with grot_ord; auto.
apply grot_ord_inv; trivial.
Qed.

Lemma G_rk x : x ∈ U -> rk x ∈ U.
elim x using wf_ax; intros.
rewrite rk_def.
apply G_osup; intros; auto with *.
apply ZFrank.rk_aux_ext.
apply G_subset; trivial.
apply G_power; trivial.
apply H; trivial.
apply G_trans with x0; trivial. 
Qed.


  Lemma U_incl_VN_grot : U ⊆ VN grot_ord.
red; intros.
apply VN_incl with (VN (rk z)); auto.
*apply VN_rk_intro.
*apply VN_mono; auto.
 apply subset_intro; auto.
 apply G_rk; trivial.
Qed.

  Lemma U_eq_VN_grot : U == VN grot_ord.
apply incl_eq.  
*apply U_incl_VN_grot.
*apply VN_incl_grot.
Qed.
(*Print Assumptions U_eq_VN_grot.*)

  Lemma G_regular : VN_regular grot_ord.
red; intros.
rewrite <- U_eq_VN_grot in H0|-*.
apply G_union; trivial.
apply G_fsup_replf; trivial.
*apply G_incl; trivial.
*apply G_fsup; trivial.
*intros.
 rewrite U_eq_VN_grot; eauto.
Qed.

  Lemma G_inaccessible : VN_inaccessible grot_ord.
split;[split|]; auto.
 exact G_limit.

 exact G_regular.
Qed.

  Lemma G_VN_is_grot : grot_univ (VN grot_ord).
apply VN_grot; trivial.
exact G_inaccessible.
Qed.

End Grothendieck_Universe.

Hint Resolve grot_ord_intro isOrd_grot_ord isOrd_grot : core.
Hint Resolve G_VN_is_grot : core.
