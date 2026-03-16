Require Import ZF Zpairs Zsum Znats Zrelations Zstable ZFord.
Require Import ZFgrothendieck.
Require Import Zlist.
Require Import Zcoc.
Require Export Zwdom.

(** * Low-level construction: encoding W-types as sets of path in a tree *)

Section W_Domain.

(* The first parameter of W-types (aka the payload) *)
Variable A : set.
(* The subterm index type *)
Variable B : set -> set.
Hypothesis Bm : morph1 B.

Section Wdom_Universe.

  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : N ∈ U.  

  Hypothesis aU : A ∈ U.
  Hypothesis bU : typ_fun B A U.

  Lemma G_Wdom : Wdom A B ∈ U.
apply Zwdom.G_Wdom; auto.
apply ext_is_unif_bound; auto.
Qed.

End Wdom_Universe.


(*******************************************************************************************)
(* Specific properties related to adding a bottom to the type (for strong normalization
   proofs) *)

Section SN_Auxiliary.


Lemma TI_Wfbot_typ o :
  isOrd o ->
  TI (Wfbot A B) o ⊆ Wdom A B.
induction 1 using isOrd_ind; intros.
red; intros.
apply TI_elim in H2; auto.
destruct H2.
revert H3; apply Wfbot_typ; auto.
Qed.

  Lemma mt_not_in_Wfbot o x :
    isOrd o ->
    x ∈ TI (Wfbot A B) o ->
    ~ x == empty.
red; intros.
apply TI_elim in H0; auto with *.
destruct H0 as (o',?,?).
rewrite H1 in H2.
apply mt_not_in_Wf in H2; trivial.
Qed.

  Lemma Wfbot_stable_set :
    let X := subset (power (Wdom A B))
               (fun X =>forall z, z ∈ X -> z==empty \/ ~z==empty) in
    stable_set X (Wfbot A B).
intros K Y KY.
eapply compose_stable_set with (F:=Wf A B)(K2:=Y)(K1:=power(Wdom A B)); auto with *.
*apply Wf_stable; intros; trivial.
*apply cc_bot_stable_set.
 intros.
 apply KY in H.
 apply subset_elim2 in H.
 destruct H as (z',eqz,mtz).
 rewrite eqz in H0; auto.
*red; intros.
 apply KY in H.
 apply subset_elim1 in H.
 rewrite power_def in H|-*.
 apply Wdom_cc_bot; trivial.
Qed.
  
End SN_Auxiliary.

(*******************************************************************************************)
(* Specific properties related to building corecusrion by
   transifinite iteration: build an element of a W-type as the
   limit of a directed family. *)

Section Corecursion_Auxiliary.

End Corecursion_Auxiliary.

End W_Domain.

#[global]Hint Resolve Wf_mono Wf_morph Wf_typ : core.
#[global]Hint Resolve Wfbot_mono Wfbot_morph Wfbot_typ : core.
