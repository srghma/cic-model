Require Import basic.
Require Import Sublogic.
Require Import Models GenModelSyntax.
Require Import ZF Zrelations Zcoc ModelZ.
Require Term Env TypeJudge.

(** Set-theoretical model of the Calculus of Constructions in IZF *)

(** * Instantiating the generic model construction *)

Module BuildModel := MakeModelSyntax(CCM).

Import BuildModel T J R.

(** Subtyping *)

Lemma sub_typ_covariant e U1 U2 V1 V2 :
  U1 <> kind ->
  eq_typ e U1 U2 ->
  sub_typ (U1::e) V1 V2 ->
  sub_typ e (Prod U1 V1) (Prod U2 V2).
Proof.
intros Unk.
red; intros.
simpl in H2|-*.
unfold CCM.inX, CCM.prod in *.
revert x H2; apply cc_prod_covariant.
*do 2 red; intros.
 rewrite H3; reflexivity.
*apply H; trivial.
*intros.
 intros z; apply H0.
 apply vcons_add_var; trivial.
Qed.

(** The model in ZF implies the consistency of CC *)

Import Term Env TypeJudge.
Load "template/Library.v".

Theorem cc_consistency : forall M M', ~ eq_typ nil M M' FALSE.
Proof.
unfold FALSE; red in |- *; intros.
specialize BuildModel.int_sound with (1 := H); intro.
destruct H0 as (H0,_).
simpl in H0.
apply abstract_consistency with (M:=int_trm(unmark_app M)) (FF:=empty); trivial.
 unfold props; apply empty_in_power.

 red; intros.
 apply empty_ax with (1:=H1); trivial.
Qed.
Print Assumptions cc_consistency.
