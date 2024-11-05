Require Import basic.
Require Import Sublogic.
Require Import Models GenModelSyntax.
Require Import ZF ZFrelations ZFcoc ModelZF.
Require Term Env TypeJudge.

(** Set-theoretical model of the Calculus of Constructions in IZF *)

(** * Instantiating the generic model construction *)

Module BuildModel := MakeModel(CCM).

Import BuildModel T J R.

Lemma El_int_arr T U i :
  int (Prod T (lift 1 U)) i == cc_arr (int T i) (int U i).
simpl.
apply cc_prod_ext.
 reflexivity.

 red; intros.
 rewrite simpl_int_lift.
 rewrite lift0_term; reflexivity.
Qed.
(** Subtyping *)

(*
Definition sub_typ_covariant : forall e U1 U2 V1 V2,
  U1 <> kind ->
  eq_typ e U1 U2 ->
  sub_typ (U1::e) V1 V2 ->
  sub_typ e (Prod U1 V1) (Prod U2 V2).
intros.
apply sub_typ_covariant; trivial.
intros.
unfold eqX, lam, app.
unfold inX in H2.
unfold prod, ZFuniv_real.prod in H2; rewrite El_def in H2.
apply cc_eta_eq in H2; trivial.
Qed.
*)

(** Universes *)
(*
Lemma cumul_Type : forall e n, sub_typ e (type n) (type (S n)).
red; simpl; intros.
red; intros.
apply ecc_incl; trivial.
Qed.

Lemma cumul_Prop : forall e, sub_typ e prop (type 0).
red; simpl; intros.
red; intros.
apply G_trans with props; trivial.
 apply (grot_succ_typ gr).

 apply (grot_succ_in gr).
Qed.
*)


(** The model in ZF implies the consistency of CC *)

Import Term Env TypeJudge.
Load "template/Library.v".

Lemma cc_consistency : forall M M', ~ eq_typ nil M M' FALSE.
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
