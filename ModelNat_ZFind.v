Set Implicit Arguments.

(** In this file, we build a consistency model of the
    Calculus of Constructions extended with natural numbers and
    the usual recursor (CC+NAT). It is a follow-up of file
    ModelZF. It shows that the natural numbers introduced in
    ZFind_nat form an instance of Nat_Model.
 *)

Require Import basic Models.
Require Import ZF ZFsum ZFwfr ZFind_nat.
Require Import ModelZF.

(** All that remains to build is the recursor *)
Definition NAT_REC f g n :=
  WFR (fun m => subset NAT (fun n => m == SUCC n))
      (fun F n => NATCASE f (fun m => g m (F m)) n) n.

#[local]Lemma Rm : morph1 (fun m => subset NAT (fun n => m == SUCC n)).
do 2 red; intros.
apply subset_morph; [reflexivity|].  
red; intros.
rewrite H; reflexivity.
Qed.

#[local]Lemma Rzero : forall y : set, ~ y ∈ subset NAT (fun n : set => ZERO == SUCC n).
red; intros.
apply subset_elim2 in H.
destruct H as (?,_,abs).
apply NATf_discr in abs; trivial.
Qed.

#[local]Lemma WFRle_zero x y :
  ZFrepl.WFRle (fun m : set => subset NAT (fun n : set => m == SUCC n)) x y ->
  y == ZERO -> x == ZERO.
induction 1; auto.
destruct H; [rewrite H;trivial|].
intros.
apply subset_elim2 in H.
destruct H.
rewrite H0 in H1.
apply NATf_discr in H1; contradiction.
Qed.

#[local]Lemma WFRle_typ x y :
  ZFrepl.WFRle (fun m : set => subset NAT (fun n : set => m == SUCC n)) x y ->
  y ∈ NAT -> x ∈ NAT.
induction 1; auto.
destruct H; [rewrite H;trivial|].
intros.
apply subset_elim1 in H; trivial.
Qed.

Instance NATREC_morph :
  Proper (eq_set ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) NAT_REC.
do 4 red; intros.
unfold NAT_REC.
apply WFR_morph; trivial.
 apply Rm.

 do 2 red; intros.
 apply NATCASE_morph; trivial.
 red; intros.
 apply H0; auto.
Qed.
Section NatrecProperties.
(*
  Let Rm : Proper (eq_set ==> eq_set ==> iff) (fun n m : set => n ∈ NAT /\ m == SUCC n).
do 3 red; intros.
rewrite H,H0; reflexivity.
Qed.
*)
  Let AccN x : x ∈ NAT -> Acc (fun n m : set => n ∈ subset NAT (fun n => m == SUCC n)) x.
intros.
apply NAT_ind with (4:=H). 
 intros.
 revert H2; apply iff_impl; eapply wf_morph with (eqA:=eq_set); auto with *.
 do 2 red; intros; apply in_set_morph; trivial.
 apply Rm; trivial.
 
 constructor; intros.
 apply Rzero in H0; contradiction.

 intros.
 constructor; intros.
 apply subset_elim2 in H2.
 destruct H2 as (y',eqy,e). 
 rewrite <-eqy in e. 
 apply SUCC_inj in e.
 revert H1; apply iff_impl; apply wf_morph with (eqA:=eq_set); auto with *.
 do 2 red; intros; apply in_set_morph; trivial.
 apply Rm; trivial.
Qed.

(*
  Let invN x y : x ∈ NAT /\ y == SUCC x -> y ∈ NAT -> x ∈ NAT.
destruct 1; trivial.
Qed.
*)
  Let casem f' g' : morph2 g' -> Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set)
                (fun F n => NATCASE f' (fun m => g' m (F m)) n).
do 3 red; intros.
apply NATCASE_morph; auto with *.
red; intros.
apply H; auto.
Qed.

  Let caseext f g :
    morph2 g ->
    forall x x' F F', x ∈ NAT -> x==x' ->
    (forall y y' : set, y ∈ subset NAT (fun y => x == SUCC y) -> y == y' -> F y == F' y') ->
    NATCASE f (fun m : set => g m (F m)) x ==
    NATCASE f (fun m : set => g m (F' m)) x'.
intros.
apply NATCASE_morph_gen; intros; auto with *.
apply H; trivial; apply H2; trivial.
apply subset_intro; trivial.
rewrite NAT_eq in H0.
apply SUCC_inv_typ_gen.
rewrite <- H3; trivial.
Qed.

  Lemma NATREC_0 f g : NAT_REC f g ZERO == f.
unfold NAT_REC; intros.
rewrite WFR_eqn; auto.
*apply NATCASE_ZERO.
*apply Rm.
*intros.
 apply WFRle_zero in H; [|reflexivity].
 rewrite NATCASE_ZERO_eq; trivial.
 rewrite H1 in H.
 rewrite NATCASE_ZERO_eq; trivial.
 reflexivity.
*apply AccN.
 apply ZERO_typ; trivial.
Qed.

Lemma NATREC_S : forall f g n, morph2 g -> n ∈ NAT ->
   NAT_REC f g (SUCC n) == g n (NAT_REC f g n).
unfold NAT_REC; intros.
rewrite WFR_eqn; auto.
*rewrite NATCASE_SUCC.
  reflexivity.

  intros; apply H; trivial.
  apply NATREC_morph; auto with *.
  
*do 2 red; intros.
 apply Rm; trivial.
  
*intros; apply caseext; trivial.
 apply WFRle_typ in H1; auto.
 apply SUCC_typ; trivial.

*apply AccN.
 apply SUCC_typ; trivial.
Qed.
End NatrecProperties.

Lemma NATREC_typ P f g n :
  morph1 P ->
  morph2 g ->
  n ∈ NAT ->
  f ∈ P ZERO ->
  (forall k h, k ∈ NAT -> h ∈ P k -> g k h ∈ P (SUCC k)) ->
  NAT_REC f g n ∈ P n.
intros.
elim H1 using NAT_ind; intros.
 rewrite <- H5; trivial.

 rewrite NATREC_0; trivial.

 rewrite NATREC_S; auto.
Qed.

(** Now we can gather (and rename) all the constructions to
    instantiate Nat_Model. *)
Module ZFind_Nats <: Models.Nat_Model CCM.
Definition N := NAT.
Definition zero := ZERO.
Definition succ := SUCC.
Definition succ_morph := ZFsum.inr_morph.

Definition zero_typ := ZERO_typ.
Definition succ_typ := SUCC_typ.

Definition natrec := NAT_REC.
Definition natrec_morph := NATREC_morph.

Definition natrec_0 := NATREC_0.
Definition natrec_S := NATREC_S.
Definition natrec_typ := NATREC_typ.

End ZFind_Nats.

Module CCN := CCM <+ ZFind_Nats.

(** Derive the judgements and typing rules of CC+nats *)
Require Import GenModelNat.
Module M <: CCNat_Rules := MakeNatModel(CCN).
