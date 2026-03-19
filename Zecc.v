Require Import ZF Zpairs ZFnats Zuniv.
Require Import Zrelations Zcoc.


(** Statement that there exists a set containing infinitely many Grothendieck universes *)

(** Actually, we should not need the existence of a set containing
    infinitely many Grothendieck universes, but only the existence of a meta-function
    ecc : nat -> set which is equivalent to introducing infinitely many symbols (one
    for each universe).
*)
Definition infinitely_many_universes :=
   { U:set | empty ∈ U /\ forall x, x ∈ U -> exists V, V ∈ U /\ Zuniv V /\ x ∈ V }.


Axiom infinite_seq_of_Zuniv : infinitely_many_universes.

Definition UU := proj1_sig infinite_seq_of_Zuniv.

Definition ecc_succ X := Zuniv_succ_ub (union UU) X.

Lemma ecc_succ_bounded X U :
  X ⊆ U ->
  Zuniv U ->
  U ∈ UU ->
  X ∈ ecc_succ X /\
  Zuniv (ecc_succ X) /\
  exists V, Zuniv V /\ ecc_succ X ⊆ V /\ V ∈ UU.
destruct (proj2_sig infinite_seq_of_Zuniv) as (u0,uS).
intros.
destruct uS with (1:=H1) as (V & ? & ? & ?).  
destruct Zuniv_succ_ub_sound with (union UU) X as (?&?&?).
{exists V; split;[trivial|split].
  apply Zu_incl with U; trivial.
  red; intros; apply union_ax; exists V; trivial. }
split;[trivial|].
split;[trivial|].
exists V; split; [trivial|split;[|trivial]].
apply H7; trivial.
apply Zu_incl with U; trivial.
Qed.


Lemma prop_Zuniv : Zuniv (ecc_succ empty).
apply ecc_succ_bounded with empty; auto with *.
 apply Zuniv_empty.
 apply (proj2_sig infinite_seq_of_Zuniv).
Qed.
Hint Resolve prop_Zuniv : core.

Lemma prop_in : props ∈ ecc_succ empty.
assert (empty ∈ ecc_succ empty).
{apply ecc_succ_bounded with empty; auto with *.
  apply Zuniv_empty.
  apply (proj2_sig infinite_seq_of_Zuniv). }
apply Zu_power; trivial.
apply Zu_singl; trivial.
Qed.


Fixpoint ecc n :=
  match n with
  | 0 => ecc_succ empty
  | S k => ecc_succ (ecc k)
  end.

Lemma ecc_bounded n :
  Zuniv (ecc n) /\
  exists V, Zuniv V /\ ecc n ⊆ V /\ V ∈ UU.
destruct (proj2_sig infinite_seq_of_Zuniv) as (u0,uS).
induction n; simpl.
*destruct uS with (1:=u0) as (U & ? & ? & ?).
 apply ecc_succ_bounded with (U:=empty); auto with *.
 apply Zuniv_empty.
*destruct IHn as (?,(V&?&?&?)).
 apply ecc_succ_bounded with (U:=V); auto with *.
Qed.

Lemma ecc_Zuniv n : Zuniv (ecc n).
apply ecc_bounded.
Qed.
Hint Resolve ecc_Zuniv : core.

Lemma ecc_in2 : forall n, ecc n ∈ ecc (S n).
simpl; intros.
destruct (ecc_bounded n) as (_,(V&?&?&?)).
apply ecc_succ_bounded with V; trivial.
Qed.

Lemma ecc_in1 : forall n, props ∈ ecc n.
induction n; simpl; intros.
 apply prop_in.

 apply Zu_trans with (ecc n); trivial.
  apply (ecc_Zuniv (S n)).

  apply ecc_in2.
Qed.

(* Derived results *)
Lemma ecc_incl : forall n x, x ∈ ecc n -> x ∈ ecc (S n).
simpl; intros.
apply Zu_trans with (ecc n); trivial.
 apply (ecc_Zuniv (S n)).

 apply ecc_in2.
Qed.

Lemma ecc_incl_le x m n :
  (m <= n)%nat -> x ∈ ecc m -> x ∈ ecc n.
induction 1; intros; auto with *.
apply ecc_incl; auto.
Qed.

Lemma ecc_incl_prop : forall x, x ∈ props -> x ∈ ecc 0.
simpl; intros.
apply Zu_trans with props; trivial.
apply prop_in.
Qed.

Lemma ecc_prod : forall n X Y,
  ext_fun X Y ->
  X ∈ ecc n ->
  unif_bound (ecc n) X Y ->
  cc_prod X Y ∈ ecc n.
intros.
apply Zu_cc_prod; trivial.
Qed.

Lemma ecc_prod2 : forall n X Y,
  ext_fun X Y ->
  X ∈ props ->
  unif_bound (ecc n) X Y ->
  cc_prod X Y ∈ ecc n.
intros.
apply Zu_cc_prod; trivial.
apply Zu_trans with props; trivial.
apply ecc_in1.
Qed.

(* *)

Lemma empty_in_ecc n : empty ∈ ecc n.
apply Zu_trans with props; auto.
apply ecc_in1.
Qed.

Lemma one_in_ecc n : singl empty ∈ ecc n.
apply Zu_trans with props; auto.
apply ecc_in1.
Qed.

(* ecc 0 is the set of hereditarily finite sets, so it contains all finite ordinals,
   but omega is in ecc 1 *)
Lemma N_incl_ecc : N ⊆ ecc_succ empty.
red; intros n tyn.
elim tyn using N_ind; intros.
*rewrite <- H0; auto.
*apply (empty_in_ecc 0).
*apply Zu_union2; auto.
 apply Zu_pair; auto.
Qed.

Lemma N_in_ecc n : N ∈ ecc (S n).
apply Zu_incl with (ecc 0); auto.
 apply ecc_incl_le with 1; [auto with arith|].
 apply ecc_in2.

 apply N_incl_ecc.
Qed.

Hint Resolve empty_in_ecc one_in_ecc N_incl_ecc N_in_ecc : core.
