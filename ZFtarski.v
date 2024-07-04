Require Import ZF.
Require Import ZFgrothendieck.

Reserved Infix "≤" (at level 70).

Require ZFord.

(** Fixpoint theorem about monotonic operators *)

(** * Construction of the fixpoint "from above" *)

(* This is the impredicative construction:
   the fixpoint of F is the intersection of all X such that F X ≤ X *)


Class inf_lattice (le : set->set->Prop) (inf : set -> set) := {
  lem : Proper (eq_set==>eq_set==>iff) le;
  le_pre : PreOrder le;
  le_anti : forall x y, le x y -> le y x -> x == y;
(*  infm : morph1 inf;*)
  inf_le : forall x z, z ∈ x -> le (inf x) z;
  inf_least : forall x w,
    (exists w0, w0 ∈ x) -> (forall z, z ∈ x -> le w z) -> le w (inf x)
}.
Existing Instance lem.
Existing Instance le_pre.

(** A is the top element of pA *)
Class rel_with_top (A pA:set) (le : set->set->Prop) :=
  is_powerA : forall x, le x A -> x ∈ pA.


(** The lattice of subsets *)

Instance inf_lattice_incl : inf_lattice incl_set inter.
split; auto with *; intros.
 apply incl_eq; trivial. 

 red; intros.
 apply inter_elim with x; trivial.

 red; intros.
 apply inter_intro; intros; trivial.
 apply H0; trivial.
Qed.

Instance incl_with_top A : rel_with_top A (power A) incl_set. 
intros x; apply power_intro.
Qed.
 

Section KnasterTarski.

Variable le : set -> set -> Prop.
Variable inf : set -> set.
Hypothesis ilat : inf_lattice le inf.
Infix "≤" := le.

Variable A : set.
Variable pA : set.
Hypothesis topA : rel_with_top A pA le.

Let pA' := subset pA (fun x => x ≤ A).
Let is_powerA' x : x ≤ A <-> x ∈ pA'.
split; intros.
 apply subset_intro; trivial.
 apply is_powerA; trivial.

 apply subset_elim2 in H; destruct H.
 rewrite H; trivial.
Qed.

Let A_pA : A ∈ pA'.
apply is_powerA'; reflexivity.
Qed.


Variable F : set -> set.

Hypothesis Fmono : Proper (le==>le) F.
Hypothesis Ftyp : forall x, x ≤ A -> F x ≤ A.

Instance Fm : morph1 F.
do 2 red; intros.
apply le_anti; apply Fmono; rewrite H; reflexivity.
Qed.

Definition is_lfp x :=
  F x == x /\ forall y, F y ≤ y -> x ≤ y.

Lemma lfp_elim x : is_lfp x -> F x == x.
intros h; apply h.
Qed.

Lemma is_lfp_unique x y :
  is_lfp x -> is_lfp y -> x == y.
intros.
apply le_anti.
 apply H.
 rewrite lfp_elim with (1:=H0); reflexivity.

 apply H0.
 rewrite lfp_elim with (1:=H); reflexivity.
Qed.

Lemma lfp_ind fx P :
  (forall X, X ≤ fx -> X ≤ P -> F X ≤ P) ->
  is_lfp fx ->
  fx ≤ P.
intros Hrec lfp.
transitivity (inf (pair P fx)).
*apply lfp.
 apply inf_least.
 {exists fx; apply pair_intro2. }
 intros.
 apply pair_elim in H; destruct H; rewrite H.
 +apply Hrec; apply inf_le; auto.
 +transitivity (F fx).
  2:rewrite (lfp_elim _ lfp); reflexivity.
  apply Fmono.
  apply inf_le; auto.
*apply inf_le; auto.
Qed.

Definition pre_fix x := x ≤ F x.
Definition post_fix x := F x ≤ x.

Lemma post_fix_A : post_fix A.
red; intros.
apply Ftyp; reflexivity.
Qed.

Let M := subset pA' post_fix.

Lemma member_A : A ∈ M.
unfold M.
apply subset_intro; trivial.
apply post_fix_A.
Qed.

Lemma post_fix1 x : x ∈ M -> F x ≤ x.
unfold M; intros.
elim subset_elim2 with (1:=H); intros.
rewrite H0; trivial.
Qed.

Definition FIX := inf M.

Lemma lower_bound x : x ∈ M -> FIX ≤ x.
unfold FIX, M; intros.
apply inf_le; trivial.
Qed.

Lemma lfp_typ : FIX ≤ A.
apply lower_bound.
apply member_A.
Qed.

Lemma post_fix2 x : x ∈ M -> F FIX ≤ F x.
intros.
apply Fmono.
apply lower_bound; trivial.
Qed.


Lemma post_fix_lfp : post_fix FIX.
red.
unfold FIX.
apply inf_least; intros.
 exists A; apply member_A.
transitivity (F z).
 apply post_fix2; trivial.
 apply post_fix1; trivial.
Qed.

Lemma incl_f_lfp : F FIX ∈ M.
unfold M; intros.
apply subset_intro.
 apply is_powerA'.
 apply Ftyp.
 apply lfp_typ.

 red.
 apply Fmono.
 apply post_fix_lfp.
Qed.

Lemma FIX_eqn : F FIX == FIX.
apply le_anti.
 apply post_fix_lfp.

 apply lower_bound.
 apply incl_f_lfp.
Qed.

Lemma knaster_tarski : is_lfp FIX.
split.
 apply FIX_eqn.

 intros.
 transitivity (inf (pair y A)). 
 2:apply inf_le; apply pair_intro1.
 apply lower_bound.
 unfold M.
 apply subset_intro; trivial.
  apply is_powerA'.
  apply inf_le; apply pair_intro2.

  red.
  apply inf_least; intros.
   exists y; apply pair_intro1.
  apply pair_elim in H0; destruct H0; rewrite H0.
   transitivity (F y); trivial.
   apply Fmono.
   apply inf_le; apply pair_intro1.

   apply Ftyp.
   apply inf_le; apply pair_intro2.
Qed.

Lemma FIX_ind : forall P,
  (forall X, X ≤ FIX -> X ≤ P -> F X ≤ P) ->
  FIX ≤ P.
intros.
apply lfp_ind; trivial.
apply knaster_tarski.
Qed.

Lemma G_FIX U : grot_univ U -> pA ∈ U -> FIX ∈ U.
intros grot G_U.
apply G_trans with pA; trivial.
apply is_powerA.
apply lfp_typ.
Qed.

(*************************************************************************************)
End KnasterTarski.

Local Notation E:=eq_set.
Instance FIX_morph_gen :
  Proper ((E==>E==>iff)==>(E==>E)==>E==>E==>(E==>E)==>E) FIX.
do 6 red; intros.
unfold FIX.
apply H0.
apply subset_morph.
 apply subset_morph; trivial.
 red; intros.
 apply H; auto with *.

 red; intros.
 unfold post_fix.
 apply H; auto with *.
Qed.
