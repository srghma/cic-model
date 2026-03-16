Require Import ZF.
Require Import ZFgrothendieck.

Reserved Infix "≤" (at level 70).

(** Fixpoint theorem about monotonic operators *)

(** * Construction of the fixpoint "from above" *)

(* This is the impredicative construction:
   the fixpoint of F is the intersection of all X such that F X ≤ X *)

Class SetOrder (le : set->set->Prop) := {
  lem : Proper (eq_set==>eq_set==>iff) le;
  le_pre : PreOrder le;
    le_anti : forall x y, le x y -> le y x -> x == y
  }.

Class inf_lattice (le : set->set->Prop) (inf : set -> set) := {
(*  infm : morph1 inf;*)
  inf_le : forall x z, z ∈ x -> le (inf x) z;
  inf_least : forall x w,
    (exists w0, w0 ∈ x) -> (forall z, z ∈ x -> le w z) -> le w (inf x)
}.

Class sup_lattice (le : set->set->Prop) (sup : set -> set) := {
(*  infm : morph1 inf;*)
  sup_le : forall x z, z ∈ x -> le z (sup x);
  sup_lub : forall x w,
    (forall z, z ∈ x -> le z w) -> le (sup x) w
}.

Existing Instance lem.
Existing Instance le_pre.

(** A is the top element of pA *)
Class rel_with_top (A pA:set) (le : set->set->Prop) :=
  is_powerA : forall x, le x A -> x ∈ pA.


(** The lattice of subsets *)

Instance SetOrder_incl : SetOrder incl_set.
split; auto with *; intros.
apply incl_eq; trivial.
Qed.

Instance inf_lattice_incl : inf_lattice incl_set inter.
split; auto with *; intros.
 red; intros.
 apply inter_elim with x; trivial.

 red; intros.
 apply inter_intro; intros; trivial.
 apply H0; trivial.
Qed.

Instance sup_lattice_incl : sup_lattice incl_set union.
split; auto with *; intros.
 red; intros.
 apply union_intro with z; trivial.

 red; intros.
 apply union_elim in H0; destruct H0 as (y,?,?).
 apply H with y; trivial.
Qed.

Instance incl_with_top A : rel_with_top A (power A) incl_set. 
intros x; apply power_intro.
Qed.
 

Section KnasterTarski.

Variable le : set -> set -> Prop.
Infix "≤" := le.
Hypothesis ord : SetOrder le.

Variable inf : set -> set.
Hypothesis ilat : inf_lattice le inf.

Variable sup : set -> set.
Hypothesis slat : sup_lattice le sup.

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

Definition is_gfp x :=
  x ≤ A /\ F x == x /\ forall y, y ≤ A -> y ≤ F y -> y ≤ x.

Lemma lfp_elim x : is_lfp x -> F x == x.
intros h; apply h.
Qed.
Lemma gfp_elim x : is_gfp x -> F x == x.
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

Lemma is_gfp_unique x y :
  is_gfp x -> is_gfp y -> x == y.
intros.
apply le_anti.
 apply H0; [apply H|].
 rewrite gfp_elim with (1:=H); reflexivity.

 apply H; [apply H0|].
 rewrite gfp_elim with (1:=H0); reflexivity.
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

Lemma gfp_ind fx P :
  P ≤ A ->
  (forall X, X ≤ A -> fx ≤ X -> P ≤ X -> P ≤ F X) ->
  is_gfp fx ->
  P ≤ fx.
intros pleA Hrec gfp.
transitivity (sup (pair P fx)).
*apply sup_le; auto.
*apply gfp.
 +apply sup_lub; intros.
  apply pair_elim in H; destruct H; rewrite H; [trivial|apply gfp].
 +apply sup_lub.
  intros.
  apply pair_elim in H; destruct H; rewrite H.
  ++apply Hrec; try (apply sup_le; auto).
    apply sup_lub; intros.
    apply pair_elim in H0; destruct H0; rewrite H0; trivial.
    apply gfp.
  ++transitivity (F fx).
    +++rewrite (gfp_elim _ gfp); reflexivity.
    +++apply Fmono.
       apply sup_le; auto.
Qed.

Definition pre_fix x := x ≤ F x.
Definition post_fix x := F x ≤ x.

Lemma post_fix_A : post_fix A.
red; intros.
apply Ftyp; reflexivity.
Qed.

Let M := subset pA' post_fix.
Let coM := subset pA' pre_fix.

Lemma member_A : A ∈ M.
unfold M.
apply subset_intro; trivial.
apply post_fix_A.
Qed.

Lemma member_coA : sup empty ∈ coM.
unfold coM.
apply subset_intro.
*apply is_powerA'.
 apply sup_lub; intros.
 apply empty_ax in H; contradiction.
*red; intros.
 apply sup_lub; intros.
 apply empty_ax in H; contradiction.
Qed.

Lemma post_fix_M x : x ∈ M -> F x ≤ x.
unfold M; intros.
elim subset_elim2 with (1:=H); intros.
rewrite H0; trivial.
Qed.

Lemma pre_fix_coM x : x ∈ coM -> x ≤ F x.
unfold M; intros.
elim subset_elim2 with (1:=H); intros.
rewrite H0; trivial.
Qed.

Definition FIX := inf M.
Definition COFIX := sup coM.

Lemma FIX_typ : FIX ≤ A.
apply inf_le.
apply member_A.
Qed.

Lemma COFIX_typ : COFIX ≤ A.
apply sup_lub; intros.
apply is_powerA'.
apply subset_elim1 in H; trivial.
Qed.

Lemma lower_bound x : x ∈ M -> FIX ≤ x.
unfold FIX, M; intros.
apply inf_le; trivial.
Qed.

Lemma upper_bound x : x ∈ coM -> x ≤ COFIX.
unfold COFIX, coM; intros.
apply sup_le; trivial.
Qed.

Lemma post_fix2 x : x ∈ M -> F FIX ≤ F x.
intros.
apply Fmono.
apply lower_bound; trivial.
Qed.
Lemma pre_fix2 x : x ∈ coM -> F x ≤ F COFIX.
intros.
apply Fmono.
apply upper_bound; trivial.
Qed.

Lemma post_fix_lfp : post_fix FIX.
red.
unfold FIX.
apply inf_least; intros.
 exists A; apply member_A.
transitivity (F z).
 apply post_fix2; trivial.
 apply post_fix_M; trivial.
Qed.

Lemma pre_fix_gfp : pre_fix COFIX.
red.
unfold COFIX.
apply sup_lub; intros.
transitivity (F z).
 apply pre_fix_coM; trivial.
 apply pre_fix2; trivial.
Qed.

Lemma lfp_M : FIX ∈ M.
apply subset_intro.
 apply is_powerA'.
 apply FIX_typ.

 apply post_fix_lfp.
Qed.

Lemma incl_f_lfp : F FIX ∈ M.
unfold M; intros.
apply subset_intro.
 apply is_powerA'.
 apply Ftyp.
 apply FIX_typ.

 red.
 apply Fmono.
 apply post_fix_lfp.
Qed.
   
Lemma incl_f_gfp : F COFIX ∈ coM.
unfold M; intros.
apply subset_intro.
 apply is_powerA'.
 apply Ftyp.
 apply COFIX_typ.

 red.
 apply Fmono.
 apply pre_fix_gfp.
Qed.

Lemma FIX_eqn : F FIX == FIX.
apply le_anti.
 apply post_fix_lfp.

 apply lower_bound.
 apply incl_f_lfp.
Qed.

Lemma COFIX_eqn : F COFIX == COFIX.
apply le_anti.
 apply upper_bound.
 apply incl_f_gfp.

 apply pre_fix_gfp.
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

Lemma knaster_tarski_gfp : is_gfp COFIX.
split; [apply COFIX_typ|].
split; [apply COFIX_eqn|].
intros.
apply upper_bound.
apply subset_intro; trivial.
apply is_powerA'; trivial.
Qed.

Lemma FIX_ind : forall P,
  (forall X, X ≤ FIX -> X ≤ P -> F X ≤ P) ->
  FIX ≤ P.
intros.
apply lfp_ind; trivial.
apply knaster_tarski.
Qed.

Lemma COFIX_ind : forall P,
  P ≤ A ->
  (forall X, X ≤ A -> COFIX ≤ X -> P ≤ X -> P ≤ F X) ->
  P ≤ COFIX.
intros.
apply gfp_ind; trivial.
apply knaster_tarski_gfp.
Qed.

Lemma G_FIX U : grot_univ U -> pA ∈ U -> FIX ∈ U.
intros grot G_U.
apply G_trans with pA; trivial.
apply is_powerA.
apply FIX_typ.
Qed.

Lemma G_COFIX U : grot_univ U -> pA ∈ U -> COFIX ∈ U.
intros grot G_U.
apply G_trans with pA; trivial.
apply is_powerA.
apply COFIX_typ.
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
Instance COFIX_morph_gen :
  Proper ((E==>E==>iff)==>(E==>E)==>E==>E==>(E==>E)==>E) COFIX.
do 6 red; intros.
unfold COFIX.
apply H0.
apply subset_morph.
 apply subset_morph; trivial.
 red; intros.
 apply H; auto with *.

 red; intros.
 unfold pre_fix.
 apply H; auto with *.
Qed.
