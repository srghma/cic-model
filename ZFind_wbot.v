Require Import ZF ZFpairs ZFnats ZFrelations ZFord ZFfix ZFstable.
Require Import ZFgrothendieck.
Require Import ZFcoc.
Require Import ZFwdom.
Require Export ZFind_w.

(** In this file we develop an alternative model of W-types where all stages are non-empty
 *)

Section W_theory.

(** * Definition and properties of the W-type operator *)

Variable A : set.
Variable B : set -> set.
Hypothesis Bm : morph1 B.

Local Notation WF := (W_F A B).
Local Notation Wd := (Wdom A B).
Local Notation Wfb := (Wfbot A B).

Hint Resolve Wintro_ext : core.

  Definition Wbot_ord := clos_ord Wfb Wd.

  Lemma Wbot_o_o : isOrd Wbot_ord.
apply clos_ord_o; auto.
Qed.
  
Lemma cc_bot_stable :
  stable_class (fun X => X ⊆ Fstages Wfb Wd) cc_bot.
unfold cc_bot; apply union2_stable_disjoint.
 do 2 red; reflexivity.

 do 2 red; trivial.

 apply cst_stable_class.

 apply id_stable_class.

 intros.
 apply singl_elim in H1.
 rewrite H1 in H2; apply H0 in H2.
 rewrite Fstages_def in H2; auto.
 destruct H2.
 apply mt_not_in_Wfbot in H3; auto with *.
Qed.

Lemma Wfbot_stable : stable_class (fun X => X ⊆ Fstages Wfb Wd) Wfb.
apply compose_stable_class with (F:=Wf A B) (K1:=fun X => X ⊆ cc_bot (Fstages Wfb Wd)); trivial.
 do 2 red; intros.
 rewrite H; reflexivity.

 apply Wf_mono; trivial.

 apply cc_bot_morph.

 apply Wf_stable0; intros; trivial.
 rewrite H.
 apply Wdom_cc_bot.
 apply Fstages_inA.

 apply cc_bot_stable.

 intros; apply cc_bot_mono; trivial.
Qed.
Hint Resolve Wfbot_stable : core.
  
  Definition W_Fbot X := W_F A B (cc_bot X).
  Definition Wibot o := TI W_Fbot o.
  Definition Wbot := Wibot Wbot_ord  .
  
  Instance W_Fbot_mono : Proper (incl_set==>incl_set) W_Fbot.
do 2 red; intros.
unfold W_Fbot; apply W_F_mono; trivial.
apply cc_bot_mono; auto with *.
Qed.

Lemma W_Fbot_stable : stable_class (fun X => X ⊆ Fstages Wfb Wd) W_Fbot.
apply compose_stable_class with (F:=WF) (K1:=fun _ => True); trivial.
 do 2 red; reflexivity.

 apply W_F_mono; trivial.

 apply cc_bot_morph.

 apply W_F_stable; trivial.

 apply cc_bot_stable.
Qed.

  Lemma mt_not_in_W_Fbot o x :
    isOrd o ->
    x ∈ Wibot o ->
    ~ x == empty.
red; intros.
apply TI_elim in H0; auto with *.
destruct H0 as (o',?,?).
unfold W_Fbot in H2.
apply W_F_elim in H2; trivial.
destruct H2 as (_,(_,?)).
rewrite H2 in H1.
symmetry in H1; apply discr_mt_couple in H1; trivial.
Qed.

Lemma Wintro_inj_bot : forall X Y x x',
  X ⊆ Wd ->
  Y ⊆ Wd ->
  x ∈ W_Fbot X ->
  x' ∈ W_Fbot Y ->
  Wintro x == Wintro x' -> x == x'.
intros X Y x x' tyf tyf' H H0 H1.
apply Wintro_inj with (4:=H) (5:=H0) (6:=H1); trivial.
 apply Wdom_cc_bot; trivial.
 apply Wdom_cc_bot; trivial.
Qed.


Lemma Wintro_typ_gen_bot : forall X x,
  X ⊆ Wd ->
  x ∈ W_Fbot X ->
  Wintro x ∈ Wd.
intros.
apply Wf_intro in H0;[|trivial].
revert H0; apply Wfbot_typ; trivial.
Qed.

Lemma W_F_Wf_iso_bot X :
  X ⊆ Wd ->
  iso_fun (W_Fbot X) (Wfb X) Wintro.
split; intros.
 apply Wintro_morph.

 red; intros.
 apply Wf_intro; trivial.

 apply Wintro_inj_bot with X X; auto.

 apply Wf_elim in H0; trivial.
 destruct H0; eauto with *.
Qed.

Lemma W_F_Wf_iso_bot' o f :
  isOrd o ->
  iso_fun (Wibot o) (TI Wfb o) f ->
  iso_fun (W_Fbot (Wibot o)) (Wfb (TI Wfb o)) (wiso B (fbot f)).
intros.
apply iso_fun_trans with (W_Fbot (TI Wfb o)).
 apply WFmap_iso; trivial.
 apply iso_cc_bot; trivial.
  intro h; apply mt_not_in_W_Fbot in h; auto with *.
  intro h; apply mt_not_in_Wfbot in h; auto with *.

 apply W_F_Wf_iso_bot.
 apply TI_Wfbot_typ; trivial.
Qed.

Lemma wisobot_ext : forall X f f',
  ~ empty ∈ X ->
  eq_fun X f f' -> eq_fun (W_Fbot X) (wiso B (fbot f)) (wiso B (fbot f')).
red; intros.
unfold wiso,comp_iso.
assert (eqbot : eq_fun (cc_bot X) (fbot f) (fbot f')).
 apply eqf_fbot; trivial.
apply Wintro_morph; trivial.
apply WFmap_ext with (A:=A); intros; trivial.
 apply W_F_elim with (2:=H1); trivial.

 rewrite H2; reflexivity.

 apply eqbot.
 apply W_F_elim with (2:=H1); trivial.

 rewrite H2; rewrite H4; reflexivity.
Qed.

Let wisobotm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) (fun f => wiso B (fbot f)).
do 3 red; intros.
apply wisom; trivial.
unfold fbot; red; intros.
apply cond_set_morph; auto.
rewrite H1; reflexivity.
Qed.

Lemma TI_W_F_Wf_iso_bot o :
  isOrd o ->
  iso_fun (Wibot o) (TI Wfb o) (TI_iso W_Fbot (fun f => wiso B (fbot f)) o).
intros.
apply TI_iso_fun; intros; auto.
 unfold W_Fbot; do 2 red; intros; apply W_F_mono; trivial.
 apply cc_bot_mono; trivial.

 apply wisobot_ext; trivial.
 intros h; apply mt_not_in_W_Fbot in h; auto with *.

 apply W_F_Wf_iso_bot'; trivial.
Qed.

  Lemma Wbot_ord_o : isOrd Wbot_ord.
apply clos_ord_o; auto with *.
Qed.
Hint Resolve Wbot_ord_o : core.

Lemma Wbot_clos_ord : closure_ordinal Wfb Wbot_ord.
apply closure_ordinal_bounded; auto with *.
Qed.
Hint Resolve Wbot_clos_ord : core.

  Lemma Wbot_fix : Wbot == W_Fbot Wbot.
unfold Wbot, Wibot.
rewrite TI_iso_fixpoint with (2:=Wfbot_mono A _ Bm) (g:=fun f => wiso B (fbot f)); auto with *.
 apply TI_closure_ordinal; auto.

 intros.
 apply wisobot_ext; trivial.
 intros h; apply mt_not_in_W_Fbot in h; auto with *.

 apply W_F_Wf_iso_bot'.
Qed.

  Lemma Wbot_stages o : isOrd o -> Wibot o ⊆ Wbot.
induction 1 using isOrd_ind; intros.
red; intros.
apply TI_elim in H2; auto with *.
destruct H2 as (o',?,?).
rewrite Wbot_fix.
revert H3; apply W_Fbot_mono; auto.
Qed.


(** * Universe facts: when A and B belong to a given (infinite) universe, then so does W(A,B). *)

Section W_Univ.

(* Universe facts *)
  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega ∈ U.  

  Hypothesis aU : A ∈ U.
  Hypothesis bU : forall a, a ∈ A -> B a ∈ U.

  Lemma G_W_Fbot X : X ∈ U -> W_Fbot X ∈ U.
intros.
unfold W_Fbot.
apply G_W_F; trivial.
apply G_union2; trivial.
apply G_singl; trivial.
apply G_incl with X; trivial.
Qed.

  Lemma G_Wbot_ord : Wbot_ord ∈ U.
apply G_clos_ord; auto.
apply G_Wdom; trivial.
Qed.

  Lemma G_Wbot : Wbot ∈ U.
apply G_TI; auto with *.
 apply G_Wbot_ord.

 apply G_W_Fbot.
Qed.

  Lemma G_Wibot o : isOrd o -> Wibot o ∈ U.
intros.
apply G_incl with Wbot; trivial.
 apply G_Wbot.    

 apply Wbot_stages; trivial.
Qed.
  
End W_Univ.

End W_theory.
