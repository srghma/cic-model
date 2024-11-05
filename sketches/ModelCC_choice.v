Require Import basic.
Require Import Sublogic.
Require Import ZF ZFrelations ZFcoc ModelZF.
Require Import ModelCC.
Require Import ZFrepl.

Module TypChoice (C : Choice_Sig CoqSublogicThms IZF_Axioms).

Import C.
Import BuildModel.
Import CCM.
Import T J R.

Definition CH_spec a f1 f2 z :=
     a == empty /\ z == app f2 (lam empty (fun _ => empty))
  \/ (exists w, w ∈ a) /\ z == app f1 (choose a).

Lemma CH_spec_morph : Proper (eq_set==>eq_set==>eq_set==>eq_set==>iff) CH_spec.
do 5 red; intros.
unfold CH_spec.
apply or_iff_morphism.
 rewrite H,H1,H2; reflexivity.
apply and_iff_morphism.
 apply ex_iff_morphism.
 red; intros.
 rewrite H; reflexivity.

 apply eq_set_morph; trivial.
 apply cc_app_morph; trivial.
 apply choose_morph; trivial.
Qed.
 
Parameter CH_spec_u : forall a f1 f2, uchoice_pred (CH_spec a f1 f2).

Definition CH : term.
left; exists (fun i => uchoice (CH_spec (i 3) (i 1) (i 0))).
do 2 red; intros.
apply uchoice_morph.
 apply CH_spec_u.
 intros.
 apply CH_spec_morph; auto with *.
  apply H.
  apply H.
  apply H.
Defined.

(* forall X, X + (X->False) is inhabited *)
#[local]Lemma typ_choice :
  typ
    ((*f1*)Prod (Prod (*X*)(Ref 2) (Prod prop (Ref 0))) (*P*)(Ref 2) ::
     (*f2*)Prod (*X*)(Ref 1) (*P*)(Ref 1) ::
     (*P*)kind::(*X*)kind::nil)
    CH (*P*)(Ref 2).
red; simpl; intros.
generalize (H 0 _ (eq_refl _)); simpl; unfold V.lams, V.shift; simpl; intros.
generalize (H 1 _ (eq_refl _)); simpl; unfold V.lams, V.shift; simpl; intros.
clear H.
set (P := i 2) in *; clearbody P.
set (Y := i 3) in *; clearbody Y.
generalize (uchoice_def _ (CH_spec_u Y (i 1) (i 0))).
set (w := uchoice (CH_spec Y (i 1) (i 0))) .
clearbody w; unfold CH_spec; intros.
destruct H.
 destruct H.
 rewrite H2.
 refine (prod_elim _ _ _ _ _ H0 _).
  admit.
 apply eq_elim with (prod empty (fun _ => prod props (fun P=>P))).
  apply prod_ext.
   auto with *.

   red; reflexivity.
 apply prod_intro; intros.
  admit.
  admit.
 elim empty_ax with x; trivial.

 destruct H.
 rewrite H2.
 refine (prod_elim _ _ _ _ _ H1 _).
  admit.
 apply choose_ax; trivial.
Admitted. (* typ_choice hidden *)

End TypChoice.
