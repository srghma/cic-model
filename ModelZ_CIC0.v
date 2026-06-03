(** Model construction (entailing consistency) for CIC0 (without
    universes) based on Zermelo set theory.
    All inductive definitions land in kind.
    NB: we should check that we only use bounded quantifications...
*)

From Stdlib Require Import List Bool.
Require Import Models TypModels.
Require Import ZF Zsum Znats Zrelations Zuniv Zcoc Zw.
Require Import ModelCC.

Import BuildModel.
Import T J R.

(** W *)

Definition W (A B:term) : term.
(*begin show*)
left; exists (fun i => Zw.W (int A i) (int1 B i)).
(*end show*)
do 3 red; intros.
apply W_morph.
*apply int_morph; trivial.
 reflexivity.
*red; intros.
 apply int1_morph; [reflexivity|trivial|trivial].
Defined.

Lemma typ_WI e A B :
  typ e (W A B) kind.
red; simpl; trivial.
Qed.

Definition Wc (x f:term) : term.
(* begin show *)
left; exists (fun i => Zwdom.Wsup (int x i) (int f i)).
(* end show *)
do 2 red; intros; apply Zwdom.Wsup_morph; apply int_morph; auto with *.
Defined.

Lemma typ_Wc e A B X F :
  A <> kind ->
  typ e X A ->
  typ e F (Prod (subst X B) (lift 1 (W A B))) ->
  typ e (Wc X F) (W A B).
intros Ank.
red; intros.
red in H; specialize H with (1:=H1).
apply in_int_not_kind in H; trivial.
red in H0; specialize H0 with (1:=H1).
rewrite in_int_not_kind in H0.
2:discriminate.
rewrite int_Prod_arr in H0.
apply in_int_not_kind; [discriminate|].
red; simpl.
apply Wsup_typ; auto with *.
change (int F i ∈ cc_arr (int(subst X B) i) (int (W A B) i)) in H0.
rewrite int_subst_eq in H0; trivial.
Qed.

(* Eliminator *)

Definition W_rect (A B P F w : term) : term.
(*begin show*)
left; exists (fun i => WREC (int A i) (int1 B i) (cc_app (int P i))
                         (fun x f Hrec => cc_app (cc_app (cc_app (int F i) x) f) Hrec)
                         (int w i)).
(*end show*)
do 3 red; intros.
apply WREC_morph_gen; auto with *.
*apply int_morph; trivial.
 reflexivity.
*red; intros.
 apply int1_morph; trivial.
 reflexivity.
*red; intros.
 rewrite H,H0; reflexivity.
*do 3 red; intros.
 rewrite H,H0,H1,H2; reflexivity.
*apply int_morph; auto with *.
Defined.

#[global]Instance W_rect_morph :
  Proper (eq_term ==> eq_term ==> eq_term ==> eq_term ==> eq_term ==> eq_term) W_rect.
do 6 red; simpl; intros.
red; intros.
apply WREC_morph_gen; auto with *.
*apply int_morph; trivial.
*red; intros.
 apply int1_morph; trivial.
*red; intros.
 rewrite H1,H4,H5; reflexivity.
*do 3 red; intros.
 rewrite H2,H4,H5,H6,H7; reflexivity.
*apply int_morph; auto with *.
Qed.

(* The type of the constructor branch of W_rect:
   forall (x:A) (f:B x->W A B), (forall i:B x, P (f i)) -> P (Wc x f)
*)
Definition W_rect_case A B P :=
  Prod A (Prod (Prod B (lift 2 (W A B))) (Prod
    (Prod (lift 1 B) (App (lift 3 P) (App (Ref 1) (Ref 0))))
    (App (lift 3 P) (Wc (Ref 2) (Ref 1))))).

Lemma W_rect_typ e A B P G w :
    typ e G (W_rect_case A B P) ->
    typ e w (W A B) ->
    typ e (W_rect A B P G w) (App P w).
intros tyG tyw.
red; intros.
rewrite in_int_not_kind; [|discriminate].
simpl.
apply WREC_typ.
*apply int1_morph; reflexivity.
*apply cc_app_morph; reflexivity.
*do 4 red; intros.
 rewrite H0,H1,H2; reflexivity.
*intros x f recf tyx tyf tyrecf.
 red in tyG; specialize tyG with (1:=H).
 rewrite in_int_not_kind in tyG; [|discriminate].
 apply cc_prod_elim  with (x:=x) in tyG; [|trivial].
 apply cc_prod_elim  with (x:=f) in tyG.
 2:{simpl.
    revert tyf; apply eq_elim; apply cc_prod_ext; [reflexivity|].
    red; intros.
    unfold int1; simpl.
    apply W_morph.
    *rewrite V.lams0; reflexivity.
    *red; intros.
     rewrite H2, V.lams0; reflexivity. }
 apply cc_prod_elim  with (x:=recf) in tyG.
 2:{simpl.
    revert tyrecf; apply eq_elim; apply cc_prod_ext.
    *rewrite simpl_int_lift1; reflexivity.
    *red; intros.
     unfold int1; simpl.
     unfold lift; rewrite int_lift_rec_eq, V.lams0.
     unfold V.shift; simpl.
     rewrite H1; reflexivity. }
 revert tyG; apply eq_elim.
 simpl.
 unfold lift; rewrite int_lift_rec_eq, V.lams0.
 unfold V.shift; simpl.
 reflexivity.
*apply tyw in H.
 rewrite in_int_not_kind in H; [trivial|discriminate].
Qed.

  
Lemma W_rect_iota e A B P X F G :
    A <> kind ->
    typ e X A ->
    typ e F (Prod (subst X B) (lift 1 (W A B))) ->
    typ e G (W_rect_case A B P) ->
    eq_typ e (W_rect A B P G (Wc X F))
      (App (App (App G X) F)
         (Abs (subst X B) (W_rect (lift 1 A) (lift1 1 B) (lift 1 P) (lift 1 G) (App (lift 1 F) (Ref 0))))).
Proof.
intros Ank tyX tyF tyG.
red; intros.
simpl.
unfold ModelZ.CCM.lam, ModelZ.CCM.app.
rewrite WREC_eqn; auto.
*apply cc_app_morph;[reflexivity|].
 apply cc_lam_morph; [rewrite int_subst_eq; reflexivity|].
 red; intros.
 apply WREC_morph_gen.
 +rewrite simpl_int_lift1; reflexivity.
 +red; intros.
  unfold int1; rewrite simpl_lift1.
  unfold lift1, lift; rewrite int_lift_rec_eq.
  apply int_morph; [reflexivity|].
  intros [|k]; unfold V.lams; simpl; trivial.
  replace (k-0) with k by auto with arith.
  reflexivity.
 +red; intros.
  rewrite simpl_int_lift1, H1; reflexivity.
 +do 3 red; intros.
  rewrite simpl_int_lift1, H1, H2, H3; reflexivity.
 +simpl; rewrite simpl_int_lift1, H0; reflexivity.
*apply int1_morph; reflexivity.
*apply cc_app_morph; reflexivity.
*do 4 red; intros.
 rewrite H0,H1,H2; reflexivity.
*intros.
 red in tyG; specialize tyG with (1:=H).
 rewrite in_int_not_kind in tyG; [|discriminate].
 apply cc_prod_elim  with (x:=x) in tyG; [|trivial].
 apply cc_prod_elim  with (x:=f) in tyG.
 2:{simpl.
    revert H1; apply eq_elim; apply cc_prod_ext; [reflexivity|].
    red; intros.
    unfold int1; simpl.
    apply W_morph.
    *rewrite V.lams0; reflexivity.
    *red; intros.
     rewrite H4, V.lams0; reflexivity. }
 apply cc_prod_elim  with (x:=recf) in tyG.
 2:{simpl.
    revert H2; apply eq_elim; apply cc_prod_ext.
    *rewrite simpl_int_lift1; reflexivity.
    *red; intros.
     unfold int1; simpl.
     unfold lift; rewrite int_lift_rec_eq, V.lams0.
     unfold V.shift; simpl.
     rewrite H3; reflexivity. }
 revert tyG; apply eq_elim.
 simpl.
 unfold lift; rewrite int_lift_rec_eq, V.lams0.
 unfold V.shift; simpl.
 reflexivity.
*apply tyX in H.
 rewrite in_int_not_kind in H; trivial.
*red in tyF; specialize tyF with (1:=H).
 rewrite in_int_not_kind in tyF; [|discriminate].
 rewrite int_Prod_arr in tyF.
 revert tyF; apply eq_elim.
 apply cc_prod_morph.
 +apply int_subst_eq.
 +red; simpl; intros; reflexivity.
Qed.

