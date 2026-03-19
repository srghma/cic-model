Require Import ZF Zpairs Zsum Znats Zrelations Ztarski Zstable.
Require Import ZFgrothendieck.
Require Import Zcoc.
Require Import ZFwfr ZFord.
Require Import ZFfix.
Require Import ZFfixfun.
Require ZFwdom.
Require Zw.
Existing Instance Zwdom.Wf_mono.
Existing Instance Zwdom.Wfbot_mono.

Include Zw.

Section W.

(* The first parameter of W-types (aka the payload) *)
Variable A : set.
(* The subterm index type *)
Variable B : set -> set.
Hypothesis Bm : morph1 B.

Notation Wdom := (Zwdom.Wdom A B).
Notation Wf := (Zwdom.Wf A B).
Notation Wsup := Zwdom.Wsup.
Notation Wfst := Zwdom.Wfst.
Notation Wsnd_fun := Zwdom.Wsnd_fun.


Notation W := (Zw.W A B).
Notation Wfbot := (Zw.Wfbot A B).
Notation Wbot := (Zw.Wbot A B).

(*******************************************************************************************)
Section FixpointByIteration.
  
(* Relating W with the iteration of a monotonic operator. We show there exists an ordinal
   for which the sequence reaches the fixpoint W.
   We introduce notion of subterm as an auxiliary tool to defining the recursor. *)

  Lemma Wf_stable_stages : stable_set (power (Fstages Wf Wdom)) Wf.
red; intros; apply Zwdom.Wf_stable; trivial.
rewrite H; apply power_mono.
apply Fstages_inA.
Qed.
Hint Resolve Wf_stable_stages : core.

  Definition W_ord := clos_ord Wf Wdom.

  Lemma W_ord_o : isOrd W_ord.
apply clos_ord_o; auto.
Qed.
Hint Resolve W_ord_o : core.

  Lemma W_ord_clos : closure_ordinal Wf W_ord.
apply closure_ordinal_bounded; auto.
Qed.

Definition Wi := TI Wf.

Lemma Wi_typ o : isOrd o -> Wi o ⊆ Wdom.
intros oo.
apply TI_pre_fix; auto.
apply Zwdom.Wf_typ; [trivial| reflexivity].
Qed.

Lemma Wi_W o : isOrd o -> Wi o ⊆ W.
intros.
apply TI_pre_fix; auto with *.
rewrite <- W_eqn; auto with *.
Qed.
  
  Lemma W_post : W ⊆ Wi W_ord.
apply W_least; [trivial|].
rewrite <- TI_mono_succ; auto.
apply W_ord_clos; auto.
Qed.

  Lemma W_clos : W == Wi W_ord.
apply incl_eq.
 red; intros; apply W_post; trivial.

 apply Wi_W; trivial.
Qed.

(** With bottom *)

Lemma Wfbot_stable_set :
  stable_set (power (Wfbot Wdom)) Wfbot.
red; intros; apply ZFwdom.Wfbot_stable_set; trivial.
rewrite H; clear X H.
red; intros.
rewrite power_def in H.
apply subset_intro.
+apply power_def; rewrite H.
 apply Wfbot_typ; auto with *.
+intros.
 apply H in H0.
 right; intro eqz; rewrite eqz in H0.
 apply Zwdom.mt_not_in_Wf in H0; trivial.
Qed.

Hint Resolve Wfbot_mono Wfbot_typ : core.
Lemma Wfbot_stable_stages :
  stable_set (power (Fstages Wfbot Wdom)) Wfbot.
red; intros; apply  ZFwdom.Wfbot_stable_set; intros; trivial.
rewrite H; clear X H.
red; intros.
rewrite power_def in H.
apply subset_intro.
*apply power_def; rewrite H.
 apply Fstages_inA.
*intros.
 apply H in H0.
 apply Fstages_def in H0; auto.
 destruct H0 as (o,oo,mt).
 apply ZFwdom.mt_not_in_Wfbot in mt; auto with *.
Qed.

Hint Resolve Wfbot_stable_stages : core.

  Definition Wbot_ord := clos_ord Wfbot Wdom.

  Lemma Wbot_ord_o : isOrd Wbot_ord.
apply clos_ord_o; auto.
Qed.
  Hint Resolve Wbot_ord_o : core.

  Lemma Wbot_ord_clos : closure_ordinal Wfbot Wbot_ord.
apply closure_ordinal_bounded; auto with *.
Qed.

  Definition Wbi := TI Wfbot.

Lemma Wbi_typ o : isOrd o -> Wbi o ⊆ Wdom.
intros oo.
apply TI_pre_fix; auto with *.
Qed.

Lemma Wbi_Wbot o : isOrd o -> Wbi o ⊆ Wbot.
intros.
apply TI_pre_fix; auto with *.
rewrite <- Wbot_eqn; trivial; reflexivity.
Qed.
  
  Lemma Wbot_post : Wbot ⊆ Wbi Wbot_ord.
apply Wbot_least; trivial.
rewrite <- TI_mono_succ; auto.
apply Wbot_ord_clos; auto.
Qed.

  Lemma Wbot_clos : Wbot == Wbi Wbot_ord.
apply incl_eq.
 red; intros; apply Wbot_post; trivial.

 apply Wbi_Wbot; trivial.
Qed.

  
End FixpointByIteration.



(*******************************************************************************************)
(* Universe facts *)

Section W_Univ.

  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : N ∈ U.  

  Hypothesis aU : A ∈ U.
  Hypothesis bU : forall a, a ∈ A -> B a ∈ U.

  Let Gdom : Wdom ∈ U.
apply ZFwdom.G_Wdom; auto.
Qed.

  Lemma G_W : W ∈ U.
apply G_incl with Wdom; trivial.
apply W_typ; trivial.
Qed.

  Lemma G_Wi o : isOrd o -> Wi o ∈ U.
intros oo.
apply G_incl with Wdom; trivial.
apply Wi_typ; trivial.
Qed.

End W_Univ.
(*
Class subtermClass (K:set->Prop) :=
  { Kinter : forall X,
      (exists z0, z0 ∈ X) ->
      (forall z, z ∈ X -> K z) ->
      K (inter X);
    Ksup : forall I X,
      ext_fun I X ->
      (forall i, i ∈ I -> K (X i)) ->
      K (sup I X);
    KW : forall X, K X -> X ⊆ W;
    KWtop : K W;
    Kintro : forall X, K X -> K (Wf X);
    Ktrans : forall X, K X -> X ⊆ Wf X }.
(* TODO
Hypothesis Kstage : forall w w',
   (forall X, K X -> w ∈ Wf X -> w' ∈ Wf X) ->
   forall X, K X -> w ∈ X -> w' ∈ X.
*)

Instance subsets_subtermClass : subtermClass (fun X => X ⊆ Wf X /\ X ⊆ W).
split; intros.
+split.
 {red; intros.
  apply Wf_stable; trivial.
  *red; intros.
   apply H0 in H2.
   apply power_def; apply H2.
  *apply inter_intro.
   intros.
   rewrite replf_ax in H2; auto.
   destruct H2 as (x,?,(_,?)).   
   rewrite H3.
   apply H0; trivial.
   apply inter_elim with (1:=H1); trivial.

   apply inter_non_empty in H1.
   destruct H1 as (w,?,?); exists (Wf w).
   rewrite replf_ax; auto.
   exists w; auto with *. }
 {red; intros.
  destruct inter_non_empty with (1:=H1) as (w,?,?).
  apply (H0 w); trivial. }
+split.
 {apply sup_lub; intros; trivial.
  destruct (H0 y) as (h,_); trivial.
  rewrite h.
  apply Zwdom.Wf_mono; auto. }
 {apply sup_lub; intros; trivial.
  apply (H0 y); trivial. }
+apply H.
+split;[|reflexivity].
 rewrite <- W_eqn; trivial; reflexivity.
+destruct H; split.
 apply Zwdom.Wf_mono; auto.
 rewrite W_eqn; trivial; apply Zwdom.Wf_mono; auto.
+apply H.
Qed.

Variable K : set -> Prop.
Hypothesis Km : Proper (eq_set==>iff) K.
Hypothesis Ksc : subtermClass K.

Hint Resolve KW Ktrans : core.
Let KW' := KW. 

Definition fsub w :=
  inter (subset (power W) (fun Z => K Z /\ w ∈ Wf Z)).

Instance fsub_morph : morph1 fsub.
do 2 red; intros.
unfold fsub.
apply inter_morph.
apply subset_morph; auto with *.
red; intros.
rewrite H; reflexivity.
Qed.
  
Lemma fsub_intro w w' :
  w ∈ W ->
  (forall X, K X -> w ∈ Wf X -> w' ∈ X) ->
  w' ∈ fsub w.
intros.
apply inter_intro; intros.
 apply subset_ax in H1.
 destruct H1 as (_,(y',eqy,(Ky,wy))).
 rewrite <- eqy in wy,Ky; auto.

 exists W.
 apply subset_intro.
  apply power_intro; trivial.
  split; [apply KWtop|].
  rewrite <- W_eqn; trivial.
Qed.

Lemma fsub_elim X x y :
  K X ->
  y ∈ Wf X ->
  x ∈ fsub y ->
  x ∈ X.
intros KX tyy xsub.
apply inter_elim with (1:=xsub).
apply subset_intro; auto.
apply power_intro; apply KW; trivial.
Qed.

Lemma Kfsub w :
  w ∈ W ->
  K (fsub w).
intros tyw.
apply Kinter.
 exists W.
 apply subset_intro; auto.
  apply power_intro; trivial.

  split; [apply KWtop|].
  rewrite <- W_eqn; trivial.

 intros.
 apply subset_elim2 in H.
 destruct H as (z',eqz,(?,_)).
 rewrite eqz; trivial.
Qed.


Definition fsub' w :=
  inter (subset (power W) (fun Z => K Z /\ w ∈ Z)).

Instance fsub'_morph : morph1 fsub'.
do 2 red; intros.
unfold fsub'.
apply inter_morph.
apply subset_morph; auto with *.
red; intros.
rewrite H; reflexivity.
Qed.

Lemma fsub'_intro w w' :
  w ∈ W ->
  (forall X, K X -> w ∈ X -> w' ∈ X) ->
  w' ∈ fsub' w.
intros.
apply inter_intro; intros.
 apply subset_ax in H1.
 destruct H1 as (_,(y',eqy,(Ky,wy))).
 rewrite <- eqy in wy,Ky; auto.

 exists W.
 apply subset_intro; auto.
 apply power_intro; trivial.
 split ;trivial.
 apply KWtop.
Qed.

Lemma fsub'_elim X x y :
  K X ->
  y ∈ X ->
  x ∈ fsub' y ->
  x ∈ X.
intros KX tyy xsub.
apply inter_elim with (1:=xsub).
apply subset_intro; auto.
apply power_intro; apply KW; trivial.
Qed.

Lemma Kfsub' w :
  w ∈ W ->
  K (fsub' w).
intros tyw.
apply Kinter.
 exists W.
 apply subset_intro; auto.
 apply power_intro; trivial.

 split ;trivial.
 apply KWtop.
 
 intros.
 apply subset_elim2 in H.
 destruct H as (z',eqz,(?,_)).
 rewrite eqz; trivial.
Qed.

Lemma fsub_elim' w x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  w ∈ fsub (Wsup x f) ->
  exists2 i, i ∈ B x & w ∈ fsub' (cc_app f i).
intros tyx tyf tyw.
pose (X := sup (B x) (fun i => fsub' (cc_app f i))).
assert (w ∈ X).
{apply fsub_elim with (3:=tyw). 
  apply Ksup.
   intros i i' tyi eqi; rewrite eqi; reflexivity.

   intros.
   apply Kfsub'.
   apply cc_prod_elim with (1:=tyf); trivial.

  apply Zwdom.Wf_intro; trivial.
  rewrite cc_eta_eq with (1:=tyf).
  apply cc_prod_intro; intros; auto.
   intros ? ? ? ?; apply cc_app_morph; trivial; reflexivity.

   unfold X; rewrite sup_def.
   2:intros i i' tyi eqi; rewrite eqi; reflexivity.
   exists x0; trivial.
   apply fsub'_intro; trivial.
   apply cc_prod_elim with (1:=tyf); trivial. }
unfold X in H; rewrite sup_ax in H.
destruct H as (?,?,(_,?)); eauto.
Qed.

Lemma fsub_Wf_intro w :
   w ∈ W ->
   w ∈ Wf (fsub w).
intros.
rewrite W_eqn in H; trivial.
apply Zwdom.Wf_elim in H.
destruct H as (x,tyx,(f,tyf,eqw)).
rewrite eqw; apply Zwdom.Wf_intro; trivial.
rewrite cc_eta_eq with (1:=tyf).
apply cc_prod_intro; auto.
 do 2 red; intros; apply cc_app_morph; auto with *.
intros.
apply fsub_intro.
*rewrite W_eqn; trivial; apply Zwdom.Wf_intro; trivial.
*intros.
 apply Zwdom.Wf_elim' with (5:=H1); auto.
 +intros; apply Zwdom.cc_prod_Wfun with (1:=W_typ _ _ Bm)(2:=tyf).
 +rewrite <-W_typ; auto.
 Qed.

Lemma fsub'fsub w0 w1 :
  w0 ∈ W ->
  w1 ∈ fsub' w0 ->
  w1 ∈ Wf (fsub w0).
intros.   
apply fsub'_elim with (3:=H0).
 apply Kintro.
 apply Kfsub; trivial.

 apply fsub_Wf_intro; trivial.
Qed.

Lemma fsub_fsub'_trans w0 w1 w2 :
  w0 ∈ W ->
  w1 ∈ fsub' w0 ->
  w2 ∈ fsub w1 ->
  w2 ∈ fsub w0.
intros.  
apply fsub_elim with (3:=H1).
 apply Kfsub; trivial.

 apply fsub'fsub; trivial.
Qed.

(*******************************************************************************************)
Section TransitiveRecursor.

Variable O : set.
Hypothesis KO : K O.

Variable P : set -> set -> set.
Hypothesis Pm : morph2 P.
Hypothesis Pmono : forall X Y x,
  K Y ->
  (forall w, w ∈ X -> exists2 w', w' ∈ Y &(* w ∈ fsub w') ->*)
   forall X, K X -> w' ∈ Wf X -> w ∈ X) ->
  P (Wf X) x ⊆ P Y x.

Variable F : set -> set -> set -> set.
Hypothesis Fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) F.
Hypothesis f_typ : forall X x recf,
  X ⊆ O ->
  K X ->
  x ∈ Wf X ->
  recf ∈ (Π w ∈ X, P X w) ->
  F X recf x ∈ P (Wf X) x.
Hypothesis Firr : forall X X' recf recf',
  X ⊆ O ->
  K X ->
  X' ⊆ O ->
  K X' ->
  recf ∈ (Π w ∈ X, P X w) ->
  recf' ∈ (Π w ∈ X', P X' w) ->
  (forall x, x ∈ X -> x ∈ X' -> cc_app recf x == cc_app recf' x) ->
  forall x, x ∈ Wf X -> x ∈ Wf X' -> F X recf x == F X' recf' x.

(*Require Import ZFlimit.*)


Let R w w' := w ∈ fsub w'.
Let Rm : Proper (eq_set==>eq_set==>iff) R.
unfold R; do 3 red; intros.
rewrite H,H0; reflexivity.
Qed.

Let G f w :=
  F (fsub w) (cc_lam (fsub w) f) w.
Let Gm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) G.
unfold G; do 3 red; intros.
apply Fm; trivial.
 apply fsub_morph; trivial.

 apply cc_lam_ext.
  apply fsub_morph; trivial.

  red; intros;auto.
Qed.  
Hint Resolve Rm Gm : core.

Let Gext x x' f f' :
  x==x' ->
  (forall y y', R y x -> y == y' -> f y == f' y') ->
  G f x == G f' x'.
intros.
unfold G.
apply Fm; [rewrite H;reflexivity| |trivial].
apply cc_lam_ext; auto with *.
rewrite H; reflexivity.
Qed.

     
Definition WSREC' := WFR fsub G.

Global Instance WSREC'_morph0 : morph1 WSREC'.
apply WFR_morph0.
Qed.


Lemma Wacc w :
  w ∈ W ->
  forall w', w' ∈ fsub' w ->
  Acc R w'.
intros tyw.
elim tyw using W_ind; intros; trivial.
*do 2 red; intros.
 apply fa_morph; intros w'.
 rewrite H; reflexivity.
*constructor; intros.
 red in H3.
 assert (y ∈ fsub (Wsup x f)).
 {apply fsub_fsub'_trans with w'; trivial.
  rewrite W_eqn; trivial; apply Zwdom.Wf_intro; trivial. }
 destruct fsub_elim' with (3:=H4) as (i,tyi,?); eauto.
Qed.

Let Oacc w :
  w ∈ O ->
  Acc R w.
intros.
apply KW' in H; trivial.  
apply Wacc with w; trivial.
apply fsub'_intro; auto.
Qed.
Hint Resolve Gext Oacc : core.

Lemma WSREC_eqn0' w :
  w ∈ O ->
  WSREC' w == F (fsub w) (λ w ∈ fsub w, WSREC' w) w.
intros; unfold WSREC' at 1.
apply WFR_eqn; auto with *.
Qed.

Lemma Pmono' x y :
  y ∈ W ->
  x ∈ fsub y ->    
  P (Wf (fsub x)) x ⊆ P (fsub y) x.
intros.
apply Pmono.
 apply Kfsub; auto.

 intros.
 exists x; trivial.
 intros.
 apply fsub_elim with (3:=H1); trivial.
Qed.


  Lemma WSREC_typ0' w :
  w ∈ O ->
  WSREC' w ∈ P (Wf (fsub w)) w.
intros; unfold WSREC'.
generalize H; eapply WFR_ind with (xx:=w); intros; auto with *.
*do 3 red; intros.
 rewrite H0,H1; reflexivity.
*apply f_typ.
 +red; intros.
  apply fsub_elim with (3:=H3); auto.
  apply Ktrans; auto.

 +apply Kfsub; auto.
  apply KW' in H2; trivial.

 +apply fsub_Wf_intro; auto.
  apply KW' in H2; trivial.

 +apply cc_prod_intro; intros.
   do 2 red; intros; apply WSREC'_morph0; trivial.
   do 2 red; intros; apply Pm; auto with *.
  apply Pmono'; trivial.
   apply KW' in H2; trivial.

   apply H1; trivial.
   apply (Ktrans _ KO) in H2; trivial.
   apply fsub_elim with (3:=H3); trivial.
Qed.

Lemma WSREC_typ' w :
  w ∈ O -> 
  WSREC' w ∈ P O w.
intros tyw.
eapply Pmono; auto.
2:apply WSREC_typ0'; trivial.
intros; exists w; trivial.
intros.
apply fsub_elim with (3:=H); trivial.
Qed.

Lemma WSREC_eqn' w :
  w ∈ O ->
  WSREC' w == F O (λ w ∈ O, WSREC' w) w.
intros.
rewrite WSREC_eqn0'; trivial.
assert (wO : w ∈ Wf O).
 apply Ktrans; trivial.
apply Firr; auto with *.
 red; intros.
 apply fsub_elim with (3:=H0); trivial.

 apply Kfsub; auto.
 apply KW with (X:=O); trivial. 

 apply cc_prod_intro.
  do 2 red; intros; apply WSREC'_morph0; trivial.
  do 2 red; intros; apply Pm; auto with *.
 intros.
 apply Pmono'; trivial.
  apply KW' in H; trivial.
 apply WSREC_typ0'; trivial.
 apply fsub_elim with (3:=H0); trivial.

 apply cc_prod_intro.
  do 2 red; intros; apply WSREC'_morph0; trivial.
  do 2 red; intros; apply Pm; auto with *.
 intros.
 eapply Pmono; trivial.
 2:apply WSREC_typ0'; trivial.
 intros.
 exists x; trivial.
 intros. 
 apply fsub_elim with (3:=H1); trivial.

 intros.
 rewrite cc_beta_eq; trivial.
  rewrite cc_beta_eq; trivial.
   reflexivity.

   do 2 red; intros; apply WSREC'_morph0; trivial.
  do 2 red; intros; apply WSREC'_morph0; trivial.

 apply fsub_Wf_intro.
 apply KW with (X:=O); trivial. 
Qed.

Lemma WSREC_eqn2' X x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, X) ->
  Wf X ⊆ O ->
  WSREC' (Wsup x f) == F O (λ w ∈ O, WSREC' w) (Wsup x f).
intros tya tyf inclO.
apply WSREC_eqn'.
apply inclO.
apply Zwdom.Wf_intro; auto.
Qed.

End TransitiveRecursor.
*)
End W.

#[global]Hint Resolve W_ord_o : core.
#[global]Hint Resolve Wbot_ord_o : core.


Local Notation E := eq_set (only parsing).

Lemma W_ord_morph : Proper (E==>(E==>E)==>E) W_ord.
do 3 red; intros.
unfold W_ord.  
apply clos_ord_morph.
 red; intros.
 apply Zwdom.Wf_morph_gen; trivial.

 apply Zwdom.Wdom_morph; trivial.
Qed.

(*Lemma fsub_ext A A' B B' K K' :
  A==A' ->
  eq_fun A B B' ->
  (forall X, X ⊆ W A B -> (K X <-> K' X)) ->
  (E==>E)%signature (fsub A B K) (fsub A' B' K').
red; intros; unfold fsub.
apply inter_morph; apply subset_morph.
 apply power_morph; apply W_ext; trivial.

 red; intros.
 rewrite power_ax in H3.
 apply and_iff_morphism; auto with *.
 apply in_set_morph; trivial.
 apply Zwdom.Wf_ext; auto with *.
Qed.
Instance fsub_morph_gen :
  Proper (E==>(E==>E)==>(E==>iff)==>E==>E) fsub.
do 5 red; intros; unfold fsub.
apply inter_morph; apply subset_morph.
 apply power_morph; apply W_morph; trivial.

 red; intros.
 apply and_iff_morphism; auto with *.
 apply in_set_morph; trivial.
 apply Zwdom.Wf_morph_gen; auto with *.
Qed.

Instance WSREC'_morph_gen :
  Proper (E==>(E==>E)==>(E==>iff)==>(E==>E==>E==>E)==>E==>E)
  WSREC'.
do 6 red; intros.
unfold WSREC'.
apply WFR_morph; trivial.
 apply fsub_morph_gen; trivial.

 do 2 red; intros.
 apply H2; trivial.
  apply fsub_morph_gen; trivial.

  apply cc_lam_ext.
   apply fsub_morph_gen; trivial.

   red; intros; auto.
Qed.
*)
