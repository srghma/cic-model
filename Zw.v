Require Import ZF Zpairs Zsum Znats Zrelations Ztarski Zfix.
Require Import Zstable.
Require Import Zuniv.
Require Import Zcoc.
Require Zwdom.

Existing Instance Zwdom.Wf_mono.
Existing Instance Zwdom.Wfbot_mono.


Lemma inter_wit' X F x :
  x ∈ inter (replf X F) ->
  exists2 w, w ∈ X & x ∈ F w.
intros.
destruct inter_non_empty with (1:=H).
rewrite replf_ax in H0.
destruct H0 as (y,?,(_,?)).
rewrite H2 in H1; eauto.
Qed.
            
Lemma stable_set2 K F X Y :
  stable_set K F ->
  X ∈ K ->
  Y ∈ K ->
  extf F X ∩ extf F Y ⊆ F (X ∩ Y).
intros Fs KX KY z h.
apply Fs; auto.
*red; intros.
 apply pair_ax in H; destruct H as [H|H]; rewrite H;trivial.
*assert (replf (pair X Y) F == pair(extf F X)(extf F Y)).
 {apply eq_set_ax; intros w.
  rewrite replf_ax.
  rewrite pair_ax.
  apply inter2_def in h; destruct h as (h1,h2).
  apply extf_def in h1,h2.
  destruct h1 as (_,h1); destruct h2 as (_,h2).
  rewrite !extf_ok; trivial.
  split.
  *intros (x,tyx,(ef,eqw)); rewrite eqw.
   rewrite pair_ax in tyx; destruct tyx as [tyx|tyx];
     apply ef in tyx; auto.
  *destruct 1; eauto. }
 rewrite H; trivial.
Qed.


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

(*******************************************************************************************)
(** * Definition and properties of the W-type operator *)

Section ImpredicativeFixpoint.

(* Using the impredicative construction of the fixpoint of a monotonic
   operator (Tarski), we get the type W. *)
Definition W := FIX incl_set inter Wdom (power Wdom) Wf.

Lemma W_lfp : is_lfp incl_set Wf W. 
apply knaster_tarski; auto with *.
Qed.

Lemma W_eqn : W == Wf W.
symmetry; apply W_lfp.
Qed.

Lemma W_least X : Wf X ⊆ X -> W ⊆ X.
apply W_lfp.
Qed.

Lemma W_typ : W ⊆ Wdom.
apply FIX_typ; auto with *.
Qed.

Lemma W_ind : forall (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  (forall x f, x ∈ A -> f ∈ (Π i ∈ B x, W) ->
   (forall i, i ∈ B x -> P (cc_app f i)) ->
   P (Wsup x f)) ->
  forall a, a ∈ W -> P a.
intros.
cut (W ⊆ subset W P).
 intros inclW; apply inclW in H1.
 apply subset_elim2 in H1; destruct H1 as (a',eqa,?).
 rewrite eqa; trivial.
apply W_least.
assert (subset W P ⊆ W).
 intro; apply subset_elim1.
assert (Wf (subset W P) ⊆ W).
 transitivity (Wf W).
  apply Zwdom.Wf_mono; trivial.
  rewrite <- W_eqn; reflexivity. 
intros z tyz.
apply subset_intro; auto.
apply Zwdom.Wf_elim in tyz; destruct tyz as (x,tyx,(f,tyf,eqz)).
rewrite eqz.
apply H0; trivial.
 revert tyf; apply cc_prod_covariant; auto with *.

 intros.
 apply cc_prod_elim with (2:=H4) in tyf.
 apply subset_elim2 in tyf; destruct tyf as (y,?,?).
 rewrite H5; trivial.
Qed.


Lemma Wsup_typ x f :
  x ∈ A ->
  f ∈ (Π __ ∈ B x, W) ->
  Wsup x f ∈ W.
intros.
rewrite W_eqn.
apply Zwdom.Wf_intro; trivial.
Qed.

Lemma Wfst_typ w :
  w ∈ W ->
  Wfst w ∈ A.
intros tyw.
rewrite W_eqn in tyw; trivial.
apply Zwdom.Wfst_typ_gen in tyw; trivial.
Qed.

Lemma Wsnd_fun_typ w :
  w ∈ W ->
  Wsnd_fun w ∈ Π __ ∈ B (Wfst w), W.
intros tyw.
rewrite W_eqn in tyw.
apply Zwdom.Wsnd_fun_typ_gen with (3:=tyw); trivial.
apply W_typ.
Qed.

Lemma Wsnd_fun_def Y x f :
  f ∈ (Π i ∈ Y, W) ->
  Wsnd_fun (Wsup x f) == f.
intros.
apply Zwdom.Wsnd_fun_Wsup.
eapply Zwdom.cc_prod_Wfun with (2:=H); apply W_typ.
Qed.

Lemma Wf_stable :
  stable_set (power W) Wf.
red; intros.
apply Zwdom.Wf_stable; auto.  
red; intros; apply H in H0.
revert H0; apply power_mono; apply W_typ.
Qed.
            
Lemma Wf_inter2 X Y:
  X ⊆ W ->
  Y ⊆ W ->
  Wf (X ∩ Y) == Wf X ∩ Wf Y.
intros.  
apply incl_eq.
*red; intros.
 apply inter2_def.
 split; revert H1; apply Zwdom.Wf_mono; auto;
   [apply inter2_incl1|apply inter2_incl2].
*red; intros.
 apply stable_set2 with (1:=Wf_stable).
 rewrite power_def; trivial.
 rewrite power_def; trivial.
 rewrite !extf_ok; auto with *.
Qed.

(** Adding bottom (for SN) *)
Lemma mt_Wdom : empty ∈ Wdom.
apply power_intro; intros.
apply empty_ax in H; contradiction.
Qed.
Hint Resolve mt_Wdom : core.

Definition Wfbot X := Wf (cc_bot X).

Instance Wfbot_mono : Proper (incl_set ==> incl_set) Wfbot.
unfold Wfbot; do 2 red; intros.
rewrite H; reflexivity.
Qed.

Lemma Wfbot_typ X : X ⊆ Wdom -> Wfbot X ⊆ Wdom.
intros.
apply Zwdom.Wf_typ; trivial.
red; intros.
apply cc_bot_ax in H0; destruct H0; auto.
rewrite H0; auto.
Qed.

Hint Resolve Wfbot_mono Wfbot_typ : core.

Definition Wbot := FIX incl_set inter Wdom (power Wdom) Wfbot.

Lemma Wbot_lfp : is_lfp incl_set Wfbot Wbot. 
apply knaster_tarski; auto with *.
Qed.

Lemma Wbot_eqn : Wbot == Wfbot Wbot.
symmetry; apply Wbot_lfp.
Qed.

Lemma Wbot_least X : Wfbot X ⊆ X -> Wbot ⊆ X.
apply Wbot_lfp.
Qed.

Lemma Wbot_typ : Wbot ⊆ Wdom.
apply FIX_typ; auto with *.
Qed.

Lemma Wbot_typ' : cc_bot Wbot ⊆ Wdom.
red; intros.
apply cc_bot_ax in H; destruct H.
 rewrite H; trivial.
 apply Wbot_typ; trivial.
Qed.

Lemma Wbot_ind : forall (P:set->Prop),
  Proper (eq_set ==> iff) P ->
  (forall x f, x ∈ A -> f ∈ (Π i ∈ B x, cc_bot Wbot) ->
   (forall i, i ∈ B x -> cc_app f i == empty \/ P (cc_app f i)) ->
   P (Wsup x f)) ->
  forall a, a ∈ Wbot -> P a.
intros.
cut (Wbot ⊆ subset Wbot P).
 intros inclW; apply inclW in H1.
 apply subset_elim2 in H1; destruct H1 as (a',eqa,?).
 rewrite eqa; trivial.
apply Wbot_least.
assert (subset Wbot P ⊆ Wbot).
 intro; apply subset_elim1.
assert (Wf (cc_bot (subset Wbot P)) ⊆ Wbot).
 transitivity (Wfbot Wbot).
  apply Zwdom.Wf_mono; trivial.
  apply cc_bot_mono; trivial.
  rewrite <- Wbot_eqn; reflexivity. 
intros z tyz.
apply subset_intro; auto.
apply Zwdom.Wf_elim in tyz;
  destruct tyz as (x,tyx,(f,tyf,eqz)).
rewrite eqz.
apply H0; trivial.
 revert tyf; apply cc_prod_covariant; auto with *.
 intros; apply cc_bot_mono; auto.
 
 intros.
 apply cc_prod_elim with (2:=H4) in tyf.
 apply cc_bot_ax in tyf; destruct tyf; auto.
 apply subset_elim2 in H5; destruct H5 as (y,?,?).
 rewrite <- H5 in H6; auto.
Qed. 
  
Lemma Wfst_typ_bot w : w ∈ Wbot -> Wfst w ∈ A.
intros.
apply Zwdom.Wfst_typ_gen with (B:=B)(X:=cc_bot Wbot); trivial.
rewrite Wbot_eqn in H; trivial.
Qed.

Lemma Wsnd_typ_bot w i :
  w ∈ Wbot ->
  i ∈ B (Wfst w) ->
  Zwdom.Wsnd w i ∈ cc_bot Wbot.
intros.  
apply Zwdom.Wsnd_typ_gen with (A:=A)(B:=B); trivial.
 apply Wbot_typ'.
 rewrite Wbot_eqn in H; trivial.
Qed.

End ImpredicativeFixpoint.


(*******************************************************************************************)
(* Universe facts *)

Section W_Univ.

  Variable U : set.
  Hypothesis Ugrot : Zuniv U.
  Hypothesis Unontriv : N ∈ U.  

  Hypothesis aU : A ∈ U.
  Hypothesis bU : unif_bound U A B.

  Let Zu_dom : Wdom ∈ U.
apply Zwdom.G_Wdom; trivial.
Qed.

  Lemma Zu_W : W ∈ U.
apply Zu_incl with Wdom; trivial.
apply W_typ.
Qed.

End W_Univ.


(*******************************************************************************************)
(** The primitive recursor *)

Section PrimRecursor.

Variable P : set -> set.
Hypothesis Pm : morph1 P.

Variable F : set -> set -> set -> set.
Hypothesis Fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) F.
Hypothesis f_typ :
  forall x f recf,
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  recf ∈ (Π i ∈ B x, P (cc_app f i)) -> 
  F x f recf ∈ P (Wsup x f).

Let G f w := F (Wfst w) (Wsnd_fun w)
               (cc_lam (B (Wfst w)) (fun i => f (Zwdom.Wsnd w i))). 

Let Gext X x x' g g' :
  X ∈ K Wf W ->
  eq_fun X g g' ->
  x ∈ Wf X -> x == x' -> G g x == G g' x'.
unfold G; intros.
apply Fm;[rewrite H2|rewrite H2|]; auto with *.
apply cc_lam_ext; [rewrite H2; reflexivity|].
red; intros.
apply H0; [|rewrite H2,H4;reflexivity].
apply Zwdom.Wsnd_typ_gen with (3:=H1); trivial.
transitivity W;[|apply W_typ].
apply KinclFX in H; trivial.
Qed.

Let Gtyp  X y f :
  X ∈ K Wf W ->
  f ∈ (Π x ∈ X, P x) ->
  y ∈ Wf X -> G (cc_app f) y ∈ P y.
intros KX tyf tyy.
unfold G.
destruct Zwdom.Wf_elim with (1:=tyy) as (x,tyx,(wf,tywf,eqy)).
assert (wff : Zwdom.isWfun wf).
{apply KinclFX in KX.
 apply Zwdom.cc_prod_Wfun with (1:=transitivity KX W_typ)(2:=tywf). }
assert (eq1 : Wfst y == x).
{rewrite eqy, Zwdom.Wfst_def; reflexivity. }
assert (eq2 : Wsnd_fun y == wf).
{rewrite eqy, Zwdom.Wsnd_fun_Wsup; [reflexivity|trivial]. }
assert (etay : y == Wsup (Wfst y) (Wsnd_fun y)).
{rewrite eq1, eq2; trivial. }
rewrite (Pm _ _ etay).
apply f_typ.
*rewrite eq1; trivial.
*rewrite eq2.
 revert tywf; apply cc_prod_covariant; auto with *.
 intros.
 apply KinclFX in KX; trivial.
*apply cc_prod_intro.
 +do 2 red; intros.
  rewrite H0; reflexivity.
 +do 2 red; intros.
  rewrite H0; reflexivity.
 +intros. 
  rewrite eq1 in H.
  apply cc_prod_elim with (1:=tyf).
  rewrite eq2.
  apply cc_prod_elim with (1:=tywf); trivial.
Qed.

Definition WREC :=
  FXREC Wf W P G.

Lemma WREC_typ w :
  w ∈ W -> 
  WREC w ∈ P w.
intros tyw.
apply FXREC_typ; auto with *.
*exact W_eqn.
*exact W_least.
*exact Wf_stable.
Qed.

Lemma WREC_eqn x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  WREC (Wsup x f) == F x f (λ i ∈ B x, WREC (cc_app f i)).
intros tya tyf.
assert (wf : Zwdom.isWfun f).
{apply Zwdom.cc_prod_Wfun with (1:=W_typ)(2:=tyf). }
unfold WREC.
rewrite FXREC_eqn; auto with *.
*unfold G.
 symmetry.
 apply Fm.
 +symmetry; apply Zwdom.Wfst_def. 
 +symmetry; apply Zwdom.Wsnd_fun_Wsup; trivial.
 +apply cc_lam_ext; [rewrite Zwdom.Wfst_def;reflexivity|].
  red; intros.
  apply FXREC_morph0; auto.
  rewrite <- H0.
  symmetry; apply Zwdom.Wsnd_def; trivial.
*exact W_eqn.
*exact W_least.
*exact Wf_stable.
*apply Wsup_typ; trivial.
Qed.

End PrimRecursor.

(*******************************************************************************************)
(** The recursor (size-based style), allowing recursive calls
    on transitive subterms *)

Section Recursor.

Variable P : set -> set.
Hypothesis Pm : morph1 P.

Variable F : set -> set -> set.
Hypothesis Fm : Proper (eq_set==>eq_set==>eq_set) F.
Hypothesis f_typ : forall X x recf,
  X ⊆ W ->
  X ⊆ Wf X -> (* X closed by subterm *)
  x ∈ Wf X ->
  recf ∈ (Π w ∈ X, P w) ->
  F recf x ∈ P x.
Hypothesis Firr : forall X recf recf',
  X ⊆ W ->
  X ⊆ Wf X ->
  (forall x, x ∈ X -> cc_app recf x == cc_app recf' x) ->
  forall x, x ∈ Wf X -> F recf x == F recf' x.

Let G f w := F (cc_lam W f) w.

Let Gext X x x' g g' :
  X ∈ K Wf W ->
  eq_fun X g g' ->
  x ∈ Wf X -> x == x' -> G g x == G g' x'.
unfold G; intros.
rewrite <- H2.
apply K_def in H;[|auto].
destruct H as (H,clos).
apply Firr with X;trivial.
intros.
rewrite !cc_beta_eq0; auto with *.
*symmetry in H0; apply eq_fun_ext in H0.
 apply ext_ext with (1:=H0); trivial.
*apply eq_fun_ext in H0.
 apply ext_ext with (1:=H0); trivial.
Qed.

Let Gtyp  X y f :
  X ∈ K Wf W ->
  f ∈ (Π x ∈ X, P x) ->
  y ∈ Wf X -> G (cc_app f) y ∈ P y.
intros KX tyf tyy.
apply K_def in KX; auto.
destruct KX as (KX,clos).
unfold G.
apply in_reg with (F (cc_lam X (cc_app f)) y).
*apply Firr with (X:=X); trivial.
 intros.
 rewrite !cc_beta_eq; auto with *.
 do 2red; intros; apply cc_app_morph; auto with*.
 do 2red; intros; apply cc_app_morph; auto with*.
*apply f_typ with X; auto with *.
 rewrite <- cc_eta_eq with (1:=tyf); trivial.
Qed.

Definition WSREC := FXREC Wf W P (fun f w => F (cc_lam W f) w).

Lemma WSREC_typ w :
  w ∈ W -> 
  WSREC w ∈ P w.
intros tyw.
apply FXREC_typ; auto with *.
*exact W_eqn.
*exact W_least.
*exact Wf_stable.
Qed.

Lemma WSREC_eqn x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  WSREC (Wsup x f) == F (λ w ∈ W, WSREC w) (Wsup x f).
intros tyx tyf.
unfold WSREC.
apply FXREC_eqn; auto with *.
*exact W_eqn.
*exact W_least.
*exact Wf_stable.
*apply Wsup_typ; trivial.
Qed.

End Recursor.

(*******************************************************************************************)

Section TransitiveRecursor.

Variable O : set.
Hypothesis KO : O ∈ K Wf W.


Let OinclW : O ⊆ W.
apply KinclFX in KO; trivial.
Qed.

Definition Wf' X := O ∩ Wf X.

Instance Wf'_mono : Proper (incl_set==>incl_set) Wf'.
do 2 red; intros.
apply inter2_mono; [reflexivity|apply Zwdom.Wf_mono; trivial].
Qed.

Instance Wf'_morph : morph1 Wf'.
auto with *.
Qed.

Lemma Wf'_eq X : Wf X ⊆ O -> Wf' X == Wf X.
unfold Wf'; rewrite (inter2_comm O (Wf X)).
intros; apply incl_inter2; trivial.
Qed.

Definition fsub' := fsub Wf' O.

Instance fsub'm : morph1 fsub'.
apply fsub_morph.
Qed.
Definition K' := K Wf' O.

Lemma K_relative X :
  X ∈ K' <-> X ∈ K Wf W /\ X ⊆ O.
apply K_def in KO; auto.
destruct KO.
unfold K'; rewrite !K_def; auto with *.
split; intros.
*destruct H1.
 split;[split;[transitivity O|]|]; trivial.
 transitivity (Wf' X); [trivial|].
 apply inter2_incl2.
*destruct H1 as ((?,?),?).
 split; [trivial|].
 red; intros.
 unfold Wf'; rewrite inter2_def.
 split; auto.
Qed.

Lemma KO' : O ∈ K'.
apply K_relative; auto with *.
Qed.
Hint Resolve KO' : core.

Lemma O_eqn : O == Wf' O.
symmetry; apply incl_inter2.
apply K_def in KO; [apply KO|auto].
Qed.

Definition X'O X := subset W (fun x => x ∈ O -> x ∈ X).

Lemma X'Oproj X : O ∩ X'O X ⊆ X.
red; intros.
apply inter2_def in H; destruct H.
apply subset_ax in H0.
destruct H0 as (_,(z',eqz,h)).
rewrite eqz in H|-*; auto.
Qed.

Lemma X'Oincl X : X ⊆ O -> X ⊆ X'O X .
red; intros.
apply subset_intro; auto.
Qed.

Lemma Wf'X'O X :
  X ⊆ O ->
  Wf' X ⊆ X ->
  Wf (X'O X) ⊆ X'O X.
intros XO FX.
red; intros.  
apply subset_intro.
{rewrite W_eqn.
 revert H; apply Zwdom.Wf_mono; trivial.
 intro; apply subset_elim1. }
intros.
apply FX.
apply inter2_def; split; [trivial|].
eapply Zwdom.Wf_mono; [trivial|apply X'Oproj|].
rewrite Wf_inter2; auto.
*apply inter2_def; split; auto.
 apply K_def in KO; [apply KO|]; auto.
*intro; apply subset_elim1.
Qed.

Lemma O_least X :
  Wf' X ⊆ X -> O ⊆ X.
intros.
transitivity (O ∩ X'O X); [|apply X'Oproj].  
transitivity (O ∩ X'O O).
{red; intros.
 apply inter2_def; split; [trivial|].
 apply subset_intro; auto. }
apply inter2_mono; [reflexivity|].
transitivity W; [intro; apply subset_elim1|].

transitivity (X'O (O ∩ X)).
apply W_least.
apply Wf'X'O; trivial.
red; intros.
apply inter2_def in H0; apply H0.
apply inter2_incl.
 apply inter2_incl1.
transitivity (Wf' X); [|trivial].
apply Wf'_mono.
red; intros.
apply inter2_def in H0; apply H0.

intros z; unfold X'O; rewrite !subset_ax.
apply and_iff_morphism; [reflexivity|].
apply ex2_morph; [reflexivity|intro z'].
apply fa_morph; intros.
rewrite inter2_def.
split;[|destruct 1]; auto.
  Qed.

 Lemma O_stable: stable_set (power O) Wf'.
red; intros.
apply inter2_incl.
*red; intros.
 destruct inter_wit' with (1:=H0) as (Y,?,?).
 rewrite O_eqn; revert H2; apply Wf'_mono.
 rewrite <- power_def; auto.
*red; intros.
 apply Wf_stable; [ rewrite H; apply power_mono; auto|]. 
 destruct inter_wit' with (1:=H0) as (Y,?,?).
 apply inter_intro; intros.
 2:{exists (Wf Y); apply replf_def; eauto with *. }    
 rewrite replf_ax in H3; destruct H3 as (a,?,(_,?)).
rewrite H4.
cut (z ∈ Wf' a).
apply inter2_incl2.
apply inter_elim with (1:=H0). 
apply replf_def; eauto with *.
 Qed.
 
Lemma fsub_eq x : x ∈ O -> fsub' x == fsub Wf W x.
intros tyx.
apply eq_set_ax; intros z.
unfold fsub', fsub.
rewrite !subset_ax.
split.
*intros (tyz,(z',eqz,insub)).
 split; [auto|exists z';[trivial|intros]].
 apply inter2_incl1 with (y:=O).
 apply insub.
 +rewrite K_relative. 
  split; [|apply inter2_incl2].
  rewrite K_def; auto.
  split; [transitivity O; [apply inter2_incl2|trivial]|].
  rewrite Wf_inter2; [|apply KinclFX in H;apply H|trivial].
  apply inter2_mono.
  apply K_def in H; [apply H|auto].
  apply K_def in KO; [apply KO|auto].
 +apply inter2_def; split; [trivial|].
  rewrite Wf_inter2; [|apply KinclFX in H;apply H|trivial].
  apply inter2_def; split; [trivial|].
  rewrite K_def in KO; [apply KO|]; auto.
*intros (tyz,(z',eqz,insub)).
 split.
 +rewrite eqz; apply insub; trivial.
  rewrite K_def in KO; [apply KO|]; auto.
 +exists z'; [trivial|intros].
  rewrite K_relative in H; destruct H.
  apply insub; trivial.
  revert H0; apply inter2_incl2.
Qed.

Hypothesis Oclos :
  forall x, x ∈ O -> Wf (fsub Wf W x) ⊆ O.

Lemma Wf_fsub_eq x : x ∈ O -> Wf' (fsub' x) == Wf (fsub Wf W x).
intros.
rewrite fsub_eq; [|trivial].
apply Wf'_eq.
auto.
Qed.


Lemma KfsubW w :
  w ∈ O ->
  fsub Wf W w ∈ K Wf W.
intros; apply Kfsub; auto.
exact W_eqn.
exact Wf_stable.
Qed.
Hint Resolve KfsubW : core.
Lemma KfsubW' w :
  w ∈ O ->
  fsub' w ∈ K Wf W.
intros.
rewrite fsub_eq; auto.
Qed.
Hint Resolve KfsubW' : core.

Variable P : set -> set -> set.
Hypothesis Pm : morph2 P.
Hypothesis Pmono : forall X Y x,
  Y ⊆ O ->
  Y ∈ K Wf W ->
  (forall w, w ∈ X -> exists2 w', w' ∈ Y &(* w ∈ fsub w') ->*)
   forall X, X ∈ K Wf W -> w' ∈ Wf X -> w ∈ X) ->
  P (Wf X) x ⊆ P Y x.

Variable F : set -> set -> set -> set.
Hypothesis Fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) F.
Hypothesis f_typ : forall X x recf,
  X ⊆ O ->
  X ∈ K Wf W ->
  x ∈ Wf X ->
  recf ∈ (Π w ∈ X, P X w) ->
  F X recf x ∈ P (Wf X) x.
Hypothesis Firr : forall X X' recf recf',
  X ⊆ O ->
  X ∈ K Wf W ->
  X' ⊆ O ->
  X' ∈ K Wf W ->
  recf ∈ (Π w ∈ X, P X w) ->
  recf' ∈ (Π w ∈ X', P X' w) ->
  (forall x, x ∈ X -> x ∈ X' -> cc_app recf x == cc_app recf' x) ->
  forall x, x ∈ Wf X -> x ∈ Wf X' -> F X recf x == F X' recf' x.

Definition P' x := P (Wf'(fsub' x)) x.

Instance P'm : morph1 P'.
do 2 red; intros.
unfold P'.
rewrite H; reflexivity.
Qed.

Lemma PmonoO x :
  x ∈ O ->    
  P' x ⊆ P O x.
intros.
unfold P'; rewrite Wf_fsub_eq; trivial.
apply Pmono; [reflexivity|trivial|].
intros.
exists x; [trivial|].
intros.
revert H0; apply fsub_inv_F; auto.
Qed.
Lemma Pmono' x y :
  y ∈ O ->
  x ∈ fsub' y ->    
  P' x ⊆ P (fsub' y) x.
intros.
unfold P'; rewrite Wf_fsub_eq; trivial.
rewrite fsub_eq in H0|-*; trivial.
apply Pmono; auto with *.
*apply fsub_inv_F; auto.
 apply K_def in KO; [apply KO|]; auto.
*intros.
 exists x; [trivial|].
 intros.
 revert H1; apply fsub_inv_F; auto.
*apply subset_elim1 in H0; trivial.
Qed.

Let G f w := F (fsub' w) (cc_lam (fsub' w) f) w.

Let Gm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) G.
unfold G; do 3 red; intros.
apply Fm; trivial.
 +apply fsub_morph; trivial.
 +apply cc_lam_ext.
  apply fsub_morph; trivial.

  red; intros;auto.
Qed.  
Hint Resolve Gm : core.

Let Gext X x x' g g' :
  X ∈ K' ->
  eq_fun X g g' ->
  x ∈ Wf' X -> x == x' -> G g x == G g' x'.
intros.
apply Fm; trivial.
*rewrite <-H2; reflexivity.
*apply cc_lam_ext; [rewrite <-H2; reflexivity|red;intros].
 apply H0; [|trivial].
 revert H3; apply fsub_inv_F; trivial.
Qed.

Let Gtyp  X y f :
  X ∈ K' ->
  f ∈ (Π x ∈ X, P' x) ->
  y ∈ Wf' X -> G (cc_app f) y ∈ P' y.
intros KX tyf tyy.
unfold G, P'.
apply inter2_def in tyy; destruct tyy as (yO,tyy).
rewrite Wf_fsub_eq;[|trivial].
rewrite fsub_eq;[|trivial].
apply f_typ; auto.
*apply fsub_inv_F; trivial.
 apply K_def in KO;[apply KO|]; auto.
*apply fsub_intro; auto with *.
 apply W_eqn.
 apply Wf_stable.
*apply cc_prod_intro; auto with *.
 do 2 red; intros; apply cc_app_morph; auto with *.
 do 2 red; intros. rewrite H0; reflexivity.
 intros.  
 rewrite <-fsub_eq;[|trivial].
 apply Pmono'; trivial.
 +rewrite fsub_eq;trivial.
 +apply cc_prod_elim with (1:=tyf).
  revert H; apply fsub_inv_F; auto.
  apply K_relative in KX; apply KX.
Qed.

Definition WSREC' := FXREC Wf' O P' G.

Global Instance WSREC'_morph0 : morph1 WSREC'.
apply FXREC_morph; auto with *.
*apply Wf'_morph.
*apply P'm.
Qed.

Lemma WSREC_typ0' w :
  w ∈ O -> 
  WSREC' w ∈ P' w.
intros tyw.
apply FXREC_typ; auto with *.
*exact O_eqn.
*exact O_least.
*exact O_stable.
Qed.

Lemma WSREC_eqn0' w :
  w ∈ O ->
  WSREC' w == F (fsub' w) (λ w ∈ fsub' w, WSREC' w) w.
intros; unfold WSREC' at 1.
apply FXREC_eqn; auto with *.
*exact O_eqn.
*exact O_least.
*exact O_stable.
Qed.


Lemma WSREC_typ' w :
  w ∈ O -> 
  WSREC' w ∈ P O w.
intros tyw.
eapply PmonoO; trivial.
apply WSREC_typ0'; trivial.
Qed.

Lemma WSREC_eqn' w :
  w ∈ O ->
  WSREC' w == F O (λ w ∈ O, WSREC' w) w.
intros tyw.
rewrite WSREC_eqn0'; trivial.
assert (wO : w ∈ Wf' O).
{rewrite <- O_eqn; trivial. }
apply Firr; auto with *.
*apply fsub_inv_F; trivial.
*apply cc_prod_intro.
 do 2 red; intros; apply WSREC'_morph0; trivial.
 do 2 red; intros; apply Pm; auto with *.
 intros.
 assert (x ∈ O).
 {revert H; apply fsub_inv_F; trivial. }
 generalize (WSREC_typ0' _ H0).
 apply Pmono'; auto.
*apply cc_prod_intro.
 do 2 red; intros; apply WSREC'_morph0; trivial.
 do 2 red; intros; apply Pm; auto with *.
 intros.
 apply PmonoO; trivial.
 apply WSREC_typ0'; trivial.
*intros.
 rewrite !cc_beta_eq; auto with *.
*cut (w ∈ Wf' (fsub' w)); [apply inter2_incl2|].
 apply fsub_intro; auto with *.
 exact O_eqn.
 exact O_stable.
*apply K_def in KO; [apply KO|]; auto.
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

End W.

Local Notation E := eq_set (only parsing).

Lemma W_ext A A' B B' :
  A == A' ->
  eq_fun A B B' ->
  W A B == W A' B'.
unfold W; intros.
apply FIX_morph_gen.
 apply incl_set_morph.

 apply inter_morph.

 apply Zwdom.Wdom_ext; trivial.

 apply power_morph.
 apply Zwdom.Wdom_ext; trivial.

 red; intros.
 apply Zwdom.Wf_ext; trivial.
Qed.

Instance W_morph : Proper (E==>(E==>E)==>E) W.
do 3 red; intros.
unfold W.
unfold FIX.
apply inter_morph.
apply subset_morph.
 apply subset_morph.
  apply power_morph.
  apply Zwdom.Wdom_morph; trivial.
 red; intros.
 apply incl_set_morph; auto with *.
 apply Zwdom.Wdom_morph; auto with *.
red; intros.
unfold post_fix.
apply incl_set_morph; auto with *.
apply Zwdom.Wf_morph_gen; auto with *.
Qed.

Instance WREC_morph_gen :
  Proper (E==>(E==>E)==>(E==>E)==>(E==>E==>E==>E)==>E==>E) WREC.
do 6 red; intros.
unfold WREC.
apply FXREC_morph; trivial.
*apply Zwdom.Wf_morph_gen; trivial.
*apply W_morph; trivial.
*do 2 red; intros.
 apply H2.
 +apply Zwdom.Wfst_morph; trivial.
 +apply Zwdom.Wsnd_fun_morph; trivial.
 +apply cc_lam_ext.
  ++apply H0; rewrite H5; reflexivity.
  ++red; intros; apply H4; rewrite H5,H7; reflexivity.
Qed.

Instance WSREC_morph_gen :
  Proper (E==>(E==>E)==>(E==>E)==>(E==>E==>E)==>E==>E) WSREC.
do 6 red; intros.
unfold WSREC.
apply FXREC_morph; trivial.
*apply Zwdom.Wf_morph_gen; trivial.
*apply W_morph; trivial.
*do 2 red; intros.
 apply H2; trivial.
 apply cc_lam_ext.
 +apply W_morph; trivial.
 +red; intros; apply H4; trivial.
Qed.

Instance K_morph_gen :
  Proper ((E==>E)==>E==>E) K.
do 3 red; intros; unfold K.
apply subset_morph; [rewrite H0; reflexivity|].
red; intros.
rewrite (H _ _ (reflexivity x1)); reflexivity.
Qed.

Instance fsub_morph_gen :
  Proper ((E==>E)==>E==>E==>E) fsub.
do 4 red; intros; unfold fsub.
apply subset_morph; [trivial|].
red; intros.
apply fa_morph; intros X.
apply impl_morph; [|intros _].
*rewrite H,H0; reflexivity.
*rewrite H1, (H _ _ (reflexivity X)); reflexivity.
Qed.

Instance fsub'_morph_gen :
  Proper (E==>(E==>E)==>E==>E==>E) fsub'.
do 5 red; intros.
apply fsub_morph_gen; trivial.
red; intros; apply inter2_morph; [trivial|].
apply Zwdom.Wf_morph_gen; trivial.
Qed.

Instance WSREC'_morph_gen :
  Proper (E==>(E==>E)==>E==>(E==>E==>E)==>(E==>E==>E==>E)==>E==>E) WSREC'.
do 7 red; intros.
unfold WSREC'.
apply FXREC_morph; trivial.
*red; intros; apply inter2_morph; [trivial|].
 apply Zwdom.Wf_morph_gen; trivial.
*unfold P'; red; intros.
 apply H2; [|trivial].
 apply inter2_morph; [trivial|].
 apply Zwdom.Wf_morph_gen; trivial.
 apply fsub'_morph_gen; trivial.
*do 2 red; intros.
 apply H3; trivial.
 +apply fsub'_morph_gen; trivial.
 +apply cc_lam_ext.
  ++apply fsub'_morph_gen; trivial.
  ++red; intros; auto.
Qed.

