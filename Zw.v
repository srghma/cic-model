Require Import ZF Zpairs Zsum Znats Zrelations Ztarski Zfix.
Require Import Zstable.
Require Import Zuniv.
Require Import Zcoc.
Require Zwdom.

Existing Instance Zwdom.Wf_mono.
Existing Instance Zwdom.Wfbot_mono.

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

Variable P : set -> set -> set.
Hypothesis Pm : morph2 P.
Hypothesis Pmono : forall X Y x,
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

(*Require Import ZFlimit.*)

Let R w w' := w ∈ fsub Wf W w'.
Let Rm : Proper (eq_set==>eq_set==>iff) R.
unfold R; do 3 red; intros.
rewrite H,H0; reflexivity.
Qed.

Let G f w :=
  cond_set (w ∈ O) (F (fsub Wf W w) (cc_lam (fsub Wf W w) f) w).
Let Gm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) G.
unfold G; do 3 red; intros.
apply cond_set_morph; [rewrite H0;reflexivity|].
apply Fm; trivial.
 apply fsub_morph; trivial.

 apply cc_lam_ext.
  apply fsub_morph; trivial.

  red; intros;auto.
Qed.  
Hint Resolve Rm Gm : core.

(*Let Gext X x x' g g' :
  X ∈ K Wf W ->
  eq_fun X g g' ->
  x ∈ Wf X -> x == x' -> G g x == G g' x'.
unfold G; intros.
apply K_def in H;[|auto].
destruct H as (H,clos).
transitivity (cond_set (x ∈ O) (F (fsub Wf W x) (λ x ∈ fsub Wf W x, g' x) x)).
*apply cond_set_morph2; [reflexivity|].
 intros tyx.
 apply Firr.
 +admit.
 +apply Kfsub; auto.
exact W_eqn.
exact Wf_stable.
apply KinclFX in KO.
apply KO; trivial.
 +admit.
 +apply Kfsub; auto.
exact W_eqn.
exact Wf_stable.
apply KinclFX in KO.
apply KO; trivial.
 +apply cc_prod_intro; auto.
  ++do 2 red; intros.
    admit.
  ++do 2 red; intros.
    rewrite H4; reflexivity.
  ++intros.
    transitivity 
      with (fsub Wf W x);trivial.
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
*)
(*
Definition Wsrec_rel' w y :=
  forall Q, Proper (eq_set==>eq_set==>iff) Q ->
  (forall X x recf,
   X ⊆ Wf X ->
   X ⊆ W ->
   x ∈ Wf X ->
   recf ∈ (Π w ∈ X, P X w) ->
   (forall w, w ∈ X -> Q w (cc_app recf w)) -> 
   Q x (G (cc_app recf) x)) -> 
  Q w y.

Instance Wsrec_rel'_morph : Proper (eq_set==>eq_set==>iff) Wsrec_rel'.
do 3 red; intros.
apply fa_morph; intros Q.
apply fa_morph; intros Qm.
apply fa_morph; intros.
apply Qm; trivial.
Qed.

Lemma Wsrec_rel'_intro X x recf :
  X ⊆ Wf X ->
  X ⊆ W ->
  x ∈ Wf X ->
  recf ∈ (Π w ∈ X, P X w) ->
  (forall w, w ∈ X -> Wsrec_rel' w (cc_app recf w)) -> 
  Wsrec_rel' x (G (cc_app recf) x).
red; intros.
apply H5 with X; trivial.
intros.
apply H3; trivial.
Qed.

Lemma Wsrec_rel'_elim w y :
  w ∈ W ->
  Wsrec_rel' w y ->
  exists2 X, X ⊆ Wf X /\ X ⊆ W /\ w ∈ Wf X &
  exists2 recf, recf ∈ (Π w ∈ X, P X w) &
    y == G (cc_app recf) w /\
    (forall w, w ∈ X -> Wsrec_rel' w (cc_app recf w)).
intros tyw inv.
apply proj2 with (A:=Wsrec_rel' w y).
pattern w, y.
apply inv; intros.
{do 3 red; intros.
 apply and_iff_morphism.
  rewrite H,H0; reflexivity.
 apply ex2_morph; intros X; auto with *.
  rewrite H; reflexivity.
 apply ex2_morph; intros recf'; auto with *.
 apply and_iff_morphism.
  apply eq_set_morph; [trivial|].
  apply Gm; [apply cc_app_morph;reflexivity|trivial].
 apply fa_morph; intros w'; auto with *. }
split.
*apply Wsrec_rel'_intro with X; trivial.
 intros.
 apply H3; trivial.
*exists X; auto.
 exists recf; trivial.
 split; auto with *.
 intros.
 apply H3; trivial.
Qed.
(*
Lemma Wsrec_rel'_elim' x f y :
  x ∈ A ->
  f ∈ (Π i ∈ B x, W) ->
  Wsrec_rel' (Wsup x f) y ->
  exists2 X, X ⊆ W /\ f ∈ (Π i ∈ B x, X) &
  exists2 recf, recf ∈ (Π w ∈ X, P w) &
    y == F recf (Wsup x f) /\
   (forall w, w ∈ X -> Wsrec_rel' w (cc_app recf w)).
intros.
assert (tyw : Wsup x f ∈ W).
 rewrite W_eqn; apply Zwdom.Wf_intro; trivial.
apply Wsrec_rel_elim in H1; trivial.
destruct H1 as (X,(XinclW,tyw'),(recf,tyrecf,(eqy,?))).
apply Zwdom.Wf_elim in tyw'; [|trivial];
  destruct tyw' as (x',tyx',(f',tyf',eqw)).
apply Zwdom.Wsup_inj_typ with (A:=A)(B:=B)(3:=H0)(4:=tyf') in eqw;
  [|apply W_typ|rewrite <-W_typ;auto].
destruct eqw as (eqx,eqf).
exists X. 
  split; trivial.
  rewrite cc_eta_eq with (1:=H0).
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.
  rewrite eqf; trivial.
  apply cc_prod_elim with (1:=tyf').
  rewrite <-eqx; trivial.
 exists recf; auto.
Qed.
*)
(*Lemma Wsrec'_ex w :
  w ∈ W ->
  exists2 y, y ∈ P W w & Wsrec_rel' w y /\ (forall y', Wsrec_rel' w y' -> y==y').
intros tyw.
pattern w; apply W_ind; intros; trivial.
{do 2 red; intros.
 apply ex2_morph; intros y'.
  rewrite H; reflexivity.
 apply and_iff_morphism.
  rewrite H; reflexivity.
 apply fa_morph; intros y''.
 rewrite H; reflexivity. }
pose (X := fsub (Wsup x f)).
(*
pose (X := replf (B x) (cc_app f)).
assert (Xdef : forall z, z ∈ X <-> exists2 i, i ∈ B x & z == cc_app f i).
{intros.
 subst X; rewrite replf_ax; auto with *.
 do 2 red; intros; apply cc_app_morph; auto with *. }
assert (XinclW : X ⊆ W).
{red; intros.
 rewrite Xdef in H2.
 destruct H2 as (i,tyi,eqz); rewrite eqz.
 apply cc_prod_elim with (1:=H0); trivial. }*)
pose (recf := λ w ∈ X, union (subset (P W w) (Wsrec_rel' w))).
assert (tyf : f ∈ Π __ ∈ B x, X).
{rewrite cc_eta_eq with (1:=H0).
 apply cc_prod_intro; intros; auto with *.
  do 2 red; intros; apply cc_app_morph; auto with *.
 rewrite Xdef; eauto with *. }
assert (tyrecf : recf ∈ Π w ∈ X, P W w).
{apply cc_prod_intro; intros.
 *do 2 red; intros.
  apply union_morph; apply subset_morph.
   rewrite H3; reflexivity.
  red; intros.
  rewrite H3; reflexivity.
 *intros ? ? ? h; rewrite h; reflexivity.
 *rewrite Xdef in H2.
  destruct H2 as (i,tyi,eqx0).
  destruct H1 with (1:=tyi).
  destruct H3.
  rewrite <- eqx0 in H2,H3.
  rewrite union_subset_singl with (y:=x1)(y':=x1); auto with *.
  intros.
  rewrite eqx0 in H7,H8.
  rewrite <- H4 with (1:=H7).
  rewrite <- H4 with (1:=H8).
  reflexivity. } 
exists (G (cc_app recf) (Wsup x f)).
*apply Pmono with (fsub (Wsup x f)).
 +admit.
 +intros.
  exists (Wsup x f).
  admit.
  admit.  
 +eapply f_typ.
  ++admit.
  ++apply Kfsub.
    admit.
  ++admit.
  ++apply cc_prod_intro.
    admit.
    admit.
    intros.    
    apply Zwdom.Wsup_typ_gen
      with X; trivial.
  apply Zwdom.Wf_intro; trivial.
 split; intros.
  apply Wsrec_rel_intro with (X:=X); intros; trivial.
   apply Zwdom.Wf_intro; trivial.
  rewrite Xdef in H2; destruct H2 as (i,tyi,eqz).
  destruct H1 with (1:=tyi).
  destruct H3.
  unfold recf; rewrite cc_beta_eq; trivial.
   rewrite <- eqz in H2,H3.
   rewrite union_subset_singl with (y:=x0)(y':=x0); intros; auto with *.
   rewrite eqz in H7,H8.
   rewrite <- H4 with (1:=H7).
   rewrite <- H4 with (1:=H8).
   reflexivity.

   do 2 red; intros.
   apply union_morph; apply subset_morph.
    rewrite H6; reflexivity.
   red; intros.
   rewrite H6; reflexivity.

   rewrite Xdef; eauto.

  apply Wsrec_rel_elim' in H2; trivial.
   destruct H2 as (X',(X'inclW,tyf'),(recf',tyrecf',(eqy,?))).
   rewrite eqy.
   apply Firr with X; trivial.
    intros.
    assert (x0 ∈ X').
     rewrite Xdef in H3; destruct H3 as (i,tyi,eqz).
     rewrite eqz.
     apply cc_prod_elim with (1:=tyf'); trivial.
    unfold recf; rewrite cc_beta_eq; trivial.
     apply union_subset_singl with (y':=cc_app recf' x0); intros; auto with *.
      apply cc_prod_elim with (1:=tyrecf'); trivial.

      rewrite Xdef in H3; destruct H3 as (i,tyi,eqx0).
      destruct H1 with (1:=tyi); intros.
      destruct H9.
      rewrite eqx0 in H7,H8.
      rewrite <- H10 with (1:=H7).
      rewrite <- H10 with (1:=H8).
      reflexivity.

     do 2 red; intros.
     apply union_morph; apply subset_morph.
      rewrite H6; reflexivity.
     red; intros.
     rewrite H6; reflexivity.

    apply Zwdom.Wf_intro; trivial.
Qed.
*)
*)
(*

Definition WSREC' := WFR fsub G.

Global Instance WSREC'_morph0 : morph1 WSREC'.
apply WFR_morph0.
Qed.


Lemma Wacc w :
  w ∈ W ->
  forall w', w' ∈ fsub' w ->
  Acc R w'.
intros tyw.
elim tyw using W_ind; intros.
 do 2 red; intros.
 apply fa_morph; intros w'.
 rewrite H; reflexivity.

 constructor; intros.
 red in H3.
 assert (y ∈ fsub (Wsup x f)).
  apply fsub_fsub'_trans with w'; trivial.
  rewrite W_eqn; apply Zwdom.Wf_intro; trivial.
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
*)
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
*)
(*Instance WSREC'_morph_gen :
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
(*Lemma wsubterms_ext A A' B B' X X' :
  A == A' ->
  eq_fun A B B' ->
  X == X' ->
  wsubterms A B X == wsubterms A' B' X'.
intros.
unfold wsubterms.
apply inter_morph.
apply subset_morph.
 apply power_morph.
 apply W_ext; trivial.

 red; intros.
 apply and_iff_morphism.
  apply incl_set_morph; auto with *.
  apply Zwdom.Wf_ext; auto with *.

  apply incl_set_morph; auto with *.
  apply inter2_morph; trivial.
  apply W_ext; auto with *.
Qed.

Instance wsubterms_morph :
  Proper (E==>(E==>E)==>E==>E) wsubterms.
do 4 red; intros.
unfold wsubterms.
apply inter_morph.
apply subset_morph.
 apply power_morph.
 apply W_morph; trivial.

 red; intros.
 rewrite (W_morph _ _ H _ _ H0).
 rewrite (Zwdom.Wf_morph_gen _ _ H _ _ H0 _ _ (reflexivity _)).
 rewrite H1; reflexivity.
Qed.
*)
