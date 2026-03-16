Require Import ZF Zrelations Znats Zstable Ztarski.

(** Bounded recursive functions over a fixpoint *)

Section BoundedRecursor.

  Variable F : set -> set.
  Variable Fmono : Proper (incl_set ==> incl_set) F.

  Let Fm := Fmono_morph _ Fmono.

  (** FX is the least fixpoint of F. *)
  Variable FX : set.
  Hypothesis FX_fix : FX == F FX.
  Hypothesis FX_ind : forall X, F X ⊆ X -> FX ⊆ X.

  Hypothesis Fs : stable_set (power FX) F.


(* All subterms *)

Definition K := subset (power FX) (fun X => X ⊆ F X).

Lemma K_def X : X ∈ K <-> X ⊆ FX /\ X ⊆ F X.
unfold K; rewrite subset_ax, power_def.
apply and_iff_morphism; [reflexivity|].
apply exists_eq_intro; intros.
rewrite <-H; reflexivity.
Qed.

  Lemma KinclFX : forall X, X ∈ K -> X ⊆ FX.
intros.
apply subset_elim1 in H; rewrite power_def in H; trivial.
Qed.

Lemma Ksub : forall X, X ∈ K -> X ⊆ F X.
intros.
apply subset_ax in H.
destruct H as (_,(X',eqX,?)).
rewrite eqX; trivial.
Qed.

Lemma KFX : FX ∈ K.
apply subset_intro; [rewrite power_def; reflexivity|].
rewrite <- FX_fix; reflexivity.
Qed.
Hint Resolve KinclFX KFX : core.

Definition fsub a :=
  subset FX (fun b => forall X, X ∈ K -> a ∈ F X -> b ∈ X).

Instance fsub_morph : morph1 fsub.
unfold fsub; do 2 red; intros.
apply subset_morph; auto with *.
red; intros.
apply fa_morph; intro X.
rewrite H; reflexivity.
Qed.

Lemma fsub_inv_F X x :
  X ∈ K ->
  x ∈ F X ->
  fsub x ⊆ X.
red; intros.
apply subset_ax in H1; destruct H1 as (_,(z',eqz,sub)).  
rewrite eqz; auto.
Qed.

Lemma fsub_intro x :
  x ∈ FX -> x ∈ F (fsub x).
intros tyx.
assert (x ∈ F (inter (subset K (fun X => x ∈ F X)))). 
{apply Fs.
 *red; intros.
  apply power_intro; intros.
  apply KinclFX with (X:=z); trivial.
  apply subset_elim1 in H; trivial.
 *apply inter_intro.
  +intros.
   rewrite replf_ax in H.
   destruct H as (?,?,(_,?)).
   rewrite H0.
   apply subset_ax in H; destruct H as (?,(x',eqx,?)).   
   rewrite eqx; trivial.
  +exists FX.
   rewrite replf_def.
   2:intros ??? h; auto.
   exists FX.
   2:apply FX_fix.
   apply subset_intro; auto.
   rewrite <- FX_fix; trivial.
}
revert H; apply Fmono.
red; intros.
apply subset_intro.
apply inter_elim with (1:=H).
apply subset_intro; auto.
rewrite <- FX_fix; trivial.

intros.
apply inter_elim with (1:=H).
apply subset_intro; trivial.
Qed.

Lemma Kfsub x : x ∈ FX -> fsub x ∈ K.
intros tyx.
pose (Y := subset K (fun X => x ∈ F X)).
assert (wY : FX ∈ Y).
{apply subset_intro; [auto|].
 rewrite <- FX_fix; trivial. }
assert (e: inter Y ⊆ fsub x).
{red; intros.
 apply subset_intro.
 {apply inter_elim with (1:=H); trivial. }
 intros.
 apply inter_elim with Y; trivial. 
 apply subset_intro; trivial. }
apply Fmono in e.
apply subset_intro.
{apply power_def; intro; apply subset_elim1. }
red; intros.
apply e.
apply Fs.
*red; intros; apply power_def.
 apply subset_elim1 in H0.
 apply KinclFX; trivial.
*apply inter_intro; intros.
 +rewrite replf_ax in H0; auto with *.
  destruct H0 as (X,?,(_,?)).
  assert (X ⊆ F X).
  {apply Ksub.
   apply subset_elim1 in H0; trivial. }
  apply subset_ax in H0.
  destruct H0 as (?,(X',eqX,xin)).
  rewrite <-eqX in xin; clear X' eqX.
  rewrite H1.
  apply H2.
  apply fsub_inv_F with (2:=xin); trivial.
 +exists (F FX).
  rewrite replf_def; auto with *.
  exists FX;[trivial|reflexivity].
Qed.
Opaque fsub.

  (** The return type *)
  Variable P : set -> set.
  Hypothesis Pm : morph1 P.

  (** The recursve definition *)
  Variable G : (set -> set) -> set -> set.
  Hypothesis Gext : forall X x x' g g',
    X ∈ K ->
    eq_fun X g g' ->
    x ∈ F X ->
    x == x' -> G g x == G g' x'.
  Hypothesis G_typ : forall X y f,
    X ∈ K ->
    f ∈ (Π x ∈ X, P x) ->
    y ∈ F X ->
    G (cc_app f) y ∈ P y.

Definition G' F a :=
  cond_set (a ∈ FX) (G F a).

Instance G'm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) G'.
do 3 red; intros.
apply cond_set_morph2.
*rewrite H0; reflexivity.
*intros.
 apply Gext with FX; trivial.
 +red; auto.
 +rewrite <- FX_fix; trivial.
Qed.

Lemma G'ext : forall X x x' g g',
  X ∈ K ->
  eq_fun X g g' ->
  x ∈ F X ->
  x == x' -> G' g x == G' g' x'.
intros.
apply cond_set_morph.
*rewrite H2; reflexivity.
*apply Gext with X; trivial.
Qed.

Lemma G'_typ : forall X y f,
  X ∈ K ->
  f ∈ (Π x ∈ X, P x) ->
  y ∈ F X ->
  G' (cc_app f) y ∈ P y.
intros.
unfold G'; rewrite cond_set_ok; eauto.
rewrite FX_fix; revert H1; apply Fmono; auto.
Qed.

Definition FXR_rel x y :=
  forall Q, Proper (eq_set==>eq_set==>iff) Q ->
  (forall X y recf,
   X ∈ K ->
   y ∈ F X ->
   recf ∈ (Π x ∈ X, P x) ->
   (forall x, x ∈ X -> Q x (cc_app recf x)) -> 
   Q y (G' (cc_app recf) y)) -> 
  Q x y.

Instance FXR_rel_morph : Proper (eq_set==>eq_set==>iff) FXR_rel.
do 3 red; intros.
apply fa_morph; intros Q.
apply fa_morph; intros Qm.
apply fa_morph; intros.
apply Qm; trivial.
Qed.

Definition FXREC x := union(subset (P x) (FXR_rel x)).

Instance FXREC_morph0 : morph1 FXREC.
do 2 red; intros.
apply union_morph; apply subset_morph;[auto|].
red; intros.
rewrite H; reflexivity.
Qed.


Lemma FXR_rel_intro X y f :
  X ∈ K ->
  y ∈ F X ->
  f ∈ (Π x ∈ X, P x) ->
  (forall x, x ∈ X -> FXR_rel x (cc_app f x)) -> 
  FXR_rel y (G' (cc_app f) y).
red; intros.
apply H4 with (X:=X); trivial.
intros.
apply H2; trivial.
Qed.

Lemma FXR_rel_ind Q x y :
  Proper (eq_set==>eq_set==>iff) Q ->
  (forall X y recf,
   X ∈ K ->
   y ∈ F X ->
   recf ∈ (Π x ∈ X, P x) ->
   (forall x, x ∈ X -> FXR_rel x (cc_app recf x)) -> 
   (forall x, x ∈ X -> Q x (cc_app recf x)) -> 
   Q y (G' (cc_app recf) y)) -> 
  FXR_rel x y -> Q x y.
intros Qm Hrec rel.
apply proj2 with (A:=FXR_rel x y).
apply rel; intros.
*do 3 red; intros.
 rewrite H,H0; reflexivity.
*split; [apply FXR_rel_intro with X; intros; auto; apply H2; trivial|].
 apply Hrec with (X:=X); trivial; apply H2; trivial.
Qed.

Lemma FXR_rel_inv_typ x y :
  FXR_rel x y -> y ∈ P x.
intros.
apply H.
{do 3 red; intros.
 rewrite H0, H1;reflexivity. }
intros.
apply G'_typ with (X:=X); trivial.
Qed.

Lemma FXR_rel_elim x y :
  FXR_rel x y ->
  exists2 X, X ∈ K /\ x ∈ F X &
  exists2 recf, recf ∈ (Π x ∈ X, P x) &
    y == G' (cc_app recf) x /\
    (forall x, x ∈ X -> FXR_rel x (cc_app recf x)).
intros rel.
elim rel using FXR_rel_ind; intros.
*do 3 red; intros.
 apply ex2_morph; intros X; auto with *;[rewrite H; reflexivity|].
 apply ex2_morph; intros recf'; auto with *.
 apply and_iff_morphism; [|reflexivity].
 apply eq_set_morph;[trivial|].
 apply G'm; [apply cc_app_morph;reflexivity|trivial].
*exists X; auto.
 exists recf; auto with *.
Qed.

Definition FXR_dom := subset FX (fun x => exists y, FXR_rel x y).

Lemma FXR_dom_F :
  FXR_dom ⊆ F FXR_dom.
red; intros.
apply subset_ax in H; destruct H as (_,(z',eqz,(y,relz))).
rewrite <-eqz in relz; clear z' eqz.
apply FXR_rel_elim in relz.
destruct relz as (X,(?,tyz),(recf,tyf,(eqy,rel))).
clear y eqy.
revert z tyz; apply Fmono.
red; intros.
apply subset_intro.
*revert H0; apply KinclFX; trivial.
*eauto.
Qed.

Lemma Kdom : FXR_dom ∈ K.
apply subset_intro.
*rewrite power_def; intro; apply subset_elim1.
*apply FXR_dom_F.
Qed.


  Lemma FXR_uniq x y y':
  FXR_rel x y -> FXR_rel x y' -> y==y'.
intros img1 img2.
revert y' img2.
apply img1.
*do 3 red; intros.
 apply fa_morph; intros y'.
 rewrite H,H0; reflexivity.
*intros X x' f tyX tyx' tyf Hrec y' imgy'.
 apply FXR_rel_elim in imgy'.
 destruct imgy' as (X',(?,?),(f',tyf',(eqy',relf'))).
 rewrite eqy'.
 apply G'ext with (X:=fsub x'); auto with *.
 +apply Kfsub.
  rewrite FX_fix; revert H0; apply Fmono; auto.
 +red; intros.
  apply Hrec.
  apply fsub_inv_F with x'; auto.
  rewrite <-H2.
  apply (relf' x0).
  apply fsub_inv_F with x'; auto.
 +apply fsub_intro.
  rewrite FX_fix.
  revert tyx'; apply Fmono.
  apply KinclFX; auto.
Qed.

Lemma FXR_eq x y :
  FXR_rel x y -> FXREC x == y.
intros.
apply union_subset_singl with (y':=y); auto with *.
*apply FXR_rel_inv_typ; trivial.
*intros ????; apply FXR_uniq.
Qed.


Lemma FXR_total : FX ⊆ FXR_dom.
apply FX_ind.
red; intros.  
 assert (fsub z ⊆ FXR_dom).
 {apply fsub_inv_F;[|trivial].
  apply Kdom. }
 assert (zfx : z ∈ FX).
 {rewrite FX_fix.
  revert H; apply Fmono.
  intro; apply subset_elim1. }
 apply subset_intro; trivial.
 exists (G' (cc_app (cc_lam (fsub z) FXREC)) z).
 assert (forall x, x ∈ fsub z -> FXR_rel x (FXREC x)).
 {intros x xsubz.
  apply H0 in xsubz.
  apply subset_ax in xsubz; destruct xsubz as (_,(x',eqx,(y,relx))).
  rewrite <-eqx in relx; clear x' eqx.
  rewrite FXR_eq with (1:=relx); trivial. }
 apply FXR_rel_intro with (X:=fsub z); auto.
 +apply Kfsub; trivial.
 +apply fsub_intro; trivial.
 +apply cc_prod_intro; intros; auto with *.
  apply FXR_rel_inv_typ; auto.
 +intros.
  rewrite cc_beta_eq; auto with *.
Qed.

Lemma FXR_FXREC x :
  x ∈ FX -> FXR_rel x (FXREC x).
intros tyx.
apply FXR_total in tyx.
apply subset_ax in tyx; destruct tyx as (_,(x',eqx,(y,relx))).
rewrite <-eqx in relx.
rewrite FXR_eq with (1:=relx); trivial.
Qed.

(*Lemma FXR_ex x :
  x ∈ FX -> exists y, FXR_rel x y.
intros tyx.
apply FXR_total in tyx.
apply subset_ax in tyx; destruct tyx as (_,(x',eqx,(y,relx))).
rewrite <-eqx in relx; eauto.
Qed.*)
(*
Lemma FXREC_eqn x :
    x ∈ FX ->
    FXREC x == G FXREC x.
intros.
destruct FXR_ex with (1:=H) as (y,rel).
rewrite FXR_eq with (1:=rel).
apply FXR_rel_elim in rel.
destruct rel as (X,(?,tyz),(recf,tyf,(eqy,rel))).
rewrite eqy; apply Gext with X; auto with *.
red; intros.
rewrite <- H2.
symmetry; apply FXR_eq; auto.
Qed.*)
Lemma FXREC_typ x :
  x ∈ FX -> FXREC x ∈ P x.
intros tyx.
apply FXR_FXREC in tyx.
apply FXR_rel_inv_typ in tyx; trivial.
Qed.

Lemma FXREC_ind Q x :
  Proper (eq_set==>eq_set==>iff) Q ->
  (forall y X, X ∈ K ->
   y ∈ F X ->
   (forall x, x ∈ X -> Q x (FXREC x)) ->
   Q y (G FXREC y)) ->            
  x ∈ FX ->
  Q x (FXREC x).
intros Qm Hrec tyx.
apply FXR_FXREC in tyx.
elim tyx using FXR_rel_ind.
{do 3 red; intros.
 rewrite H,H0; reflexivity. }
intros.
assert (eqf : eq_fun X (cc_app recf) FXREC).
{red; intros.
 rewrite <-H5; clear x' H5.
 symmetry; apply FXR_eq; auto. }
rewrite G'ext with (x:=y)(x':=y)(2:=eqf); auto with *.
unfold G'; rewrite cond_set_ok;[|rewrite FX_fix; revert H0;apply Fmono;auto].
apply Hrec with X; trivial.
intros.
red in eqf.
rewrite <-eqf with (x:=x0); auto with *.
Qed.

Lemma FXREC_eqn x :
    x ∈ FX ->
    FXREC x == G FXREC x.
intros tyx.
assert (eqG: forall y, y ∈ FX -> G FXREC y == G' FXREC y).
{intros; unfold G'; rewrite cond_set_ok; auto with *. }
rewrite eqG; trivial.
elim tyx using FXREC_ind; intros.
*intros ?? h ?? h'; rewrite h,h'; reflexivity. 
*apply eqG.
 rewrite FX_fix; revert H0;apply Fmono;auto.
Qed.

End BoundedRecursor.

Local Notation E := eq_set (only parsing).

Instance Kmorph0 F : morph1 (K F).
do 2 red; intros.
unfold K.
apply subset_morph; [rewrite H; reflexivity|].
red; intros; reflexivity.
Qed.
Instance Kmorph : Proper ((E==>E)==>E==>E) K.
do 3 red; intros.
unfold K.
apply subset_morph; [rewrite H0; reflexivity|].
red; intros.
rewrite (H _ _ (reflexivity x1)); reflexivity.
Qed.

Instance fsub_morph_gen  :
  Proper ((E==>E)==>E==>E==>E) fsub.
do 4 red; intros.
unfold fsub.
apply subset_morph; [trivial|].
red; intros.
apply fa_morph; intros X.
apply impl_morph.
*apply in_set_morph;[reflexivity|].
 apply Kmorph; trivial.
*intros.
 rewrite H1, (H _ _ (reflexivity X)); reflexivity.
Qed.

Instance FXR_rel_morph_gen :
  Proper ((E==>E)==>E==>(E==>E)==>((E==>E)==>E==>E)==>E==>E==>iff) FXR_rel. 
do 7 red; intros.
unfold FXR_rel.
apply fa_morph; intros Q.
apply fa_morph; intros Qm.
apply impl_morph;[|intros;rewrite H3,H4; reflexivity].
apply fa_morph; intros X.
apply fa_morph; intros y'.
apply fa_morph; intros recf.
apply impl_morph; 
  [apply in_set_morph;[reflexivity|apply Kmorph; trivial]|intros].
apply impl_morph; 
  [apply in_set_morph;[reflexivity|apply H; reflexivity]|intros].
apply impl_morph;[|intros].
*apply in_set_morph;[reflexivity|apply cc_prod_morph; auto with *].
*apply fa_morph; intros.
 apply Qm; [reflexivity|].
 unfold G'.
 apply cond_set_morph; [rewrite H0; reflexivity|].
 apply H2;[|reflexivity].
 apply cc_app_morph; reflexivity.
Qed.

Instance FXREC_morph :
  Proper ((E==>E)==>E==>(E==>E)==>((E==>E)==>E==>E)==>E==>E) FXREC. 
do 6 red; intros.
unfold FXREC.
apply union_morph.
apply subset_morph; auto.
red; intros.
apply FXR_rel_morph_gen; auto with *.
Qed.

(*Class subtermClass (K:set) :=
  { KinclFX : forall X, X ∈ K -> X ⊆ FX;
    Kinter : forall P:set->Prop,
      subset FX (fun b => forall X, X ∈ K -> P X -> b ∈ X) ∈ K;
    KFX : FX ∈ K }. *)
(*


Instance all_subterms : subtermClass (subset (power FX) (fun X => X ⊆ F X)).
set (K := subset (power FX) (fun X => X ⊆ F X)).
split.
*intros.
 apply subset_elim1 in H; rewrite power_def in H; trivial.
*intros.
 set (I := subset FX (fun b : set => forall X : set, X ∈ K -> P X -> b ∈ X)).
 assert (I == inter (singl FX ∪ subset K P)).
 {admit. }
 apply subset_intro; [rewrite power_def;intro; apply subset_elim1|].
 transitivity (F(inter (singl FX ∪ subset K P))).
2:rewrite <-H; reflexivity.
 red; intros.
 apply Fs.
 red; intros.
rewrite power_def.
apply union2_ax in H1; destruct H1.
apply singl_elim in H1; rewrite H1; reflexivity.
apply subset_elim1 in H1; eapply KinclFX; eauto.

apply inter_intro; intros.
rewrite replf_ax in H1.
destruct H1.
rewrite H2.
apply union2_ax in H1; destruct H1.
admit.

rewrite H in H0.
apply inter_elim with (1:=H0).
apply union2_intro


apply subset_ax in H1; destruct H1.
destruct H3.

 apply subset_ax in H.
 destruct H as (tyz,(z',eqz,clos)).



 rewrite eqz; apply clos.
apply subset_intro.
apply subset_intro.
 rewrite power_def.
 transitivity (F FX); [|apply eq_incl;symmetry; apply FX_fix].
 apply Fmono.
 intro; apply subset_elim1.

 apply Fmono.
 
 rewrite FX_fix.
 
*apply subset_intro; [rewrite power_def; reflexivity|].
 rewrite <- FX_fix; reflexivity.





Class subtermClass (K:set) :=
  { KinclFX : forall X, X ∈ K -> X ⊆ FX;
    Kinter : forall P,
      subset FX (fun b => forall X, X ∈ subset K P -> b ∈ X) ∈ K;
    KFX : FX ∈ K }. 


Instance direct_subterms : subtermClass (power FX).
split.
*intros.
 rewrite power_def in H; trivial.
*intros.
 rewrite power_def.
 intro; apply subset_elim1. 
*rewrite power_def; reflexivity.
Qed.

Instance all_subterms : subtermClass (subset (power FX) (fun X => X ⊆ F X)).
split.
*intros.
 apply subset_elim1 in H; rewrite power_def in H; trivial.
*intros.
 set (K := subset (subset (power FX) (fun X => X ⊆ F X)) P).
 apply subset_intro; [rewrite power_def;intro; apply subset_elim1|].
 red; intros.
 apply subset_ax in H.
 destruct H as (tyz,(z',eqz,clos)).
 rewrite eqz; apply clos.
apply subset_intro.
apply subset_intro.
 rewrite power_def.
 transitivity (F FX); [|apply eq_incl;symmetry; apply FX_fix].
 apply Fmono.
 intro; apply subset_elim1.

 apply Fmono.
 
 rewrite FX_fix.
 
*rewrite power_def; reflexivity.



  Variable K : set.
Hypothesis Kcl : subtermClass K.
(*Hypothesis KinclFX : forall X, X ∈ K -> X ⊆ FX.
Hypothesis Kinter :
  forall P,
    subset FX (fun b => forall X, X ∈ subset K P -> b ∈ X) ∈ K.
Hypothesis KFX : FX ∈ K. *)
(*Hypothesis Ksup :
  forall P, P ⊆ K -> union P ∈ K.*)

(*Definition compl Y :=
  subset FX (fun b => forall X, X ∈ subset K (fun X=>Y ⊆ X) -> b ∈ X).

Lemma Kcompl a : compl a ∈ K.
apply Kinter.
Qed.
*)
Hint Resolve KFX : core.

(** Strict subterms of [a] *)
Definition fsub a :=
  subset FX (fun b => forall X, X ∈ K -> a ∈ F X -> b ∈ X).

Instance fsub_morph : morph1 fsub.
unfold fsub; do 2 red; intros.
apply subset_morph; auto with *.
red; intros.
apply fa_morph; intro X.
rewrite H; reflexivity.
Qed.

Lemma Kfsub x : fsub x ∈ K.
unfold fsub.
apply in_reg
  with (subset FX (fun b => forall X, X ∈ subset K(fun X=>x ∈ F X)->b∈X)).
2:apply Kinter.
apply subset_morph; [reflexivity|].
red; intros.
apply fa_morph; intros Y.
rewrite subset_ax.
split; intros.
*apply H0.
 split; trivial.
 exists Y; auto with *.
*destruct H1 as (?,(Y',eqY,?)).
 apply H0; trivial.
 rewrite eqY; trivial.
Qed.

Lemma fsub_inv_F X x :
  X ∈ K ->
  x ∈ F X ->
  fsub x ⊆ X.
red; intros.
apply subset_ax in H1; destruct H1 as (_,(z',eqz,sub)).  
rewrite eqz; auto.
Qed.


Lemma fsub_intro x :
  x ∈ FX -> x ∈ F (fsub x).
intros tyx.
assert (x ∈ F (inter (subset K (fun X => x ∈ F X)))). 
{apply Fs.
 *red; intros.
  apply power_intro; intros.
  apply KinclFX with (X:=z); trivial.
  apply subset_elim1 in H; trivial.
 *apply inter_intro.
  +intros.
   rewrite replf_ax in H.
   destruct H.
   rewrite H0.
   apply subset_ax in H; destruct H as (?,(x',eqx,?)).   
   rewrite eqx; trivial.

   intros ??? h; auto.
  +exists FX.
   rewrite replf_ax.
   2:intros ??? h; auto.
   exists FX.
   2:apply FX_fix.
   apply subset_intro; auto.
   rewrite <- FX_fix; trivial.
}
revert H; apply Fmono.
red; intros.
apply subset_intro.
apply inter_elim with (1:=H).
apply subset_intro; auto.
rewrite <- FX_fix; trivial.

intros.
apply inter_elim with (1:=H).
apply subset_intro; trivial.
Qed.


(** Functions defined by recursion on subterms *)
Section Iter.

Variable G : (set -> set) -> set -> set.
Hypothesis Gm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) G.
Hypothesis Gext : forall X x x' g g',
    X ∈ K ->
    eq_fun X g g' ->
    x ∈ F X ->
    x == x' -> G g x == G g' x'.
(*
Definition G' F a :=
  cond_set (a ∈ FX) (G F a).

Lemma G'm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) G'.
do 3 red; intros.
apply cond_set_morph2.
 rewrite H0; reflexivity.

 intros.
 apply Gm; trivial.
 red; intros. 
 apply H; trivial.
Qed.

Lemma G'ext : forall x x' g g',
  x ∈ FX ->
  eq_fun (fsub x) g g' ->
  x == x' -> G' g x == G' g' x'.
intros.
apply cond_set_morph.
 rewrite H1; reflexivity.

 apply Gm; trivial.
Qed.
*)

Variable P : set -> set.
Hypothesis Pm : morph1 P.
Hypothesis G_typ : forall X y f,
  X ∈ K ->
  f ∈ (Π x ∈ X, P x) ->
  y ∈ F X ->
  G (cc_app f) y ∈ P y.

Definition FXR_rel x y :=
  forall Q, Proper (eq_set==>eq_set==>iff) Q ->
  (forall X y recf,
   X ∈ K ->
   y ∈ F X ->
   recf ∈ (Π x ∈ X, P x) ->
   (forall x, x ∈ X -> Q x (cc_app recf x)) -> 
   Q y (G (cc_app recf) y)) -> 
  Q x y.

Instance FXR_rel_morph : Proper (eq_set==>eq_set==>iff) FXR_rel.
do 3 red; intros.
apply fa_morph; intros Q.
apply fa_morph; intros Qm.
apply fa_morph; intros.
apply Qm; trivial.
Qed.

Definition FXREC x := union(subset (P x) (FXR_rel x)).

Instance FXREC_morph0 : morph1 FXREC.
do 2 red; intros.
apply union_morph; apply subset_morph;[auto|].
red; intros.
rewrite H; reflexivity.
Qed.


Lemma FXR_rel_intro X y f :
  X ∈ K ->
  y ∈ F X ->
  f ∈ (Π x ∈ X, P x) ->
  (forall x, x ∈ X -> FXR_rel x (cc_app f x)) -> 
  FXR_rel y (G (cc_app f) y).
red; intros.
apply H4 with (X:=X); trivial.
intros.
apply H2; trivial.
Qed.

Lemma FXR_rel_ind Q x y :
  Proper (eq_set==>eq_set==>iff) Q ->
  (forall X y recf,
   X ∈ K ->
   y ∈ F X ->
   recf ∈ (Π x ∈ X, P x) ->
   (forall x, x ∈ X -> FXR_rel x (cc_app recf x)) -> 
   (forall x, x ∈ X -> Q x (cc_app recf x)) -> 
   Q y (G (cc_app recf) y)) -> 
  FXR_rel x y -> Q x y.
intros Qm Hrec rel.
apply proj2 with (A:=FXR_rel x y).
apply rel; intros.
*do 3 red; intros.
 rewrite H,H0; reflexivity.
*split; [apply FXR_rel_intro with X; intros; auto; apply H2; trivial|].
 apply Hrec with (X:=X); trivial; apply H2; trivial.
Qed.

Lemma FXR_rel_inv_typ x y :
  FXR_rel x y -> y ∈ P x.
intros.
apply H.
{do 3 red; intros.
 rewrite H0, H1;reflexivity. }
intros.
apply G_typ with (X:=X); trivial.
Qed.

Lemma FXR_rel_elim x y :
  FXR_rel x y ->
  exists2 X, X ∈ K /\ x ∈ F X &
  exists2 recf, recf ∈ (Π x ∈ X, P x) &
    y == G (cc_app recf) x /\
    (forall x, x ∈ X -> FXR_rel x (cc_app recf x)).
intros rel.
elim rel using FXR_rel_ind; intros.
*do 3 red; intros.
 apply ex2_morph; intros X; auto with *;[rewrite H; reflexivity|].
 apply ex2_morph; intros recf'; auto with *.
 apply and_iff_morphism; [|reflexivity].
 apply eq_set_morph;[trivial|].
 apply Gm; [apply cc_app_morph;reflexivity|trivial].
*exists X; auto.
 exists recf; auto with *.
Qed.

Definition FXR_dom := subset FX (fun x => exists y, FXR_rel x y).

Lemma FXR_dom_F :
  FXR_dom ⊆ F FXR_dom.
red; intros.
apply subset_ax in H; destruct H as (_,(z',eqz,(y,relz))).
rewrite <-eqz in relz; clear z' eqz.
apply FXR_rel_elim in relz.
destruct relz as (X,(?,tyz),(recf,tyf,(eqy,rel))).
clear y eqy.
revert z tyz; apply Fmono.
red; intros.
apply subset_intro.
*revert H0; apply KinclFX; trivial.
*eauto.
Qed.

Lemma FXR_uniq x y y':
  FXR_rel x y -> FXR_rel x y' -> y==y'.
intros img1 img2.
revert y' img2.
apply img1.
*do 3 red; intros.
 apply fa_morph; intros y'.
 rewrite H,H0; reflexivity.
*intros X x' f tyX tyx' tyf Hrec y' imgy'.
 apply FXR_rel_elim in imgy'.
 destruct imgy' as (X',(?,?),(f',tyf',(eqy',relf'))).
 rewrite eqy'.
 apply Gext with (X:=fsub x'); auto with *.
 +apply Kfsub.
 +red; intros.
  apply Hrec.
  apply fsub_inv_F with x'; auto.
  rewrite <-H2.
  apply (relf' x0).
  apply fsub_inv_F with x'; auto.
 +apply fsub_intro.
  rewrite FX_fix.
  revert tyx'; apply Fmono.
  apply KinclFX; auto.
Qed.

Lemma FXR_eq x y :
  FXR_rel x y -> FXREC x == y.
intros.
apply union_subset_singl with (y':=y); auto with *.
*apply FXR_rel_inv_typ; trivial.
*intros ????; apply FXR_uniq.
Qed.

Hypothesis Kdom : FXR_dom ∈ K.

Lemma FXR_total : FX ⊆ FXR_dom.
apply FX_ind.
red; intros.  
 assert (fsub z ⊆ FXR_dom).
 {apply fsub_inv_F; trivial. }
 assert (zfx : z ∈ FX).
 {rewrite FX_fix.
  revert H; apply Fmono.
  intro; apply subset_elim1. }
 apply subset_intro; trivial.
 exists (G (cc_app (cc_lam (fsub z) FXREC)) z).
 assert (forall x, x ∈ fsub z -> FXR_rel x (FXREC x)).
 {intros x xsubz.
  apply H0 in xsubz.
  apply subset_ax in xsubz; destruct xsubz as (_,(x',eqx,(y,relx))).
  rewrite <-eqx in relx; clear x' eqx.
  rewrite FXR_eq with (1:=relx); trivial. }
 apply FXR_rel_intro with (X:=fsub z); auto.
 +apply Kfsub.
 +apply fsub_intro; trivial.
 +apply cc_prod_intro; intros; auto with *.
  apply FXR_rel_inv_typ; auto.
 +intros.
  rewrite cc_beta_eq; auto with *.
Qed.

Lemma FXR_ex x :
  x ∈ FX -> exists y, FXR_rel x y.
intros tyx.
apply FXR_total in tyx.
apply subset_ax in tyx; destruct tyx as (_,(x',eqx,(y,relx))).
rewrite <-eqx in relx; eauto.
Qed.
(*
Lemma FXREC_eqn x :
    x ∈ FX ->
    FXREC x == G FXREC x.
intros.
destruct FXR_ex with (1:=H) as (y,rel).
rewrite FXR_eq with (1:=rel).
apply FXR_rel_elim in rel.
destruct rel as (X,(?,tyz),(recf,tyf,(eqy,rel))).
rewrite eqy; apply Gext with X; auto with *.
red; intros.
rewrite <- H2.
symmetry; apply FXR_eq; auto.
Qed.*)

Lemma FXREC_ind Q x :
  Proper (eq_set==>eq_set==>iff) Q ->
  (forall y X, X ∈ K ->
   (forall x, x ∈ X -> Q x (FXREC x)) ->
   (Q y (G FXREC y))) ->            
  x ∈ FX ->
  Q x (FXREC x).
intros Qm Hrec tyx.
assert (FXR_rel x (FXREC x)).
{destruct FXR_ex with (1:=tyx) as (y,rel).
 rewrite FXR_eq with (1:=rel); trivial. }
elim H using FXR_rel_ind.
{do 3 red; intros.
 rewrite H0,H1; reflexivity. }
intros.
assert (eqf : eq_fun X (cc_app recf) FXREC).
{red; intros.
 rewrite <-H6; clear x' H6.
 symmetry; apply FXR_eq; auto. }
rewrite Gext with (x:=y)(x':=y)(2:=eqf); auto with *.
apply Hrec with X; trivial.
intros.
red in eqf.
rewrite <-eqf with (x:=x0); auto with *.
Qed.

Lemma FXREC_eqn x :
    x ∈ FX ->
    FXREC x == G FXREC x.
intros tyx.
elim tyx using FXREC_ind; intros; [|reflexivity].
intros ?? h ?? h'; rewrite h,h'; reflexivity. 
Qed.
 *)

