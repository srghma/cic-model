Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFstable ZFord.
Require Import ZFgrothendieck.
Require Import ZFlist.
Require Import ZFcoc.

Definition complete o X := forall f,
  increasing_bounded o f ->
  (exists2 o', o' ∈ o & forall o'', o' ⊆ o'' -> o'' ∈ o -> f o'' ∈ X) ->
  sup o f ∈ X.

Lemma complete_power X o :
  isOrd o ->
  complete o (power X).
red; intros.
apply power_intro; intros.
rewrite sup_ax in H2; auto.
destruct H2 as (i, lto, zin).
assert (io : isOrd i) by eauto using isOrd_inv.
destruct H1 as (o',o'lto,limf).
apply power_elim with (f (i ⊔ o')).
*apply limf; auto.
 apply osup2_incl2; trivial.
 apply osup2_lt; trivial.
*revert zin; apply H0; auto.
  apply osup2_lt; trivial.
  apply osup2_incl1; trivial.
Qed.

(** * Low-level construction: encoding W-types as sets of path in a tree *)

Section W_Domain.

(* The first parameter of W-types (aka the payload) *)
Variable A : set.
(* The subterm index type *)
Variable B : set -> set.
Hypothesis Bm : morph1 B.

(** The construction domain and the constructor. Note that the constructor does not
    use A or B. *)
Definition Wdom := rel (List (sup A B)) A.

Definition Wsup x f :=
   singl (couple Nil x) ∪
   replf (subset f (fun z => z == couple (fst z) (couple (fst (snd z)) (snd (snd z)))))
     (fun z => couple (Cons (fst z) (fst (snd z))) (snd (snd z))).

Global Instance Wsup_morph : morph2 Wsup.
do 3 red; intros.
unfold Wsup.
apply union2_morph.
 rewrite H; reflexivity.

 apply replf_morph_raw.
  apply subset_morph; trivial.
  red; intros; reflexivity.

  red; intros.
  rewrite H1; reflexivity.
Qed.


Lemma Wsup_def x f p :
  (p ∈ Wsup x f <->
   p == couple Nil x \/
   exists i l y, couple i (couple l y) ∈ f /\ p == couple (Cons i l) y).
unfold Wsup.
rewrite union2_ax.
rewrite replf_ax.
apply or_iff_morphism.
 split; intros.
  apply singl_elim in H; trivial.
  rewrite H; apply singl_intro.

 split; intros.
  destruct H as (z,z_in_f,eqp).
  rewrite subset_ax in z_in_f.
  destruct z_in_f as (z_in_f,(z',eqz,etaz)).
  rewrite <- eqz in etaz; clear z' eqz.
  rewrite etaz in z_in_f.
  do 3 econstructor; split; [exact z_in_f|trivial].

  destruct H as (i&l&y&in_f&etap).
  exists (couple i (couple l y)).
   apply subset_intro; trivial.
   rewrite snd_def, !fst_def, snd_def.
   reflexivity.

   rewrite snd_def, !fst_def, snd_def.
   trivial.

 do 2 red; intros.
 rewrite H0; reflexivity.
Qed.

Lemma Wsup_hd_prop a x f :
  couple Nil a ∈ Wsup x f <-> a == x.
rewrite Wsup_def.
split; intros.
 destruct H as [eqc|(i&l&y&_&eqc)].
  apply couple_injection in eqc; destruct eqc; trivial.

  apply couple_injection in eqc; destruct eqc as (eqc,_).
  apply discr_mt_couple in eqc; contradiction.

 left; rewrite H; reflexivity.
Qed.

Lemma Wsup_tl_prop i l a x f :
  couple (Cons i l) a ∈ Wsup x f <-> couple l a ∈ cc_app f i.
rewrite Wsup_def.
rewrite <- couple_in_app.
split; intros.
 destruct H as [eqc|(i'&l'&y&in_f&eqc)].
  apply couple_injection in eqc; destruct eqc as (eqc,_).
  symmetry in eqc.
  apply discr_mt_couple in eqc; contradiction.

  apply couple_injection in eqc; destruct eqc as (eqc,eqa).
  apply couple_injection in eqc; destruct eqc as (eqi,eql).
  rewrite eqi,eql,eqa; auto.

 right.
 exists i; exists l; exists a; auto with *.
Qed.

Lemma Wsup_incl_hd_inv x x' f f' :
    Wsup x f ⊆ Wsup x' f' -> x==x'.
intros.
assert (couple Nil x ∈ Wsup x' f').
{apply H.
 apply Wsup_def; auto with *. }
apply Wsup_hd_prop in H0; trivial.
Qed.

Lemma Wsup_mono x x' f f' :
  x == x' ->
  is_cc_fun (B x) f ->
  (forall i, i ∈ B x -> cc_app f i ⊆ cc_app f' i) ->
  Wsup x f ⊆ Wsup x' f'.
intros eqx tyf lef; rewrite <- eqx; clear x' eqx.
intros z; rewrite !Wsup_def.
destruct 1; auto.
right.
destruct H as (i&l&y&isp&eqz).
exists i; exists l; exists y; split; trivial.
assert (i ∈ B x).
{apply tyf in isp.
 destruct isp as (_,ity). 
 rewrite fst_def in ity; trivial. }
rewrite couple_in_app in isp|-*.
apply lef; trivial.
Qed.

Lemma Wsup_typ_gen x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, Wdom) ->
  Wsup x f ∈ Wdom.
intros.
assert (tyf := cc_prod_is_cc_fun _ _ _ H0).
apply power_intro; intros.
rewrite Wsup_def in H1; trivial.
destruct H1 as [eqz|(i&l&y&in_f&eqz)]; rewrite eqz.
 apply couple_intro; trivial.
 apply Nil_typ.

 destruct tyf with (1:=in_f) as (_,tyi).
 rewrite fst_def in tyi.
 specialize cc_prod_elim with (1:=H0) (2:=tyi); intros tyapp.
 rewrite couple_in_app in in_f.
 apply power_elim with (2:=in_f) in tyapp.
 apply couple_intro.
  apply Cons_typ.
   rewrite sup_ax; eauto with *.
   apply fst_typ in tyapp; rewrite fst_def in tyapp; trivial.

  apply snd_typ in tyapp; rewrite snd_def in tyapp; trivial.
Qed.


(** Inverse of Wsup: Wfst and Wsnd_fun *)

Definition Wfst w :=
  snd (union (subset w (fun p => exists x, p == couple Nil x))).

Global Instance Wfst_morph : morph1 Wfst.
do 2 red; intros.
unfold Wfst.
apply snd_morph; apply union_morph.
apply subset_morph; trivial.
red; intros.
reflexivity.
Qed.

Lemma Wfst_def x f :
  Wfst (Wsup x f) == x.
unfold Wfst.
rewrite union_subset_singl with (y:=couple Nil x)(y':=couple Nil x); auto with *.
 apply snd_def.

 rewrite Wsup_hd_prop; reflexivity.

 exists x; reflexivity.

 intros y y' tyy tyy' (x1,eqy) (x2,eqy').
 rewrite eqy in tyy|-*.
 rewrite eqy' in tyy'|-*.
 rewrite Wsup_hd_prop in tyy.
 rewrite Wsup_hd_prop in tyy'.
 rewrite tyy,tyy'; reflexivity.
Qed.

(** The family of subterms *)
Definition Wsnd_fun w :=
   replf (subset w (fun z => exists i l x, z == couple (Cons i l) x))
     (fun z => couple (fst (fst z)) (couple (snd (fst z)) (snd z))).

Global Instance Wsnd_fun_morph : morph1 Wsnd_fun.
do 2 red; intros.
unfold Wsnd_fun.
apply replf_morph_raw.
 apply subset_morph; auto with *.
red; intros.
rewrite H0; reflexivity.
Qed.


Lemma Wsnd_fun_raw0 w z :
  z ∈ Wsnd_fun w <-> z == couple (fst z) (couple (fst (snd z)) (snd (snd z))) /\
                          couple (Cons (fst z) (fst (snd z))) (snd (snd z)) ∈ w.
unfold Wsnd_fun; intros.
rewrite replf_ax.
2:do 2 red; intros; rewrite H0; reflexivity.
split; intros.
 destruct H as (t,?,?).
 rewrite H0; rewrite !snd_def, !fst_def.
 split; [reflexivity|].
 apply subset_ax in H; destruct H as (?,(t',eqt',(i0&l0&x0&eqt))).
 rewrite eqt',eqt,!fst_def,!snd_def.
 rewrite eqt',eqt in H; trivial.

 destruct H.
 exists (couple (Cons (fst z) (fst (snd z))) (snd (snd z))).
  apply subset_intro; trivial.
  eexists; eexists; eexists; reflexivity.

  unfold Cons; rewrite H, !snd_def, !fst_def, !snd_def; reflexivity.
Qed.

Lemma Wsnd_fun_raw i p x w :
  couple i (couple p x) ∈ Wsnd_fun w <-> couple (Cons i p) x ∈ w.
rewrite Wsnd_fun_raw0, !fst_def, !snd_def, !fst_def.
split; auto with *.
destruct 1; trivial.
Qed.


Lemma Wsnd_fun_def_raw x f :
  Wsnd_fun (Wsup x f) ==
  subset f (fun z => z == couple (fst z) (couple (fst (snd z)) (snd (snd z)))).
apply eq_set_ax; intros z.
rewrite Wsnd_fun_raw0.
rewrite Wsup_def.
rewrite subset_ax.
split.
+intros (eqz,[abs|(i & l & y & inf & eqc)]).
 *exfalso.
  apply couple_injection in abs; destruct abs as (abs,_).
  symmetry in abs; apply discr_mt_couple in abs; trivial.
 *apply couple_injection in eqc; destruct eqc as (eql,eqy).
  apply couple_injection in eql; destruct eql as (eqi,eql).
  rewrite <-eqi,<-eql,<-eqy in inf.  
  rewrite <- eqz in inf.
  split; trivial.
  exists z; [reflexivity|trivial].
+intros (inf,(z',eqz,eqc)).
 rewrite <- eqz in eqc.
 split; trivial. 
 right.
 rewrite eqc in inf.
 eauto 20 with *.
Qed.
 
Lemma Wsnd_fun_def_dom Y x f :
  f ∈ (Π i ∈ Y, Wdom) ->
  Wsnd_fun (Wsup x f) == f.
intros tyf.
rewrite Wsnd_fun_def_raw.
symmetry; apply subset_ext; intros; trivial.
exists x0; auto with *.
destruct (cc_prod_is_cc_fun _ _ _ tyf _ H) as (eqx,tyx).
apply transitivity with (1:=eqx).
apply couple_morph;[reflexivity|].
rewrite eqx in H.
rewrite couple_in_app in H.
specialize cc_prod_elim with (1:=tyf) (2:=tyx); intros tyapp.
apply power_elim with (2:=H) in tyapp.
apply surj_pair in tyapp; trivial.
Qed.


(** The individual subterms Wsnd can be derived from Wsnd_fun, but expressing
    Wsnd_fun in terms of Wsnd would require to depend on parameter B, which we
    rather avoid here. *)
Definition Wsnd w i := cc_app (Wsnd_fun w) i.

Global Instance Wsnd_morph : morph2 Wsnd.
do 3 red; intros.
apply cc_app_morph; trivial.
apply Wsnd_fun_morph; trivial.
Qed.

Lemma Wsnd_mono w1 w2 x :
  w1 ⊆ w2 ->
  Wsnd w1 x ⊆ Wsnd w2 x.
unfold Wsnd, Wsnd_fun; intros.
red; intros.  
rewrite <- couple_in_app in H0|-*.
revert H0; apply replf_mono_raw.
 intros z0.
 rewrite subset_ax.
 rewrite subset_ax.
 destruct 1; auto.

 red; intros.
 rewrite H0; reflexivity.
Qed.

Lemma Wsnd_def_raw i p x w :
  couple p x ∈ Wsnd w i <-> couple (Cons i p) x ∈ w.
unfold Wsnd.
rewrite <- couple_in_app.
rewrite Wsnd_fun_raw0; rewrite !snd_def, !fst_def.
split; auto with *.
destruct 1; trivial.
Qed.

Lemma Wsnd_def x f i :
  cc_app f i ∈ Wdom ->
  Wsnd (Wsup x f) i == cc_app f i.
intros tyf.
unfold Wsnd; rewrite Wsnd_fun_def_raw.
apply eq_set_ax; split; intros.
 apply couple_in_app in H.
 apply subset_ax in H; destruct H as (?,_).
 apply couple_in_app; trivial.

 apply couple_in_app. 
 apply subset_intro.
  apply couple_in_app; trivial.

  rewrite fst_def, snd_def.
  apply couple_morph;[reflexivity|].
  apply power_elim with (2:=H) in tyf.
  apply surj_pair in tyf; trivial.
Qed.

Lemma Wsup_inj x x' f f' :
  x ∈ A ->
  x' ∈ A ->
  (forall i, i ∈ B x -> cc_app f i ∈ Wdom) ->
  (forall i, i ∈ B x' -> cc_app f' i ∈ Wdom) ->
  Wsup x f == Wsup x' f' -> x == x' /\ (forall i, i ∈ B x -> cc_app f i == cc_app f' i).
intros tyx tyx' tyf tyf' eqw.
assert (eqx : x==x').
{rewrite <- (Wfst_def x f).
 rewrite <- (Wfst_def x' f').
 rewrite eqw; reflexivity. }
split; intros; trivial.
rewrite <- (Wsnd_def x f i); auto.
rewrite eqx in H.
rewrite <- (Wsnd_def x' f' i); auto.
rewrite eqw; reflexivity.
Qed.


(** The type operator on the construction domain *)
Definition Wf X :=
  sup A (fun x => replf (Π __ ∈ B x, X) (fun f => Wsup x f)). 

Hint Resolve Wsup_morph : core.

Lemma Wf_intro X x f :
  x ∈ A ->
  f ∈ cc_prod (B x) (fun _ => X) ->
  Wsup x f ∈ Wf X.
intros.
unfold Wf.
rewrite sup_ax.
 exists x; trivial.
 rewrite replf_ax; auto with *.
  exists f; auto with *.

  do 2 red; intros; apply Wsup_morph; auto with *.

 do 2 red; intros.
 apply replf_morph_raw.
  apply cc_prod_morph; auto with *.
  red; intros; reflexivity.

  red; intros; apply Wsup_morph; trivial.
Qed.

Lemma Wf_elim : forall a X,
  a ∈ Wf X ->
  exists2 x, x ∈ A & exists2 f, f ∈ Π i ∈ B x, X & a == Wsup x f.
intros.
unfold Wf in H.
rewrite sup_ax in H.
 destruct H as (x,tyx,tya).
 rewrite replf_ax in tya.
  destruct tya as (f,tyf,eqa).
  exists x; trivial.
  exists f; trivial.

  do 2 red; intros; apply Wsup_morph; auto with *.

 do 2 red; intros.
 apply replf_morph_raw.
  apply cc_prod_morph; auto with *.
  red; intros; reflexivity.

  red; intros; apply Wsup_morph; trivial.
Qed.

Lemma Wf_elim' X x f :
  x ∈ A ->
  (forall i, i ∈ B x -> cc_app f i ∈ Wdom) ->
  X ⊆ Wdom ->
  Wsup x f ∈ Wf X ->
  forall i, i ∈ B x -> cc_app f i ∈ X.
intros tyx tyf Xincl tyw.
apply Wf_elim in tyw.
destruct tyw as (x',tyx',(f',tyf',eqw)).
apply Wsup_inj in eqw; intros; auto.
trivial.
 destruct eqw as (eqx,eqf).
 rewrite eqf; trivial.
 apply cc_prod_elim with (1:=tyf').
 rewrite <- eqx; trivial.

 apply Xincl.
 apply cc_prod_elim with (1:=tyf'); trivial.
Qed.

Instance Wf_mono : Proper (incl_set ==> incl_set) Wf.
intros X Y inclXY a tya.
apply Wf_elim in tya; destruct tya as (x,tyx,(f,tyf,eqz)); rewrite eqz.
apply Wf_intro; trivial.
revert tyf; apply cc_prod_covariant; auto with *.
Qed.

Instance Wf_morph : morph1 Wf.
apply Fmono_morph; auto with *.
Qed.
Hint Resolve Wf_mono Wf_morph : core.

Lemma Wf_typ X :
  X ⊆ Wdom -> Wf X ⊆ Wdom.
red; intros.
apply Wf_elim in H0; destruct H0 as (x,tyx,(f,tyf,eqz)); rewrite eqz.
apply Wsup_typ_gen; trivial.
revert tyf; apply cc_prod_covariant; auto with *.
Qed.
Hint Resolve Wf_typ : core.

Lemma Wfst_typ_gen X w :
  w ∈ Wf X ->
  Wfst w ∈ A.
intros tyw.
apply Wf_elim in tyw; trivial.
destruct tyw as (x,tyx,(f,tyf,eqw)).
rewrite eqw,Wfst_def; trivial.
Qed.

Lemma Wsnd_fun_typ_gen X w :
  X ⊆ Wdom ->
  w ∈ Wf X ->
  Wsnd_fun w ∈ Π __ ∈ B (Wfst w), X.
intros XinclW tyw.
apply Wf_elim in tyw; trivial.
destruct tyw as (x,tyx,(f,tyf,eqw)).
apply in_reg with f.
 rewrite eqw, Wsnd_fun_def_dom.
 reflexivity.
 eapply cc_prod_covariant;[|reflexivity|intros; apply XinclW|].
  do 2 red; reflexivity.
  exact tyf.
apply eq_elim with (2:=tyf).
apply cc_prod_ext.
 rewrite eqw,Wfst_def; reflexivity.
 red; reflexivity.
Qed.

Lemma Wsnd_typ_gen X w i :
  X ⊆ Wdom ->
  w ∈ Wf X ->
  i ∈ B (Wfst w) ->
  Wsnd w i ∈ X.
intros.
apply Wsnd_fun_typ_gen in H0; trivial.
apply cc_prod_elim with (1:=H0); trivial.
Qed.


Lemma Wf_stable_gen (K:set->Prop) :
  (forall X, K X -> X ⊆ Wdom) ->
 stable_class K Wf.
red; intros Kdef X Xty z H.
assert (forall a, a ∈ X -> z ∈ Wf a).
 intros.
 apply inter_elim with (1:=H).
 rewrite replf_ax.
 2:red;red;intros;apply Wf_morph; trivial.
 exists a; auto with *.
destruct inter_wit with (2:=H); auto.
assert (tyz := H0 _ H1).
apply Wf_elim in tyz.
destruct tyz as (x',tyx,(f,tyf,eqz)).
rewrite eqz.
apply Wf_intro; trivial.
rewrite cc_eta_eq with (1:=tyf).
apply cc_prod_intro; intros.
 intros ? ? ? h; rewrite h; reflexivity.
 do 2 red; reflexivity.
apply inter_intro; eauto.
intros.
specialize H0 with (1:=H3).
apply Wf_elim in H0.
destruct H0 as (x'',tyx',(f',tyf',eqz')).
rewrite eqz in eqz'.
apply Wsup_inj in eqz'; trivial; intros.
 destruct eqz' as (eqx,eqf).
 rewrite eqf; trivial.
 apply cc_prod_elim with (1:=tyf').
 rewrite <- eqx; trivial.

 apply (Kdef x); auto.
 apply cc_prod_elim with (1:=tyf); trivial.

 apply (Kdef y); auto.
 apply cc_prod_elim with (1:=tyf'); trivial.
Qed.
  
Section Wdom_Universe.

  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : ZFord.omega ∈ U.  

  Hypothesis aU : A ∈ U.
  Hypothesis bU : forall a, a ∈ A -> B a ∈ U.

  Lemma G_Wdom : Wdom ∈ U.
unfold Wdom.
apply G_rel; trivial.
apply G_List; trivial.
apply G_sup; trivial.
apply morph_is_ext; trivial.
Qed.

End Wdom_Universe.

(*******************************************************************************************)
(* Specific properties related to adding a bottom to the type (for strong normalization
   proofs) *)

Section SN_Auxiliary.

  Lemma mt_not_in_Wf X : ~ empty ∈ Wf X.
intro.
apply Wf_elim in H.
destruct H as (x,_,(f,_,?)).
apply empty_ax with (x:=couple Nil x).
rewrite H; apply Wsup_def; auto with *.
Qed.

  Lemma Wdom_cc_bot X :
    X ⊆ Wdom -> cc_bot X ⊆ Wdom.
red; intros.
apply cc_bot_ax in H0; destruct H0; auto.
rewrite H0; apply power_intro; intros.
apply empty_ax in H1; contradiction.
Qed.

  Definition Wfbot X := Wf (cc_bot X).

  Instance Wfbot_mono : Proper (incl_set ==> incl_set) Wfbot.
do 2 red; intros.
unfold Wfbot; apply Wf_mono; trivial.
apply cc_bot_mono; trivial.
Qed.

  Instance Wfbot_morph : morph1 Wfbot.
apply Fmono_morph; auto with *.
Qed.

  Hint Resolve Wfbot_mono Wfbot_morph : core.

  Lemma mt_not_in_Wfbot o x :
    isOrd o ->
    x ∈ TI Wfbot o ->
    ~ x == empty.
red; intros.
apply TI_elim in H0; auto with *.
destruct H0 as (o',?,?).
rewrite H1 in H2.
apply mt_not_in_Wf in H2; trivial.
Qed.

Lemma Wfbot_typ : forall X,
  X ⊆ Wdom -> Wfbot X ⊆ Wdom.
intros.
unfold Wfbot; apply Wf_typ; trivial.
apply Wdom_cc_bot; trivial.
Qed.
Hint Resolve Wfbot_typ : core.

Lemma TI_Wfbot_typ o :
  isOrd o ->
  TI Wfbot o ⊆ Wdom.
induction 1 using isOrd_ind; intros.
red; intros.
apply TI_elim in H2; auto.
destruct H2.
revert H3; apply Wfbot_typ; auto.
Qed.


Lemma Wfbot_stable_gen K :
  (forall X, K X -> X ⊆ Wdom /\ (forall z, z ∈ X -> z==empty \/ ~z==empty)) ->
  stable_class K Wfbot.
intros Fprop.
apply compose_stable_class with (F:=Wf) (K1:=fun X => X ⊆ Wdom); trivial.
 do 2 red; intros.
 rewrite H; reflexivity.

 apply cc_bot_morph.

 apply Wf_stable_gen; intros; trivial.

 apply cc_bot_stable; intros.
 apply (proj2 (Fprop _ H)); trivial.

 intros X KX.
 apply Wdom_cc_bot.
 apply Fprop; trivial.
Qed.
  
End SN_Auxiliary.

(*******************************************************************************************)
(* Specific properties related to building corecusrion by
   transifinite iteration: build an element of a W-type as the
   limit of a directed family. *)

Section Corecursion_Auxiliary.
  
Lemma pre_incl_eq X w1 w2 :
  X ⊆ Wdom ->
  X ⊆ Wf X -> (* X is closed by subterm *)
  w1 ∈ X ->
  w2 ∈ X ->
  w1 ⊆ w2 ->
  w2 == w1.
intros Xty Xcl cw1 cw2 incl12.
apply incl_eq; trivial.
red; intros.
assert (tyz : exists2 p, p ∈ List (sup A B) & exists2 a, a ∈ A & z == couple p a).
{specialize power_elim with (1:=Xty _ cw2) (2:=H); intros.
 exists (fst z);[apply fst_typ in H0; trivial|].
 exists (snd z);[apply snd_typ in H0; trivial|].
 apply surj_pair with (1:=H0). }
destruct tyz as (p,typ,(a,tya,eqz)).
assert (forall a w1 w2, a ∈ A -> w1 ⊆ w2 -> w1 ∈ X -> w2 ∈ X ->
                        couple p a ∈ w2 -> couple p a ∈ w1).
{clear z eqz incl12 cw1 cw2 H w1 w2 a tya.
 elim typ using List_ind; intros.
 {do 2 red; intros.
  apply fa_morph; intros a.
  apply fa_morph; intros w1.
  apply fa_morph; intros w2.
  rewrite H; reflexivity. }

 {apply Xcl in H1; apply Wf_elim in H1; destruct H1 as (a1,_,(f1,_,eqw1)).
  apply Xcl in H2; apply Wf_elim in H2; destruct H2 as (a2,_,(f2,_,eqw2)).
  rewrite eqw1 in H0|-*; rewrite eqw2 in H0,H3; clear eqw1 eqw2.
  apply Wsup_incl_hd_inv in H0.
  apply Wsup_hd_prop in H3; apply Wsup_hd_prop.
  rewrite H0; trivial. }

 {assert (tyw2 :=H5).
  apply Xcl in H4; apply Wf_elim in H4; destruct H4 as (a1,_,(f1,tyf1,eqw1)).
  apply Xcl in H5; apply Wf_elim in H5; destruct H5 as (a2,_,(f2,tyf2,eqw2)).
  rewrite eqw1 in H3|-*; rewrite eqw2 in H3,H6,tyw2; clear eqw1 eqw2.
  assert (same_x := H3); apply Wsup_incl_hd_inv in same_x.
  apply Wsup_tl_prop in H6; apply Wsup_tl_prop.
  assert (tyx2 : x ∈ B a2).
  {apply couple_in_app in H6.
   apply cc_prod_is_cc_fun in tyf2.
   apply tyf2 in H6.
   destruct H6 as (_,tyx).
   rewrite fst_def in tyx; trivial. }
  assert (tyx1 : x ∈ B a1).
  {rewrite same_x; trivial. }
  revert H6; apply H1; auto.
  +apply Wsnd_mono with (x:=x) in H3; auto.
   rewrite !Wsnd_def in H3; auto.
    apply Xty; apply cc_prod_elim with (1:=tyf2); trivial.
    apply Xty; apply cc_prod_elim with (1:=tyf1); trivial.
  +apply cc_prod_elim with (1:=tyf1); trivial.
  +apply cc_prod_elim with (1:=tyf2); trivial. } }
revert H; rewrite eqz; apply H0; trivial.
Qed.

Lemma Wsup_sup o o' X f :
  isOrd o ->
  o' ∈ o ->
  increasing_bounded o f ->
  X ⊆ Wdom ->
  (forall i, o' ⊆ i -> i ∈ o -> f i ∈ Wf X) ->
  exists2 a0, a0 ∈ A &
    sup o f == Wsup a0 (λ i ∈ B a0, sup o (fun x => Wsnd (f x) i)).
intros oo lto fincr Xty finX.
assert (oo' : isOrd o') by eauto using isOrd_inv.
assert (fext : ext_fun o f) by auto.
assert (eqsm : forall A, ext_fun A (fun i1 => sup o (fun x => Wsnd (f x) i1))).
{do 2 red; intros.
 apply sup_morph; auto with *.
 red; intros.
 apply Wsnd_morph; auto. }
assert (sfm : forall i, ext_fun o (fun x => Wsnd (f x) i)).
{do 2 red; intros.
 apply Wsnd_morph; auto with *. }
assert (oio : o' ⊆ o') by reflexivity.
assert (tyf0 := finX o' oio lto).
apply Wf_elim in tyf0; destruct tyf0 as (a0,tya0,(f0,tyf0,eqf0)).
exists a0; trivial.
apply eq_set_ax; intros z.
rewrite sup_ax; trivial.
split; intros. 
*destruct H as (y,tyy,tyz).
 assert (yo : isOrd y) by eauto using isOrd_inv.
 pose (y' := y ⊔ o').
 assert (tyy' : f y' ∈ Wf X).
 {apply finX; auto.
  apply osup2_incl2; trivial.
  apply osup2_lt; auto. }
 apply Wf_elim in tyy'; destruct tyy' as (a1,_,(f1,tyf1,eqf1)).
 assert (fdir: f o' ⊆ f y').
 {apply fincr; auto.
  apply osup2_lt; auto.
  apply osup2_incl2; trivial. }
  rewrite eqf0,eqf1 in fdir.
 apply Wsup_incl_hd_inv in fdir.
 assert (fdir' : f y ⊆ f y').
 {apply fincr; auto.
  apply osup2_lt; auto.
  apply osup2_incl1; trivial. }
 rewrite eqf1 in fdir'.
 apply fdir' in tyz.
 revert tyz; apply Wsup_mono; auto with *.
  apply cc_prod_is_cc_fun in tyf1; trivial.
  intros.
  rewrite cc_beta_eq; auto.
  2:rewrite fdir; trivial.
  rewrite <- (Wsnd_def a1 f1 i),<-eqf1.
  apply sup_incl with (1:=sfm i); trivial.
  apply osup2_lt; trivial.
  apply Xty; apply cc_prod_elim with (1:=tyf1); trivial.

*apply Wsup_def in H.
 destruct H as [?|(i&l&y&?&eqz)].
  exists o'; trivial.
  rewrite H,eqf0.
  apply Wsup_def; auto with *.
 
  apply cc_lam_def in H; trivial.
  destruct H as (x,tyx,(y',tyy',eqq)).
  apply couple_injection in eqq; destruct eqq.
  rewrite <- H0 in tyy'.
  apply sup_ax in tyy'; trivial.
  destruct tyy' as (y'',?,?).
  exists y''; trivial.
  rewrite eqz.
  apply Wsnd_def_raw.
  rewrite H; trivial.
Qed.

  Lemma Wf_complete o X :
    isOrd o ->
    X ⊆ Wdom -> complete o X -> complete o (Wf X).
intros oo tyX Xcl.
red in Xcl.
red; intros f fincr (o',lto, limf).  
assert (fext : ext_fun o f) by auto.
assert (eqsm : forall A, ext_fun A (fun i1 => sup o (fun x => Wsnd (f x) i1))).
{do 2 red; intros.
 apply sup_morph; auto with *.
 red; intros.
 apply Wsnd_morph; auto. }
assert (sfm : forall i, ext_fun o (fun x => Wsnd (f x) i)).
{do 2 red; intros.
 apply Wsnd_morph; auto with *. }
destruct Wsup_sup with (3:=fincr)(4:=tyX)(2:=lto) as (a,tya,eqf); trivial. 
rewrite eqf; apply Wf_intro; trivial.
apply cc_prod_intro; intros; auto.
apply Xcl; auto.
+red; intros.
 apply Wsnd_mono.
 apply fincr; auto.
+exists o'; trivial.
 intros.
 specialize limf with (1:=H0)(2:=H1).
 apply Wf_elim in limf; destruct limf as (a1,_,(f1,tyf1,eqf1)).
 assert (f o'' ⊆ sup o f) by auto.
 rewrite eqf, eqf1 in H2.
 apply Wsup_incl_hd_inv in H2.
 rewrite <- H2 in H.
 rewrite eqf1,Wsnd_def; trivial.
 apply cc_prod_elim with (1:=tyf1); trivial.
 apply tyX.
 apply cc_prod_elim with (1:=tyf1); trivial.
Qed.
    
  Lemma Wdom_complete o : isOrd o -> complete o Wdom.
intros.
apply complete_power; trivial.
Qed.


End Corecursion_Auxiliary.

End W_Domain.

#[global]Hint Resolve Wf_mono Wf_morph Wf_typ : core.
#[global]Hint Resolve Wfbot_mono Wfbot_morph Wfbot_typ : core.

(*******************************************************************************************)
(* Morphism properties of discharged operations *)

Local Notation E := eq_set (only parsing).

Instance Wf_morph_gen :
  Proper (E==>(E==>E)==>E==>E) Wf.
do 4 red; intros.
unfold Wf.
apply sup_morph; trivial.
red; intros.
apply replf_morph_raw.
 apply cc_prod_ext; auto with *.
 red; intros; trivial.

 red; intros.
 apply Wsup_morph; trivial.
Qed.

Lemma Wf_ext A A' B B' X X' :
  A == A' ->
  eq_fun A B B' ->
  X == X' ->
  Wf A B X == Wf A' B' X'.
intros; unfold Wf.
apply sup_morph; auto with *.
red; intros.
apply replf_morph_raw.
 apply cc_prod_ext; auto with *.

 red; trivial.

 red; intros.
 apply Wsup_morph; trivial.
Qed.


Lemma Wdom_ext A A' B B' :
  A == A' ->
  eq_fun A B B' ->
  Wdom A B == Wdom A' B'.
intros; unfold Wdom.
apply rel_morph; trivial.
apply ZFlist.List_morph.
apply sup_morph; auto with *.
Qed.
 

Instance Wdom_morph : Proper (E==>(E==>E)==>E) Wdom.
do 3 red; intros.
apply Wdom_ext; trivial.
red; intros; apply H0; trivial.
Qed.
