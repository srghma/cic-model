Require Import ZF Zpairs Zsum Znats Zrelations.
Require Import Zlist.
Require Import Zcoc.
Require Import Zuniv.

(** * Low-level construction: encoding W-types as sets of path in a tree *)

Definition increasing_bounded o F :=
  forall x x', x < o -> x' < o -> x ⊆ x' -> F x ⊆ F x'.

Definition complete I X :=
  forall f,
    typ_fun f I X ->
    increasing_bounded I f ->
    sup I f ∈ X.

Lemma complete_power I X : complete I (power X).
intros f tyf fincr.
apply power_intro; intros.
rewrite sup_ax in H.
destruct H as (i, tyi, (_,zin)).
apply power_elim with (f i); auto.
Qed.


(** First we define W-objects without reference to the parameters A and B *)
Section W_Objects.

Definition isWelt p :=
  isCouple p /\ isList (fst p).
Definition isWobj w :=
  forall p, p ∈ w -> isWelt p.
Definition isWfun f :=
  forall p, p ∈ f -> isCouple p /\ isWelt (snd p).

#[global]Instance isWelt_morph : Proper(eq_set==>iff) isWelt.
Proof.
do 2 red; intros.
apply and_iff_morphism; rewrite H; reflexivity.
Qed.
#[global]Instance isWobj_morph : Proper(eq_set==>iff) isWobj.
Proof.
do 2 red; intros.
apply fa_morph; intro; rewrite H; reflexivity.
Qed.
#[global]Instance isWfun_morph : Proper(eq_set==>iff) isWfun.
Proof.
do 2 red; intros.
apply fa_morph; intro; rewrite H; reflexivity.
Qed.

Lemma isWobj_cc_app f i :
  isWfun f ->
  isWobj (cc_app f i).
unfold isWfun, isWobj; intros.
apply couple_in_app in H0.
destruct H with (1:=H0) as (_,we).
rewrite snd_def in we; trivial.
Qed.

  Lemma isWfun_cc_lam A f :
    ext_fun A f ->
    (forall x, x ∈ A -> isWobj (f x)) ->
    isWfun (cc_lam A f).
Proof.
unfold isWobj, isWfun.
intros fext fw p inf.
rewrite cc_lam_def in inf;[|trivial].
destruct inf as (x,tyx,(y,tyy,eqp)).
rewrite eqp, snd_def.
split;[trivial|eauto].
Qed.

  Lemma isWobj_sup X f :
    ext_fun X f ->
    (forall x, x ∈ X -> isWobj (f x)) ->
    isWobj (sup X f).
  Proof.
red; intros.
rewrite sup_ax in H1.
destruct H1 as (x,?,(_,?)).
apply H0 with (x:=x); trivial.
Qed.

Definition Wsup x f :=
   singl (couple Nil x) ∪
   replf f (fun p => let i := fst p in let wp := snd p in
                     couple (Cons i (fst wp)) (snd wp)).

#[global] Instance Wsup_morph : morph2 Wsup.
Proof.
do 3 red; intros.
unfold Wsup.
apply union2_morph;[rewrite H; reflexivity|].
apply replf_morph_raw; [trivial|].
red; intros.
rewrite H1; reflexivity.
Qed.

  
  
Lemma Wsup_def x f p :
  isWfun f ->
  (p ∈ Wsup x f <->
   p == couple Nil x \/
   exists i l y, couple i (couple l y) ∈ f /\ p == couple (Cons i l) y).
Proof.
intros fw.
unfold Wsup.
rewrite union2_ax.
rewrite replf_def.
2:{do 2 red; intros.
   rewrite H0; reflexivity. }
apply or_iff_morphism.
*split; intros.
 +apply singl_elim in H; trivial.
 +rewrite H; apply singl_intro.
*split; intros.
 +destruct H as (z,z_in_f,eqp).
  destruct fw with (1:=z_in_f) as (zc,(z2c,_)).
  red in zc,z2c.
  rewrite z2c in zc.
  rewrite zc in z_in_f,eqp; rewrite !snd_def, !fst_def in eqp.
  eauto.
 +destruct H as (i&l&y&in_f&eqp).
  eexists; [eassumption|].
  rewrite !snd_def, !fst_def; trivial.
Qed.


Lemma Wsup_hd_prop a x f :
  couple Nil a ∈ Wsup x f <-> a == x.
unfold Wsup.
rewrite union2_ax.
rewrite replf_def.
2:{do 2 red; intros.
   rewrite H0; reflexivity. }
split; intros.
*destruct H as [eqa|(p,_,abs)].
 +apply singl_elim in eqa.
  apply couple_injection in eqa; apply eqa.
 +apply couple_injection in abs; destruct abs as (abs,_).
  symmetry in abs; apply discr_Cons_Nil in abs; contradiction.
*left; rewrite H; apply singl_intro.
Qed.

Lemma Wsup_tl_prop i l a x f :
  isWfun f ->
  isList l ->
  couple (Cons i l) a ∈ Wsup x f <-> couple l a ∈ cc_app f i.
intros fw ll.
rewrite Wsup_def; [|trivial].
rewrite <- couple_in_app.
split; intros.
*destruct H as [eqc|(i'&l'&y&in_f&eqc)].
 +apply couple_injection in eqc; destruct eqc as (eqc,_).
  apply discr_Cons_Nil in eqc; contradiction.
 +apply couple_injection in eqc; destruct eqc as (eqc,eqa).
  apply Cons_inj in eqc; trivial.
  ++destruct eqc as (eqi,eql).
    rewrite eqi,eql,eqa; trivial.
  ++apply fw in in_f.
    destruct in_f as (_,in_f).
    red in in_f.
    rewrite snd_def,fst_def in in_f; apply in_f.
*right.
 exists i; exists l; exists a; auto with *.
Qed.

Lemma Wsup_obj x f :
  isWfun f ->
  isWobj (Wsup x f).
Proof.
red; intros.
rewrite Wsup_def in H0; [|trivial].
destruct H0 as [eqp|(i&l&y&inf&eqp)].
*rewrite eqp; red; rewrite fst_def; auto.
*apply H in inf.
 destruct inf as (_,(_,lst)).
rewrite snd_def,fst_def in lst.
rewrite eqp; red; rewrite fst_def; auto.
Qed.
#[global]Opaque Wsup.

Hint Resolve Wsup_obj : core.

Lemma Wsup_mono x x' f f' :
  x == x' ->
  isWfun f ->
  isWfun f' ->
  (forall i p, couple i p ∈ f -> couple i p ∈ f') ->
  Wsup x f ⊆ Wsup x' f'.
intros eqx tyf tyf' lef; rewrite <- eqx; clear x' eqx.
intros z; rewrite !Wsup_def; trivial.
destruct 1; [left;trivial|right].
destruct H as (i&l&y&isp&eqz).
apply lef in isp.
eauto.
Qed.

Lemma Wsup_incl_hd_inv x x' f f' :
    Wsup x f ⊆ Wsup x' f' -> x==x'.
intros.
assert (couple Nil x ∈ Wsup x' f').
{apply H.
 apply Wsup_hd_prop; reflexivity. }
apply Wsup_hd_prop in H0; trivial.
Qed.

(** Inverse of Wsup: Wfst and Wsnd_fun *)

Definition Wfst w :=
  snd (union (subset w (fun p => exists x, p == couple Nil x))).

#[global] Instance Wfst_morph : morph1 Wfst.
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

#[global] Opaque Wfst.

(** The family of subterms *)
Definition Wsnd_fun w :=
   replf (subset w (fun z => exists i l, isList l /\ fst z == Cons i l))
     (fun z => couple (Hd (fst z)) (couple (Tl (fst z)) (snd z))).

Global Instance Wsnd_fun_morph : morph1 Wsnd_fun.
Proof.
do 2 red; intros.
apply replf_morph.
*apply subset_morph; [trivial|].
 red; intros; reflexivity.
*red; intros.
 rewrite H1; reflexivity.
Qed.

Lemma Wsnd_fun_mono w1 w2 :
  w1 ⊆ w2 ->
  Wsnd_fun w1 ⊆ Wsnd_fun w2.
unfold Wsnd_fun; intros.
apply replf_mono_dom.
intros z0.
rewrite subset_ax.
rewrite subset_ax.
destruct 1; auto.
Qed.

Lemma Wsnd_fun_ax w z :
  isWobj w ->
  z ∈ Wsnd_fun w <->
  exists i p x, isList p /\ z == couple i (couple p x) /\ couple (Cons i p) x ∈ w.
intros ww.
unfold Wsnd_fun.
rewrite replf_def.
2:{do 2 red; intros; rewrite H0; reflexivity. }
split.
*intros (p, pcons, eqc).
 rewrite subset_ax in pcons; destruct pcons as (inw,(p',eqp,(i&l&lst&eql))).
 rewrite <-eqp in eql; clear p' eqp.
 rewrite eql,Hd_Cons,Tl_Cons in eqc;[|trivial].
 destruct (ww _ inw) as (pc,_).
 red in pc; rewrite pc in inw; clear pc.
 do 3 eexists; split; [exact lst|split;[exact eqc|]].
 rewrite eql in inw; trivial.
*intros (i&p&x&ls&eqz&inw).
 exists (couple (Cons i p) x);
   [apply subset_intro;[|do 2 eexists; split;[|rewrite fst_def;reflexivity]]|]; trivial.
 rewrite fst_def, snd_def.
 rewrite Hd_Cons,Tl_Cons; trivial.
Qed.

#[global] Opaque Wsnd_fun.

Lemma isWfun_Wsnd_fun w :
  isWobj w ->
  isWfun (Wsnd_fun w).
Proof.
intros ww z inf.
rewrite Wsnd_fun_ax in inf;[|trivial].
destruct inf as (i & p & x & lst & eqz & inw).
rewrite eqz, snd_def.
split;[trivial|].
split;[trivial|].
rewrite fst_def; trivial.
Qed.

Lemma Wsnd_fun_def i p x w :
  isWobj w ->
  isList p ->
  couple i (couple p x) ∈ Wsnd_fun w <-> couple (Cons i p) x ∈ w.
intros ww lstp.
rewrite Wsnd_fun_ax; [|trivial].
split.
*intros (i' & p' & x' & lstp' & eqc & inw).
 apply couple_injection in eqc; destruct eqc as (eqi,eqc).
 apply couple_injection in eqc; destruct eqc as (eqp,eqx).
 rewrite eqi,eqp,eqx; trivial.
*do 3 eexists; split;[|split;[reflexivity|]]; trivial.
Qed.

Lemma Wsnd_fun_Wsup x f :
  isWfun f ->
  Wsnd_fun (Wsup x f) == f.
Proof.
intros fw.
assert (ww : isWobj (Wsup x f)) by auto.
apply eq_set_ax; intros z.
rewrite Wsnd_fun_ax; [|auto].
split.
*intros (i&p&y&lstp&eqz&inw).
 rewrite eqz.
 red in ww; specialize ww with (1:=inw).
 rewrite Wsup_tl_prop in inw; trivial.
 apply couple_in_app in inw; trivial.
*intros inf.
 destruct  (fw _ inf) as (zc,(cc,pl)).
 red in zc, cc; rewrite cc in zc; rewrite zc in inf.
 do 3 eexists; split; [|split;[exact zc|]]; trivial.
 rewrite Wsup_tl_prop; trivial.
 rewrite <- couple_in_app; trivial.
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
unfold Wsnd; intros.
intros z.
rewrite <- !couple_in_app.
apply Wsnd_fun_mono; trivial.
Qed.

Lemma Wsnd_def x f i :
  isWfun f ->
  Wsnd (Wsup x f) i == cc_app f i.
intros tyf.
unfold Wsnd.
rewrite Wsnd_fun_Wsup; [reflexivity|trivial].
Qed.

Lemma Wsup_inj x x' f f' :
  isWfun f ->
  isWfun f' ->
  Wsup x f == Wsup x' f' ->
  x == x' /\ f==f'.
Proof.
intros fw fw' eqw.
split.
*rewrite <- (Wfst_def x f).
 rewrite <- (Wfst_def x' f').
 rewrite eqw; reflexivity.
*rewrite <- (Wsnd_fun_Wsup x f); [|trivial].
 rewrite <- (Wsnd_fun_Wsup x' f'); [|trivial].
 rewrite eqw; reflexivity.
Qed.



End W_Objects.

Section W_Domain.

(* The first parameter of W-types (aka the payload) *)
Variable A : set.
(* The subterm index type *)
Variable B : set -> set.
Hypothesis Bm : morph1 B.

(** The construction domain and the constructor. Note that the constructor does not
    use A or B. *)
Definition Wdom := rel (List (sup A B)) A.

Lemma Wdom_Wobj w :
  w ∈ Wdom -> isWobj w.
Proof.
unfold Wdom, isWobj; intros.
apply power_elim with (2:=H0) in H.
rewrite prodcart_ax in H.
destruct H as (pc & ty1 & ty2).
split; trivial.
apply List_list in ty1; trivial.
Qed.

Lemma cc_prod_Wfun I X f :
  X ⊆ Wdom ->
  f ∈ (Π i ∈ I, X) ->
  isWfun f.
Proof.
red; intros inc tyf p inf.
rewrite cc_prod_def in tyf; [|auto with *].
destruct tyf as ((r,dom),tyf).
red in r; specialize r with (1:=inf).
split; [auto|].
red in r; rewrite r in inf; clear r.
assert (tyi : fst p ∈ I).
{apply dom; rewrite rel_domain_ax; eauto. }
apply tyf in tyi.
apply inc in tyi.
apply couple_in_app in inf.
apply power_elim with (2:=inf) in tyi.
rewrite prodcart_ax in tyi.
destruct tyi as (pc&ty1&_).
split; [auto|].
apply List_list in ty1; trivial.
Qed.

Lemma Wsup_typ_gen x f :
  x ∈ A ->
  f ∈ (Π i ∈ B x, Wdom) ->
  Wsup x f ∈ Wdom.
intros tyx ty_f.
assert (ff := cc_prod_Wfun _ _ _ (reflexivity _) ty_f).
assert (tyf := cc_prod_is_cc_fun _ _ _ ty_f).
apply power_intro; intros z tyz.
rewrite Wsup_def in tyz; trivial.
destruct tyz as [eqz|(i&l&y&in_f&eqz)]; rewrite eqz.
*apply couple_intro; trivial.
 apply Nil_typ.
*assert (tyi : i ∈ B x).
 {apply tyf.
  rewrite rel_domain_ax; eauto. }
 specialize cc_prod_elim with (1:=ty_f) (2:=tyi); intros tyapp.
 rewrite couple_in_app in in_f.
 apply power_elim with (2:=in_f) in tyapp.
 apply couple_intro.
 +apply Cons_typ.
  ++rewrite sup_ax; eauto with *.
  ++apply fst_typ in tyapp; rewrite fst_def in tyapp; trivial.
 +apply snd_typ in tyapp; rewrite snd_def in tyapp; trivial.
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
rewrite sup_def.
 exists x; trivial.
 rewrite replf_def; auto with *.
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
destruct H as (x,tyx,(_,tya)).
rewrite replf_ax in tya.
destruct tya as (f,tyf,(_,eqa)).
exists x; trivial.
exists f; trivial.
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
*apply cc_prod_Wfun in tyf;[|trivial].
 rewrite eqw; rewrite Wsnd_fun_Wsup; auto with *.
*revert tyf; apply cc_prod_covariant; [auto with *| |reflexivity].
 rewrite eqw, Wfst_def; reflexivity.
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

Lemma Wsup_inj_typ X X' Y Y' x x' f f' :
  Y ⊆ Wdom ->
  Y' ⊆ Wdom ->
  f ∈ cc_arr X Y ->
  f' ∈ cc_arr X' Y' ->
  Wsup x f == Wsup x' f' ->
  x == x' /\ f==f'.
Proof.
intros.  
apply Wsup_inj; eauto using cc_prod_Wfun.
Qed.

Lemma Wf_elim' X x f :
  x ∈ A ->
  isWfun f ->
(*  (forall i, i ∈ B x -> cc_app f i ∈ Wdom A B) ->*)
  X ⊆ Wdom ->
  Wsup x f ∈ Wf X ->
  forall i, i ∈ B x -> cc_app f i ∈ X.
intros tyx tyf Xincl tyw.
apply Wf_elim in tyw; trivial.
destruct tyw as (x',tyx',(f',tyf',eqw)).
apply Wsup_inj in eqw; intros; auto.
*destruct eqw.
 rewrite H1.
 apply cc_prod_elim with (1:=tyf').
 rewrite <-H0; trivial.
*apply cc_prod_Wfun with (1:=Xincl) in tyf'; trivial.
Qed.

Lemma Wf_stable :
  stable_set (power Wdom) Wf.
Proof.
red; intros X Xty z H.
assert (forall a, a ∈ X -> z ∈ Wf a).
{intros.
 apply inter_elim with (1:=H).
 rewrite replf_def.
 2:red;red;intros;apply Wf_morph; trivial.
 exists a; auto with *. }
destruct inter_wit with (1:=H).
assert (tyz := H0 _ H1).
apply Wf_elim in tyz; trivial.
destruct tyz as (x',tyx,(f,tyf,eqz)).
rewrite eqz.
apply Wf_intro; trivial.
rewrite cc_eta_eq with (1:=tyf).
apply cc_prod_intro; intros.
{intros ? ? ? h; rewrite h; reflexivity. }
{do 2 red; reflexivity. }
apply inter_intro; eauto.
intros.
specialize H0 with (1:=H3).
apply Wf_elim in H0; trivial.
destruct H0 as (x'',tyx',(f',tyf',eqz')).
rewrite eqz in eqz'.
apply Wsup_inj in eqz'; trivial; intros.
*destruct eqz' as (eqx,eqf).
 rewrite eqf; trivial.
 apply cc_prod_elim with (1:=tyf').
 rewrite <- eqx; trivial.

*apply Xty in H1; apply power_def in H1.
 apply cc_prod_Wfun with (1:=H1) in tyf; trivial.
*apply Xty in H3; apply power_def in H3.
 apply cc_prod_Wfun with (1:=H3) in tyf'; trivial.
Qed.

Section Wdom_Universe.

  Variable U : set.
  Hypothesis Ugrot : Zuniv U.
  Hypothesis Unontriv : N ∈ U.  

  Hypothesis aU : A ∈ U.
  Hypothesis bU : unif_bound U A B.

  Lemma G_Wdom : Wdom ∈ U.
unfold Wdom.
apply Zu_rel; trivial.
apply Zu_List; trivial.
apply Zu_sup; trivial.
apply morph_is_ext; trivial.
Qed.

(*  Lemma G_Wsup X f :
    X ∈ U ->
    f ∈ cc_prod  ->
    Wsup X f ∈ U.*)

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
rewrite H; apply Wsup_hd_prop; auto with *.
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
(*
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
*)
Lemma Wfbot_typ : forall X,
  X ⊆ Wdom -> Wfbot X ⊆ Wdom.
intros.
unfold Wfbot; apply Wf_typ; trivial.
apply Wdom_cc_bot; trivial.
Qed.
Hint Resolve Wfbot_typ : core.

(*Lemma TI_Wfbot_typ o :
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
*)  
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
  apply List_list in H0.
  assert (fw1 : isWfun f1)
    by (apply cc_prod_Wfun in tyf1; auto with *).
  assert (fw2 : isWfun f2)
    by (apply cc_prod_Wfun in tyf2; auto with *).
  apply Wsup_tl_prop in H6; trivial.
  apply Wsup_tl_prop; trivial.
  assert (tyx2 : x ∈ B a2).
  {apply couple_in_app in H6.
   apply cc_prod_is_cc_fun in tyf2.
   apply tyf2; rewrite rel_domain_ax; eauto. }
  assert (tyx1 : x ∈ B a1).
  {rewrite same_x; trivial. }
  revert H6; apply H1; auto.
  +apply Wsnd_mono with (x:=x) in H3; auto.
   rewrite !Wsnd_def in H3; auto.
  +apply cc_prod_elim with (1:=tyf1); trivial.
  +apply cc_prod_elim with (1:=tyf2); trivial. } }
revert H; rewrite eqz; apply H0; trivial.
Qed.


Lemma Wsup_cont I Y i0 x g :
  i0 ∈ I ->
  ext_fun I g ->
  (forall i, i ∈ I -> isWfun (g i)) ->
  (forall i, i ∈ I -> rel_domain  (g i) ⊆ Y) ->
  sup I (fun i => Wsup x (g i)) ==
  Wsup x (λ y ∈ Y, sup I (fun i => cc_app (g i) y)).
Proof.
intros wit gext gw gdom.
assert (eqsm : ext_fun Y (fun y => sup I (fun i => cc_app (g i) y))).
{do 2 red; intros.
 apply sup_morph; auto with *.
 red; intros.
 rewrite (gext _ _ H1 H2), H0; reflexivity. }
assert (am : forall a, ext_fun I (fun i => cc_app (g i) a)).
{intros a ?? tyx eqx; rewrite (gext _ _ tyx eqx); reflexivity. }
apply eq_set_ax; intros z.
rewrite sup_def.
2:{intros ?? tyx eqx; rewrite (gext _ _ tyx eqx); reflexivity. }
rewrite Wsup_def.
2:{apply isWfun_cc_lam;[trivial|].
   intros.
   apply isWobj_sup; [trivial|].
   intros.
   apply isWobj_cc_app; auto. }
split; intros.
 +destruct H as (i,tyi,tyz).
  rewrite Wsup_def in tyz; auto.
  destruct tyz as [?|(a & l & y & ing & eqz)]; [left;trivial|right].
  do 3 eexists; split; [|exact eqz].
  rewrite cc_lam_def; [|trivial].
  exists a.  
  ++apply (gdom i); trivial.
    rewrite rel_domain_ax; eauto.
  ++exists (couple l y);[|reflexivity].  
    rewrite sup_def;[|trivial].
    exists i; [trivial|].
    rewrite <- couple_in_app;trivial.
 +destruct H as [eqz|(a&l&y&insup&eqz)].
  ++exists i0;[trivial|].
    rewrite Wsup_def;[left; trivial|auto].
  ++rewrite cc_lam_def in insup; [|trivial].
    destruct insup as (a',_,(c,insup,eqc)).
    apply couple_injection in eqc; destruct eqc as (eqa,eqc).    
    rewrite <-eqc in insup.
    rewrite eqa in eqz.
    rewrite sup_ax in insup.
    destruct insup as (i,tyi,(_,inw)).
    rewrite <- couple_in_app in inw.
    exists i; [trivial|].    
    rewrite Wsup_def; auto.
    right.
    do 3 eexists; split; [|exact eqz]; trivial.
Qed.

    
Lemma Wf_complete I X i0 :
  i0 ∈ I ->
  (forall i j, i ∈ I -> j ∈ I -> exists2 k, k ∈ I & i ⊆ k /\ j ⊆ k) -> 
  X ⊆ Wdom -> complete I X -> complete I (Wf X).
intros tyi0 dirI tyX Xcl.
red in Xcl.
red; intros f tyf fmono.
assert (fext : ext_fun I f) by auto.
assert (eqsm : forall Y, ext_fun Y (fun i1 => sup I (fun x => Wsnd (f x) i1))).
{do 2 red; intros.
 apply sup_morph; auto with *.
 red; intros.
 apply Wsnd_morph; auto. }
assert (sfm : ext_fun I (fun i => Wsnd_fun (f i))).
{do 2 red; intros.
 apply Wsnd_fun_morph; auto with *. }
assert (tyfi0 := tyf _ tyi0).
apply Wf_elim in tyfi0.
destruct tyfi0 as (x0,tyx0,(g0,_,eqfi0)).
assert (f_wsup : forall i, i ∈ I -> f i == Wsup x0 (Wsnd_fun (f i))).
{intros.
 assert (tyfi := tyf _ H).
 apply Wf_elim in tyfi; trivial.
 destruct tyfi as (x,tyx,(g,tyg,eqf)).
 assert (eqx : x == x0).
 {destruct dirI with (1:=tyi0) (2:=H) as (j,tyj,(i0j,ij)).
  assert (tyfj := tyf _ tyj).
  apply Wf_elim in tyfj.
  destruct tyfj as (x',tyx',(g',_,eqfj)).
  apply fmono in i0j; trivial.
  apply fmono in ij; trivial.
  rewrite eqf in ij.
  rewrite eqfi0 in i0j.
  rewrite eqfj in ij,i0j.
  apply Wsup_incl_hd_inv in i0j.
  apply Wsup_incl_hd_inv in ij.
  rewrite ij,i0j;reflexivity. }
 rewrite eqf.
 rewrite eqx, Wsnd_fun_Wsup; [reflexivity|].
 apply cc_prod_Wfun with (1:=tyX) (2:=tyg). }
assert (f_eq : sup I f ==
                 Wsup x0 (cc_lam (B x0) (fun x => sup I (fun i => Wsnd (f i) x)))).
{unfold Wsnd.
 rewrite <- Wsup_cont with (1:=tyi0); auto.
 *apply sup_morph;[reflexivity|].
  red; intros.
  rewrite <- (fext _ _ H H0); auto.
 *intros.
  apply isWfun_Wsnd_fun.
  eapply Wdom_Wobj.
  eapply Wf_typ with (1:=tyX); auto.
 *intros.
  assert (tyfi := tyf _ H).
  apply Wsnd_fun_typ_gen in tyfi; trivial.
  rewrite cc_prod_def in tyfi;[|trivial].
  destruct tyfi as ((_,dom),_).
  rewrite dom.
  rewrite f_wsup; trivial.
  rewrite Wfst_def; reflexivity. }
rewrite f_eq.
apply Wf_intro; trivial.
apply cc_arr_intro; auto.
intros y tyy.
apply Xcl.
*red; intros.
 eapply Wsnd_typ_gen with (1:=tyX); auto.
 rewrite f_wsup; trivial.
 rewrite Wfst_def; trivial.
*red; intros.
 apply Wsnd_mono; auto.
Qed.
    
Lemma Wdom_complete I :
  complete I Wdom.
intros.
apply complete_power.
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
apply List_morph.
apply sup_morph; auto with *.
Qed.
 

Instance Wdom_morph : Proper (E==>(E==>E)==>E) Wdom.
do 3 red; intros.
apply Wdom_ext; trivial.
red; intros; apply H0; trivial.
Qed.
