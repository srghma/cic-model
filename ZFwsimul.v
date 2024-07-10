Require Import ZF ZFpairs ZFrelations ZFcoc ZFlist ZFord ZFfix.
Require Import ZFwdom.
Require ZFw.

Lemma wsup_fsub A B (bm : morph1 B) X x f :
  X ⊆ Fstages (Wf A B) (Wdom A B) ->
  x ∈ A ->
  f ∈ (Π __∈B x, X) ->
  fsub (Wf A B) (Wdom A B) (Wsup x f) == replf (B x) (fun i => cc_app f i).
intros.
rewrite eq_set_ax; intros z.
unfold fsub.
rewrite subset_ax.
split; intros.
+destruct H2 as (?,(z',eqz,?)).
 rewrite eqz in H2|-*; clear z eqz. 
 apply H3.
 {red; intros ? h.
  rewrite replf_ax in h.
  2:do 2 red; intros; apply cc_app_morph; auto with *.
  destruct h as (i,tyi,eqz).
  rewrite eqz.
  specialize cc_prod_elim with (1:=H1)(2:=tyi).
  apply H. }
 {apply Wf_intro; trivial.
  rewrite cc_eta_eq with (1:=H1).
  apply cc_prod_intro; intros; auto with *.
   do 2 red; intros; apply cc_app_morph; auto with *.
  rewrite replf_ax.
  2:do 2 red; intros; apply cc_app_morph; auto with *.
  exists x0; auto with *. }

+rewrite replf_ax in H2.
 2:do 2 red; intros; apply cc_app_morph; auto with *.
 destruct H2 as (i,tyi,eqz).
 split.
 {rewrite eqz.
  specialize cc_prod_elim with (1:=H1)(2:=tyi).
  apply H. }
{exists z;[reflexivity|].
 intros.
 rewrite eqz.
 apply Wf_elim in H3; trivial.
 destruct H3 as (x',tyx,(f',tyf',eqs)).
 apply Wsup_inj with (A:=A)(B:=B) in eqs; trivial.
 +destruct eqs as (eqx,eqf).
  rewrite eqf; trivial.
  apply cc_prod_elim with (1:=tyf').
  rewrite <- eqx; trivial.
 +intros.
  specialize cc_prod_elim with (1:=H1)(2:=H3) as ty.
  apply H in ty.
  revert ty; apply Fstages_inA.
 +intros.
  specialize cc_prod_elim with (1:=tyf')(2:=H3) as ty.
  apply H2 in ty.
  revert ty; apply Fstages_inA. }
Qed.

Section Wsimulation.
  Variable A : set.
  Variable B : set -> set.
  Hypothesis Bm : morph1 B.

  Variable A' : set.
  Variable B' : set -> set.
  Hypothesis Bm' : morph1 B'.

  Variable f : set -> set.
  Hypothesis fm : morph1 f.
  Hypothesis ftyp : typ_fun f A A'.

(* /!\ g should not depend on x!
  Variable g : set -> set -> set.
  Hypothesis gm : morph2 g.
  Hypothesis giso : forall x, x ∈ A -> iso_fun (B x) (B' (f x)) (g x). *)
  Hypothesis Beq : forall x, x ∈ A -> B x == B' (f x).
  
  Notation Wd  := (Wdom A B).
  Notation Wd' := (Wdom A' B').
  Notation Wf  := (ZFwdom.Wf A B).
  Notation Wf' := (ZFwdom.Wf A' B').
  
  Lemma eq_index : sup A B ⊆ sup A' B'.
red; intros z.
rewrite ! sup_ax; auto.
intros (x,tyx,inB); exists (f x); auto.                        
rewrite <-Beq; trivial.
Qed.
  Hint Resolve eq_index : core.
  
  Definition Wfmap w := replf w (fun p => couple (fst p) (f (snd p))).

  Let Wfmapm w : ext_fun w (fun p => couple (fst p) (f (snd p))).
do 2 red; intros.
rewrite H0; reflexivity.
Qed.

  Instance Wfmap_morph : morph1 Wfmap.
  Admitted.
  
  Lemma Wfmap_typ : typ_fun Wfmap Wd Wd'.
intros w tyw.
apply power_intro; intros.
unfold Wfmap in H; rewrite replf_ax in H; trivial.
destruct H as (p,inw,eqz).
rewrite eqz.
specialize power_elim with (1:=tyw) (2:=inw); intro.
apply couple_intro.
+apply fst_typ in H.
 revert H; apply List_mono; trivial.

+apply snd_typ in H; auto.
Qed.

  Lemma Wfmap_def w z :
    w ∈ Wd ->
    z ∈ Wfmap w <-> exists2 x, z == couple (fst z) (f x) & couple (fst z) x ∈ w.
intros tyw.
unfold Wfmap; rewrite replf_ax; trivial.
split; intros.    
+destruct H as (p,?,eqz).
 exists (snd p); rewrite eqz.
 *rewrite fst_def; reflexivity.
 *rewrite fst_def.
  specialize power_elim with (1:=tyw) (2:=H); intro.
  rewrite <- surj_pair with (1:=H0); trivial.
+destruct H as (x,eqz,inw).
 exists (couple (fst z) x); trivial.
 rewrite fst_def, snd_def; trivial.
Qed.

  Lemma Wfmap_sup X x g :
    X ⊆ Wd ->
    x ∈ A ->
    g ∈ (Π __∈B x, X) ->
    Wfmap (Wsup x g) == Wsup (f x) (cc_lam (B' (f x)) (fun i => Wfmap (cc_app g i))).
intros tyX tyx tyg.
assert (m : ext_fun (B' (f x))
   (fun i0 : set => replf (cc_app g i0) (fun p : set => couple (fst p) (f (snd p))))).
{do 2 red; intros.
 apply replf_morph; [rewrite H0; reflexivity|].
 red; intros.
 rewrite H2; reflexivity. }
unfold Wfmap.
apply eq_set_ax; intros z.
rewrite replf_ax; auto.
rewrite Wsup_def.
split ;intros.
+destruct H as (p,insup,eqz).
 rewrite Wsup_def in insup.
 destruct insup as [eqp|(i&l&y&inlam&eqp)].
 {left.
  rewrite eqz,eqp,fst_def,snd_def; reflexivity. }
 {right.
  rewrite eqp,fst_def,snd_def in eqz.
  exists i; exists l; exists (f y).
  split;[|trivial].
  rewrite cc_eta_eq with (1:=tyg) in inlam.
  rewrite cc_lam_def in inlam.
  2:do 2 red; intros; apply cc_app_morph; auto with *.
  destruct inlam as (i',tyi,(y',tyy,eqc)).
  apply couple_injection in eqc; destruct eqc as (eqi,eqc).
  rewrite <- eqi in tyi,tyy.
  rewrite <- eqc in tyy.
  rewrite cc_lam_def; trivial.
  exists i.
   rewrite  <-Beq; trivial.
  exists (couple l (f y));[|reflexivity].
  rewrite replf_ax; auto.
  exists (couple l y); trivial.
 rewrite fst_def, snd_def; reflexivity. }
+destruct H as [eqz|(i&l&y&inlam&eqz)].
 {exists (couple Nil x).
   apply Wsup_def; left;reflexivity.
   rewrite eqz,fst_def,snd_def; reflexivity. }
 {rewrite cc_lam_def in inlam; trivial.
  destruct inlam as (i',tyi,(y',tyy,eqc)).
  apply couple_injection in eqc; destruct eqc as (eqi,eqc).
  rewrite <- eqc in tyy.
  rewrite replf_ax in tyy; auto.
  destruct tyy as (p,inw,eqc').
  apply couple_injection in eqc'; destruct eqc' as (eql,eqy).
  rewrite eqy in eqz.
  rewrite <- eqi in tyi,inw.
  exists (couple (Cons i l) (snd p)).
  2:rewrite fst_def, snd_def; trivial.
  rewrite Wsup_def; right.
  exists i; exists l; exists (snd p); split;[|reflexivity].
  rewrite <-Beq in tyi; trivial.
  apply cc_prod_elim with (2:=tyi) in tyg.
  apply tyX in tyg.
  specialize power_elim with (1:=tyg)(2:=inw); intros isp.
  apply couple_in_app in inw.
  rewrite surj_pair with (1:=isp) in inw.
  rewrite <- eql in inw; trivial. }
Qed.

  Lemma Wfmap_typ_sub X Y :
    X ⊆ Wd ->
    typ_fun Wfmap X Y ->
    typ_fun Wfmap (Wf X) (Wf' Y).
intros tyX tyf w tyw.
apply Wf_elim in tyw; auto with *.
destruct tyw as (x,tyx,(g,tyg,eqw)).
rewrite eqw.
rewrite Wfmap_sup with (X:=X); trivial.
apply Wf_intro; auto.
apply cc_prod_intro; intros; auto.
{do 2 red; intros.
 rewrite H0; reflexivity. }
apply tyf.
apply cc_prod_elim with (1:=tyg); trivial.
rewrite Beq; auto.
Qed.

  
  Lemma Wfmap_typ_TI o: isOrd o -> typ_fun Wfmap (TI Wf o) (TI Wf' o).
induction 1 using isOrd_ind; red; intros.
apply TI_elim in H2; auto with *.
destruct H2.
specialize H1 with (1:=H2).
apply TI_intro with x0.
 apply Wf_morph; auto.
 trivial.
 trivial.
apply Wfmap_typ_sub with (2:=H1); trivial.
apply ZFw.Wi_typ; trivial.
apply isOrd_inv with y; trivial.
Qed.

  Lemma Wfmap_stages : typ_fun Wfmap (Fstages Wf Wd) (Fstages Wf' Wd').
red; intros.
rewrite Fstages_def in H|-*; auto with *.
destruct H.
exists x0; [exact H|].
apply Wfmap_typ_TI; auto.
Qed.

Existing Instance fsub_morph.
  
Lemma Wfmap_fsub o w :
  isOrd o ->
  w ∈ Wf (TI Wf o) ->
  typ_fun Wfmap (fsub Wf Wd w) (fsub Wf' Wd' (Wfmap w)).
red; intros.
apply Wf_elim in H0; [|auto].
destruct H0 as (x',tyx',(f',tyf',eqw)).
rewrite eqw in H1.
rewrite wsup_fsub with (3:=tyx')(4:=tyf') in H1; auto.
2:apply TI_Fstages; auto.
rewrite replf_ax in H1.
2:do 2 red; intros; apply cc_app_morph; auto with *.
destruct H1 as (i,tyi,eqx).
rewrite eqx; clear x eqx.
rewrite eqw.
rewrite Wfmap_sup with (2:=tyx')(3:=tyf').
2:{apply TI_pre_fix; auto with *. }
rewrite wsup_fsub with (X:=TI Wf' o); auto.
+rewrite replf_ax.
 2:do 2 red; intros; apply cc_app_morph; auto with *.
 rewrite Beq in tyi; trivial.
 exists i; trivial.
 rewrite cc_beta_eq; auto with *.
 do 2 red; intros.
 rewrite H1; reflexivity. 
+apply TI_Fstages; auto with *.
+apply cc_prod_intro; auto with *.
 do 2 red; intros.
 rewrite H1; reflexivity. 
 intros.
 apply Wfmap_typ_TI; trivial.
 apply cc_prod_elim with (1:=tyf'); trivial.
 rewrite Beq; trivial.
Qed.

Lemma Wfmap_Fixrec x :
  x ∈ Fstages Wf Wd ->
  Fix_rec Wf  Wd  (F_a Wf Wd)   x ⊆
  Fix_rec Wf' Wd' (F_a Wf' Wd') (Wfmap x).
intros.
rewrite Fstages_def in H; auto.
destruct H as (o,oo,tyw).
revert x tyw; elim oo using isOrd_ind; intros.
rewrite Fr_eqn with (o:=y); auto.
2:intros; apply F_a_morph; auto with *.
rewrite Fr_eqn with (o:=y); auto.
2:intros; apply F_a_morph; auto with *.
2:apply Wfmap_typ_TI; auto.
unfold F_a at 1.
apply osup_lub.
 apply ZFfix.Fe1; trivial.
 apply isOrd_osup.
  apply ZFfix.Fe1; trivial.
  intros; apply isOrd_succ; apply F_a_ord; auto.
  apply subset_elim1 in H2; trivial.
red; intros.
apply TI_elim in tyw; [|auto|auto].
destruct tyw as (o',o'lt,tyw).
apply osup_intro with (x:=Wfmap x0).
 apply ZFfix.Fe1; trivial.

 apply Wfmap_fsub with o'; auto with *.
 apply isOrd_inv with y; trivial.

 revert z H3; apply osucc_mono; auto.
  apply F_a_ord; auto.
  apply subset_elim1 in H2; trivial.

  apply F_a_ord; auto.
  apply subset_elim1 in H2.
  apply Wfmap_stages; trivial.
  
  apply H1 with o'; trivial.
  unfold fsub in H2; apply subset_elim2 in H2.
  destruct H2 as (x',eqx,?).
  rewrite eqx; apply H2; trivial.
  apply TI_Fstages; auto.
  apply isOrd_inv with y; trivial.
Qed.

Lemma Wfmap_W_ord :
  ZFw.W_ord A B ⊆ ZFw.W_ord A' B'.
unfold ZFw.W_ord.
unfold clos_ord.
apply osup_lub.
 apply ZFfix.Fe1.
 apply isOrd_osup.
  apply ZFfix.Fe1; trivial.
  intros; apply isOrd_succ; apply F_a_ord; auto.
red; intros.
apply osup_intro with (x:=Wfmap x).
 apply ZFfix.Fe1; trivial.
 apply Wfmap_stages; trivial.

 revert H0; apply osucc_mono; auto.
  apply F_a_ord; auto.
  apply F_a_ord;[auto|auto|].
  apply Wfmap_stages; trivial.
 apply Wfmap_Fixrec; trivial.
Qed.
  
End Wsimulation.
