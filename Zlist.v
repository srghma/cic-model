From Stdlib Require Import Wf_nat.
Require Import ZF Zpairs Znats Zrelations Ziso.

Definition next n := singl zero ∪ replf n succ.
#[global]Instance next_moph : morph1 next.
do 2 red; intros.
apply union2_morph;[reflexivity|].
apply replf_morph; auto with *.
red; intros; apply succ_morph; trivial.
Qed.

Lemma lt_0_next n : zero ∈ next n.
apply union2_intro1; apply singl_intro.
Qed.
Lemma next_ax x n :
   x ∈ next n <-> x == zero \/ exists2 m, m ∈ n & x == succ m.
unfold next.
rewrite union2_ax.
rewrite replf_def;[|do 2 red; intros; apply succ_morph;trivial].
apply or_iff_morphism; [|reflexivity].
split ;intros.
apply singl_elim in H; trivial.
apply singl_intro_eq; trivial.
Qed.

Lemma succ_equiv n :
  n ∈ N -> succ n == next n.
intros.
apply eq_set_ax; intros z.
split ;intros.
*apply next_ax.
 destruct (N_case z).
  apply N_trans with (succ n); trivial.
  apply succ_typ; trivial.
 left; trivial.
 right; exists (pred z); trivial.
 apply lt_inv; trivial.
 rewrite <- H1; trivial.
*rewrite next_ax in H0; destruct H0.
  rewrite H0; apply lt_0_succ; trivial.
 destruct H0.
 rewrite H1.
 apply lt_mono; trivial.
 apply N_trans with n; trivial.
Qed.

Lemma next_typ n : n ∈ N -> next n ∈ N.
intros; rewrite <- succ_equiv; trivial.
apply succ_typ; trivial.
Qed.


#[global]Instance rel_domain_morph : morph1 rel_domain.
do 2 red; intros.
unfold rel_domain.
apply subset_morph; [rewrite H;reflexivity|].
red; intros.
apply ex_morph; intro.
rewrite H; reflexivity.
Qed.

Definition Nil := lam zero (fun _ => empty).
Definition Cons x l :=
  lam (next (rel_domain l)) (fun n => natcase n x (app l (pred n))).

#[global] Instance Cons_morph : morph2 Cons.
unfold Cons; do 3 red; intros.
apply lam_morph; [rewrite H0;reflexivity|].
red; intros.
rewrite H,H0,H2; reflexivity.
Qed.

Lemma discr_Cons_Nil x l : ~ Cons x l == Nil.
assert (rel_domain (Cons x l) == next (rel_domain l)).
{apply lam_domain.
 do 2 red; intros.
rewrite H0; reflexivity. }
assert (rel_domain Nil == empty).
{apply lam_domain; auto with *. }
intro abs; rewrite abs in H.
rewrite H in H0.
apply (empty_ax zero).
rewrite <- H0.
apply lt_0_next.
Qed.

Definition Hd l := app l zero.
Definition Tl l :=
  lam (pred (rel_domain l)) (fun k => app l (succ k)).

#[global]Instance Hd_morph : morph1 Hd.
do 2 red; intros; unfold Hd.
rewrite H; reflexivity.
Qed.
#[global]Instance Tl_morph : morph1 Tl.
do 2 red; intros; unfold Tl.
apply lam_morph; [rewrite H;reflexivity|].
red; intros; rewrite H, H1; reflexivity.
Qed.

Definition isList l :=
  isFunction l /\ rel_domain l ∈ N.

#[global]Instance isList_morph : Proper(eq_set==>iff)isList.
do 2 red; intros.
unfold isList; rewrite H; reflexivity.
Qed.

Lemma isList_Nil : isList Nil.
unfold Nil; split.
*apply lam_isFunction; auto with *.
*rewrite lam_domain;[|auto with *].
 apply zero_typ.
Qed.

Lemma isList_Cons x l : isList l -> isList (Cons x l).
unfold Cons; split.
*apply lam_isFunction.
*rewrite lam_domain;[|intros ??? h; rewrite h; reflexivity].
 apply next_typ; apply H.
Qed.

#[global]Hint Resolve isList_Nil isList_Cons : core.

Lemma Hd_Cons x l : Hd (Cons x l) == x.
unfold Hd,Cons.
rewrite beta_eq.
*rewrite natcase_0; auto with *.
*intros ??? h; rewrite h; reflexivity.
*apply lt_0_next.
Qed.

Lemma Tl_Cons x l :
  isList l ->
  Tl (Cons x l) == l.
intros (lf,ld).
unfold Tl,Cons.
eapply transitivity; [|symmetry; eapply eta_eq;[trivial|reflexivity]].
symmetry; apply lam_morph.
*rewrite lam_domain;[|intros ??? h; rewrite h; reflexivity].
 rewrite <- succ_equiv;[|trivial].
 symmetry; apply pred_succ_eq; trivial.
*red; intros.
 assert (x0 ∈ N).
 {apply N_trans with (1:=H); trivial. }
   rewrite beta_eq;[|intros ??? h; rewrite h; reflexivity|].
 +rewrite natcase_succ with (m:=x0);[|trivial|rewrite H0; reflexivity].
  rewrite <-H0,pred_succ_eq; auto with *.
 +rewrite <-H0.
  rewrite next_ax; right; eauto with *.
Qed.

Lemma Cons_inj x1 x2 l1 l2 :
  isList l1->
  isList l2->
  Cons x1 l1 == Cons x2 l2 -> x1==x2 /\ l1==l2.
split.
*rewrite <- (Hd_Cons x1 l1).
 rewrite <- (Hd_Cons x2 l2).
 rewrite H1; reflexivity.
*rewrite <- (Tl_Cons x1 l1);[|trivial].
 rewrite <- (Tl_Cons x2 l2);[|trivial].
 rewrite H1; reflexivity.
Qed.

(**)

Lemma Nil_func A : Nil ∈ func zero A.
apply lam_is_func; [auto with *|].
intros.
apply empty_ax in H; contradiction.
Qed.


Lemma Cons_func A n x l :
  n ∈ N ->
  x ∈ A ->
  l ∈ func n A ->
  Cons x l ∈ func (succ n) A.
intros; unfold Cons.
assert (eql:succ n == next (rel_domain l)).
{rewrite fun_domain_func with (1:=H1).
 apply succ_equiv; trivial. }
rewrite eql.
apply lam_is_func.
*do 2 red; intros.
 rewrite H3; reflexivity.
*intros.
 rewrite <-eql in H2.
 assert (x0 ∈ N).
 {apply N_trans with (succ n); trivial.
  apply succ_typ; trivial. }
 destruct N_case with (1:=H3) as [?|?].
 +rewrite natcase_0; trivial.
 +rewrite natcase_succ with (m:=pred x0); trivial.
  ++assert (pred x0 ∈ n).
    {rewrite H4 in H2.
     apply lt_inv in H2; trivial. }
    apply app_typ with (1:=H1); trivial.
  ++apply pred_typ.
    apply N_trans with (succ n); trivial.
    apply succ_typ; trivial.
Qed.

  Lemma Tl_func A n l : 
    n ∈ N ->
    l ∈ func (succ n) A ->
    Tl l ∈ func n A.
unfold Tl.
intros tyn tyl.
assert (eqn:n==pred(rel_domain l)).
{rewrite fun_domain_func with (1:=tyl).
 rewrite pred_succ_eq; auto with *. }
rewrite eqn.
apply lam_is_func; [intros ??? e; rewrite e; reflexivity|].
intros.
rewrite <- eqn in H.
apply app_typ with (1:=tyl).
apply lt_mono; trivial.
apply N_trans with n; trivial.
Qed.

  Lemma Nil_ext A l :
    l ∈ func zero A -> l == Nil.
intros.
rewrite func_eta with (1:=H).
apply lam_morph; [reflexivity|].
intros ?? h ?; apply empty_ax in h; contradiction.
Qed.

  Lemma Cons_ext A n l :
    n ∈ N ->
    l ∈ func (succ n) A ->
    l == Cons (Hd l) (Tl l).
intros.
eapply transitivity;[apply func_eta with (1:=H0)|]. 
unfold Cons.
apply lam_morph.
*apply Tl_func in H0; trivial.
 rewrite fun_domain_func with (1:=H0); auto with *.
 apply succ_equiv; trivial.
*red; intros.
 rewrite <- H2.
 assert (x ∈ N).
 {apply N_trans with (succ n); auto.
  apply succ_typ; trivial. }
 destruct N_case with (1:=H3).
 +rewrite natcase_0;[|trivial].
  rewrite H4; reflexivity.
 +rewrite natcase_succ with (pred x);[|apply pred_typ|];trivial.
  unfold Tl.
  rewrite beta_eq.
  ++rewrite <- H4; auto with *.
  ++intros ??? e; rewrite e; reflexivity.
  ++rewrite fun_domain_func with (1:=H0).
    apply lt_inv;[apply pred_typ; apply succ_typ; trivial|].
    rewrite <-H4,pred_succ_eq; trivial.
Qed.



(*

Definition Nil := empty.
Definition Cons x l :=
  singl(couple zero x) ∪ replf l (fun p => couple (succ (fst p)) (snd p)).

#[local] Instance Cons_m1 : morph1 (fun p => couple (succ (fst p)) (snd p)).
intros ?? h; rewrite h; reflexivity.
Qed.

#[global] Instance Cons_Morph : morph2 Cons.
do 3 red; intros.
unfold Cons.
apply union2_morph; [rewrite H; reflexivity|].
apply replf_morph; trivial.
red; intros.
rewrite H2; reflexivity.
Qed.


Lemma discr_Cons_Nil x l : ~ Cons x l == Nil.
unfold Nil, Cons.
intro e.
apply (empty_ax (couple zero x)).
rewrite <- e.
apply union2_intro1.
apply singl_intro.
Qed.

Lemma Cons_def x l z :
  z ∈ Cons x l <->
    z == couple zero x \/
    exists2 p, p ∈ l & z == couple (succ (fst p)) (snd p).
unfold Cons.
rewrite union2_ax.
apply or_iff_morphism.
*split; intros; [apply singl_elim|apply singl_intro_eq]; trivial.
*rewrite replf_ax; auto with *.
Qed.

Transparent func.
Lemma Nil_func A : Nil ∈ func zero A.
unfold func.
apply subset_intro;[|split; intros].
*apply power_intro; intros.
 apply empty_ax in H; contradiction.
*apply empty_ax in H; contradiction.
*apply empty_ax in H; contradiction.
Qed.


Lemma Cons_func A n x l :
  n ∈ N ->
  x ∈ A ->
  l ∈ func n A ->
  Cons x l ∈ func (succ n) A.
unfold func.
intros tyn tyx tyl.
rewrite subset_ax in tyl|-*.
destruct tyl as (lrel,(l',eql,(tot&fn))).
split;[|exists (Cons x l);[reflexivity|split]].
*apply power_intro; intros z zty.
 rewrite Cons_def in zty; destruct zty as [zmt|(p,pinl,eqz)].
 +rewrite zmt; apply couple_intro;[|trivial].
  apply lt_0_succ; auto.
 +apply power_elim with (1:=lrel) in pinl.
  rewrite eqz; apply couple_intro;[|apply snd_typ in pinl;trivial].
  apply fst_typ in pinl.
  apply lt_mono; auto.
  apply N_trans with n; trivial.
*intros m mltn.
 assert (tym : m ∈ N).
 {apply N_trans with (succ n); trivial.
  apply succ_typ; trivial. }
 destruct N_case with (1:=tym) as [z0|zs].
 +exists x; trivial.
  rewrite z0.
  apply Cons_def; left; auto with *.
 +destruct tot with (pred m) as (y,tyy,inl).
  ++rewrite zs in mltn; apply lt_inv in mltn; trivial.
  ++rewrite <- eql in inl.
    exists y; trivial.
    rewrite Cons_def; right.
    exists (couple (pred m) y);[trivial|].
    rewrite fst_def,snd_def.
    rewrite zs,pred_succ_eq;[reflexivity|apply pred_typ;trivial].
*intros.
 rewrite Cons_def in H,H0.
 destruct H as [ec|(p,pl,ec)]; destruct H0 as [ec'|(p',pl',ec')];
   apply couple_injection in ec; destruct ec as (ec1,ec2);
   apply couple_injection in ec'; destruct ec' as (ec1',ec2').
 +rewrite ec2,ec2'; reflexivity.
 +rewrite ec1' in ec1; apply discr in ec1; contradiction.
 +rewrite ec1 in ec1'; apply discr in ec1'; contradiction.
 +assert (fst p == fst p').
  {rewrite ec1 in ec1'.
   apply succ_inj; trivial.
   +apply N_trans with n; trivial.
    apply power_elim with (2:=pl) in lrel.
    apply fst_typ in lrel; trivial.    
   +apply N_trans with n; trivial.
    apply power_elim with (2:=pl') in lrel.
    apply fst_typ in lrel; trivial. }
  apply fn with (fst p).
  ++rewrite ec2,<-eql.
    apply power_elim with (2:=pl) in lrel.
    rewrite <-surj_pair with (1:=lrel); trivial.
  ++rewrite H,ec2',<-eql.
    apply power_elim with (2:=pl') in lrel.
    rewrite <-surj_pair with (1:=lrel); trivial.
Qed.


Definition Hd l := app l zero.
Definition Tl l :=
  replf (subset l (fun p => exists2 n, n ∈ N & p==couple(succ n)(snd p)))
    (fun p => couple (pred (fst p)) (snd p)). 


#[global]Instance Hd_morph : morph1 Hd.
do 2 red; intros; unfold Hd.
rewrite H; reflexivity.
Qed.
#[global]Instance Tl_morph : morph1 Tl.
do 2 red; intros; unfold Tl.
apply replf_morph; trivial.
*apply subset_morph; auto with *.
*red; intros.
 rewrite H1; reflexivity.
Qed.

Lemma Hd_def z l :
  z ∈ Hd l <-> exists2 x, couple zero x ∈ l & z ∈ x.
unfold Hd.
Transparent app.
unfold app.
rewrite union_ax.
split; intros.
*destruct H.
 apply subset_ax in H0.
 destruct H0.
 destruct H1.
 rewrite <- H1 in H2.
 exists x; trivial.
*destruct H.
 exists x; trivial.
 apply subset_intro; trivial.
 unfold rel_image.
 apply subset_intro;[|eauto].
 apply union_intro with (pair zero x). 
 apply pair_intro2.
 apply union_intro with (couple zero x); trivial.
Transparent couple.
 unfold couple.
 apply pair_intro2.
Qed.

Lemma Tl_def z l :
  z ∈ Tl l <->
    exists2 n, n ∈ N &
    exists2 x,
     couple (succ n) x ∈ l & z == couple n x.
unfold Tl.
rewrite replf_ax.
2:{intros ?? _ e; rewrite <- e; reflexivity. }
split; intros.
*destruct H.
 rewrite subset_ax in H; destruct H.
 destruct H1.
 destruct H2.
 rewrite <- H1 in H3; clear H1.
 rewrite H3 in H,H0.
 rewrite fst_def,snd_def in H0.
rewrite pred_succ_eq in H0; trivial.
 exists x1; trivial.
 exists (snd x); trivial.
*destruct H.
 destruct H0.
 exists (couple (succ x) x0);[|rewrite fst_def,snd_def,pred_succ_eq;trivial].
 apply subset_intro; trivial.
 exists x; trivial.
 rewrite snd_def; reflexivity.
Qed.

Lemma Hd_Cons x l : Hd (Cons x l) == x.
apply eq_set_ax; intros z.
rewrite Hd_def.
split; intros.
*destruct H as (x',?,?).
 apply Cons_def in H.
 destruct H.
 +apply couple_injection in H; destruct H.
  rewrite <-H1; trivial.
 +destruct H as (p,_,e).
  apply couple_injection in e; destruct e.
  symmetry in H; apply discr in H; contradiction.
*exists x; trivial.
 rewrite Cons_def; left; reflexivity.
Qed.

Lemma Tl_Cons x l :
  (exists A, l ∈ rel N A) ->
  Tl (Cons x l) == l.
intros (A,tyl).
apply eq_set_ax; intros z.
rewrite Tl_def.
split; intros.
*destruct H as (n,?,(y,?,?)).
 rewrite H1.
 rewrite Cons_def in H0.
 destruct H0.
 +apply couple_injection in H0; destruct H0.
  apply discr in H0; contradiction.
 +destruct H0 as (p,?,?).
  apply couple_injection in H2; destruct H2.
  apply power_elim with (2:=H0) in tyl.
  rewrite surj_pair with (1:=tyl) in H0.
  apply fst_typ in tyl.
  rewrite H3.
  apply succ_inj in H2; auto.
  rewrite H2; trivial.
*apply power_elim with (2:=H) in tyl.
 exists (fst z); [apply fst_typ in tyl;trivial|].
 exists (snd z);[|apply surj_pair with (1:=tyl)].
 rewrite Cons_def; right.
 eauto with *.
Qed.
*)
Section ListDefs.

  Variable A : set.

  Definition List := sup N (fun n => func n A).

  Lemma List_def l :
    l ∈ List <-> exists2 n, n ∈ N & l ∈ func n A.
unfold List; rewrite sup_def; [reflexivity|].
intros ??? e; rewrite e; reflexivity.
Qed.

Lemma List_list l :
  l ∈ List -> isList l.
intros.
apply List_def in H.
destruct H as (n,tyn,lf).
rewrite func_def in lf.
destruct lf as (_ & lf & ld).
split; [trivial|].
rewrite ld; trivial.
Qed.

(*


  Definition LISTf (X:set) := singl empty ∪ prodcart A X.

Instance LISTf_mono : Proper (incl_set ==> incl_set) LISTf.
do 2 red; intros.
unfold LISTf.
apply union2_mono; auto with *.
apply prodcart_mono; auto with *.
Qed.

Instance LISTf_morph : Proper (eq_set ==> eq_set) LISTf.
apply Fmono_morph.
apply LISTf_mono.
Qed.

  Hint Resolve LISTf_morph LISTf_mono : core.
  
  Lemma LISTf_ind : forall X (P : set -> Prop),
    Proper (eq_set ==> iff) P ->
    P Nil ->
    (forall x l, x ∈ A -> l ∈ X -> P (Cons x l)) ->
    forall a, a ∈ LISTf X -> P a.
unfold LISTf; intros.
apply union2_elim in H2; destruct H2 as [H2|H2].
 apply singl_elim in H2.
 rewrite H2; trivial.

 rewrite surj_pair with (1:=H2).
 apply H1.
  apply fst_typ in H2; trivial.
  apply snd_typ in H2; trivial.
Qed.

  Lemma Nil_typ0 : forall X, Nil ∈ LISTf X.
intros.
unfold Nil, LISTf.
apply union2_intro1; apply singl_intro.
Qed.

  Lemma Cons_typ0 : forall X x l,
    x ∈ A -> l ∈ X -> Cons x l ∈ LISTf X.
intros.
unfold Cons, LISTf.
apply union2_intro2.
apply couple_intro; trivial.
Qed.
*)
  (* LIST_case is f when l is Nil, or g when l is Cons *)
  Definition LIST_case l f g :=
    cond_set (l == Nil) f ∪ cond_set (exists x,exists l', l == Cons x l') g.

  Global Instance LIST_case_morph : Proper (eq_set==>eq_set==>eq_set==>eq_set) LIST_case.
do 4 red; intros; unfold LIST_case.
apply union2_morph.
 rewrite H; rewrite H0; reflexivity.

 apply cond_set_morph; trivial.
 apply ex_morph; intro.
 apply ex_morph; intro.
 rewrite H; reflexivity.
Qed.

  Lemma LIST_case_Nil f g : LIST_case Nil f g == f.
unfold LIST_case.
rewrite eq_set_ax; intros z.
rewrite union2_ax.
rewrite cond_set_ax.
rewrite cond_set_ax.
intuition auto with *.
destruct H1 as (?,(?,e)).
symmetry in e; apply discr_Cons_Nil in e; contradiction.
Qed.

  Lemma LIST_case_Cons x l f g : LIST_case (Cons x l) f g == g.
unfold LIST_case.
rewrite eq_set_ax; intros z.
rewrite union2_ax.
rewrite cond_set_ax.
rewrite cond_set_ax.
intuition.
 apply discr_Cons_Nil in H1; contradiction.

 right; split; trivial.
 exists x; exists l; reflexivity.
Qed.

(*  Lemma List_iso : iso_fun (LISTf List) List.
apply eq_intro; intros.
*unfold List.
 rewrite <- TI_mono_succ; auto.
 revert H; apply TI_incl; auto.
*elim H using LISTf_ind.
 +do 2 red; intros.
  rewrite H0; reflexivity.
 +apply TI_intro with (osucc zero); auto.
  apply Nil_typ0.
 +intros.
  apply TI_elim in H1; auto.
  destruct H1 as (o,tyo,tyl).  
  apply TI_intro with (osucc o); auto.
  apply Cons_typ0; trivial.
  rewrite TI_mono_succ; auto.
  apply isOrd_inv with omega; trivial.  
Qed.
*)



  Lemma List_ind : forall P : set -> Prop,
    Proper (eq_set ==> iff) P ->
    P Nil ->
    (forall x l, x ∈ A -> l ∈ List -> P l -> P (Cons x l)) ->
    forall a, a ∈ List -> P a.
intros.
rewrite List_def in H2.
destruct H2 as (n,tyn,tya).
revert a tya.
elim tyn using N_ind; intros.
*rewrite <-H3 in tya; auto.
*rewrite Nil_ext with (1:=tya); trivial.
*rewrite Cons_ext with (2:=tya);[|trivial].
 apply H1.
 +apply app_typ with (1:=tya).
  apply lt_0_succ; trivial.
 +apply List_def; exists n0; trivial.
  apply Tl_func; trivial.
 +apply H3.
  apply Tl_func; trivial.
Qed.

  Lemma Nil_typ : Nil ∈ List.
intros.
apply List_def; exists zero; [apply zero_typ|].
apply Nil_func.
Qed.

  Lemma Cons_typ : forall x l,
    x ∈ A -> l ∈ List -> Cons x l ∈ List.
intros.
rewrite List_def in H0; destruct H0 as (n,tyn,tyl).
rewrite List_def; exists (succ n); [apply succ_typ;trivial|].
apply Cons_func; trivial.
Qed.

End ListDefs.

Instance List_mono : Proper (incl_set ==> incl_set) List.
do 3 red; intros.
rewrite List_def in H0|-*.
destruct H0 as (n,?,tyz); exists n; trivial.
revert tyz; apply func_mono; auto with *.
Qed.

Instance List_morph : morph1 List.
apply Fmono_morph.
apply List_mono.
Qed.
