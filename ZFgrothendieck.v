Require Import Zlist.
Require Import Zpairs Zsum Znats Zrelations ZFrepl ZFord ZFfix ZFfixfun.
Require Import Zuniv.
Import ZF Zrelations.


Record grot_univ (U:set) : Prop := {
  G_trans : forall x y, y ∈ x -> x ∈ U -> y ∈ U;
  G_pair : forall x y, x ∈ U -> y ∈ U -> pair x y ∈ U;
  G_power : forall x, x ∈ U -> power x ∈ U;
  G_union : forall x, x ∈ U -> union x ∈ U;
  G_fsup : forall I f, I ∈ U ->
                       f ∈ rel I U ->
                       isFunction f ->
                       rel_image f ∈ U }.

Instance grot_univ_morph : Proper (eq_set==>iff) grot_univ.
apply morph_impl_iff1; auto with *.
do 3 red; intros.
destruct H0 as (Gtr,G2,Gpow,Gun,Gfs).
split; intros.
*rewrite <- H in H1|-*; eauto.
*rewrite <- H in H0,H1|-*; auto.
*rewrite <- H in H0|-*; auto.
*rewrite <- H in H0|-*; auto.
*rewrite <- H in H0,H1|-*.
 apply Gfs with I; intros; auto.
Qed.

Lemma grot_empty : grot_univ empty.
split; intros.
*elim empty_ax with (1:=H0).
*elim empty_ax with (1:=H0).
*elim empty_ax with (1:=H).
*elim empty_ax with (1:=H).
*elim empty_ax with (1:=H).
Qed.
(* TODO: grot_succ empty == HF *)

Lemma grot_univ_zermelo U :
  grot_univ U -> Zuniv U.
destruct 1; split; trivial.
Qed.
#[global]Hint Resolve grot_univ_zermelo : core.
  
Section EquivalenceOfClosureByReplacement.

  (* Showing that all 3 formulation of closure by union are equivalent:
   1- closure by replf
   2- closure by repl
   3- closure by function image
   2 =>(obvious) 1 =>(G_replf_fsup) 3 =>(G_fsup_repl) 2
    We also prove 3 => 1 without reference to repl
   *)

  Variable U : set.
  Hypothesis G_incl :
    forall x y, x ∈ U -> y ⊆ x -> y ∈ U.
  
Lemma G_replf_fsup :
  (forall A F,
      ext_fun A F ->
      A ∈ U ->
      (forall x, x ∈ A -> F x ∈ U) ->
      replf A F ∈ U) ->
  (forall I f,
      I ∈ U ->
      f ∈ rel I U ->
      isFunction f ->
      rel_image f ∈ U).
intros G_replf.
intros.
assert (incl_set (rel_image f) (replf (rel_domain f) (app f))).
{red; intros.
 apply rel_image_ax in H2. 
 destruct H2.
 apply replf_ax; exists x;[|split].
 *apply rel_domain_ax; eauto.
 *red; intros.
  rewrite H3; reflexivity.
 *symmetry; apply app_defined; trivial. }
apply G_incl with (2:=H2).
apply G_replf; [do 2 red; intros; apply app_morph; auto with *|trivial|intros].
*apply G_incl with I; trivial.
 red; intros.
 rewrite rel_domain_ax in H3.
 destruct H3 as (y,?).
 apply power_def in H0.
 apply H0 in H3. 
 apply fst_typ in H3.
rewrite fst_def in H3; trivial. 
*apply app_typ with (2:=H3).
 clear x H2 H3.
 rewrite func_def.
 split; [|split;auto with *].
 destruct H1 as (H1,_). 
 apply relation_is_rel; auto with *.
 apply rel_image_incl with (1:=H0).
Qed.

Lemma G_fsup_replf :
  (forall I f,
      I ∈ U ->
      f ∈ rel I U ->
      isFunction f ->
      rel_image f ∈ U) ->
  (forall A F,
      ext_fun A F ->
      A ∈ U ->
      (forall x, x ∈ A -> F x ∈ U) ->
      replf A F ∈ U).
intros G_fsup.
intros.
apply G_incl with (rel_image (lam A F)).
*apply G_fsup with A; [trivial| |apply lam_isFunction].
 apply func_rel_incl.
 apply lam_is_func; trivial.
*red; intros.
 apply replf_ax in H2.
 destruct H2 as (x,tyx,(efx,eqz)).
 apply rel_image_ax.
 exists x.
 rewrite eqz.
 apply lam_ax_couple.
 split; [|split]; auto with *.
Qed.

Lemma G_fsup_repl :
  (forall I f,
      I ∈ U ->
      f ∈ rel I U ->
      isFunction f ->
      rel_image f ∈ U) ->
  (forall I R,
      repl_rel I R -> I ∈ U ->
      (forall x y, x ∈ I -> R x y -> y ∈ U) ->
      repl I R ∈ U).
intros G_fsup.
intros.
pose (f := inject_rel R I U).  
assert (extR : ext_rel I R).  
{red; intros.
 split; apply H; auto.
 *rewrite <-H3; trivial.
 *symmetry; trivial.
 *symmetry; trivial. }
apply G_incl with (rel_image f).
*apply G_fsup with I; [trivial|apply inject_rel_is_rel|].
 split.
 +apply rel_isRelation with I U.
  apply inject_rel_is_rel.
 +intros.
  apply inject_rel_elim in H2; auto with *.
  destruct H2 as (ty1&ty2&rel).
  apply inject_rel_elim in H3; auto with *.
  destruct H3 as (_&ty2'&rel').
  apply (proj2 H) with x; trivial.
*red; intros.
 apply repl_ax in H2; [|apply H|apply H].
 destruct H2 as (x,tyx,eqz).
 apply rel_image_ax.
 exists x.
 apply inject_rel_intro; eauto.
Qed.


End EquivalenceOfClosureByReplacement.

Section GrothendieckUniverse.

Variable U : set.
Hypothesis grot : grot_univ U.

Lemma G_incl : forall x y, x ∈ U -> y ⊆ x -> y ∈ U.
intros.
apply G_trans with (power x); trivial.
 rewrite power_ax; auto.

 apply G_power; trivial.
Qed.

Lemma G_subset : forall x P, x ∈ U -> subset x P ∈ U.
intros.
apply G_incl with x; trivial.
red; intros.
apply subset_elim1 in H0; trivial.
Qed.
  
Lemma G_replf : forall A F,
  ext_fun A F ->
  A ∈ U ->
  (forall x, x ∈ A -> F x ∈ U) ->
  replf A F ∈ U.
apply G_fsup_replf; [apply G_incl|apply G_fsup; trivial].
Qed.

Lemma G_sup A B :
  ext_fun A B ->
  A ∈ U ->
  (forall x, x ∈ A -> B x ∈ U) ->
  sup A B ∈ U.
intros.
apply G_union; trivial.
apply G_replf; trivial.
Qed.

Lemma G_power_inv x :
  power x ∈ U -> x ∈ U.
intros.
apply G_trans with (power x); trivial.
apply power_def; reflexivity.
Qed.

Lemma G_union_inv x :
  union x ∈ U -> x ∈ U.
intros.
apply G_incl with (power (union x)); [apply G_power; auto|].
red; intros.
apply power_def; red; intros.
apply union_intro with z; trivial.
Qed.

Lemma G_singl : forall x, x ∈ U -> singl x ∈ U.
unfold singl; intros; apply G_pair; auto.
Qed.

Lemma G_union2 : forall x y, x ∈ U -> y ∈ U -> x ∪ y ∈ U.
intros.
unfold union2.
apply G_union; trivial.
apply G_pair; trivial.
Qed.

Lemma G_nat x : x ∈ U -> N ⊆ U.
red; intros.
elim H0 using N_ind; intros.
 rewrite <- H2; trivial.

 apply G_incl with x; trivial.

 apply G_union2; trivial.
 apply G_singl; trivial.
Qed.


Lemma G_couple : forall x y, x ∈ U -> y ∈ U -> couple x y ∈ U.
intros.
apply G_union_inv.
rewrite union_couple_eq.
apply G_pair; trivial.
Qed.

Local Transparent prodcart sigma.

Lemma G_prodcart : forall A B, A ∈ U -> B ∈ U -> prodcart A B ∈ U.
intros.
unfold prodcart.
apply G_subset; intros; trivial.
apply G_power; trivial.
apply G_power; trivial.
apply G_union2; trivial.
Qed.

  Lemma G_sigma A B :
    ext_fun A B ->
    A ∈ U ->
    (forall x, x ∈ A -> B x ∈ U) ->
    sigma A B ∈ U.
intros.
apply G_subset; trivial.
apply G_prodcart; trivial.
apply G_sup; trivial.
Qed.

Opaque prodcart sigma.

Lemma ext_is_unif_bound A F :
  ext_fun A F ->
  A ∈ U ->
  typ_fun F A U ->
  unif_bound U A F.
exists (sup A F).
*apply G_sup; trivial.
*red; intros.
 apply sup_ax; eauto.
Qed.

  Lemma G_sum X Y : X ∈ U -> Y ∈ U -> sum X Y ∈ U.
unfold sum; intros.
apply G_union2; apply G_prodcart; trivial.
 apply G_singl; apply G_nat with X; trivial.
 apply zero_typ.

 apply G_singl; apply G_nat with X; trivial.
 apply succ_typ;  apply zero_typ.
Qed.

Lemma G_sumcase A B f g a :
  morph1 f ->
  morph1 g ->
  a ∈ sum A B ->
  (forall a, a ∈ A -> f a ∈ U) ->
  (forall a, a ∈ B -> g a ∈ U) ->
  sum_case f g a ∈ U.
intros.
apply sum_case_ind with (6:=H1); intros; auto.
apply morph_impl_iff1; auto with *.
do 3 red; intros.
rewrite <- H4; trivial.
Qed.

Lemma G_rel : forall A B, A ∈ U -> B ∈ U -> rel A B ∈ U.
intros.
unfold rel.
apply G_power; trivial.
apply G_prodcart; trivial.
Qed.

Lemma G_func : forall A B, A ∈ U -> B ∈ U -> func A B ∈ U.
Proof.
intros.
eapply G_incl;[|apply func_bound; trivial].
do 3 (apply G_power;trivial).
apply G_union2; trivial.
Qed.

Lemma G_dep_func : forall X Y,
  ext_fun X Y ->
  X ∈ U ->
  (forall x, x ∈ X -> Y x ∈ U) ->
  dep_func X Y ∈ U.
Proof.
intros.
eapply G_incl;[|apply dep_func_bound; trivial].
do 3 (apply G_power;trivial).
apply G_union2; trivial.
apply G_sup; trivial.
Qed.

Local Transparent lam app cc_lam cc_app.
Lemma G_app f x :
  f ∈ U -> x ∈ U -> app f x ∈ U.
unfold app; intros.
apply G_union; trivial.
apply G_subset.
unfold rel_image.
apply G_subset.
apply G_union; trivial.
apply G_union; trivial.
Qed.

  Lemma G_cc_lam A F :
    A ∈ U ->
    (forall x, x ∈ A -> F x ∈ U) ->
    cc_lam A F ∈ U.
intros.
unfold cc_lam.
apply G_sup; intros; trivial.
{do 2 red; intros; apply replf_morph; auto.
 rewrite H2; reflexivity.
 red; intros; apply couple_morph; trivial. }
apply G_replf.
*do 2 red; intros.
 rewrite H3; reflexivity.
*apply G_incl with (F x); auto.
 red; intros.
 apply extf_def in H2; apply H2.
*intros.
 apply G_couple; [apply G_trans with A; trivial|]. 
 apply extf_def in H2; destruct H2.
 apply G_trans with (F x); auto.
Qed.

  Lemma G_cc_app f x :
    f ∈ U -> x ∈ U -> cc_app f x ∈ U.
unfold cc_app; intros.
unfold rel_image.
apply G_subset.
apply G_union; trivial.
apply G_union; trivial.
apply G_subset; trivial.
Qed.
Opaque lam app cc_lam cc_app.

  Lemma G_cc_prod A B :
    ext_fun A B ->
    A ∈ U ->
    (forall x, x ∈ A -> B x ∈ U) ->
    cc_prod A B ∈ U.
intros.
eapply G_incl;[|apply cc_prod_bound; trivial].
do 3 (apply G_power;trivial).
apply G_union; trivial.
apply G_pair; trivial.
apply G_union; trivial.
apply G_sup; trivial.
Qed.

  Lemma G_TR F o :
    Proper ((eq_set==>eq_set)==>eq_set==>eq_set) F ->
    (forall o o' f f', isOrd o -> o==o' -> eq_fun o f f' -> F f o == F f' o') ->
    isOrd o ->
    o ∈ U ->
    (forall f o, ext_fun o f -> o ∈ U ->
     (forall o', o' ∈ o -> f o' ∈ U) ->
     F f o ∈ U) ->
    TR F o ∈ U.
intros Fm Fext oo oU FU.
apply TR_typ with (X:=fun _ => U); auto.
 do 2 red; reflexivity.
intros.
apply FU; auto.
apply G_incl with o; trivial.
Qed.

  Lemma G_TI F o :
    morph1 F ->
    isOrd o ->
    o ∈ U ->
    (forall x, x ∈ U -> F x ∈ U) ->
    TI F o ∈ U.
intros.
apply G_TR; trivial; intros.
 do 3 red; intros.
 apply sup_morph; auto.
 red; intros; auto.

 apply sup_morph; auto with *.
 red; intros.
 apply H; auto.

 apply G_sup; auto.
 do 2 red; intros; apply H; auto.
Qed.

Lemma G_osup2 x y :
  isOrd x -> x ∈ U -> y ∈ U -> x ⊔ y ∈ U.
intro wfx; revert y; induction wfx using isOrd_ind.
intros.
rewrite osup2_def; trivial.
 apply G_union2; trivial.
  apply G_union2; trivial.

  apply G_union; trivial.
  apply G_replf; trivial; intros.
   do 2 red; intros; apply replf_morph; auto with *.
   red; intros; apply osup2_morph; trivial.

   apply G_replf; trivial; intros.
    do 2 red; intros; apply osup2_morph; auto with *.

    eauto using G_trans.
Qed.

  Lemma G_Fstages F A : A ∈ U -> Fstages F A ∈ U.
intros.
unfold Fstages.
apply G_subset; trivial.
Qed.

  Lemma G_TIF A F :
    Proper ((eq_set==>eq_set)==>eq_set==>eq_set) F ->
    mono_fam A F ->
    (forall X a, a ∈ A -> morph1 X -> typ_fun X A U -> F X a ∈ U) ->
    forall o a, isOrd o -> o ∈ U -> a ∈ A -> TIF A F o a ∈ U.
intros Fm Fmono Uty o a oo oty aty.
revert a aty.
apply isOrd_ind with (2:=oo); intros o' oo' o'le orec; intros.
rewrite TIF_eq; trivial.
apply G_sup; trivial.
 do 2 red; intros.
 apply Fm; auto with *.
 apply TIF_morph; trivial.

 apply G_incl with o; trivial.

 intros.
 apply Uty; trivial.
  apply TIF_morph; auto with *.

  red; intros.
  apply orec; trivial.
Qed.

Section NonTrivial.

  Hypothesis Unontriv : empty ∈ U.

End NonTrivial.


Section OrdInfinite.

  Hypothesis Uinf : omega ∈ U.

  Lemma G_empty_omega : empty ∈ U.
apply G_trans with omega; trivial.
apply zero_omega.
Qed.

  Lemma G_N : N ∈ U.
pose (f := fun X => singl zero ∪ replf X succ).
assert (fm : morph1 f).
 do 2 red; intros.
 apply union2_morph; auto with *.
 apply replf_morph; trivial.
 red; intros; apply succ_morph; trivial.
assert (N ⊆ TI f omega).
 red; intros.
 apply nat2set_reflect in H.
 destruct H.
 rewrite H.
 clear z H.
 induction x; simpl.
  apply TI_intro with empty; trivial.
  apply union2_intro1.
  apply singl_intro.

  apply TI_elim in IHx; trivial.
  destruct IHx.
  apply TI_intro with (osucc x0); auto.
  apply union2_intro2.
  rewrite replf_def.
  2:do 2 red; intros; apply succ_morph; trivial.
  exists (nat2set x); auto with *.
  apply TI_intro with x0; auto.
   eauto using isOrd_inv.

   apply lt_osucc; eauto using isOrd_inv.
apply G_incl with (2:=H); trivial.
apply G_TI; trivial; intros.
apply G_union2; trivial.
 apply G_singl; trivial.
 apply G_empty_omega.

 apply G_replf; trivial.
  do 2 red; intros; apply succ_morph; trivial.

  intros.
  unfold succ.
  apply G_union2; eauto using G_trans.
  apply G_singl; trivial.
  apply G_trans with x; trivial.
Qed.

End OrdInfinite.

Section Infinite.

  Hypothesis Uinf : N ∈ U.

  Lemma G_inf_nontriv : empty ∈ U.
apply G_trans with N; trivial.
apply zero_typ.
Qed.
  Hint Resolve G_inf_nontriv : core.

  Lemma G_omega : omega ∈ U.
apply G_sup; auto with *.
intros.
apply ZFnats.natrec_typ with (P:=fun _=>U); auto with *.
*do 2 red; reflexivity.
*do 3 red; intros.
 rewrite H1; reflexivity.
*intros.
 apply G_subset.
 apply G_power; auto.
Qed.

  Lemma G_List A : A ∈ U -> List A ∈ U.
intros.
unfold List.
apply G_sup;
  [intros ??? e; rewrite e; reflexivity|trivial|].
intros.
apply G_func;[|trivial].
apply G_trans with N; trivial.
Qed.

Lemma G_osup I f :
  ext_fun I f ->
  (forall x, x ∈ I -> isOrd (f x)) ->
  I ∈ U ->
  (forall x, x ∈ I -> f x ∈ U) ->
  osup I f ∈ U.
intros ef ford IU fU.
apply osup_univ; trivial; intros.
 apply G_sup; trivial.

 apply G_singl.
 apply G_osup2; eauto using G_trans.
Qed.

  Lemma G_clos_ord F A :
    Proper (incl_set ==> incl_set) F ->
    (forall X, X ⊆ A -> F X ⊆ A) ->
    A ∈ U ->
    clos_ord F A ∈ U.
intros.
assert (Fm := Fmono_morph _ H).
unfold clos_ord.
apply G_osup; intros; trivial.
 do 2 red; intros; apply osucc_morph.
 apply Fix_rec_morph; auto with *.
 do 2 red; intros.
 apply F_a_morph_gen; auto with *.

 apply isOrd_succ.
 apply F_a_ord; auto.

 apply G_Fstages; trivial.

 unfold osucc; apply G_subset; trivial; apply G_power; trivial.
 apply subset_elim1 with (P:=isOrd).
 apply Fix_rec_typ; auto; intros.
  apply F_a_morph; trivial.

  unfold F_a.
  apply subset_intro.
   apply G_osup.
    do 2 red; intros.
    apply osucc_morph; apply H3; trivial.

    intros.
    apply isOrd_succ.
    apply H5 in H6.
    apply subset_elim2 in H6; destruct H6.
    rewrite H6; trivial.

    unfold fsub.
    apply G_subset; trivial.
    apply G_Fstages; trivial.

    intros.
    unfold osucc.
    apply G_subset; trivial.
    apply G_power; trivial.
    apply H5 in H6.
    apply subset_elim1 in H6; trivial.

   apply isOrd_osup.
    do 2 red; intros; apply osucc_morph; apply H3; trivial.

    intros.
    apply isOrd_succ.
    apply H5 in H6.
    apply subset_elim2 in H6; destruct H6.
    rewrite H6; trivial.
Qed.

End Infinite.

(*
Section ZF_Universe.

  Hypothesis coll_ax : forall A (R:set->set->Prop), 
    (forall x x' y y', x ∈ A -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x, x ∈ A -> exists y, R x y) ->
    exists B, forall x, x ∈ A -> exists2 y, y ∈ B & R x y.

  (* Grothendieck universe is closed by collection *)
  Hypothesis G_coll : forall A (R:set->set->Prop), 
    A ∈ U ->
    (forall x x' y y', x ∈ A -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x, x ∈ A -> exists2 y, y ∈ U & R x y) ->
    exists2 B, B ∈ U & forall x, x ∈ A -> exists2 y, y ∈ B & R x y.


  Lemma G_ttcoll : forall A (R:set->set->Prop),
  (forall x x' y y', x ∈ A -> x == x' -> y == y' -> R x y -> R x' y') ->
  (forall x, x ∈ A -> exists y, R x y) ->
  A ⊆ U ->
  exists2 X, morph1 X &
  (forall x, x ∈ A -> X x ∈ U) /\
  exists2 f, morph2 f &
    forall x, x ∈ A -> exists2 i, i ∈ X x & R x (f x i).
intros.


intros.
destruct (coll_ax A R) as (B,HB); trivial.


End ZF_Universe.
*)

End GrothendieckUniverse.

(** Intersection *)

Lemma grot_inter : forall UU,
  (exists x, x ∈ UU) ->
  (forall x, x ∈ UU -> grot_univ x) ->
  grot_univ (inter UU).
destruct 1.
split; intros.
*apply inter_intro; intros; eauto.
 destruct (H0 _ H3) as (trans,_,_,_,_).
 apply trans with x0; trivial.
 apply inter_elim with (1:=H2); trivial.

*apply inter_intro; intros; eauto.
 destruct (H0 _ H3) as (_,clos_pair,_,_,_).
 apply clos_pair; eapply inter_elim; eauto.

*apply inter_intro; intros; eauto.
 destruct (H0 _ H2) as (_,_,clos_pow,_,_).
 apply clos_pow; eapply inter_elim; eauto.

*apply inter_intro; intros; eauto.
 destruct (H0 _ H2) as (_,_,_,clos_un,_).
 apply clos_un; eapply inter_elim; eauto.

*apply inter_intro; intros; eauto.
 destruct (H0 _ H4) as (_,_,_,_,clos_fsup).
 apply clos_fsup with I; trivial; intros.
 +eapply inter_elim; eauto.
 +revert H2; apply rel_mono; [reflexivity|].
  red; intros.
  eapply inter_elim; eauto.
Qed.

(* The intersection of all Grothendieck universes satisfying P given
   an superset UU (containing at least one universe satisfying P) *)
Definition intersection_grot (UU:set) (P:set->Prop) :=
  subset UU (fun y => forall V, grot_univ V -> P V -> y ∈ V).

Lemma grot_intersection (P:set->Prop) UU :
  (exists U, grot_univ U /\ P U /\ U ⊆ UU) ->
  grot_univ (intersection_grot UU P).
intros (U & gU & pU & Uincl).
assert (Vdef : forall z, z ∈ intersection_grot UU P <-> forall V, grot_univ V -> P V -> z ∈ V).
{unfold intersection_grot; intros.
 split; intros. 
 *destruct subset_elim2 with (1:=H) as (z',eqz,?); clear H.
  rewrite eqz; auto.
 *apply subset_intro; [|auto].
  apply Uincl; auto. }
split; intros.
*rewrite Vdef in H0|-*; intros.
 apply G_trans with x; auto.
*rewrite Vdef in H,H0|-*; intros.
 apply G_pair; auto.
*rewrite Vdef in H|-*; intros.
 apply G_power; auto.
*rewrite Vdef in H|-*; intros.
 apply G_union; auto.
*rewrite Vdef in H|-*; intros.
 apply G_fsup with I; auto.
 revert H0; apply rel_mono; [reflexivity|].
 red; intros.
 rewrite Vdef in H0; auto.
Qed.


(** Successor *)

(** [y] is the the successor of [x]
    if it the least Grothendieck universe of which [x] is an element *)
Definition grot_succ_pred x y :=
  grot_univ y /\ x ∈ y /\ forall U, grot_univ U -> x ∈ U -> y ⊆ U.

Instance grot_succ_pred_morph : Proper (eq_set==>eq_set==>iff) grot_succ_pred.
do 3 red; intros.
apply and_iff_morphism.
 apply grot_univ_morph; trivial.
apply and_iff_morphism.
 apply in_set_morph; trivial.
apply fa_morph; intros U.
rewrite H; rewrite H0; reflexivity.
Qed.

(** Build the successor given an upper bound *)
Definition grot_succ_ub UU x := intersection_grot UU (fun U => x ∈ U).

Instance grot_succ_ub_morph : morph2 grot_succ_ub.
do 3 red; intros; apply subset_morph; trivial.
red; intros.
apply fa_morph; intros z.
rewrite H0; reflexivity.
Qed.

Lemma grot_succ_ub_sound UU x :
  (exists U, grot_univ U /\ x ∈ U /\ U ⊆ UU) ->
  grot_succ_pred x (grot_succ_ub UU x).
intros has_ub.
destruct (has_ub) as (U&gU&xin&ub).
split;[|split]; intros.
*apply grot_intersection; trivial.

*apply subset_intro; auto.

*red; intros.
 unfold grot_succ_ub, intersection_grot in H1;
   rewrite subset_ax in H1; destruct H1 as (_,(z',eqz,?)).
 rewrite eqz; auto.
Qed.


(** The Tarski-Grothendieck set theory *)
Definition grothendieck := forall x, exists2 U, grot_univ U & x ∈ U.



(* Using uchoice: no need for an approximation *)

Module WithUChoice.
  
Definition grot_succ U := ZFrepl.uchoice (grot_succ_pred U).

Instance grot_succ_morph : morph1 grot_succ.
do 2 red; intros.
apply ZFrepl.uchoice_morph_raw.
apply grot_succ_pred_morph; trivial.
Qed.

Lemma grot_succ_incl x y :
  x ∈ grot_succ y ->
  uchoice_pred (grot_succ_pred x) ->
  uchoice_pred (grot_succ_pred y) ->
  grot_succ x ⊆ grot_succ y.
intros.
specialize ZFrepl.uchoice_def with (1:=H0); intros (_,(_,xmin)).
specialize ZFrepl.uchoice_def with (1:=H1); intros (?,(?,_)).
apply xmin; trivial.
Qed.

Lemma grot_succ_mono x y :
  x ⊆ y ->
  uchoice_pred (grot_succ_pred x) ->
  uchoice_pred (grot_succ_pred y) ->
  grot_succ x ⊆ grot_succ y.
intros.
apply grot_succ_incl; trivial.
specialize ZFrepl.uchoice_def with (1:=H1); intros (?,(?,_)).
apply G_incl with y; trivial.
Qed.

Definition grot_succ_U U x :=
  subset U (fun y => forall V, grot_univ V -> x ∈ V -> y ∈ V).

Lemma grot_succ_ex x y :
  grot_succ_pred x y ->
  uchoice_pred (grot_succ_pred x).
split;[|split]; intros.
 revert H1; apply grot_succ_pred_morph; auto with *.

 exists y; trivial.

 destruct H0 as (?,(?,?)).
 destruct H1 as (?,(?,?)).
 apply incl_eq; auto.
Qed.

Lemma grot_succ_U_typ x :
  uchoice_pred (grot_succ_pred x) ->
  grot_univ (grot_succ x).
intro.
apply ZFrepl.uchoice_def in H; apply H.
Qed.

Lemma grot_succ_U_in x :
  uchoice_pred (grot_succ_pred x) ->
  x ∈ grot_succ x.
intro.
apply ZFrepl.uchoice_def in H; destruct H as (_,(?,_)); trivial.
Qed.

Lemma grot_succ_U_lst U x :
  grot_univ U ->
  x ∈ U ->
  grot_succ x ⊆ U.
intros.
assert (grot_succ_pred x (grot_succ_ub U x)).
{apply grot_succ_ub_sound; eauto with *. }
apply grot_succ_ex in H1.
apply ZFrepl.uchoice_def in H1.
destruct H1 as (_,(_,?)); auto.
Qed.

(** The Tarski-Grothendieck set theory *)

Section TarskiGrothendieck.

Variable gr : grothendieck.

Lemma grot_inter_unique : forall x, uchoice_pred (grot_succ_pred x).
intros.
destruct (gr x) as (U, gU, xU).
assert (grot_succ_pred x (grot_succ_ub U x)).
{apply grot_succ_ub_sound; eauto with *. }
apply WithUChoice.grot_succ_ex in H; trivial.
Qed.

Lemma grot_succ_typ : forall x, grot_univ (grot_succ x).
intros.
apply grot_succ_U_typ.
apply grot_inter_unique.
Qed.

Lemma grot_succ_in : forall x, x ∈ grot_succ x.
intros.
apply grot_succ_U_in.
apply grot_inter_unique.
Qed.

End TarskiGrothendieck.

End WithUChoice.

