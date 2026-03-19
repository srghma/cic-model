Require Import basic Zpairs Zsum Zrelations.
Require Import ZFcont.
Require Import ZFord ZFfix ZFfixrec.
Require Import ZFfixfun.
Import ZF.
Require Export Ziso.
Set Implicit Arguments.

(** * Transfinite iteration *)

Section TI_iso.

  Let isoF F g o f := cc_lam (F (TI F o)) (g (cc_app f)).
  
  Definition TI_iso F g o :=
    cc_app (REC (isoF F g) o).

Lemma iso_cont : forall F G o f,
  Proper (incl_set ==> incl_set) F ->
  Proper (incl_set ==> incl_set) G ->
  morph1 f ->
  isOrd o ->
  (forall o', o' ∈ o -> iso_fun (TI F (osucc o')) (TI G (osucc o')) f) ->
  iso_fun (TI F o) (TI G o) f.
intros F G o f Fmono Gmono fm oo iso'.
assert (Fm := Fmono_morph _ Fmono).
assert (Gm := Fmono_morph _ Gmono).
constructor; intros; trivial.
 red; intros. 
 apply TI_elim in H; trivial.
 destruct H.
 apply TI_intro with x0; trivial.
 rewrite <- TI_mono_succ; eauto using isOrd_inv.
 apply (iso_typ (iso' _ H)).
 rewrite TI_mono_succ; eauto using isOrd_inv.

 apply TI_elim in H; trivial.
 destruct H.
 apply TI_elim in H0; trivial.
 destruct H0.
 red in H,H0.
 assert (exists2 z, z ∈ o & x ∈ F (TI F z) /\ x' ∈ F (TI F z)).
  destruct (isOrd_dir _ oo x0 x1); trivial.
  destruct H5.
  exists x2; trivial.
  split.
   revert H2; apply Fmono.
   apply TI_mono; eauto using isOrd_inv.

   revert H3; apply Fmono.
   apply TI_mono; eauto using isOrd_inv.
 destruct H4.
 destruct H5.
 apply (iso_inj (iso' _ H4)); trivial.
  rewrite TI_mono_succ; eauto using isOrd_inv.
  rewrite TI_mono_succ; eauto using isOrd_inv.

 apply TI_elim in H; auto.
 destruct H.
 destruct (iso_surj (iso' _ H)) with y.
  rewrite TI_mono_succ; eauto using isOrd_inv.
 exists x0; trivial.
 apply TI_intro with x; trivial.
 rewrite <- TI_mono_succ; eauto using isOrd_inv.
Qed.

  Variable F G : set -> set.
  Variable g : (set -> set) -> set -> set.
  Hypothesis Fmono : Proper (incl_set ==> incl_set) F.
  Hypothesis Gmono : Proper (incl_set ==> incl_set) G.
  Hypothesis gm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) g.
  Hypothesis gext : forall o f f',
    morph1 f ->
    isOrd o ->
    eq_fun (TI F o) f f' ->
    eq_fun (F (TI F o)) (g f) (g f').
  Hypothesis isog : forall o f, isOrd o ->
    iso_fun (TI F o) (TI G o) f -> iso_fun (F (TI F o)) (G (TI G o)) (g f).

  Let Fm := Fmono_morph _ Fmono.
  Let Gm := Fmono_morph _ Gmono.
  Let egf : forall o' f, isOrd o' -> ext_fun (F (TI F o')) (g (cc_app f)).
do 2 red; intros.
apply gm; trivial.
apply cc_app_morph; auto with *.
Qed.


Section IsoFamilyCorollary.
  (** If we have a family of isomorphism, then the least fixpoints of F and G
      are isomorphic, and they have the same closure ordinal  *)
  Variable isof : set -> set -> set.
  Hypothesis isof_iso : forall o, isOrd o -> iso_fun (TI F o) (TI G o) (isof o).
  Hypothesis isof_def : forall o x, isOrd o -> x ∈ TI F o -> isof o x == g (isof o) x.
  
  Lemma TI_same_fixpoint_by_iso o :
    isOrd o ->
    (TI F o == F (TI F o) <-> TI G o == G (TI G o)).
intros oord.
assert (iso1 := isof_iso oord).
assert (iso2 := isog oord iso1).
assert (same_iso : eq_fun (TI F o) (isof o) (g (isof o))).
{red; intros.
 transitivity (isof o x').
  apply iso1; trivial.
 rewrite H0 in H.
 apply isof_def; trivial. }
assert (iso1' : iso_fun (TI F o) (TI G o) (g (isof o))).
{generalize iso1; apply iso_fun_ext; auto with *.
 apply gm.
 apply iso1. }
clear iso1.
split; intros.
*apply iso_fun_sym in iso1'.
 apply iso_fun_inj with (TI F o) (iso_inv (TI F o) (g (isof o))); trivial.
 +apply iso_fun_sym.
  generalize iso2; apply iso_fun_morph; auto with *.
  apply iso_funm in iso2; trivial.

 +rewrite <- TI_mono_succ; auto.
  apply TI_incl; auto.

*apply iso_fun_inj with (TI G o) (g (isof o)); trivial.
 +apply iso_change_rhs with (G (TI G o)); auto with *.

 +rewrite <- TI_mono_succ; auto.
  apply TI_incl; auto.
Qed.

  Lemma TI_same_closure_ordinal_by_iso o :
    isOrd o ->
    (closure_ordinal F o <-> closure_ordinal G o). 
intros oo.
rewrite TI_closure_ordinal; trivial.
rewrite TI_closure_ordinal; trivial.
apply TI_same_fixpoint_by_iso; trivial.
Qed.

End IsoFamilyCorollary.

  Lemma TI_iso_recursor_hyps ord :
    recursor_hyps ord (TI F)
      (fun o f => iso_fun (TI F o) (TI G o) (cc_app f)) (isoF F g).
constructor; intros.
 apply TI_morph.

 red; intros.
 apply TI_mono_eq; auto.

 revert H3; apply iso_fun_ext; auto with *.
  apply TI_morph; trivial.
  apply TI_morph; trivial.

  red; intros.
  rewrite <- H4; auto.

  apply iso_cont; trivial.
  apply cc_app_morph; reflexivity.

 do 3 red; intros.
 apply cc_lam_ext.
  apply Fm; apply TI_morph; auto.

  red; intros.
  apply gm; trivial.
  apply cc_app_morph; auto with *.

 clear H0; rename H1 into ffun, H2 into fiso.
 split.
  rewrite TI_mono_succ; auto with *.
  apply is_cc_fun_lam; auto.

  apply isog in fiso; trivial.
  revert fiso; apply iso_fun_ext.
   apply cc_app_morph; reflexivity.
   symmetry; apply TI_mono_succ; eauto using isOrd_inv.
   symmetry; apply TI_mono_succ; eauto using isOrd_inv.

   red; intros.  
   unfold isoF; rewrite cc_beta_eq; auto.
    rewrite H1; reflexivity.

    rewrite <- H1; trivial.

 (* irrel : *)
 red; intros.
 clear H.
 red; intros.
 destruct H1 as (oo0,(ofun,oiso)); destruct H2 as (oo',(o'fun,o'iso)).
 unfold isoF at 1; rewrite cc_beta_eq; auto.
 2:rewrite TI_mono_succ in H; auto with *.
 unfold isoF; rewrite cc_beta_eq; auto.
  apply (@gext o); auto with *.
   red; intros.
   rewrite <- H2; auto.

   rewrite <- TI_mono_succ; auto.

  rewrite TI_mono_succ in H; auto with *.
  revert H; apply Fmono; apply TI_mono; auto.
Qed.

  Lemma TI_iso_recursor ord :
    isOrd ord ->
    recursor_spec ord (TI F)
      (fun o f => iso_fun (TI F o) (TI G o) (cc_app f))
      (isoF F g)
      (REC (isoF F g)).
intros; apply REC_recursor_spec; trivial.
apply TI_iso_recursor_hyps.
Qed.
  
  Lemma TI_iso_fun o:
    isOrd o ->
    iso_fun (TI F o) (TI G o) (TI_iso F g o) /\
    (forall x, x ∈ TI F o -> TI_iso F g o x == g (TI_iso F g o) x).
intros oord.
split; intros.
 apply rec_spec_typ with (2:=oord) (1:=TI_iso_recursor oord); auto with *.

 unfold TI_iso.
 rewrite rec_spec_eqn with (1:=TI_iso_recursor oord) (2:=oord); auto with *.
 unfold isoF; rewrite cc_beta_eq; auto with *.
 rewrite <- TI_mono_succ; auto.
 revert H; apply TI_incl; auto.
Qed.

  Lemma TI_iso_irrel o' o'' :
    isOrd o' ->
    isOrd o'' ->
    o' ⊆ o'' ->
    eq_fun (TI F o') (TI_iso F g o') (TI_iso F g o'').
red; intros.
unfold TI_iso at 2; rewrite <- H3.
apply rec_spec_irr with (1:=TI_iso_recursor H0); auto with *.
Qed.

  
  Lemma TI_iso_fixpoint o :
    isOrd o ->
    (TI F o == F (TI F o) <-> TI G o == G (TI G o)).
apply TI_same_fixpoint_by_iso with (isof := TI_iso F g); intros; apply TI_iso_fun; trivial.
Qed.

End TI_iso.


Section TIF_iso.

  Variable A : set.
  Variable F G : (set -> set) -> set -> set.
  Hypothesis Fm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) F.
  Hypothesis Gm : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) G.
  Hypothesis Fmono : mono_fam A F.
  Hypothesis Gmono : mono_fam A G.

Lemma TIF_iso_cont : forall o f,
  (forall a, a ∈ A -> morph1 (f a)) ->
  isOrd o ->
  (forall a o', a ∈ A -> o' ∈ o ->
   iso_fun (TIF A F (osucc o') a) (TIF A G (osucc o') a) (f a)) ->
  forall a, a ∈ A -> iso_fun (TIF A F o a) (TIF A G o a) (f a).
intros o f fm oo iso' a tya.
constructor; intros; auto.
 red; intros. 
 apply TIF_elim in H; trivial.
 destruct H.
 apply TIF_intro with x0; trivial.
 rewrite <- TIF_mono_succ; eauto using isOrd_inv.
 apply (iso_typ (iso' _ _ tya H)).
 rewrite TIF_mono_succ; eauto using isOrd_inv.

 apply TIF_elim in H; trivial.
 destruct H.
 apply TIF_elim in H0; trivial.
 destruct H0.
 red in H,H0.
 assert (exists2 z, z ∈ o & x ∈ F (TIF A F z) a /\ x' ∈ F (TIF A F z) a).
  destruct (isOrd_dir _ oo x0 x1); trivial.
  destruct H5.
  exists x2; trivial.
  split.
   revert H2; apply Fmono; auto with *.
    apply TIF_morph; reflexivity.
    apply TIF_morph; reflexivity.
   red; intros.
   transitivity (TIF A F x2 a0).
    apply TIF_mono; eauto using isOrd_inv.

    red; intro; apply eq_elim.
    apply TIF_morph; auto with *.

   revert H3; apply Fmono; auto with *.
    apply TIF_morph; reflexivity.
    apply TIF_morph; reflexivity.
   red; intros.
   transitivity (TIF A F x2 a0).
    apply TIF_mono; eauto using isOrd_inv.

    red; intro; apply eq_elim.
    apply TIF_morph; auto with *.
 destruct H4.
 destruct H5.
 apply (iso_inj (iso' _ _ tya H4)); trivial.
  rewrite TIF_mono_succ; eauto using isOrd_inv.
  rewrite TIF_mono_succ; eauto using isOrd_inv.

 apply TIF_elim in H; auto.
 destruct H.
 destruct (iso_surj (iso' _ _ tya H)) with y.
  rewrite TIF_mono_succ; eauto using isOrd_inv.
 exists x0; trivial.
 apply TIF_intro with x; trivial.
 rewrite <- TIF_mono_succ; eauto using isOrd_inv.
Qed.


  Let fmrph g f o :
    isOrd o ->
    Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set==>eq_set) g ->
    ext_fun (sigma A (fun a' => TIF A F (osucc o) a'))
     (fun p => g (fun x y => cc_app f (couple x y)) (fst p) (snd p)).
do 2 red; intros.
apply H0.
2:apply fst_morph; trivial.
2:apply snd_morph; trivial.
do 2 red; intros.
rewrite H3; rewrite H4; reflexivity.
Qed.

  Let isoF g := fun o f =>
         cc_lam (sigma A (fun a' => TIF A F (osucc o) a'))
                (fun p => g (fun x y => cc_app f (couple x y)) (fst p) (snd p)).

  Definition TIF_iso g o a x :=
    cc_app (REC (isoF g) o) (couple a x).


  Variable g : (set -> set -> set) -> set -> set -> set.
  Hypothesis gm : Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set==>eq_set) g.
  Hypothesis gext :
     forall X f f', morph1 X -> morph2 f -> morph2 f' ->
     (forall a, a ∈ A -> eq_fun (X a) (f a) (f' a)) ->
     forall a, a ∈ A -> eq_fun (F X a) (g f a) (g f' a).
  Hypothesis isog :
     forall X Y f, morph1 X -> morph1 Y -> morph2 f ->
     (forall a, a ∈ A -> iso_fun (X a) (Y a) (f a)) ->
      forall a, a ∈ A -> iso_fun (F X a) (G Y a) (g f a).


Section IsoFamilyCorollary.
  (** If we have a family of isomorphism, then the least fixpoints of F and G
      are isomorphic, and they have the same closure ordinal  *)
  Variable isof : set -> set -> set -> set.
  Hypothesis isofm : forall o, isOrd o -> morph2 (isof o).
  Hypothesis isof_iso :
    forall o a, isOrd o -> a ∈ A -> iso_fun (TIF A F o a) (TIF A G o a) (isof o a).
  Hypothesis isof_def :
    forall o a x, isOrd o -> a ∈ A -> x ∈ TIF A F o a -> isof o a x == g (isof o) a x.
  
  Lemma TIF_same_fixpoint_by_iso o :
    isOrd o ->
    ((forall a, a ∈ A -> TIF A F o a == F (TIF A F o) a) <->
     (forall a, a ∈ A -> TIF A G o a == G (TIF A G o) a)).
intros oord.
assert (iso1 := fun a => @isof_iso _ a oord).
assert (iso2:forall a : set, a ∈ A -> iso_fun (F (TIF A F o) a) (G (TIF A G o) a) (g (isof o) a)).
{apply isog; auto with *.
 apply TIF_morph; auto with *.
 apply TIF_morph; auto with *. }
assert (same_iso : forall a, a ∈ A -> eq_fun (TIF A F o a) (isof o a) (g (isof o) a)).
{red; intros.
 transitivity (isof o a x').
 apply isofm; auto with *.
 rewrite H1 in H0.
 apply isof_def; trivial. }
assert (iso1' : forall a, a ∈ A -> iso_fun (TIF A F o a) (TIF A G o a) (g (isof o) a)).
{intros a tya.
 generalize (iso1 _ tya); apply iso_fun_ext; auto with *. }
clear iso1.
split; intros.
*assert (iso1 := iso_fun_sym (iso1' a H0)).
 clear iso1'.
 apply iso_fun_inj with (TIF A F o a) (iso_inv (TIF A F o a) (g (isof o) a)); trivial.
 +apply iso_fun_sym.
  generalize (iso2 a H0); apply iso_fun_morph; auto with *.
  apply iso_funm with (1:=iso2 a H0); trivial.

 +rewrite <- TIF_mono_succ; auto.
  apply TIF_incl; auto.

*apply iso_fun_inj with (TIF A G o a) (g (isof o) a); auto.
 +apply iso_change_rhs with (G (TIF A G o) a); auto with *.
  symmetry; apply H; trivial.
 +rewrite <- TIF_mono_succ; auto.
  apply TIF_incl; auto.
Qed.

End IsoFamilyCorollary.


  Variable o : set.
  Variable oo : isOrd o.

  Lemma TIF_iso_recursor_hyps :
    recursor_hyps o (fun o => sigma A (fun a' => TIF A F o a'))
      (fun o f => forall a, a ∈ A -> iso_fun (TIF A F o a) (TIF A G o a) (fun x => cc_app f (couple a x)))
      (isoF g).
constructor; intros.
*do 2 red; intros; apply sigma_morph; auto with *.
 red; intros; apply TIF_morph; auto with *.

*red; intros.
 rewrite <- sigma_cont.
 2:do 3 red; intros; apply TIF_morph; auto with *.
 2:apply osucc_morph; trivial.
 apply sigma_ext; intros; auto with *.
 rewrite TIF_eq; auto with *.
 apply sup_morph; intros; auto with *.
 red; intros.
 rewrite <- TIF_mono_succ; eauto using isOrd_inv.
 apply TIF_morph; trivial.
 apply osucc_morph; trivial.

 (* iso *)
*generalize (H3 _ H4); apply iso_fun_ext; auto with *.
  do 2 red; intros. rewrite H5; reflexivity.
  apply TIF_morph; auto with *.
  apply TIF_morph; auto with *.

  red; intros.
  rewrite <- H6; apply H2.
  apply couple_intro_sigma; trivial.
  do 2 red; intros; apply TIF_morph; auto with *.

 (* Q continuity *)
*apply TIF_iso_cont with (f:=fun a0 x => cc_app f (couple a0 x)); auto.
 do 2 red; intros.
 rewrite H5; reflexivity.

 (* F morph *)
*do 3 red; intros.
 apply cc_lam_morph; intros.
  apply sigma_morph; auto with *.
  red; intros; apply TIF_morph; trivial.
  apply osucc_morph; trivial.

  red; intros.
  apply gm.
   do 2 red; intros.
   rewrite H0; rewrite H2; rewrite H3; reflexivity.

   apply fst_morph; trivial.

   apply snd_morph; trivial.

 (* Q typing *)
*split.
  apply is_cc_fun_lam; auto.

  intros.
  apply isog with (a:=a) in H2; trivial.
  2:apply TIF_morph; auto with *.
  2:apply TIF_morph; auto with *.
   revert H2; apply iso_fun_ext.
    do 2 red; intros. apply cc_app_morph;[reflexivity|].
    rewrite H2; reflexivity.

    symmetry; apply TIF_mono_succ; eauto using isOrd_inv.
    symmetry; apply TIF_mono_succ; eauto using isOrd_inv.

    red; intros.  
    unfold isoF; rewrite cc_beta_eq; auto.
     apply gm.
      do 2 red; intros; apply cc_app_morph; auto with *.
      apply couple_morph; trivial.

      symmetry; apply fst_def.

      rewrite snd_def; auto with *.

    apply couple_intro_sigma; trivial.
     do 2 red; intros; apply TIF_morph; auto with *.

     rewrite <- H4.
     rewrite TIF_mono_succ; auto.

   do 3 red; intros.
   rewrite H4, H5; reflexivity.

 (* irrel : *)
*red; intros.
 red; intros.
 destruct H1 as (oo0,(ofun,oiso)); destruct H2 as (oo',(o'fun,o'iso)).
 unfold isoF; rewrite cc_beta_eq; auto.
 assert (tyfx := fst_typ_sigma _ _ _ H4).
 rewrite cc_beta_eq; auto.
 +red in gext.
  apply gext with (X:=TIF A F o0); auto with *.
  ++apply TIF_morph; auto with *.
  ++do 3 red; intros; apply cc_app_morph; auto with *.
    apply couple_morph; trivial.
  ++do 3 red; intros; apply cc_app_morph; auto with *.
    apply couple_morph; trivial.
  ++red; intros.
    rewrite <- H5; apply H3.
    apply couple_intro_sigma; trivial.
    do 2 red; intros; apply TIF_morph; auto with *.
  ++apply snd_typ_sigma with (y:=fst x) in H4; [|reflexivity].
    revert H4; apply eq_elim.
    apply TIF_mono_succ; auto with *.

 +revert H4; apply sigma_mono; auto with *.
  {do 2 red; intros; apply TIF_morph; auto with *. }
  intros.
  transitivity (TIF A F (osucc o') x0).
  {apply TIF_mono; auto with *.
   red; intros.
   apply ole_lts; eauto using isOrd_inv.
   apply olts_le in H2; transitivity o0; trivial. }
  {red; intro; apply eq_elim.
   apply TIF_morph; auto with *. }
Qed.

  Lemma TIF_iso_recursor :
    recursor_spec o (fun o => sigma A (fun a' => TIF A F o a'))
      (fun o f => forall a, a ∈ A -> iso_fun (TIF A F o a) (TIF A G o a) (fun x => cc_app f (couple a x)))
      (isoF g)
      (REC (isoF g)).
apply REC_recursor_spec; trivial.
apply TIF_iso_recursor_hyps.    
Qed.
  
  Lemma TIF_iso_fun :
    (forall a, a ∈ A -> iso_fun (TIF A F o a) (TIF A G o a) (TIF_iso g o a)) /\
    (forall a x, a ∈ A -> x ∈ TIF A F o a -> TIF_iso g o a x == g (TIF_iso g o) a x) /\
    (forall a o' x, isOrd o' -> o' ⊆ o -> a ∈ A -> x ∈ TIF A F o' a ->
     TIF_iso g o' a x == TIF_iso g o a x).
split.
 intros a tya.
 unfold TIF_iso.
 revert a tya.
 apply rec_spec_typ with (1:=TIF_iso_recursor) (2:=oo); auto with *.

split.
 intros a x tya tyx.
 assert (couple a x ∈ sigma A (fun a' => TIF A F o a')).
  apply couple_intro_sigma; trivial.
  do 2 red; intros; apply TIF_morph; auto with *.
 unfold TIF_iso; rewrite rec_spec_eqn with (1:=TIF_iso_recursor) (2:=oo); auto with *.
 unfold isoF; rewrite cc_beta_eq; auto with *.
  apply gm.
   do 2 red; intros.
   apply cc_app_morph; auto with *.
   apply couple_morph; trivial.

   apply fst_def.

   apply snd_def.

 revert H; apply sigma_mono; auto with *.
  do 2 red; intros; apply TIF_morph; auto with *.

  intros.
  transitivity (TIF A F (osucc o) x0).
   apply TIF_mono; auto.
   red; intros; apply isOrd_trans with o; auto.

   red; intro; apply eq_elim.
   apply TIF_morph; auto with *.

 intros a o' x oo' ole aty xty.
 unfold TIF_iso.
 apply rec_spec_irr with (1:=TIF_iso_recursor); auto with *.
 apply couple_intro_sigma; trivial.
 do 2 red; intros; apply TIF_morph; auto with *.
Qed.

End TIF_iso.

Lemma TIF_iso_morph :
  Proper (eq_set==>((eq_set==>eq_set)==>eq_set==>eq_set)==>((eq_set==>eq_set==>eq_set)==>
          eq_set==>eq_set==>eq_set)==>eq_set==>eq_set==>eq_set==>eq_set)
    TIF_iso.
do 7 red; intros.
unfold TIF_iso.
apply cc_app_morph.
2:apply couple_morph; trivial.
apply REC_morph_gen; trivial.
do 2 red; intros.
apply cc_lam_ext.
 apply sigma_morph; auto.
 red; intros.
 apply TIF_morph_gen; trivial.
 apply osucc_morph; trivial.
red; intros.
apply H1.
 do 2 red; intros.
 apply cc_app_morph; trivial.
 apply couple_morph; trivial.

 apply fst_morph; trivial.
 apply snd_morph; trivial.
Qed.
