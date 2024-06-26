Require Import ZF ZFpairs ZFsum ZFrelations ZFord ZFfix ZFfixfun.
Require Import ZFstable ZFiso ZFind_w ZFspos.

(** Inductive families. Indexes are modelled as a constraint over an inductive
    type defined without considering the index values.
 *)

Require Import ZFind_wd.

Section InductiveFamily.

Variable Arg : set.

(** Given a function [f] that computes the index of any element of [X],
    [index(f)] shall compute the index of any element of [F(X)] it assumes
    the index information is stored within the data (not the case of non-uniform
    parameters...).
 *)
Record dpositive := mkDPositive {
  carrier :> positive;
  dpos_oper : (set -> set) -> set -> set;
  w3 : set -> set -> set;
  w4 : set -> set -> Prop
}.

Definition eqdpos (p1 p2:dpositive) :=
  eqpos p1 p2 /\
  (forall X X' a a', (eq_set==>eq_set)%signature X X' -> a==a' -> dpos_oper p1 X a == dpos_oper p2 X' a') /\
  (forall x x' i i', x==x' -> i==i' -> w3 p1 x i == w3 p2 x' i') /\
  (forall x x' i i', x==x' -> i==i' -> (w4 p1 x i <-> w4 p2 x' i')).

Instance eqdpos_sym : Symmetric eqdpos.
red; intros.
destruct H as (?&?&?&?); split;[|split;[|split]]; intros; symmetry; auto.
+apply H0; symmetry; trivial.
+ apply H1; symmetry; trivial.
+apply H2; symmetry; trivial.
Qed.
  
Instance eqdpos_trans : Transitive eqdpos.
red; intros.
destruct H as (?&?&?&?); destruct H0 as (?&?&?&?).
split;[|split;[|split]]; intros.
+transitivity y; trivial.
+transitivity (dpos_oper y X a); auto with *.
 apply H1; [|reflexivity].
 transitivity X'; auto with *.
+transitivity (w3 y x0 i); auto with *.
+transitivity (w4 y x0 i); auto with *.
Qed.

Instance eqdpos_morph : Proper (eqdpos==>eqdpos==>iff) eqdpos.
do 3 red; intros.
split; intros.
+transitivity x;[auto with *|].
 transitivity x0;[auto with *|trivial].
+transitivity y;[auto with *|].
 transitivity y0;[trivial|auto with *].
Qed.

Record isDPositive (p:dpositive) := {
  dpos_pos : isPositive p;
  dpm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) (dpos_oper p);
  dpmono : mono_fam Arg (dpos_oper p);
  w3m : morph2 (w3 p);
  w4m : Proper (eq_set==>eq_set==>iff) (w4 p);
  w3typ : forall x i, x ∈ w1 p -> i ∈ w2 p x -> w3 p x i ∈ Arg;
  dpm_iso : forall X a,
    ext_fun Arg X ->
    a ∈ Arg ->
    dpos_oper p X a == subset (pos_oper p (sup Arg X))
      (fun w => let w := wf p w in
       w4 p (fst w) a /\ forall i, i ∈ w2 p (fst w) -> cc_app (snd w) i ∈ X (w3 p (fst w) i))
}.

Definition dINDi p := TIF Arg (dpos_oper p).

Existing Instance dpm.
Hint Resolve dpmono : core.

Lemma dINDi_succ_eq : forall p o a,
  isDPositive p -> isOrd o -> a ∈ Arg -> dINDi p (osucc o) a == dpos_oper p (dINDi p o) a.
intros.
unfold dINDi.
apply TIF_mono_succ; auto with *.
Qed.

Lemma INDi_mono : forall p o o',
  isDPositive p -> isOrd o -> isOrd o' -> o ⊆ o' ->
  incl_fam Arg (dINDi p o) (dINDi p o').
intros.
red; intros.
assert (tm := TIF_mono); red in tm.
unfold dINDi.
apply tm; auto with *.
Qed.

Definition dIND (p:dpositive) := dINDi p (IND_clos_ord p).

Lemma dIND_eq : forall p a, isDPositive p -> a ∈ Arg -> dIND p a == dpos_oper p (dIND p) a.
unfold dIND; intros.
(*rewrite <- dINDi_succ_eq; trivial.
2:{unfold IND_clos_ord.
   apply W_o_o.
   apply dpos_pos; trivial. }
apply incl_eq.
+apply w3m.
auto with *.*)
unfold dINDi.
assert (oo : isOrd (IND_clos_ord p)).
 unfold IND_clos_ord.
 apply W_o_o.
 apply H.
(**)
rewrite TIF_eq; auto with *.
apply eq_set_ax; intros z.
rewrite sup_ax.
2:{do 2 red; intros.
   apply dpm; auto with *.
   red; intros.
   apply TIF_morph; trivial. }
split; intro.
+destruct H1.
 revert H2; apply (dpmono _ H); auto with *.
 *apply TIF_morph; reflexivity.
 *apply TIF_morph; reflexivity.
 *red; intros.
  apply TIF_incl; auto with *.
+rewrite (dpm_iso _ H) in H1; trivial.
 assert (H1' := subset_elim1 _ _ _ H1).
 admit.
Admitted. (* TODO *)

Lemma dINDi_dIND : forall p o,
  isDPositive p ->
  isOrd o ->
  forall a, a ∈ Arg ->
  dINDi p o a ⊆ dIND p a.
induction 2 using isOrd_ind; intros.
unfold dINDi.
rewrite TIF_eq; auto with *.
red; intros.
rewrite sup_ax in H4.
 destruct H4.
 rewrite dIND_eq; trivial.
 revert H5; apply H; auto.
  apply TIF_morph; reflexivity.

  unfold dIND, dINDi.
  do 2 red; intros; apply TIF_morph; auto with *.

  red; intros.
  apply H2; trivial.

 do 2 red; intros; apply dpm; auto with *.
 red; intros.
 apply TIF_morph; auto with *.
Qed.

(** Library of dependent positive operators *)

(** Constraint on the index: corresponds to the conclusion of the constructor *)
Definition dpos_inst i :=
  mkDPositive (pos_cst (singl empty)) (fun _ a => cond_set (i==a) (singl empty))
    (fun _ _ => empty) (fun _ a => i==a).

Lemma dpos_inst_morph : Proper (eq_set==>eqdpos) dpos_inst.
do 2 red; intros.
split;[|split;[|split]]; simpl; intros; auto with *.
+apply pos_cst_morph; reflexivity.
+apply cond_set_morph;[|reflexivity].
 rewrite H,H1; reflexivity.
+rewrite H,H1; reflexivity.
Qed.

Lemma isDPos_inst i : isDPositive (dpos_inst i).
constructor; simpl; intros.
 apply isPos_cst.

 do 4 red; intros.
 rewrite H0; reflexivity.

 do 2 red; intros.
 reflexivity.

 do 3 red; reflexivity.

 do 3 red; intros.
 rewrite H0; reflexivity.

 apply empty_ax in H0; contradiction.

 apply eq_set_ax; intros z.
 rewrite cond_set_ax; rewrite subset_ax.
 split; destruct 1; split; trivial.
  exists z; auto with *.
  split; intros; trivial.
  apply empty_ax in H3; contradiction.

  destruct H2 as (?,_,(?,_)); trivial.
Qed.

Definition dpos_cst A := mkDPositive (pos_cst A) (fun _ _ => A) (fun _ _ => empty) (fun _ _ => True).

Instance dpos_cst_morph : Proper (eq_set==>eqdpos) dpos_cst.
do 2 red; intros.
split;[|split;[|split]]; simpl; intros; auto with *.
apply pos_cst_morph; trivial.
Qed.

Lemma isDPos_cst A : isDPositive (dpos_cst A).
constructor; simpl; intros.
 apply isPos_cst.

 do 4 red; reflexivity.

 do 2 red; intros; reflexivity.

 do 3 red; reflexivity.

 do 3 red; reflexivity.

 apply empty_ax in H0; contradiction.

 apply eq_set_ax; intros z.
 rewrite subset_ax.
 split;[split|destruct 1]; trivial.
 exists z;[reflexivity|].
 split; intros; trivial.
 apply empty_ax in H2; contradiction.
Qed.

Definition dpos_rec j := mkDPositive pos_rec (fun X _ => X j) (fun _ _ => j) (fun _ _ => True).

 Instance dpos_rec_morph : Proper (eq_set==>eqdpos) dpos_rec.
do 2 red; intros.
split;[|split;[|split]]; simpl; intros; auto with *.
apply pos_rec_morph.
Qed.

Lemma isDPos_rec j : j ∈ Arg -> isDPositive (dpos_rec j).
constructor; simpl; intros; trivial.
 apply isPos_rec.

 do 4 red; intros.
 apply H0; reflexivity.

 do 2 red; intros.
 apply H2; trivial.

 do 3 red; reflexivity.

 do 3 red; reflexivity.

 apply subset_ext; intros.
  destruct H3.
  rewrite sup_ax in H2; trivial.
  destruct H2 as (b,?,?).
  assert (h := H4 _ (singl_intro empty)).
  unfold trad_reccall,comp_iso in h.
  rewrite snd_def in h; rewrite cc_beta_eq in h; trivial.
  apply singl_intro.

  rewrite sup_ax; trivial.
  exists j; trivial.

  exists x; [reflexivity|].
  split;[trivial|intros].
  unfold trad_reccall, comp_iso.
  rewrite snd_def; rewrite cc_beta_eq; trivial.
Qed.

Definition dpos_sum (F G:dpositive) :=
  mkDPositive (pos_sum F G)
    (fun X a => sum (dpos_oper F X a) (dpos_oper G X a))
    (fun x i => sum_case (fun x1 => w3 F x1 i) (fun x2 => w3 G x2 i) x)
    (fun x i => (forall x1, x == inl x1 -> w4 F x1 i) /\
                (forall x2, x == inr x2 -> w4 G x2 i)).

Lemma sum_isomap_inl f g x a :
  (forall a', a==a' -> f a == f a') ->
  x == inl a -> sum_isomap f g x == inl (f a).
intros.
unfold sum_isomap.
rewrite sum_case_inl0; [|eauto].
rewrite <- (H (dest_sum x));[reflexivity|].
rewrite H0, dest_sum_inl; reflexivity.
Qed.
Lemma sum_isomap_inr f g x b :
  (forall b', b==b' -> g b == g b') ->
  x == inr b -> sum_isomap f g x == inr (g b).
intros.
unfold sum_isomap.
rewrite sum_case_inr0; [|eauto].
rewrite <- (H (dest_sum x));[reflexivity|].
rewrite H0, dest_sum_inr; reflexivity.
Qed.

Lemma sum_sigma_iso_inl x p :
  x == inl p -> sum_sigma_iso x == couple (inl (fst p)) (snd p).
unfold sum_sigma_iso; intros.
rewrite sum_case_inl0; [|eauto].
rewrite H, dest_sum_inl; reflexivity.
Qed.
Lemma sum_sigma_iso_inr x p :
  x == inr p -> sum_sigma_iso x == couple (inr (fst p)) (snd p).
unfold sum_sigma_iso; intros.
rewrite sum_case_inr0; [|eauto].
rewrite H, dest_sum_inr; reflexivity.
Qed.
Lemma trad_sum_inl f g p x :
  (forall p', p == p' -> f p == f p') ->
  x == inl p ->
  trad_sum f g x == couple (inl (fst (f p))) (snd (f p)). 
intros.
unfold trad_sum, comp_iso.  
rewrite sum_sigma_iso_inl with (p:=f p);[reflexivity|].
apply sum_isomap_inl; trivial.
Qed.
Lemma trad_sum_inr f g p x :
  (forall p', p == p' -> g p == g p') ->
  x == inr p ->
  trad_sum f g x == couple (inr (fst (g p))) (snd (g p)). 
intros.
unfold trad_sum, comp_iso.  
rewrite sum_sigma_iso_inr with (p:=g p);[reflexivity|].
apply sum_isomap_inr; trivial.
Qed.


Lemma isDPos_sum F G :
  isDPositive F ->
  isDPositive G ->
  isDPositive (dpos_sum F G).
intros Fdp Gdp.
destruct (Fdp) as (Fp,Fdm,Fdmo,F3m,F4m,Fty,Fdep).
destruct (Gdp) as (Gp,Gdm,Gdmo,G3m,G4m,Gty,Gdep).
constructor; simpl; intros.
*apply isPos_sum; trivial.

*do 4 red; intros.
 apply sum_morph.
  apply Fdm; trivial.
  apply Gdm; trivial.

*do 2 red; intros.
 apply sum_mono.
  apply Fdmo; trivial.
  apply Gdmo; trivial.

*do 3 red; intros.
 apply sum_case_morph; trivial.
  red; intros.
  apply F3m; trivial.

  red; intros.
  apply G3m; trivial.

*do 3 red; intros.
 apply and_iff_morphism.
  apply fa_morph; intros x1.
  rewrite <- H.
  apply fa_morph; intros _.
  apply F4m; auto with *.

  apply fa_morph; intros x2.
  rewrite <- H.
  apply fa_morph; intros _.
  apply G4m; auto with *.

*apply sum_case_ind0 with (2:=H); intros.
  do 2 red; intros.
  rewrite H1; reflexivity.

  rewrite H2; rewrite dest_sum_inl.
  apply Fty; trivial.
  assert (F2m := w2m _ Fp).
  rewrite sum_case_inl0 in H0; eauto.
  revert H0; apply eq_elim; symmetry; apply F2m; trivial.
  rewrite H2; rewrite dest_sum_inl; reflexivity.

  rewrite H2; rewrite dest_sum_inr.
  apply Gty; trivial.
  assert (G2m := w2m _ Gp).
  rewrite sum_case_inr0 in H0; eauto.
  revert H0; apply eq_elim; symmetry; apply G2m; trivial.
  rewrite H2; rewrite dest_sum_inr; reflexivity.

*apply eq_set_ax; intros z.
 rewrite subset_ax.
 split; intro.
 {split.
  +revert H1; apply sum_mono.
   -rewrite dpm_iso; trivial.
    intros w h; apply subset_elim1 in h; trivial.
   -rewrite dpm_iso; trivial.
    intros w h; apply subset_elim1 in h; trivial.
  +exists z;[reflexivity|].
   apply sum_ind with (3:=H1); intros.
   {rewrite Fdep in H2; trivial.
    destruct subset_elim2 with (1:=H2).
    simpl in H5.
    destruct H5.
    split.
     split; intros.
      revert H5; apply F4m; auto with *.
      rewrite H4 in H3.
      rewrite trad_sum_inl with (2:=H3), fst_def in H7.
      2:apply (w_iso _ Fp x0).
      apply inl_inj in H7; symmetry; assumption.

      rewrite trad_sum_inl with (2:=H3), fst_def in H7.
      2:apply (w_iso _ Fp x0).
      apply discr_sum in H7; contradiction.

     intros.
     rewrite H4 in H3.
     assert (eqt : trad_sum (wf F) (wf G) z == couple (inl (fst (wf F x0))) (snd (wf F x0))).
     {rewrite trad_sum_inl with (2:=H3).
      2:apply (w_iso _ Fp x0).
      reflexivity. }
     rewrite sum_case_inl0 in H7.
     2:{exists (fst (wf F x0)).
        rewrite eqt, fst_def; reflexivity. }
     assert (tyi : i ∈ w2 F (fst (wf F x0))).
     {apply eq_elim with (2:=H7).
      apply (w2m _ Fp).
      rewrite eqt, fst_def, dest_sum_inl.
      reflexivity. }
     specialize H6 with (1:=tyi).
     revert H6; apply in_set_morph.
     rewrite eqt, snd_def; reflexivity.
     symmetry; apply H.
    +apply Fty; trivial.
     rewrite H3 in H1.
     apply sum_inv_l in H1.
     assert (x0 ∈ pos_oper F (sup Arg X)).
     {rewrite Fdep in H1; auto.
        apply subset_elim1 in H1; trivial. }
     apply (iso_typ (w_iso _ Fp (sup Arg X))) in H6.
     apply fst_typ_sigma in H6; trivial.
    +rewrite sum_case_inl0.
     apply w3m; [trivial| |reflexivity].
     rewrite eqt, fst_def, dest_sum_inl; reflexivity.
     exists (fst (wf F x0)).
     rewrite eqt, fst_def; reflexivity. }
   {rewrite Gdep in H2; trivial.
    destruct subset_elim2 with (1:=H2).
    simpl in H5.
    destruct H5.
    split.
     split; intros.
      rewrite trad_sum_inr with (2:=H3), fst_def in H7.
      2:apply (w_iso _ Gp y).
      symmetry in H7; apply discr_sum in H7; contradiction.

     revert H5; apply G4m; auto with *.
     rewrite H4 in H3.
     rewrite trad_sum_inr with (2:=H3), fst_def in H7.
     2:apply (w_iso _ Gp y).
     apply inr_inj in H7; symmetry; assumption.

     intros.
     rewrite H4 in H3.
     assert (eqt : trad_sum (wf F) (wf G) z == couple (inr (fst (wf G x))) (snd (wf G x))).
     {rewrite trad_sum_inr with (2:=H3).
      2:apply (w_iso _ Gp y).
      reflexivity. }
     rewrite sum_case_inr0 in H7.
     2:{exists (fst (wf G x)).
        rewrite eqt, fst_def; reflexivity. }
     assert (tyi : i ∈ w2 G (fst (wf G x))).
     {apply eq_elim with (2:=H7).
      apply (w2m _ Gp).
      rewrite eqt, fst_def, dest_sum_inr.
      reflexivity. }
     specialize H6 with (1:=tyi).
     revert H6; apply in_set_morph.
     rewrite eqt, snd_def; reflexivity.
     symmetry; apply H.
    +apply Gty; trivial.
     rewrite H3 in H1.
     apply sum_inv_r in H1.
     assert (x ∈ pos_oper G (sup Arg X)).
     {rewrite Gdep in H1; auto.
        apply subset_elim1 in H1; trivial. }
     apply (iso_typ (w_iso _ Gp (sup Arg X))) in H6.
     apply fst_typ_sigma in H6; trivial.
    +rewrite sum_case_inr0.
     apply w3m; [trivial| |reflexivity].
     rewrite eqt, fst_def, dest_sum_inr; reflexivity.
     exists (fst (wf G x)).
     rewrite eqt, fst_def; reflexivity. } }
 {admit. }
Admitted. (* TODO *)


Definition dpos_consrec (F G:dpositive) :=
  mkDPositive (pos_consrec F G)
    (fun X a => prodcart (dpos_oper F X a) (dpos_oper G X a))
    (fun x => sum_case (w3 F (fst x)) (w3 G (snd x)))
    (fun x i => w4 F (fst x) i /\ w4 G (snd x) i).

Instance dpos_consrec_morph : Proper (eqdpos==>eqdpos==>eqdpos) dpos_consrec.
do 3 red; intros.
unfold dpos_consrec.
split;[|split;[|split]]; simpl; intros.
+apply pos_consrec_morph; [apply H|apply H0].
+apply prodcart_morph.
  apply H; trivial.
  apply H0; trivial.
+apply sum_case_morph; trivial.
  red; intros; apply H; trivial.  
  apply fst_morph; trivial.
  red; intros; apply H0; trivial.  
  apply snd_morph; trivial.
+apply and_iff_morphism.
 apply H; trivial.
  apply fst_morph; trivial.
  red; intros; apply H0; trivial.  
  apply snd_morph; trivial.
Qed.


Lemma isDPos_consrec F G :
  isDPositive F ->
  isDPositive G ->
  isDPositive (dpos_consrec F G).
intros (Fp,Fdm,Fdmo,F3m,F4m,Fty,?) (Gp,Gdm,Gdmo,G3m,G4m,Gty,?).
constructor; simpl; intros.
 apply isPos_consrec; trivial.

 do 4 red; intros.
 apply prodcart_morph.
  apply Fdm; trivial.
  apply Gdm; trivial.

 do 2 red; intros.
 apply prodcart_mono.
  apply Fdmo; trivial.
  apply Gdmo; trivial.

 do 3 red; intros.
 apply sum_case_morph; trivial.
  red; intros.
  apply F3m; trivial.
  apply fst_morph; trivial.

  red; intros.
  apply G3m; trivial.
  apply snd_morph; trivial.

 do 3 red; intros.
 apply and_iff_morphism.
  apply F4m; trivial.
  apply fst_morph; trivial.

  apply G4m; trivial.
  apply snd_morph; trivial.

 apply sum_case_ind with (6:=H0); intros.
  do 2 red; intros.
  rewrite H1; reflexivity.

  apply F3m; reflexivity.

  apply G3m; reflexivity.

  apply Fty; trivial.
  apply fst_typ in H; trivial.

  apply Gty; trivial.
  apply snd_typ in H; trivial.

 admit.
Admitted. (* TODO *)

Definition dpos_norec (A:set) (F:set->dpositive) :=
  mkDPositive (pos_norec A F)
    (fun X a => sigma A (fun y => dpos_oper (F y) X a))
    (fun x i => w3 (F (fst x)) (snd x) i)
    (fun x i => w4 (F (fst x)) (snd x) i).

Lemma isDPos_norec A F :
  Proper (eq_set ==> eqdpos) F ->
  (forall x, x ∈ A -> isDPositive (F x)) ->
  isDPositive (dpos_norec A F).
constructor; simpl; intros.
 apply isPos_consnonrec.
  do 2 red; intros.
  apply H in H1.
  apply H1.

  intros.
  apply H0; trivial.

 do 4 red; intros.
 apply sigma_morph; auto with *.
 red; intros.
 apply H; trivial.

 do 2 red; intros.
 apply sigma_mono; auto with *.
  do 2 red; intros. 
  apply H in H6.
  apply H6; auto with *.

  do 2 red; intros. 
  apply H in H6.
  apply H6; auto with *.

  intros.
  transitivity (dpos_oper (F x) Y a).
   apply H0; trivial.

   red; intro; apply eq_elim.
   apply (H _ _ H6); auto with *.

 do 3 red; intros.
 assert (ef := fst_morph _ _ H1).
 assert (es := snd_morph _ _ H1).
 apply H in ef.
 destruct ef as (?,(?,(?,?))).
 apply H5; trivial.

 do 3 red; intros.
 assert (ef := fst_morph _ _ H1).
 assert (es := snd_morph _ _ H1).
 apply H in ef.
 destruct ef as (?,(?,(?,?))).
 apply H6; trivial.

 assert (fty := fst_typ_sigma _ _ _ H1).
 apply snd_typ_sigma with (y:=fst x) in H1; auto with *.
  apply H0; trivial.

  do 2 red; intros.
  apply H in H4.
  apply H4.

 admit.
Admitted. (* TODO *)

Definition dpos_param (A:set) (F:set->dpositive) :=
  mkDPositive (pos_param A F)
    (fun X a => cc_prod A (fun y => dpos_oper (F y) X a))
    (fun x i => w3 (F (fst i)) (cc_app x (fst i)) (snd i))
    (fun x i => forall k, k ∈ A -> w4 (F k) (cc_app x k) i).

Lemma isDPos_param A F :
  Proper (eq_set ==> eqdpos) F ->
  (forall x, x ∈ A -> isDPositive (F x)) ->
  isDPositive (dpos_param A F).
constructor; simpl; intros.
 apply isPos_param.
  do 2 red; intros.
  apply H in H1.
  apply H1.

  intros.
  apply H0; trivial.

 do 4 red; intros.
 apply cc_prod_ext; auto with *.
 red; intros.
 apply H; trivial.

 do 2 red; intros.
 apply cc_prod_covariant; intros; auto with *.
  do 2 red; intros. 
  apply H in H6.
  apply H6; auto with *.

  apply H0; trivial.

 do 3 red; intros.
 assert (ef := fst_morph _ _ H2).
 assert (es := snd_morph _ _ H2).
 apply H in ef.
 destruct ef as (?,(?,(?,?))).
 apply H5; trivial.
 apply cc_app_morph; trivial.
 apply fst_morph; trivial.

 do 3 red; intros.
 apply fa_morph; intros k.
 apply fa_morph; intros kty.
 apply H0; trivial.
 rewrite H1; reflexivity.

 assert (fty := fst_typ_sigma _ _ _ H2).
 apply snd_typ_sigma with (y:=fst i) in H2; auto with *.
  apply H0; trivial.
  apply cc_prod_elim with (1:=H1); trivial.

  do 2 red; intros.
  apply H; trivial.
  rewrite H4; reflexivity.

 admit.
Admitted. (* TODO *)


End InductiveFamily.


Module Wd.

Section Wd.
(** Parameters of W-types *)
Variable A : set.
Variable B : set -> set.
Hypothesis Bext : ext_fun A B.

(** Index type *)
Variable Arg : set.

(** Constraints on the subterms *)
Hypothesis f : set -> set -> set.
Hypothesis fm : morph2 f.
Hypothesis ftyp : forall x i,
  x ∈ A -> i ∈ B x -> f x i ∈ Arg.

(** Instance introduced by the constructors *)
Hypothesis g : set -> set.
Hypothesis gm : morph1 g.

Definition Wdp : dpositive :=
  dpos_norec A (fun x => dpos_consrec (dpos_param (B x) (fun i => dpos_rec (f x i))) (dpos_inst (g x))).

Definition Wsup x h := couple x (couple (cc_lam (B x) h) empty).

Lemma sup_typ X x h :
  morph1 X ->
  morph1 h ->
  x ∈ A ->
  (forall i, i ∈ B x -> h i ∈ X (f x i)) ->
  Wsup x h ∈ dpos_oper Wdp X (g x).
simpl; intros.
apply couple_intro_sigma; trivial.
 do 2 red; intros.
 apply prodcart_morph.
  apply cc_prod_ext; auto.
  red; intros; apply H. 
  apply fm; auto.
 apply cond_set_morph; auto with *.
 rewrite H4; reflexivity.

 apply couple_intro.
  apply cc_prod_intro; intros; auto with *.
  do 2 red; intros; apply H; apply fm; auto with *. 

  rewrite cond_set_ax; split.
   apply singl_intro.
   reflexivity.
Qed.

End Wd.
End Wd.
