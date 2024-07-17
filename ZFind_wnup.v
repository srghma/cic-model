Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFord ZFfix ZFstable.
Require Import ZFgrothendieck.
Require Import ZFlist ZFfixfun.
Require Import ZFiso.
Require Import ZFlimit.
Require Import ZFwsimul ZFencode.

Existing Instance TIF_morph.

(** A dependent version of ZFind_w: Arg is the type of indexes
   This should support non-uniform parameters.
 *)
Require ZFind_w.
Module W0 := ZFind_w.

Section W_theory.

(** We want to model the following inductive type with non-uniform parameter [a]:
[[
Inductive Wd (a:Arg) :=
| C : forall (x:A a), (forall (i:B a x), Wd (f a x i)) -> Wd a.
]]
*)

Variable Arg : set.
Variable A : set -> set.
Variable B : set -> set -> set.
Variable f : set -> set -> set -> set.
Hypothesis Am : morph1 A.
Hypothesis Bm : morph2 B.
Hypothesis fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) f.
Hypothesis ftyp : forall a x y,
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  f a x y ∈ Arg.


(** The intended type operator: parameter is not part of the data-structure *)

Definition W_Fd (X:set->set) a :=
  Σ x ∈ A a, Π y ∈ B a x, X (f a x y).

Definition Wi o a := TIF Arg W_Fd o a.

Instance Wi_morph : morph2 Wi.
unfold Wi; apply TIF_morph.
Qed.

Instance W_Fd_morph : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) W_Fd.
unfold W_Fd; do 3 red; intros.
apply sigma_morph; auto.
red; intros.
apply cc_prod_morph.
 apply Bm; auto.

 red; intros; apply H; apply fm; trivial.
Qed.


Lemma W_Fd_mono : mono_fam Arg W_Fd.
do 2 red; intros.
unfold W_Fd.
apply sigma_mono; intros; auto with *.
 do 2 red; intros; apply cc_prod_morph;[apply Bm|red; intros;apply H; apply fm]; auto with *.
 do 2 red; intros; apply cc_prod_morph;[apply Bm|red; intros;apply H0; apply fm]; auto with *.

 apply cc_prod_covariant; auto with *.
  do 2 red; intros; apply H0; apply fm; auto with *.

  apply Bm; auto with *.

  intros.
  rewrite <- H4.
  auto.
Qed.
Hint Resolve W_Fd_mono : core.

Lemma W_Fd_eta w X a :
  morph1 X ->
  w ∈ W_Fd X a ->
  w == couple (fst w) (cc_lam (B a (fst w)) (fun i => cc_app (snd w) i)).
intros.
transitivity (couple (fst w) (snd w)).
 apply surj_pair with (1:=subset_elim1 _ _ _ H0).

 apply couple_morph;[reflexivity|].
 apply snd_typ_sigma with (y:=fst w) in H0; auto with *.
  apply cc_eta_eq with (1:=H0).

  do 2 red; intros.
  apply cc_prod_ext.
   apply Bm; auto with *.

   red; intros; apply H; apply fm; auto with *.
Qed.

Lemma W_Fd_intro X x x' a a' g :
  morph1 X ->
  a ∈ Arg ->
  a == a' ->
  x ∈ A a' ->
  x == x' ->
  ext_fun (B a x') g ->
  (forall i, i ∈ B a x' -> g i ∈ X (f a x' i)) ->
  couple x (cc_lam (B a x') g) ∈ W_Fd X a'.
intros.
apply couple_intro_sigma; trivial.
 do 2 red; intros.
 apply cc_prod_ext.
  apply Bm; auto with *.

  red; intros.
  apply H; apply fm; auto with *.

 apply cc_prod_intro'; intros; auto.
  do 2 red; intros; apply H; apply fm; auto with *.
  apply Bm; auto with *.
  rewrite <- H1; rewrite H3; auto.
Qed.

Lemma W_Fd_elim X a w :
  morph1 X ->
  w ∈ W_Fd X a ->
  w == couple (fst w) (snd w) /\
  fst w ∈ A a /\
  (forall i, i ∈ B a (fst w) -> cc_app (snd w) i ∈ X (f a (fst w) i)).
intros.
apply sigma_elim in H0.
 destruct H0 as (?&?&?).
 split; trivial.
 split; trivial.
 intros.
 apply cc_prod_elim with (1:=H2); trivial.

 do 2 red; intros.
 apply cc_prod_ext.
  apply Bm; auto with *.

  red; intros.
  apply H; apply fm; auto with *.
Qed.

Definition W_Fd_map g a w :=
  couple (fst w) (λ i ∈ B a (fst w), g (f a (fst w) i) (cc_app (snd w) i)).

Instance W_Fd_map_morph :
  Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set==>eq_set) W_Fd_map.
do 5 red; intros.
unfold W_Fd_map.
apply couple_morph.
 apply fst_morph; trivial.
apply cc_lam_morph.
 apply Bm; trivial.
 apply fst_morph; trivial.

 red; intros.
 apply H.
  apply fm; trivial.
  apply fst_morph; trivial.

  apply cc_app_morph; trivial.
  apply snd_morph; trivial.
Qed.

Lemma W_Fd_map_eq X g a w :
  morph1 X ->
  morph2 g ->
  a ∈ Arg ->
  w ∈ W_Fd X a ->
  fst (W_Fd_map g a w) == fst w /\
  (forall i, i ∈ B a (fst w) -> cc_app (snd (W_Fd_map g a w)) i == g (f a (fst w) i)(cc_app (snd w) i)).
intros.
unfold W_Fd_map.
split; intros.
 apply fst_def.

 rewrite snd_def.
 rewrite cc_beta_eq; auto with *.
 do 2 red; intros.
 rewrite <- H5; reflexivity.
Qed.

Lemma W_Fd_map_typ X Y g :
  morph1 X ->
  morph1 Y ->
  morph2 g ->
  (forall a x, a ∈ Arg -> x ∈ X a -> g a x ∈ Y a) ->
  forall a w, a ∈ Arg ->
  w ∈ W_Fd X a ->
  W_Fd_map g a w ∈ W_Fd Y a.
intros Xm Ym gm gty a w aty wty.
apply W_Fd_elim in wty; trivial.
destruct wty as (eta & w1 & w2).
apply W_Fd_intro; auto with *.
do 2 red; intros.
rewrite <- H0; reflexivity.
Qed.

Lemma W_Fd_map_inj X g a w w' :
  morph1 X ->
  morph2 g ->
  (forall a x x', a ∈ Arg -> x ∈ X a -> x' ∈ X a -> g a x == g a x' -> x == x') ->
  a ∈ Arg ->
  w ∈ W_Fd X a ->
  w' ∈ W_Fd X a ->
  W_Fd_map g a w == W_Fd_map g a w' ->
  w == w'.
intros Xm gm ginj aty wty wty' eqw.
destruct W_Fd_map_eq with (4:=wty) (g:=g) as (wm1,wm2); trivial.
destruct W_Fd_map_eq with (4:=wty') (g:=g) as (wm1',wm2'); trivial.
assert (eqw1 : fst w == fst w').
 rewrite <- wm1, <- wm1'.
 rewrite eqw; reflexivity.
apply sigma_elim in wty.
destruct wty as (e & w1 & w2).
apply sigma_elim in wty'.
destruct wty' as (e' & w1' & w2').
rewrite e,e'.
rewrite cc_eta_eq with (1:=w2).
rewrite cc_eta_eq with (1:=w2').
apply couple_morph; trivial.
apply cc_lam_ext; auto.
 apply Bm; auto with *.
red; intros.
apply ginj with (f a (fst w) x); auto.
 apply cc_prod_elim with (1:=w2); trivial.

 rewrite <- H0, eqw1.
 apply cc_prod_elim with (1:=w2'); trivial.
 rewrite <- eqw1; trivial.

 rewrite <- wm2; trivial.
 rewrite <- H0, eqw1.
 rewrite <- wm2'; trivial.
 rewrite eqw; reflexivity.
 rewrite <- eqw1; trivial.

do 2 red; intros.
apply cc_prod_ext.
 apply Bm; auto with *.

 red; intros.
 apply Xm; apply fm; auto with *.
do 2 red; intros.
apply cc_prod_ext.
 apply Bm; auto with *.

 red; intros.
 apply Xm; apply fm; auto with *.
Qed.

Lemma W_Fd_map_surj X Y g :
  morph1 X ->
  morph1 Y ->
  morph2 g ->
  (forall a, a ∈ Arg -> iso_fun (X a) (Y a) (g a)) ->
  forall a w', a ∈ Arg ->
  w' ∈ W_Fd Y a ->
  exists2 w, w ∈ W_Fd X a & W_Fd_map g a w == w'.
intros Xm Ym gm giso a w' aty wty'.
destruct W_Fd_elim with (2:=wty') as (etaw' & w1' & w2'); trivial.
exists (couple (fst w')
        (λ i ∈ B a (fst w'),
         union (subset (X (f a (fst w') i)) (fun x => cc_app (snd w') i == g (f a (fst w') i) x)))).
 apply W_Fd_intro; auto with *.
   do 2 red; intros.
   apply union_morph; apply subset_morph.
    rewrite H0; reflexivity.
    red; intros.
    rewrite H0; reflexivity.

  intros.
  assert (iso' := giso (f a (fst w') i) (ftyp _ _ _ aty w1' H)).
  destruct (iso_surj iso') with (y:=cc_app (snd w') i); auto.
  rewrite union_subset_singl with (y:=x) (y':=x); auto with *.
  intros.
  rewrite H4 in H5.
  apply (iso_inj iso') in H5; auto.

 apply transitivity with (2:=symmetry etaw').
 unfold W_Fd_map; apply couple_morph.
  rewrite fst_def; reflexivity.

  destruct sigma_elim with (2:=wty') as (_ & _ & w2).
do 2 red; intros.
apply cc_prod_ext.
 apply Bm; auto with *.

 red; intros.
 apply Ym; apply fm; auto with *.

  symmetry.
  rewrite cc_eta_eq with (1:=w2).
  apply cc_lam_ext.
   rewrite fst_def; reflexivity.
  red; intros.
  rewrite H0 in H|-*. clear x H0.
  rewrite fst_def, snd_def.
  rewrite cc_beta_eq; trivial.
   assert (iso' := giso (f a (fst w') x') (ftyp _ _ _ aty w1' H)).
   destruct (iso_surj iso') with (y:=cc_app (snd w') x'); auto.
   rewrite union_subset_singl with (y:=x) (y':=x); auto with *.
   intros.
   rewrite H4 in H5.
   apply (iso_inj iso') in H5; auto.

   do 2 red; intros.
   apply union_morph; apply subset_morph.
    rewrite H1; reflexivity.
    red; intros.
    rewrite H1; reflexivity.
Qed.

Lemma W_Fd_map_iso X Y g :
  morph1 X ->
  morph1 Y ->
  morph2 g ->
  (forall a, a ∈ Arg -> iso_fun (X a) (Y a) (g a)) ->
  forall a, a ∈ Arg -> iso_fun (W_Fd X a) (W_Fd Y a) (W_Fd_map g a).
intros.
split; intros.
 do 2 red; intros.
 apply W_Fd_map_morph; auto with *.

 red; intros.
 eapply W_Fd_map_typ with (X:=X); auto.
 intros.
 apply (iso_typ (H2 _ H5)); trivial.

 apply W_Fd_map_inj with (5:=H4) (6:=H5) in H6; auto.
 intros.
 apply (iso_inj (H2 _ H7)); trivial.

 eapply W_Fd_map_surj with (6:=H4); auto.
Qed.

(**************************************************)

(** The intermediate W-type: the parameter is turned into a constructor argument that
    we later on constrain (like indexes of inductive families)
    Arg appears in the data, so if it is big, the resulting inductive type is big.
 *)

Let A' := sigma Arg A.
Let B' a' := B (fst a') (snd a').
Instance B'_morph : morph1 B'.
do 2 red; intros; apply Bm; [apply fst_morph|apply snd_morph]; trivial.
Qed.
Hint Resolve B'_morph : core.
Let B'ext : ext_fun A' B'.
auto with *.
Qed.

Lemma A'_intro a x :
  a ∈ Arg ->
  x ∈ A a ->
  couple a x ∈ A'.
intros; apply couple_intro_sigma; auto.
Qed.

Lemma A'_elim x :
  x ∈ A' -> fst x ∈ Arg /\ snd x ∈ A (fst x) /\ x == couple (fst x) (snd x).
intros.
assert (eqx := surj_pair _ _ _ (subset_elim1 _ _ _ H)).
specialize fst_typ_sigma with (1:=H); intros.
apply snd_typ_sigma with (y:=fst x) in H; auto with *.
Qed.

(** [instance a w] means tree [w] corresponds to the member of the family with
    index value [a]:
    - the Arg component of A' must be [a]
    - the condition is hereditary
 *)
Inductive instance a w : Prop :=
| I_node :
    a == fst (fst w) ->
    (forall i, i ∈ B' (fst w) -> instance (f a (snd (fst w)) i) (cc_app (snd w) i)) ->
    instance a w.

Instance instance_morph : Proper (eq_set==>eq_set==>iff) instance.
apply morph_impl_iff2; auto with *.
do 4 red; intros.
revert y y0 H H0.
induction H1; intros.
constructor; intros.
 rewrite <- H3; rewrite <- H2; trivial.

 apply H1 with i.
  rewrite H3; trivial.
  rewrite H3; rewrite H2; reflexivity.
  rewrite H3; reflexivity.
Qed.

(** We show there is an iso between the intended type (Wi)
   and the encoding (W0.W A' B'):
   tr (f:X->Y) : W0.W_F A' B' X --> U_a (W_Fd (A a) (B a) Y) 
   See also more refined result below.
 *)
Definition tr f w :=
  couple (snd (fst w)) (λ i ∈ B'(fst w), f (cc_app (snd w) i)).

Instance tr_morph : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) tr.
do 3 red; intros.
unfold tr.
apply couple_morph.
 rewrite H0; reflexivity.

 apply cc_lam_morph.
  rewrite H0; reflexivity.

  red; intros.
  apply H; rewrite H0; rewrite H1; reflexivity.
Qed.

Let tr_cont o z :
 isOrd o ->
 (z ∈ TI (W0.W_F A' B') o <->
  (exists2 o', o' ∈ o & z ∈ TI (W0.W_F A' B') (osucc o'))).
intros.
rewrite TI_mono_eq; auto.
rewrite sup_ax; auto with *.
do 2 red; intros; apply TI_morph.
rewrite H1; reflexivity.
Qed.

Let tr_ext o g g' :
 isOrd o ->
 eq_fun (TI (W0.W_F A' B') o) g g' ->
 eq_fun (TI (W0.W_F A' B') (osucc o)) (tr g) (tr g').
red; intros.
unfold tr.
apply couple_morph.
 rewrite H2; reflexivity.

 unfold B'; apply cc_lam_ext.
  rewrite H2; reflexivity.

  red; intros.
  apply H0.
   rewrite TI_mono_succ in H1; auto.
   apply W0.W_F_elim in H1; auto.
   destruct H1 as (_,(?,_)); auto.

   rewrite H2; rewrite H4; reflexivity.
Qed.

(** Isomorphism result for the step function.
    - the parameter constraint on subterms (of type X) is modelled by P *)
Lemma tr_iso a X Y P g :
  Proper (eq_set==>eq_set==>iff) P ->
  morph1 Y ->
  a ∈ Arg ->
  (forall a, a ∈ Arg -> iso_fun (subset X (P a)) (Y a) g) ->
  let Wd := subset (W0.W_F A' B' X)
     (fun w => fst (fst w) == a /\
        forall i, i ∈ B a (snd (fst w)) -> P (f a (snd (fst w)) i) (cc_app (snd w) i)) in
  iso_fun Wd (W_Fd Y a) (tr g).
intros Pm; intros.
unfold tr.
assert (gm := iso_funm (H1 _ H0)).
(*assert (gext : forall x x', x ∈ Wd -> x == x' ->
             eq_fun (B' (fst x)) (fun i => g (cc_app (snd x) i)) (fun i => g (cc_app (snd x') i))).
 do 2 red; intros.
 unfold Wd in H2; rewrite subset_ax in H2; destruct H2 as (?,(w,?,(?,?))).
 apply W0.W_F_elim in H2; auto.
 destruct H2 as (?,(?,_)).
 apply A'_elim in H2; destruct H2 as (?,(?,_)).
 apply (iso_funm (H1 _ (ftyp _ _ _ H2 H10 H4))).
 rewrite H3; rewrite H5; reflexivity.*)
constructor; intros.
 do 2 red; intros.
 apply couple_morph.
  rewrite H2; reflexivity.

  apply cc_lam_ext.
   rewrite H2; reflexivity.

   red; intros.
   rewrite H2; rewrite H4; reflexivity.

 (* typ *)
 red; intros.
 assert (h:=H2); unfold Wd in h; rewrite subset_ax in h; destruct h.
 destruct H4 as (x0,eqx0,(inst,insts)); rewrite <- eqx0 in inst.
 apply W0.W_F_elim in H3; auto.
 destruct H3 as (ty1,(ty2,eqx)).
 apply A'_elim in ty1; destruct ty1 as (tya,(tyx,eqy)).
 apply W_Fd_intro; intros; auto with *.
  rewrite <- inst; trivial.

  do 2 red; intros.
  rewrite H4; reflexivity.

  specialize ty2 with (1:=H3).
  apply (iso_typ (H1 _ (ftyp _ _ _ tya tyx H3))).
  apply subset_intro; auto.
  rewrite inst in H3,tyx|-*.
  rewrite eqx0.
  apply insts; rewrite <- eqx0; auto.

 (* inj *)
 assert (h:=H2); unfold Wd in h; rewrite subset_ax in h; destruct h.
 destruct H6 as (x0,eqx0,(inst,insts)); rewrite <- eqx0 in inst.
 apply W0.W_F_elim in H5; auto.
 destruct H5 as (ty1,(ty2,eqx)).
 assert (h:=H3); unfold Wd in h; rewrite subset_ax in h; destruct h.
 destruct H6 as (x1,eqx1,(inst',insts')); rewrite <- eqx1 in inst'.
 apply W0.W_F_elim in H5; auto.
 destruct H5 as (ty1',(ty2',eqx')).
 rewrite eqx; rewrite eqx'.
 assert (h:=ty1); apply A'_elim in h; destruct h as (tya,(tyx,eqy)).
 assert (h:=ty1'); apply A'_elim in h; destruct h as (tya',(tyx',eqy')).
 apply W0.WFi_inv in H4; intros.
  destruct H4.
  apply W0.WFi_ext with A'; intros; auto with *.
   rewrite eqy; rewrite eqy'.
   rewrite inst; rewrite inst'; rewrite H4; reflexivity.

   red; intros.
   generalize (H5 _ _ H7 H8); intro.
   unfold B' in H7; rewrite inst in tyx,H7.
   apply (iso_inj (H1 _ (ftyp _ _ _ H0 tyx H7))) in H9; auto.
    apply subset_intro; auto.
     rewrite <- inst in H7; auto.
    rewrite eqx0.
    apply insts; rewrite <- eqx0; auto.

    apply subset_intro; auto.
     rewrite H6 in H7.
     rewrite H8 in H7.
     rewrite <- inst' in H7; auto.
    rewrite H6 in H7|-*; rewrite eqx1 in H7|-*; rewrite <- H8; apply insts'; auto.

   do 2 red; intros.
   rewrite H6; reflexivity.

   do 2 red; intros.
   rewrite H6; reflexivity.

  rewrite eqy; rewrite eqy'.
  rewrite inst; rewrite inst'; rewrite H5; reflexivity.

 (* surj *)
 specialize fst_typ_sigma with (1:=H2); intros ty1.
 assert (eqy := surj_pair _ _ _ (subset_elim1 _ _ _ H2)).
 apply snd_typ_sigma with (y:=fst y) in H2; auto with *.
2:{
do 2 red; intros; apply cc_prod_morph.
 rewrite H4; reflexivity.
 red; intros.
 rewrite H4; rewrite H5; reflexivity. }

 assert (bm : ext_fun (B' (couple a (fst y)))
    (fun i => iso_inv (subset X (P (f a (fst y) i))) g (cc_app (snd y) i))).
  do 2 red; intros.
  apply iso_inv_ext.
   apply subset_morph; auto with *.
   red; intros; rewrite H4; reflexivity.

   apply morph_is_ext.
   apply (iso_funm (H1 _ H0)).

   rewrite H4; reflexivity.
 exists (couple (couple a (fst y))
    (λ i ∈ B' (couple a (fst y)), iso_inv (subset X (P (f a (fst y) i))) g (cc_app (snd y) i))).
  apply subset_intro.
   apply W0.W_F_intro; intros; auto with *.
    apply A'_intro; auto.

    unfold B' in H3; rewrite fst_def in H3; rewrite snd_def in H3.
    apply cc_prod_elim with (2:=H3) in H2.
    apply iso_inv_typ with (1:=H1 _ (ftyp _ _ _ H0 ty1 H3)) in H2.
    apply subset_elim1 in H2; trivial.

   split; intros.
    rewrite fst_def; rewrite fst_def; reflexivity.

    rewrite fst_def in H3|-*.
    rewrite snd_def in H3|-*.
    rewrite snd_def.
    rewrite cc_beta_eq; trivial.
     apply cc_prod_elim with (2:=H3) in H2.
     apply iso_inv_typ with (1:=H1 _ (ftyp _ _ _ H0 ty1 H3)) in H2.
     apply subset_elim2 in H2; destruct H2.
     rewrite <- H2 in H4; auto.

     unfold B'; rewrite fst_def; rewrite snd_def; trivial.     

  apply transitivity with (2:=symmetry eqy).
  apply couple_morph.
   rewrite fst_def; rewrite snd_def; reflexivity.

   rewrite cc_eta_eq with (1:=H2).
   symmetry.
   apply cc_lam_ext.
    unfold B'; rewrite fst_def.
    rewrite fst_def; rewrite snd_def; reflexivity.

    red; intros.
    assert (cc_app (snd y) x ∈ Y (f a (fst y) x)).
     apply cc_prod_elim with (1:=H2); trivial.
    transitivity (g (iso_inv (subset X (P(f a(fst y) x'))) g (cc_app (snd y) x'))).
     rewrite H4 in H3,H5|-*.
     rewrite iso_inv_eq with (1:=H1 _ (ftyp _ _ _ H0 ty1 H3)); auto with *.

     rewrite H4 in H3.
     apply (iso_funm (H1 _ (ftyp _ _ _ H0 ty1 H3))).
     rewrite snd_def.
     rewrite cc_beta_eq; auto with *.
     unfold B'; rewrite fst_def; rewrite snd_def; trivial.
Qed.


Lemma tr_iso_it a o :
  isOrd o ->
  a ∈ Arg ->
  iso_fun (subset (TI (W0.W_F A' B') o) (instance a))
          (TIF Arg W_Fd o a) (TRF tr o).
intros oo; revert a; elim oo using isOrd_ind; intros.
constructor; intros.
 do 2 red; intros.
 apply TRF_morph0; auto with *.

 red; intros.
 rewrite subset_ax in H3; destruct H3.
 destruct H4 as (x',eqx,inst); rewrite <- eqx in inst; clear x' eqx.
 apply TI_elim in H3; auto.
 destruct H3 as (o', ?,?).
 rewrite TRF_indep with (T:=TI(W0.W_F A' B')) (o':=o'); intros; auto with *.
  apply TIF_intro with o'; auto with *.
  assert (h:=H1 _ H3); apply tr_iso with (a:=a) in h; auto with *.
  apply (iso_typ h).
  apply subset_intro; trivial.
  destruct inst; split; intros; auto with *.
  apply H6.
  unfold B'; rewrite <- H5; trivial.

  rewrite TI_mono_succ; auto with *.
  apply isOrd_inv with y; auto.

 rewrite subset_ax in H3; destruct H3.
 destruct H6.
 rewrite subset_ax in H4; destruct H4.
 destruct H8.
 apply TI_elim in H3; auto.
 destruct H3.
 apply TI_elim in H4; auto.
 destruct H4.
 assert (x2 ⊔ x3 ∈ y).
  apply osup2_lt; auto.
 assert (h:=H1 _ H12); apply tr_iso with (a:=a) in h; auto with *.
 rewrite TRF_indep with (T:=TI(W0.W_F A' B'))(o':=x2 ⊔ x3) in H5; intros; auto with *.
  rewrite TRF_indep with (T:=TI(W0.W_F A' B'))(o':=x2 ⊔ x3) in H5; intros; auto with *.
   apply (iso_inj h) in H5; trivial.
    apply subset_intro.
     revert H10; apply W0.W_F_mono; auto with *.
     apply TI_mono; auto with *.
      apply isOrd_osup2; eauto using isOrd_inv.
      eauto using isOrd_inv.
      apply osup2_incl1; eauto using isOrd_inv.

     rewrite <- H6 in H7; destruct H7; split; auto with *.
     intros.
     apply H13; unfold B'; rewrite <- H7; trivial.

    apply subset_intro.
     revert H11; apply W0.W_F_mono; auto with *.
     apply TI_mono; auto with *.
      apply isOrd_osup2; eauto using isOrd_inv.
      eauto using isOrd_inv.
      apply osup2_incl2; eauto using isOrd_inv.

     rewrite <- H8 in H9; destruct H9; split; auto with *.
     intros.
     apply H13; unfold B'; rewrite <- H9; trivial.

   rewrite TI_mono_succ; eauto using isOrd_inv.
   revert H11; apply W0.W_F_mono; auto.
   apply TI_mono; auto with *.
    apply isOrd_osup2; eauto using isOrd_inv.
    eauto using isOrd_inv.
    apply osup2_incl2; eauto using isOrd_inv.

  rewrite TI_mono_succ; eauto using isOrd_inv.
  revert H10; apply W0.W_F_mono; auto.
  apply TI_mono; auto with *.
   apply isOrd_osup2; eauto using isOrd_inv.
   eauto using isOrd_inv.
   apply osup2_incl1; eauto using isOrd_inv.

 (* surj *)
 apply TIF_elim in H3; auto with *.
 destruct H3.
 assert (h:=H1 _ H3); apply tr_iso with (a:=a) in h; auto with *.
 destruct (iso_surj h) with y0; trivial.
 rewrite subset_ax in H5; destruct H5.
 destruct H7.
 destruct H8.
 exists x0.
  apply subset_intro.
   apply TI_intro with x; auto.

   constructor; intros.
    rewrite H7; auto with *.

    rewrite H7.
    apply H9.
    unfold B' in H10; rewrite H7 in H10; rewrite H8 in H10; trivial.

  rewrite TRF_indep with (T:=TI(W0.W_F A' B')) (o':=x); auto with *.
  rewrite TI_mono_succ; auto.
  apply isOrd_inv with y; trivial.
Qed.

(** * Fixpoint *)

Definition W_ord := W0.W_ord A' B'.

Lemma W_ord_o : isOrd W_ord.
apply W0.W_ord_o; trivial.
Qed.
Hint Resolve W_ord_o : core.

Definition W := Wi W_ord.

Lemma W_eqn a : a ∈ Arg -> W a == W_Fd W a.
unfold W,Wi; intros.
rewrite <- TIF_mono_succ; auto with *.
apply eq_intro; intros.
 revert H0; apply TIF_incl; auto with *.

 destruct (iso_surj (tr_iso_it _ _ (isOrd_succ _ W_ord_o) H)) with z; trivial.
 rewrite subset_ax in H1; destruct H1.
 destruct H3.
 rewrite <- H3 in H4; clear x0 H3.
 rewrite TI_mono_succ in H1; auto.
 unfold W_ord in H1; fold (W0.W A' B') in H1.
 rewrite <- W0.W_eqn in H1; trivial.
 rewrite <- H2.
 apply in_reg with (TRF tr W_ord x).
  apply TI_elim in H1; auto with *.
  destruct H1.
  rewrite TRF_indep with (T:=TI(W0.W_F A' B')) (o':=x0); auto with *.
   rewrite TRF_indep with (T:=TI(W0.W_F A' B')) (o':=x0); auto with *.
    apply isOrd_trans with W_ord; auto.

    rewrite TI_mono_succ; eauto using isOrd_inv.

   rewrite TI_mono_succ; eauto using isOrd_inv.

 apply (iso_typ (tr_iso_it _ _ W_ord_o H)).  
 apply subset_intro; trivial.
Qed.

Lemma W_post o :
  isOrd o -> 
  incl_fam Arg (Wi o) W.
intros oo; elim oo using isOrd_ind; intros.
red; red; intros.
apply TIF_elim in H3; auto with *.
destruct H3.
specialize H1 with (1:=H3).
apply W_Fd_mono in H1.
2:apply TIF_morph; reflexivity.
2:apply TIF_morph; reflexivity.
apply H1 in H4; trivial.
rewrite W_eqn; trivial.
Qed.

(** * Universe facts *)

Section W_Univ.

  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega ∈ U.  

  (** The size of Arg matters: *)
  Hypothesis ArgU : Arg ∈ U.
  Hypothesis aU : forall a, a ∈ Arg -> A a ∈ U.
  Hypothesis bU : forall a x, a ∈ Arg -> x ∈ A a -> B a x ∈ U.

  Lemma G_W_Fd X :
    morph1 X ->
    (forall a, a ∈ Arg -> X a ∈ U) ->
    forall a, a ∈ Arg -> W_Fd X a ∈ U.
unfold W_Fd; intros.
apply G_sigma; intros; auto.
 do 2 red; intros.
 apply cc_prod_ext.
  rewrite H3; reflexivity.

  red; intros.
  rewrite H3; rewrite H5; reflexivity.

 apply G_cc_prod; intros; auto.
 do 2 red; intros.
 rewrite H4; reflexivity.
Qed.

  Lemma G_Wi o a : isOrd o -> o ∈ U -> a ∈ Arg -> Wi o a ∈ U.
unfold Wi.
unfold TIF; intros.
apply G_cc_app; trivial.
2:apply G_trans with Arg; trivial.
apply G_TR; trivial.
 do 3 red; intros.
 apply cc_lam_morph; auto with *.
 red; intros.
 apply sup_morph; trivial.
 red; intros.
 apply W_Fd_morph; trivial.
 red; intros.
 apply cc_app_morph; auto.

 intros.
 apply cc_lam_morph; auto with *; red; intros.
 apply sup_morph; auto with *.
 red; intros.
 apply W_Fd_morph; auto with *.
 apply cc_app_morph; auto with *.

 intros.
 apply G_cc_lam; trivial; intros.
  do 2 red; intros; apply sup_morph; auto with *.
  red; intros.
  apply W_Fd_morph; auto with *.
  apply cc_app_morph; auto with *.

  apply G_sup; trivial.
   do 2 red; intros.
   apply W_Fd_morph; auto with *.
   apply cc_app_morph; auto with *.

   intros.
   apply G_W_Fd; intros; auto.
    apply cc_app_morph; reflexivity.

    apply G_cc_app; auto.
    apply G_trans with Arg; trivial.
Qed.

  Lemma G_W_ord : W_ord ∈ U.
apply W0.G_W_ord; trivial.
 apply G_sigma; trivial.
 do 2 red; intros; apply Am; trivial.

 intros.
 apply bU.
  apply fst_typ_sigma in H; trivial.

  apply snd_typ_sigma with (y:=fst a) in H; auto with *.
Qed.

  Lemma G_W a : a ∈ Arg -> W a ∈ U.
intros.
unfold W.
apply G_Wi; auto.
apply G_W_ord.
Qed.

End W_Univ.

End W_theory.

(* More on W_Fd: *)

Hint Resolve B'_morph : core.

Section MoreMorph.

Local Notation E := eq_set (only parsing).

Lemma W_Fd_morph_all :
  Proper ((E==>E)==>(E==>E==>E)==>(E==>E==>E==>E)==>(E==>E)==>E==>E) W_Fd.
do 6 red; intros.
unfold W_Fd.
apply sigma_morph.
 apply H; trivial.

 red; intros.
 apply cc_prod_morph.
  apply H0; trivial.

  red; intros.
  apply H2; apply H1; trivial.
Qed.

Lemma Wi_morph_all : Proper (E==>(E==>E)==>(E==>E==>E)==>(E==>E==>E==>E)==>E==>E==>E) Wi.
do 7 red; intros.
unfold Wi.
unfold TIF.
apply cc_app_morph; trivial.
apply ZFord.TR_morph; trivial.
do 2 red; intros.
apply cc_lam_morph; trivial.
red; intros.
apply sup_morph; trivial.
red; intros.
apply W_Fd_morph_all; trivial.
apply cc_app_morph.
apply H5; trivial.
Qed.

  Lemma W_ord_morph_all : Proper (E==>(E==>E)==>(E==>E==>E)==>E) W_ord.
do 4 red; intros.
unfold W_ord.
apply W0.W_ord_morph.
 apply sigma_morph; trivial.

 red; intros.
 apply H1.
  apply fst_morph; trivial. 
  apply snd_morph; trivial. 
Qed.

Lemma W_morph_all : Proper (E==>(E==>E)==>(E==>E==>E)==>(E==>E==>E==>E)==>E==>E) W.
do 6 red; intros.
unfold W.
apply Wi_morph_all; trivial.
apply W_ord_morph_all; auto.
Qed.

End MoreMorph.

(** * Waiving the universe constraint on Arg: *)

Section BigParameter.

Variable Arg : set.
Variable A : set -> set.
Variable B : set -> set -> set.
Variable f : set -> set -> set -> set.
Hypothesis Am : morph1 A.
Hypothesis Bm : morph2 B.
Hypothesis fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) f.
Hypothesis ftyp : forall a x y,
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  f a x y ∈ Arg.

(** We show the above encoding with small index simulates [W], and
    hence the closure ordinal of [W a] is small for each parameter [a].
 *)

Let f' a b := f a (fst b) (snd b).
Let idx' a := sigma (A a) (B a).
Notation Arg' := (Aenc Arg idx' f').
Notation decode := (Dec f').
Let fenc a x y := extln a (couple x y).

Let f'_typ a b : a ∈ Arg -> b ∈ idx' a -> f' a b ∈ Arg.
unfold f'; intros tya tyi.
apply sigma_elim in tyi; auto with *.
2:do 2 red; intros; apply Bm; auto with *.
destruct tyi as (_ & ? & ?).
apply ftyp; trivial.
Qed.
Local Instance idx'm : morph1 idx'.
do 2 red; intros.
apply sigma_morph; auto with *.
Qed.
Local Instance f'm : morph2 f'.
do 3 red; intros.
unfold f'.
rewrite H,H0; reflexivity.
Qed.
Local Instance fencm : Proper (eq_set ==> eq_set ==> eq_set ==> eq_set) fenc.
do 4 red; intros.
unfold fenc.
apply extln_morph; trivial.
apply couple_morph; trivial.
Qed.

Let idx'_intro a p x i :
  a ∈ Arg ->
  p ∈ Arg' a ->
  x ∈ A (decode a p) ->
  i ∈ B (decode a p) x ->
  couple x i ∈ idx' (decode a p).
intros.
apply couple_intro_sigma; trivial.  
do 2 red; intros.
apply Bm; auto with *.
Qed.

Let decode_fenc a p x i :
  a ∈ Arg ->
  p ∈ Arg' a ->
  x ∈ A (decode a p) ->
  i ∈ B (decode a p) x ->
  decode a (fenc p x i) == f (decode a p) x i.
intros.
unfold fenc.
rewrite Dec_extln with (A:=Arg)(B:=idx')(f:=f'); auto with *.
unfold f'.
rewrite fst_def, snd_def; reflexivity.
Qed.
  
Hint Resolve f'_typ idx'm f'm fencm : core.

Let A'' a q := A (decode a q).
Let B'' a q := B (decode a q).

Local Instance A''_morph : morph2 A''.
unfold A''.
do 3 red; intros.
rewrite H,H0; reflexivity.
Qed.
Local Instance B''_morph : Proper (eq_set==>eq_set==>eq_set==>eq_set) B''.
unfold B''; do 4 red; intros.
rewrite H,H0,H1; reflexivity.
Qed.
Local Instance A''_morph' a : morph1 (A'' a).
apply A''_morph; reflexivity.
Qed.

Local Instance B''_morph' a : morph2 (B'' a).
apply B''_morph; reflexivity.
Qed.

Let W_Fd' a      := W_Fd (A'' a) (B'' a) fenc.
Let Wi'   a o a' := Wi (Arg' a) (A'' a) (B'' a) fenc o a'.
            
Instance W_Fd'_morph a' : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) (W_Fd' a').
do 3 red; intros.
apply W_Fd_morph; auto with *.
Qed.


Lemma Wi_rebase o a :
  isOrd o ->
  a ∈ Arg ->
  Wi Arg A B f o a ==
  Wi' a o empty.
intros.
symmetry.
unfold Wi', Wi.
transitivity (TIF Arg (W_Fd A B f) o (decode a empty)).
2:apply TIF_morph; [reflexivity|apply Dec_mt with (A:=Arg)(B:=idx'); auto].
generalize empty (Aenc_intro1 Arg idx' f' idx'm f'm  f'_typ _ H0).
apply isOrd_ind with (2:=H).
intros ord oord leo Hrec p typ.
rewrite !TIF_eq; auto with *.
2:apply W_Fd_morph; auto with *.
2:apply Dec_typ with (B:=idx'); trivial.
2:apply W_Fd'_morph.
apply sup_morph; auto with *.
red; intros o' o'' o'lt eqo.
unfold W_Fd.
symmetry.
apply sigma_ext.
*unfold A''; reflexivity.
*intros x x' tyx eqx.
 apply cc_prod_ext.
 +unfold B''; apply Bm; [reflexivity|trivial].
 +intros i i' tyi eqi.
  rewrite Hrec; trivial.
  2:rewrite <-eqx,<-eqi; apply extln_typ; trivial.  
  2:apply idx'_intro; trivial.
  apply TIF_morph; [symmetry; trivial|].
  symmetry; rewrite <-eqx,<-eqi.
  unfold fenc.
  apply decode_fenc; trivial.
Qed.


(** The closure ordinal for a given value of the parameter *)
Definition W_ord_a a :=
  W_ord (Arg' a) (A'' a) (B'' a).

Lemma isOrd_W_ord_a a : isOrd (W_ord_a a).
intros.
unfold W_ord_a.
apply W_ord_o.
apply B''_morph'.
Qed.
Hint Resolve isOrd_W_ord_a : core.

Lemma W_ord_a_smaller a :
  a ∈ Arg -> W_ord_a a ⊆ W_ord Arg A B.
unfold W_ord_a.
intros.
apply Wfmap_W_ord with (f:=fun p => couple (decode a (fst p)) (snd p)); intros; auto with *.
+do 2 red; intros.
 rewrite H0; reflexivity.
+red; intros.
 apply sigma_elim in H0; auto with *.
 destruct H0 as (eqx&typ&tyx).
 apply couple_intro_sigma; auto with *.
 apply Dec_typ with (A:=Arg)(B:=idx'); trivial. 
+unfold B''.
 rewrite fst_def, snd_def; reflexivity.
Qed.

Lemma W_rebase a :
  a ∈ Arg ->
  W Arg A B f a == W (Arg' a) (A'' a) (B'' a) fenc empty.
intros.
unfold W.
rewrite Wi_rebase; auto using W_ord_o.
unfold Wi'.
apply incl_eq.
 fold (W (Arg' a) (A'' a) (B'' a) fenc empty).
 apply W_post; auto using W_ord_o with *.
  intros.
  apply extln_typ; trivial.  
  apply idx'_intro; trivial.

  apply Aenc_intro1; trivial.

 unfold Wi.
 apply TIF_mono; auto using W_ord_o with *.
  apply W_Fd'_morph.

  apply Aenc_intro1; trivial.

  assert (tmp := W_ord_a_smaller).
  unfold W_ord_a in tmp; auto.
Qed.

Lemma W_eqn_a a :
  a ∈ Arg ->
  W Arg A B f a == Wi Arg A B f (W_ord_a a) a.
intros.
rewrite W_rebase; trivial.
rewrite Wi_rebase; trivial.
reflexivity.
Qed.

(** Showing the encoding [WW] is small even when Arg is big
 *)

Section UniverseFacts.
  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega ∈ U.  

  (** We don't assume Arg is in U... *)
  Hypothesis aU : forall a, a ∈ Arg -> A a ∈ U.
  Hypothesis bU : forall a x, a ∈ Arg -> x ∈ A a -> B a x ∈ U.

  Let G_Arg' a : a ∈ Arg -> Arg' a ∈ U.
intros.
apply G_Aenc; trivial.
intros.
apply G_sigma; auto with *.
do 2 red; intros; apply Bm; auto with *.
Qed.

  (* ... but the closure ordinal is in U, for each value of [a] *)
  Lemma G_W_ord_a a : a ∈ Arg -> W_ord_a a ∈ U.
intros.
unfold W_ord_a.
apply G_W_ord; auto with *.
 intros.
 apply aU.
 apply Dec_typ with (A:=Arg)(B:=idx'); trivial. 

 intros.
 apply bU; trivial.
 apply Dec_typ with (A:=Arg)(B:=idx'); trivial. 
Qed.

  Lemma G_W_big a : a ∈ Arg -> W Arg A B f a ∈ U.
intros.
rewrite W_rebase; trivial.
unfold W.
apply G_Wi; auto using W_ord_o with *.
 intros; apply extln_typ; trivial.
 apply idx'_intro; trivial.
                         
 intros.
 apply aU.
 apply Dec_typ with (A:=Arg)(B:=idx'); trivial. 

 intros.
 apply bU; trivial.
 apply Dec_typ with (A:=Arg)(B:=idx'); trivial. 

 change (W_ord_a a ∈ U).
 apply G_W_ord_a; trivial.

 apply Aenc_intro1; trivial.
Qed.

End UniverseFacts.

End BigParameter.

Instance W_ord_a_morph :
  Proper (eq_set==>(eq_set==>eq_set)==>(eq_set==>eq_set==>eq_set)==>
          (eq_set==>eq_set==>eq_set==>eq_set)==>eq_set==>eq_set)
    W_ord_a.
do 6 red; intros.
unfold W_ord_a.
apply W_ord_morph_all.
 apply Aenc_morph_gen; trivial.

 red; intros; apply sigma_morph; auto with *.
 do 2 red; intros; apply H2; try rewrite H5; auto with *.

 red; intros.
 apply H0; apply Dec_morph_gen; auto with *.
 do 2 red; intros; apply H2; try rewrite H6; auto with *.

 do 2 red; intros.
 apply H1; trivial.
 apply Dec_morph_gen; auto with *.
 do 2 red; intros; apply H2; try rewrite H7; auto with *.
Qed.

Section Test.
Let x := (W_eqn, G_W_big).
Print Assumptions x.
End Test.
