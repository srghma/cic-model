
(** In this file, we show equivalence results between the Skolemized
   and existentially quantified presentations of ZF.
 *)

Require Import basic Sublogic.
Require Export ZFdef.
Require EnsEm.
Require Zskol.


(*
Module Type ExReplacement (L:SublogicTheory) (ExZ:SetTheory L).
  Import L.
  Parameter repl_ex : forall a (R:ExZ.set->ExZ.set->Prop),
  (forall x x' y y', ExZ.in_set x a -> ExZ.eq_set x x' -> ExZ.eq_set y y' -> R x y -> R x' y') ->
  (forall x y y', ExZ.in_set x a -> R x y -> R x y' -> ExZ.eq_set y y') ->
  #exists b, forall x, ExZ.in_set x b <-> #exists2 y, ExZ.in_set y a & R y x.
End ExReplacement.



Module SkolemReplacement (L:SublogicTheory) (ExZ:SetTheory L)(Repl : ExReplacement L ExZ).
  Import L.

  Parameter set : Type.
  Parameter eq_set : set -> set -> Prop.
  Parameter in_set : set -> set -> Prop.
  Infix "==" := eq_set.
  Infix "∈" := in_set.
  Parameter eq_setoid: Equivalence eq_set.
  Existing Instance eq_setoid.
  Parameter in_morph : Proper (eq_set ==> eq_set ==> iff) in_set.
  Existing Instance in_morph.
  
Parameter Z2set : ExZ.set -> set.
Parameter eq_equiv : forall x y, Z2set x == Z2set y <-> ExZ.eq_set x y.
Parameter in_equiv : forall a b, in_set (Z2set a) (Z2set b) <-> ExZ.in_set a b.
Lemma eq_Zeq : forall x y, Z2set x == Z2set y -> ExZ.eq_set x y.
intros x y; apply eq_equiv.
Qed.
Lemma Zeq_eq : forall x y, ExZ.eq_set x y -> Z2set x == Z2set y.
intros x y; apply eq_equiv.
Qed.
Lemma inZ_in : forall a b, ExZ.in_set a b -> Z2set a ∈ Z2set b.
intros a b; apply in_equiv.
Qed.
Lemma in_inZ : forall a b, Z2set a ∈ Z2set b -> ExZ.in_set a b.
intros a b; apply in_equiv.
Qed.

Instance Z2set_morph : Proper (ExZ.eq_set ==> eq_set) Z2set.
exact Zeq_eq.
Qed.
Parameter Z2set_surj : forall x, #exists y, x == Z2set y.

  Parameter set_intro :
  forall f : ExZ.set -> Prop,
    (#exists u, f u) /\
    (forall a a', f a -> f a' -> ExZ.eq_set a a') -> set.
  Parameter set_elim : forall P h z, 
    z ∈ set_intro P h <-> #exists2 a:ExZ.set, P a & z ∈ Z2set a.


Definition funDom (R:set -> set -> Prop) x :=
  forall x' y y', R x y -> R x' y' -> x == x' -> y == y'.
Definition downR (R:set -> set -> Prop) x' y' :=
  exists2 x, x == Z2set x' /\ funDom R x & exists2 y, y == Z2set y' & R x y.

Lemma downR_morph : Proper
  ((eq_set ==> eq_set ==> iff) ==> ExZ.eq_set ==> ExZ.eq_set ==> iff) downR.
do 4 red; intros.
unfold downR.
apply Zeq_eq in H0.
apply Zeq_eq in H1.
apply ex2_morph; red; intros.
 apply and_iff_morphism.
  rewrite H0; reflexivity.

  unfold funDom.
  split; intros.
   rewrite <- (fun e1 => H a a e1 y2 y2) in H3; auto with *.
   rewrite <- (fun e1 => H x' x' e1 y' y') in H4; eauto with *.

   rewrite (fun e1 => H a a e1 y2 y2) in H3; auto with *.
   rewrite (fun e1 => H x' x' e1 y' y') in H4; eauto with *.

 apply ex2_morph; red; intros.
  rewrite H1; reflexivity.
  apply H; reflexivity.
Qed.

Lemma downRm : forall R x x' y y',
  ExZ.eq_set x x' ->
  ExZ.eq_set y y' ->
  downR R x y ->
  downR R x' y'.
intros.
destruct H1 as (xx,(eqx,fdomx), (yy,eqy,rel)).
exists xx.
 split; trivial.
 rewrite eqx.
 rewrite eq_equiv; trivial.
exists yy; trivial.
rewrite eqy.
rewrite eq_equiv; trivial.
Qed.

Lemma downR_fun : forall R x y y',
  downR R x y ->
  downR R x y' ->
  ExZ.eq_set y y'.
intros.
destruct H as (xx,(eqx,fdomx), (yy,eqy,rel)).
destruct H0 as (xx',(eqx',_), (yy',eqy',rel')).
apply eq_Zeq.
rewrite <- eqy; rewrite <- eqy'.
red in fdomx.
apply fdomx with xx'; trivial.
rewrite eqx; rewrite eqx'.
reflexivity.
Qed.


Lemma repl0 : forall (a:set) (R:set->set->Prop), set.
intros a R.
apply set_intro with
 (fun a' => forall x,
  ExZ.in_set x a' <-> #exists2 y, Z2set y ∈ a & downR R y x).
split; intros.
 Tdestruct (Z2set_surj a).
 assert (R'm := fun x0 x' y y' (_:ExZ.in_set x0 x) => downRm R x0 x' y y').
 assert (R'fun := fun x0 y y' (_:ExZ.in_set x0 x) => downR_fun R x0 y y').
 Tdestruct (Repl.repl_ex x (downR R) R'm R'fun); intros.
 Texists x0; intros.
 rewrite H0.
 apply Tr_morph; apply ex2_morph; red; intros.
 2:reflexivity.
 split; intros.
  rewrite H.
  apply inZ_in; trivial.

  apply in_inZ.
  rewrite <- H; trivial.

 rewrite ExZ.eq_set_ax; intros.
 rewrite H.
 rewrite H0.
 reflexivity.
Defined.

Definition incl_set x y := forall z, z ∈ x -> z ∈ y.

Lemma repl0_mono :
  Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl0.
do 4 red; simpl; intros.
apply set_elim.
apply set_elim in H1.
Tdestruct H1 as (a,H1,ina).
Tdestruct (Z2set_surj z).
rewrite H2 in ina.
apply in_equiv in ina.
Texists (subset a (fun 

assert (a = 

intros z'.
rewrite H1.
rewrite H2 in ina.
apply in_equiv in ina.
apply H1 in ina.
Tdestruct ina.
split; intros.
*Tdestruct H5.
 Texists x3;[auto|].
 destruct H6 as (x3',(?,?),(z'',?,?)).
 exists x3'; [split;[trivial|]|].
  red; intros.
  red in H7; eapply H7 with x3';[| |reflexivity].
   revert H10; apply H0; reflexivity.
   revert H11; apply H0; [trivial|reflexivity].
 exists z''; trivial.
 revert H9; apply H0; reflexivity.
*Tdestruct H5.
 Texists x3.
 {
 destruct H6 as (x3',(?,?),(z'',?,?)).
 exists x3'; [split;[trivial|]|].
  red; intros.
  red in H7; eapply H7 with x3';[| |reflexivity].
   revert H10; apply H0; reflexivity.
   revert H11; apply H0; [trivial|reflexivity].
 exists z''; trivial.
 revert H9; apply H0; reflexivity.

 red.

auto. 

  intros w; specialize H1 with w.
rewrite H1.

rewrite in_set_elim in *.
Tdestruct H1.
destruct H2.
simpl in *; intros.
Tdestruct (Z2set_surj y).
assert (R'm := fun x x' y y' (_:ExZ.in_set x x3) => downRm y0 x x' y y').
assert (R'fun := fun x y y' (_:ExZ.in_set x x3) => downR_fun y0 x y y').
Tdestruct (Repl.repl_ex x3 (downR y0) R'm R'fun).
Texists x1; trivial.
exists x4; trivial.
 intro; rewrite H5.
 apply Tr_morph; apply ex2_morph; red; intros; auto with *.
 rewrite H4.
 symmetry; apply in_equiv.

 rewrite H5.
 rewrite H2 in H3.
 clear x2 H1 H2 x4 H5.
 Tdestruct H3.
 Texists x2.
  apply H in H1.
  rewrite H4 in H1; rewrite in_equiv in H1; trivial.

  revert H2; apply iff_impl; apply downR_morph; auto with *.
Qed. 

Lemma repl_sig :
  { repl |
    Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl /\
    forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    forall x, x ∈ repl a R <-> #exists2 y, y ∈ a & R y x }.
exists repl0; split.
 exact repl0_mono.
split; intros.
 rewrite in_set_elim in H1.
 Tdestruct H1.
 destruct H2; simpl in *.
 rewrite H2 in H3.
 Tdestruct H3.
 destruct H4.
 destruct H5.
 destruct H4.
 Texists x3.
  rewrite H4; trivial.
 revert H6; apply H; auto with *.
  rewrite H4; trivial.

  apply Eq_proj in H1.
  rewrite H1; trivial.

 Tdestruct H1.
 apply In_intro; simpl; intros.
 rewrite H4; clear H4.
 Tdestruct (Z2set_surj x0).
 Texists x1.
  rewrite <- H4; trivial.
 exists x0.
  split; intros; eauto.
  red; intros.
  apply H0 with x0; trivial.
  revert H6; apply H; auto with *.
  rewrite <- H7; trivial.

  exists x; trivial.
  apply Eq_proj; trivial.
Defined.

Definition repl := proj1_sig repl_sig.
Lemma repl_mono : 
  Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl.
Proof (proj1 (proj2_sig repl_sig)).
Lemma repl_ax:
    forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    forall x, x ∈ repl a R <-> #exists2 y, y ∈ a & R y x.
Proof.
exact (proj2 (proj2_sig repl_sig)).
Qed.

End SkolemReplacement.

*)

Module Skolem (L:SublogicTheory). (*<: IZF_R_sig L *)

(** We assume we have a model of set theory with existential axioms in
    sublogic L. We could do the same with the abstract signature... *)
Module ExZ := EnsEm.RawEnsembles L.
Import L.

Include Zskol.Skolem L ExZ.
(** uchoice holds, but we need to give the proof that P is a specification to
    the Skolem symbol. *)

Definition uchoice_pred (P:set->Prop) :=
  (forall x x', x == x' -> P x -> P x') /\
  (#exists x, P x) /\
  (forall x x', P x -> P x' -> x == x').

Definition uchoice (P : set -> Prop) (Hp : uchoice_pred P) : set.
exists (fun z => P (Z2set z)).
destruct Hp.
destruct H0.
split; intros.
 Tdestruct H0.
 Tdestruct (Z2set_surj x).
 Texists x0; apply H with x; trivial.

 apply eq_Zeq.
 auto.
Defined.

Lemma uchoice_ax : forall P h x,
  (x ∈ uchoice P h <-> #exists2 z, P z & x ∈ z).
split; intros.
 destruct H.
 Tdestruct H.
 destruct H0.
 simpl in H0.
 Texists (Z2set x1); trivial.
 apply In_intro; intros.
 simpl in H3.
 rewrite H3.
 destruct (proj2_sig x).
 rewrite (H5 x' x0); trivial.

 Tdestruct H.
 destruct H0.
 Tdestruct H0.
 destruct H1.
 constructor.
 Texists x1; trivial.
 simpl.
 exists x2; trivial.
 apply (proj1 h x0); trivial.
 apply Eq_proj; trivial.
Qed.

Lemma uchoice_morph_raw : forall (P1 P2:set->Prop) h1 h2,
  (forall x x', x == x' -> (P1 x <-> P2 x')) ->
  uchoice P1 h1 == uchoice P2 h2.
intros.
apply eq_set_ax; intros.
rewrite uchoice_ax.
rewrite uchoice_ax.
apply Tr_morph; apply ex2_morph; red; intros.
 apply H; reflexivity.

 reflexivity.
Qed.


Instance uchoice_pred_morph : Proper ((eq_set ==> iff) ==> iff) uchoice_pred.
apply morph_impl_iff1; auto with *.
do 3 red; intros.
destruct H0 as (?,(?,?)); split;[|split]; intros.
 assert (x x0).
  revert H4; apply H; auto with *.
 revert H5; apply H; trivial.

 Tdestruct H1; Texists x0.
 revert H1; apply H; auto with *.

 apply H2; [revert H3|revert H4]; apply H; auto with *.
Qed.


Lemma uchoice_ext : forall (P:set->Prop) h x, (#P x) -> x == uchoice P h.
intros.
apply eq_set_ax;intros.
rewrite uchoice_ax.
Telim H; intro.
split; intros.
 Texists x; trivial.

 Tdestruct H0.
 destruct h.
 destruct H3.
 rewrite (H4 x x1); auto.
Qed.

Lemma uchoice_def : forall P h, #P (uchoice P h).
intros.
destruct h.
destruct a.
Tdestruct t.
Tin; apply p with x; trivial.
apply uchoice_ext; trivial.
Tin; trivial.
Qed.

(** * Skolemizing Replacement *)

Definition funDom (R:set -> set -> Prop) x :=
  forall x' y y', R x y -> R x' y' -> x == x' -> y == y'.
Definition downR (R:set -> set -> Prop) x' y' :=
  exists2 x, x == Z2set x' /\ funDom R x & exists2 y, y == Z2set y' & R x y.

Lemma downR_morph : Proper
  ((eq_set ==> eq_set ==> iff) ==> ExZ.eq_set ==> ExZ.eq_set ==> iff) downR.
do 4 red; intros.
unfold downR.
apply Zeq_eq in H0.
apply Zeq_eq in H1.
apply ex2_morph; red; intros.
 apply and_iff_morphism.
  rewrite H0; reflexivity.

  unfold funDom.
  split; intros.
   rewrite <- (fun e1 => H a a e1 y2 y2) in H3; auto with *.
   rewrite <- (fun e1 => H x' x' e1 y' y') in H4; eauto with *.

   rewrite (fun e1 => H a a e1 y2 y2) in H3; auto with *.
   rewrite (fun e1 => H x' x' e1 y' y') in H4; eauto with *.

 apply ex2_morph; red; intros.
  rewrite H1; reflexivity.
  apply H; reflexivity.
Qed.

Lemma downRm : forall R x x' y y',
  ExZ.eq_set x x' ->
  ExZ.eq_set y y' ->
  downR R x y ->
  downR R x' y'.
intros.
destruct H1 as (xx,(eqx,fdomx), (yy,eqy,rel)).
exists xx.
 split; trivial.
 rewrite eqx.
 rewrite eq_equiv; trivial.
exists yy; trivial.
rewrite eqy.
rewrite eq_equiv; trivial.
Qed.

Lemma downR_fun : forall R x y y',
  downR R x y ->
  downR R x y' ->
  ExZ.eq_set y y'.
intros.
destruct H as (xx,(eqx,fdomx), (yy,eqy,rel)).
destruct H0 as (xx',(eqx',_), (yy',eqy',rel')).
apply eq_Zeq.
rewrite <- eqy; rewrite <- eqy'.
red in fdomx.
apply fdomx with xx'; trivial.
rewrite eqx; rewrite eqx'.
reflexivity.
Qed.


(** If we have existential replacement, then we build skolemized replacement *)
Module Type ExReplacement.
  Parameter repl_ex : forall a (R:ExZ.set->ExZ.set->Prop),
    (forall x x' y y', ExZ.in_set x a -> ExZ.eq_set x x' -> ExZ.eq_set y y' -> R x y -> R x' y') ->
    (forall x y y', ExZ.in_set x a -> R x y -> R x y' -> ExZ.eq_set y y') ->
    #exists b, forall x, ExZ.in_set x b <-> #exists2 y, ExZ.in_set y a & R y x.
End ExReplacement.
Module SkolemReplacement (Repl : ExReplacement).

Lemma repl0 : forall (a:set) (R:set->set->Prop), set.
intros a R.
exists
 (fun a' => forall x,
  ExZ.in_set x a' <-> #exists2 y, Z2set y ∈ a & downR R y x).
split; intros.
 Tdestruct (Z2set_surj a).
 assert (R'm := fun x0 x' y y' (_:ExZ.in_set x0 x) => downRm R x0 x' y y').
 assert (R'fun := fun x0 y y' (_:ExZ.in_set x0 x) => downR_fun R x0 y y').
 Tdestruct (Repl.repl_ex x (downR R) R'm R'fun); intros.
 Texists x0; intros.
 rewrite H0.
 apply Tr_morph; apply ex2_morph; red; intros.
 2:reflexivity.
 split; intros.
  rewrite H.
  apply inZ_in; trivial.

  apply in_inZ.
  rewrite <- H; trivial.

 rewrite ExZ.eq_set_ax; intros.
 rewrite H.
 rewrite H0.
 reflexivity.
Defined.

Local Notation incl_set := (fun x y => forall z, z ∈ x -> z ∈ y).

Lemma repl0_mono :
  Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl0.
do 4 red; simpl; intros.
rewrite in_set_elim in *.
Tdestruct H1.
destruct H2.
simpl in *; intros.
Tdestruct (Z2set_surj y).
assert (R'm := fun x x' y y' (_:ExZ.in_set x x3) => downRm y0 x x' y y').
assert (R'fun := fun x y y' (_:ExZ.in_set x x3) => downR_fun y0 x y y').
Tdestruct (Repl.repl_ex x3 (downR y0) R'm R'fun).
Texists x1; trivial.
exists x4; trivial.
 intro; rewrite H5.
 apply Tr_morph; apply ex2_morph; red; intros; auto with *.
 rewrite H4.
 symmetry; apply in_equiv.

 rewrite H5.
 rewrite H2 in H3.
 clear x2 H1 H2 x4 H5.
 Tdestruct H3.
 Texists x2.
  apply H in H1.
  rewrite H4 in H1; rewrite in_equiv in H1; trivial.

  revert H2; apply iff_impl; apply downR_morph; auto with *.
Qed. 

Lemma repl_sig :
  { repl |
    Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl /\
    forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    forall x, x ∈ repl a R <-> #exists2 y, y ∈ a & R y x }.
exists repl0; split.
 exact repl0_mono.
split; intros.
 rewrite in_set_elim in H1.
 Tdestruct H1.
 destruct H2; simpl in *.
 rewrite H2 in H3.
 Tdestruct H3.
 destruct H4.
 destruct H5.
 destruct H4.
 Texists x3.
  rewrite H4; trivial.
 revert H6; apply H; auto with *.
  rewrite H4; trivial.

  apply Eq_proj in H1.
  rewrite H1; trivial.

 Tdestruct H1.
 apply In_intro; simpl; intros.
 rewrite H4; clear H4.
 Tdestruct (Z2set_surj x0).
 Texists x1.
  rewrite <- H4; trivial.
 exists x0.
  split; intros; eauto.
  red; intros.
  apply H0 with x0; trivial.
  revert H6; apply H; auto with *.
  rewrite <- H7; trivial.

  exists x; trivial.
  apply Eq_proj; trivial.
Defined.

Definition repl := proj1_sig repl_sig.
Lemma repl_mono : 
  Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl.
Proof (proj1 (proj2_sig repl_sig)).
Lemma repl_ax:
    forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    forall x, x ∈ repl a R <-> #exists2 y, y ∈ a & R y x.
Proof.
exact (proj2 (proj2_sig repl_sig)).
Qed.

End SkolemReplacement.

(** * Collection *)

Definition downR' (R:set -> set -> Prop) x' y' :=
  exists2 x, x == Z2set x' & exists2 y, y == Z2set y' & R x y.

Lemma downR'_morph : Proper
  ((eq_set ==> eq_set ==> iff) ==> ExZ.eq_set ==> ExZ.eq_set ==> iff) downR'.
do 4 red; intros.
unfold downR'.
apply Zeq_eq in H0.
apply Zeq_eq in H1.
apply ex2_morph; red; intros.
 rewrite H0; reflexivity.

 apply ex2_morph; red; intros.
  rewrite H1; reflexivity.
  apply H; reflexivity.
Qed.

(** Without further axiom, we can only prove an existential collection
    for the sets of defined here, using the existential collection of
    the original sets. *)
Module Type ExCollection.
  Parameter coll_ex : forall A (R:ExZ.set->ExZ.set->Prop), 
    Proper (ExZ.eq_set ==> ExZ.eq_set ==> iff) R ->
    #exists B, forall x, ExZ.in_set x A ->
         (#exists y, R x y) -> #exists2 y, ExZ.in_set y B & R x y.
End ExCollection.
Module LiftCollection (Coll : ExCollection).

Lemma coll_ex : forall A (R:set->set->Prop), 
    Proper (eq_set ==> eq_set ==> iff) R ->
    #exists B, forall x, x ∈ A ->
         (#exists y, R x y) -> #exists2 y, y ∈ B & R x y.
intros.
Tdestruct (Z2set_surj A) as (A',?).
Tdestruct (Coll.coll_ex A' _ (downR'_morph R R H)) as (B,HB).
Texists (Z2set B).
intros.
rewrite H0 in H1.
Tdestruct (Z2set_surj x) as (x',?).
rewrite H3 in H1; rewrite in_equiv in H1.
assert (#exists y, downR' R x' y).
 Tdestruct H2 as (y,?).
 Tdestruct (Z2set_surj y) as (y',?).
 Texists y'; red; eauto.
Tdestruct (HB _ H1 H4) as (y,?,(x'',?,(y',?,?))).
Texists y'.
 rewrite H7; rewrite in_equiv; trivial.

 rewrite H3; rewrite <- H6; trivial.
Qed.
End LiftCollection.

(** ** Skolemizing Collection in classical logic using existential *replacement*
       (since in classical logic, replacement implies collection). *)

Module ClassicCollection (ExR : ExReplacement).

Module Repl := SkolemReplacement(ExR).
(** Proving that collection can be skolemized in classical ZF:
    we need excluded-middle to prove coll_ax_uniq (see EnsEm)
 *)

Section Classic.

Hypothesis EM : forall P, #(P \/ #¬ P).
(** We need to provide a spec that is more specific than what appears here
    (it is not uniquely satifiable). Instead, we specify coll as the
    smallest Veblen universe that satisfies collection. This is why we need
    excluded-middle. *)
Lemma coll_sig : forall A (R:set->set->Prop), 
  {coll| Proper (eq_set==>eq_set==>iff) R ->
     forall x, x ∈ A ->
     (#exists y, R x y) ->
     (#exists2 y, y ∈ coll & R x y) }.
intros A R.
pose (R' := downR' R).
assert (R'm : Proper (ExZ.eq_set==>ExZ.eq_set==>iff) R').
{apply morph_impl_iff2; auto with *.
 do 4 red; intros.
 destruct H1 as (x'',?,(y'',?,?)).
 exists x'';[|exists y'';trivial].
  transitivity (Z2set x); trivial.
  apply Zeq_eq; trivial.

  transitivity (Z2set x0); trivial.
  apply Zeq_eq; trivial. }
apply set_intro with
  (fun C => exists2 A', A == Z2set A' &
       forall z, ExZ.in_set z C <->
                   #exists2 v, ExZ.in_set z v &
                                 exists2 x, ExZ.in_set x A' &
                                 ExZ.coll_unique_rel R' x v); intros.
*Tdestruct (Z2set_surj A) as (A',e).
 Tdestruct (ExR.repl_ex A' (ExZ.coll_unique_rel R')
              (ExZ.coll_rel_morph A' R' R'm) (ExZ.coll_rel_uniq A' R'))
   as (B,Bax).
 Texists (ExZ.union B).
 exists A'; trivial.
 intros.
 rewrite ExZ.union_ax.
 split; intros.
 +Tdestruct H as (v, zinv, vinB).
  apply Bax in vinB.
  Tdestruct vinB as (x,tyx,img).
  Texists v; trivial.
  exists x; trivial.
 +Tdestruct H as (v, zinv, (x,tyx,img)).
  Texists v; trivial.
  apply Bax.
  Texists x; trivial.
*destruct H as (A',A'def,H).
 destruct H0 as (A'',A''def,H0).
 rewrite A'def in A''def.
 apply eq_Zeq in A''def.
 apply ExZ.eq_set_ax; intros z.
 rewrite H,H0.
 apply Tr_morph.
 apply ex2_morph; red; intros; [reflexivity|].
 apply ex2_morph; red; intros; [|reflexivity].
 apply ExZ.in_set_morph; [reflexivity|trivial].
*Tdestruct (Z2set_surj x) as (x',ex).
 assert (wit : #exists v, ExZ.coll_unique_rel R' x' v).
 {apply ExZ.coll_rel_ex with (1:=EM).
  Tdestruct H1 as (y,rel).
  Tdestruct (Z2set_surj y) as (y',ey).
  Texists y'. 
  exists x; trivial.
  exists y; trivial. }
 rewrite ex in H0.
 Tdestruct wit as (v,rel).
 destruct (rel) as ((y',(x'',x''def,(y,ydef,rel')),inv),_).
 rewrite <- ex in x''def.
 rewrite x''def in rel'; clear x'' x''def.
 Texists y; trivial.
 apply In_intro; simpl; intros.
 apply Eq_proj in H2.
 destruct H3 as (A',A'def,H3).
 rewrite ydef in H2; apply eq_Zeq in H2.
 rewrite <- H2; clear H2 x'0.
 apply H3.
 Texists v; trivial.
 exists x'; trivial.
 rewrite A'def in H0.
 apply in_inZ; trivial.
Qed.

Definition coll A R := proj1_sig (coll_sig A R).
Lemma coll_ax : forall A (R:set->set->Prop), 
  Proper (eq_set==>eq_set==>iff) R ->
  forall x, x ∈ A -> (#exists y, R x y) ->
  #exists2 y, y ∈ coll A R & R x y.
Proof (fun A R => proj2_sig (coll_sig A R)).

End Classic.
End ClassicCollection.

End Skolem.

(** * Instance *)


(** Several useful instances *)

(** Model of IZF_R *)

Module IZF_R <: IZF_R_sig CoqSublogicThms.
  Include Skolem CoqSublogicThms.
  Parameter tt_repl_ax : ExZ.ttrepl ExZ.eq_set.
  Module Re <: ExReplacement.
    Definition repl_ex := ExZ.ttrepl_implies_repl_ex tt_repl_ax.
  End Re.
  Include SkolemReplacement Re.
End IZF_R.

Definition IZFRpack := (IZF_R.repl_mono,IZF_R.repl_ax,IZF_R.wf_ax).
Print Assumptions IZFRpack. (* TTrepl *)

(** Model of IZF_C *)

Module IZF_C <: IZF_C_sig CoqSublogicThms.
  Include Skolem CoqSublogicThms.
  Parameter tt_coll_ax : ExZ.ttcoll ExZ.eq_set.
  Module Co <: ExCollection.
    Definition coll_ex := ExZ.collection_ax tt_coll_ax.
  End Co.
  Include LiftCollection Co.
End IZF_C.

Definition IZFCpack := (IZF_C.coll_ex,IZF_C.wf_ax).
Print Assumptions IZFCpack. (* TTcoll (with intuitionistic equality on sets) *)

(** A model of ZF, based only on TTColl (no ecluded-middle in the
    metatheory).
 *)
Module ZF <: ZF_sig ClassicSublogicThms.
  Include Skolem ClassicSublogicThms.
  Import ClassicSublogicThms.
  Parameter tt_repl_ax : ExZ.ttrepl ExZ.eq_set. (* Replacement, stated in classical logic *)
  Module Re <: ExReplacement.
    Definition repl_ex := ExZ.ttrepl_implies_repl_ex tt_repl_ax.
  End Re.
  Module Co := ClassicCollection Re.
  Definition coll := Co.coll classic.
  Definition coll_ax := Co.coll_ax classic.
End ZF.

Definition ZFpack := ZF.coll_ax.
Print Assumptions ZFpack. (* TTColl (with classical equality on sets) *)
(* Eval cbv beta delta - [ ZF.ExZ.eq_set Proper respectful iff ] iota in ZF.ExZ.ttcoll.
 *)
