
(** In this file, we show equivalence results between the Skolemized
   and existentially quantified presentations of ZF.
 *)

Require Import basic Sublogic.
Require Export ZFdef.
Require EnsEm.


Module Skolem (L:SublogicTheory) (ExZ:Zermelo_Ex_sig L) <: Zermelo_sig L.

Import L.

Instance Zsetoid: Equivalence ExZ.eq_set.
Proof.
split; red; intros; rewrite ExZ.eq_set_ax in *; intros.
 reflexivity.
 symmetry; trivial.
 transitivity (ExZ.in_set x0 y); trivial.
Qed.

Instance Zin_morph : Proper (ExZ.eq_set ==> ExZ.eq_set ==> iff) ExZ.in_set.
Proof.
do 3 red; intros.
rewrite ExZ.eq_set_ax in H0.
split; intros.
 rewrite <- H0.
 apply ExZ.in_reg with x; trivial.

 rewrite H0.
 symmetry in H.
 apply ExZ.in_reg with y; trivial.
Qed. 

(** * Existential sets and their relation with regular sets *)

(** The type of existential sets *)
Definition set :=
  { f : ExZ.set -> Prop |
    (#exists u, f u) /\
    (forall a a', f a -> f a' -> ExZ.eq_set a a') }.

Lemma set_intro : forall (f:ExZ.set->Prop) (P:set->Prop),
  (#exists u, f u) ->
  (forall a a', f a -> f a' -> ExZ.eq_set a a') ->
  (forall Hex Huniq, P (exist _ f (conj Hex Huniq))) ->
  sig P.
intros.
exists (exist _ f (conj H H0)); trivial.
Qed.

(** Membership. (Uses an inductive to avoid unwanted unfolding...) *)
Inductive in_set_ (x y:set) : Prop :=
 InSet
  (_:#exists2 x', proj1_sig x x' &
      exists2 y', proj1_sig y y' & ExZ.in_set x' y').

Definition in_set := in_set_.

Lemma in_set_isL x y : isL (in_set x y).
red.
constructor.
Telim H; intro.
destruct H; trivial.
Qed.
Global Hint Resolve in_set_isL : core.

Lemma in_set_elim : forall x y, in_set x y <->
  #exists2 x', proj1_sig x x' &
   exists2 y', proj1_sig y y' & ExZ.in_set x' y'.
split; intros.
 destruct H; trivial.
 constructor; trivial.
Qed.

Notation "x ∈ y" := (in_set x y).

(** Equality *)
Definition eq_set a b := forall x, x ∈ a <-> x ∈ b.

Notation "x == y" := (eq_set x y).

Lemma eq_set_isL x y : isL (x == y).
red; red; intros.
Telim H; auto.
Qed.
Global Hint Resolve eq_set_isL : core.

Lemma eq_set_ax : forall a b, a == b <-> (forall x, x ∈ a <-> x ∈ b).
reflexivity.
Qed.

Instance eq_setoid: Equivalence eq_set.
Proof.
split; do 2 red; intros.
 reflexivity.
 symmetry; trivial.
 transitivity (x0 ∈ y); trivial.
Qed.

Lemma In_intro: forall x y: set,
  (forall x' y', proj1_sig x x' -> proj1_sig y y' -> ExZ.in_set x' y') ->
  x ∈ y.
intros.
destruct (proj2_sig x).
Tdestruct H0.
destruct (proj2_sig y).
Tdestruct H2.
constructor.
Texists x0; trivial.
exists x1; auto.
Qed.

Lemma In_elim (P:Prop) (x y:set):
  isL P ->
  (forall x' y', proj1_sig x x' -> proj1_sig y y' -> ExZ.in_set x' y' -> P) ->
  x ∈ y -> P.
intros.
rewrite in_set_elim in H1.
Tdestruct H1.
destruct H2.
eauto.
Qed.

(** Lifting sets to existential sets *)
Definition Z2set (x:ExZ.set) : set.
exists (fun a => ExZ.eq_set a x).
split.
 Texists x; reflexivity.

 intros; transitivity x; trivial.
 symmetry; trivial.
Defined.

Lemma Eq_proj : forall (x:set) x', proj1_sig x x' -> x == Z2set x'.
intros.
destruct (proj2_sig x).
clear H0.
split; intros.
 rewrite in_set_elim in H0.
 Tdestruct H0.
 destruct H2.
 constructor.
 Texists x1; simpl; trivial.
 exists x2; auto.

 rewrite in_set_elim in H0.
 Tdestruct H0; simpl in *.
 destruct H2.
 constructor.
 Texists x1; simpl; trivial.
 exists x'; trivial.
 rewrite <- H2; trivial.
Qed.

(** Perservation of equality and membership by lifting *)
Lemma inZ_in : forall a b, ExZ.in_set a b -> Z2set a ∈ Z2set b.
unfold Z2set, in_set; simpl.
intros.
constructor; simpl.
Texists a; try reflexivity.
exists b; try reflexivity; trivial.
Qed.

Lemma in_inZ : forall a b, Z2set a ∈ Z2set b -> ExZ.in_set a b.
intros.
rewrite in_set_elim in H.
Tdestruct H.
destruct H0.
unfold Z2set in *; simpl in *.
apply ExZ.in_reg with x; trivial.
rewrite <- H0; auto.
Qed.

Lemma in_equiv a b : in_set (Z2set a) (Z2set b) <-> ExZ.in_set a b.
split; intros.
 apply in_inZ; trivial.
 apply inZ_in; trivial.
Qed.

Lemma eq_Zeq : forall x y, Z2set x == Z2set y -> ExZ.eq_set x y.
intros.
rewrite ExZ.eq_set_ax; split; intros.
 apply in_inZ.
 apply (proj1 (H (Z2set x0))).
 apply inZ_in; trivial.

 apply in_inZ.
 apply (proj2 (H (Z2set x0))).
 apply inZ_in; trivial.
Qed.

Lemma Zeq_eq : forall x y, ExZ.eq_set x y -> Z2set x == Z2set y.
intros.
split; intros.
 rewrite in_set_elim in H0.
 Tdestruct H0.
 destruct H1.
 simpl in H1.
 constructor.
 Texists x1; trivial.
 exists x2; trivial.
 simpl.
 transitivity x; trivial.

 rewrite in_set_elim in H0.
 Tdestruct H0.
 destruct H1.
 simpl in H1.
 constructor.
 Texists x1; trivial.
 exists x2; trivial.
 simpl.
 transitivity y; trivial.
 symmetry; trivial.
Qed.

Lemma eq_equiv x y : Z2set x == Z2set y <-> ExZ.eq_set x y.
split; intros.
 apply eq_Zeq; trivial.
 apply Zeq_eq; trivial.
Qed.

Instance Z2set_morph : Proper (ExZ.eq_set ==> eq_set) Z2set.
exact Zeq_eq.
Qed.

(** Compatibility axiom *)
Lemma in_reg : forall a a' b, a == a' -> a ∈ b -> a' ∈ b.
intros.
rewrite in_set_elim in H0.
Tdestruct H0 as (a0,eq_a,(b0,eq_b,in_ab)).
destruct (proj2_sig a') as (h,_).
Tdestruct h as (a'0, eq_a').
constructor.
Texists a'0; trivial.
exists b0; trivial.
apply ExZ.in_reg with a0; trivial.
apply eq_Zeq.
rewrite <- (Eq_proj _ _ eq_a).
rewrite <- (Eq_proj _ _ eq_a').
trivial.
Qed.

Instance in_morph : Proper (eq_set ==> eq_set ==> iff) in_set.
Proof.
unfold eq_set in |- *; split; intros.
 apply in_reg with x; auto.
 elim (H0 x); auto.

 apply in_reg with y; auto.
  symmetry  in |- *; auto.
  elim (H0 y); auto.
Qed.

(** Surjectivity of lifting *)
Lemma Z2set_surj : forall x, #exists y, x == Z2set y.
intros.
destruct (proj2_sig x).
Tdestruct H.
Texists x0.
split; intros.
 rewrite in_set_elim in H1.
 Tdestruct H1.
 destruct H2.
 constructor.
 Texists x2; trivial.
 exists x3; trivial.
 simpl; auto.

 rewrite in_set_elim in H1.
 Tdestruct H1.
 destruct H2.
 constructor.
 Texists x2; trivial.
 simpl in H2.
 exists x0; trivial.
 rewrite <- H2; trivial.
Qed.

(**)

Lemma ex2_equiv (P Q:_->Prop) (P' Q':_->Prop) :
  (forall x x', x == Z2set x' -> (P x <-> P' x')) ->
  (forall x x', x == Z2set x' -> (Q x <-> Q' x')) ->
  ((#ex2 P Q) <-> (#ex2 P' Q')).
split; intros.
 Tdestruct H1.
 Tdestruct (Z2set_surj x) as (x',?).
 Texists x'.
  revert H1; apply -> H; trivial.
  revert H2; apply -> H0; trivial.

 Tdestruct H1.
 Texists (Z2set x).
  revert H1; apply <- H; reflexivity.
  revert H2; apply <- H0; reflexivity.
Qed.

Lemma set_intro' (P:set->Prop) (P':set->Prop) :
  (forall x, isL (P x)) ->
  Proper (eq_set ==> iff) P ->
  (forall z, (forall x, x ∈ z <-> P x) -> P' z) ->
  (#exists z, forall x, ExZ.in_set x z <-> P (Z2set x)) ->
  sig P'.
intros.
apply set_intro with (fun z => forall x, ExZ.in_set x z <-> P (Z2set x)); trivial.
 intros.
 apply ExZ.eq_set_ax; intros.
 rewrite H3; rewrite H4; reflexivity.

 intros. 
 apply H1.
 split; intros.
  apply In_elim with (3:=H3); simpl; intros; auto.
  apply Eq_proj in H4.
  rewrite H4; rewrite <- H5; trivial.

  apply In_intro; simpl; intros.
  apply Eq_proj in H4.
  rewrite H5.
  rewrite <- H4; trivial.
Qed.

(** well-founded induction *)

Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, (forall y, y ∈ x -> #P y) -> #P x) ->
  forall x, #P x.
intros.
assert (elm : forall xs, isL (forall x, x == Z2set xs -> #P x)).
{intro xs; apply fa_isL; intro x'.
 apply imp_isL; auto. }
cut (forall xs (x:set), x == Z2set xs -> #P x).
{intros.
 Tdestruct (Z2set_surj x).
 eauto. }
clear x.
intros xs.
apply elm.
elim xs using (ExZ.wf_ax (fun xs => forall x, x==Z2set xs -> #P x)); intros.
assert (H0' := fun y h => elm _ (H0 y h)); clear H0.
Tin; intros.
apply H; intros.
Tdestruct (Z2set_surj y).
rewrite H0,H2 in H1.
apply in_inZ in H1; eauto.
Qed.

(** * Skolemizing Zermelo axioms *)

(** empty set *)

Lemma empty_sig : { empty | forall x, x ∈ empty -> #False }.
apply set_intro' with (P:=fun _ => #False); intros; auto.
 do 2 red; reflexivity.

 rewrite H in H0; trivial.

 Tdestruct ExZ.empty_ex; intros.
 red in H.
 Texists x; split; intros; eauto.
Tabsurd; trivial.
Qed.

Definition empty := proj1_sig empty_sig.
Lemma empty_ax: forall x, x ∈ empty -> #False.
Proof proj2_sig empty_sig.

Section Pair.
(** pair *)

Let pair_spec a b x := #(x == a \/ x == b).

Let pair_spec_morph a b :
  Proper (eq_set ==> iff) (pair_spec a b).
unfold pair_spec; intros.
do 2 red; intros.
rewrite H; reflexivity.
Qed.

Lemma lift_pair a b :
    (#exists2 a', Z2set a' == a &
      exists2 b', Z2set b' == b &
      exists c', forall z, ExZ.in_set z c' <-> #(ExZ.eq_set z a' \/ ExZ.eq_set z b')) ->
    { pair | forall x, x ∈ pair <-> pair_spec a b x }.
intros expair.
apply set_intro' with (P:=pair_spec a b); unfold pair_spec; intros; auto.
*apply pair_spec_morph; trivial.
*Tdestruct expair as (a',adef,(b',bdef,(c',cdef))).
 Texists c'; intros.
 rewrite cdef, <-adef, <-bdef.
 apply Tr_morph.
 apply or_iff_morphism; symmetry; apply eq_equiv.
Qed.

Lemma pair_sig : forall a b,
  { pair | forall x, x ∈ pair <-> pair_spec a b x }.
intros a b.
apply lift_pair.
Tdestruct (Z2set_surj a) as (a',?).
Tdestruct (Z2set_surj b) as (b',?).
Tdestruct (ExZ.pair_ex a' b') as (w,?).
Texists a'; [symmetry;trivial|exists b';[symmetry;trivial|]].
exists w; trivial.
Qed.

Definition pair a b := proj1_sig (pair_sig a b).
Lemma pair_ax: forall a b x, x ∈ pair a b <-> #(x == a \/ x == b).
exact (fun a b => proj2_sig (pair_sig a b)).
Qed.

End Pair.

Section Union.
(** union *)

Let union_spec a x := #exists2 y, x ∈ y & y ∈ a.

Let union_spec_morph a :
  Proper (eq_set==>iff) (union_spec a).
do 2 red; intros.
apply Tr_morph; apply ex2_morph; red; intros; auto with *.
rewrite H; reflexivity.
Qed.


Lemma union_sig: forall a,
  { union | forall x, x ∈ union <-> union_spec a x }.
intro a.
apply set_intro' with (P:=union_spec a); unfold union_spec; intros; auto.
 apply union_spec_morph; trivial.

 Tdestruct (Z2set_surj a) as (a',?).
 Tdestruct (ExZ.union_ex a') as (z,spec).
 Texists z; intros.
 rewrite spec.
 symmetry; apply ex2_equiv; intros.
  rewrite H0; apply in_equiv.

  rewrite H0; rewrite H; apply in_equiv.
Qed.

Definition union a := proj1_sig (union_sig a).
Lemma union_ax: forall a x,
  x ∈ union a <-> #exists2 y, x ∈ y & y ∈ a.
Proof fun a => proj2_sig (union_sig a).

End Union.

Section Subset.
(** subset *)

Let subset_spec a P x := x ∈ a /\ #exists2 x', x == x' & P x'.

Let subset_spec_morph a P :
  Proper (eq_set ==> iff) (subset_spec a P).
do 2 red; intros.
apply and_iff_morphism.
 rewrite H; reflexivity.

 apply Tr_morph; apply ex2_morph; red; intros; auto with *.
 rewrite H; reflexivity.
Qed.

Lemma subset_sig: forall a P,
  { subset | forall x, x ∈ subset <->
             (x ∈ a /\ #exists2 x', x==x' & P x') }.
intros a P.
apply set_intro' with (P:=subset_spec a P); unfold subset_spec; intros; auto.
 apply subset_spec_morph; trivial.

 Tdestruct (Z2set_surj a) as (a',?).
 Tdestruct (ExZ.subset_ex a' (fun z => #exists2 z', z' == Z2set z & P z')) as (w,?).
 Texists w; intros.
 rewrite H0.
 apply and_iff_morphism.
  rewrite H; symmetry; apply in_equiv.

  split; intros.
   Tdestruct H1.
   Tdestruct H2.
   Texists x1; trivial.
   rewrite H2; apply eq_equiv; trivial.

   Tdestruct H1.
   Texists x; auto with *.
   Texists x0; auto with *.
Qed.

Definition subset a P := proj1_sig (subset_sig a P).
Lemma subset_ax : forall a P x,
    x ∈ subset a P <-> (x ∈ a /\ #exists2 x', x==x' & P x').
Proof fun a P => proj2_sig (subset_sig a P).

End Subset.

Section PowerSet.
(** power set *)

Let power_spec a x := forall y, y ∈ x -> y ∈ a.

Let power_spec_morph a :
  Proper (eq_set ==> iff) (power_spec a).
do 2 red; intros.
apply fa_morph; intro.
rewrite H; reflexivity.
Qed.

Lemma power_sig: forall a,
  { power | forall x, x ∈ power <-> (forall y, y ∈ x -> y ∈ a) }.
intro a.
apply set_intro' with (P:=power_spec a); unfold power_spec; intros; auto.
 apply power_spec_morph; trivial.

 Tdestruct (Z2set_surj a) as (a',?).
 Tdestruct (ExZ.power_ex a') as (z,spec).
 Texists z; intros.
 rewrite spec.
 split; intros.
  Tdestruct (Z2set_surj y).
  rewrite H; rewrite H2; apply in_equiv; apply H0; apply in_equiv.
  rewrite <- H2; trivial.

  apply in_equiv; rewrite <- H; apply H0; apply in_equiv; trivial.
Qed.

Definition power a := proj1_sig (power_sig a).
Lemma power_ax:
  forall a x, x ∈ power a <-> (forall y, y ∈ x -> y ∈ a).
Proof fun a => proj2_sig (power_sig a).

End PowerSet.


(** infinite set (natural numbers) *)

Definition Nat x :=
  forall (P:set),
  empty ∈ P ->
  (forall x, x ∈ P -> union (pair x (pair x x)) ∈ P) ->
  x ∈ P.

Instance Nat_morph : Proper (eq_set ==> iff) Nat.
unfold Nat; split; intros.
 rewrite <- H; apply H0; trivial.
 rewrite H; apply H0; trivial.
Qed.

Lemma Nat_S : forall x,
  Nat x -> Nat (union (pair x (pair x x))).
unfold Nat; intros; auto.
Qed.

Definition infinite_sig :
  { infty | empty ∈ infty /\
      forall x, x ∈ infty -> union (pair x (pair x x)) ∈ infty }.
apply set_intro' with (P:=Nat).
 unfold Nat; auto.

 apply Nat_morph.

 intros.
 split; intros.
  rewrite H; red; auto.

  rewrite H in H0|-*.
  apply Nat_S; trivial.

 Tdestruct ExZ.infinity_ex as (infty,?,?).
 Tdestruct (ExZ.subset_ex infty (fun x => Nat(Z2set x))) as (z,spec).
 Texists z.
 split; intros.
  rewrite spec in H1.
  destruct H1.
  red; Tdestruct H2.
  revert H3; apply Nat_morph.
  apply eq_equiv; trivial.

  rewrite spec.
  split.
  2:Texists x; auto with *.
  apply in_equiv; apply H1; intros.
   Tdestruct H.
   assert (empty == Z2set x0).
    apply eq_set_ax; split; intros.
     Tabsurd; apply empty_ax with (1:=H3).

     Tdestruct (Z2set_surj x1).
     Tabsurd; apply H with x2.
     apply in_equiv; rewrite<- H4; trivial.
   rewrite H3; apply in_equiv; trivial.

   Tdestruct (Z2set_surj x0).
   rewrite H3 in H2; apply in_equiv in H2.
apply H0 in H2; clear H0.
Tdestruct H2.
apply in_equiv in H2; revert H2; apply in_reg.
rewrite eq_set_ax.
intros.
rewrite union_ax.
Tdestruct (Z2set_surj x3).
rewrite H2; rewrite in_equiv.
rewrite H0.
split; intros.
 Tdestruct H4.
  Texists (pair x0 x0).
   rewrite pair_ax; Tleft.
   rewrite H2; rewrite H3; apply eq_equiv; trivial.

   rewrite pair_ax; Tright; reflexivity. 

  Texists x0.
   rewrite H2; rewrite H3; apply in_equiv; trivial.

   rewrite pair_ax; Tleft; reflexivity.

 Tdestruct H4.
 rewrite <- eq_equiv.
 rewrite <- in_equiv.
 rewrite <- H3.
 rewrite <- H2.
 rewrite pair_ax in H5; Tdestruct H5.
  Tright; rewrite <- H5; trivial.

  rewrite H5 in H4.
  Tleft.
  rewrite pair_ax in H4; Tdestruct H4; trivial.
Qed.
Definition infinite := proj1_sig infinite_sig.
Lemma infinity_ax1: empty ∈ infinite.
Proof proj1 (proj2_sig infinite_sig).

Lemma infinity_ax2: forall x,
  x ∈ infinite -> union (pair x (pair x x)) ∈ infinite.
Proof.
exact (proj2 (proj2_sig infinite_sig)).
Qed.


(*
Lemma replf_sig a f :
  {b | 
*)
End Skolem.

