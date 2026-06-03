Require Import ZFskol.
Require Import Choice.
Require Import Sublogic.
Require EnsEm.

(** In this file, we give an attempt to build a model of IZF
   in Coq.
 *)

Module IZF_R <: IZF_R_Ex_sig CoqSublogicThms.
Import CoqSublogicThms.


Include EnsEm.RawEnsembles CoqSublogicThms.

(* We only use the following instance of unique choice for
   replacement: *)
Definition ttrepl' :=
  forall a:set, unique_choice {x|in_set x a} set eq_set.

Axiom choice_axiom : forall A B, choice A B.

(* We show it is a consequence of [choice]. *)
Lemma ttrepl_axiom : ttrepl'.
red; red; intros.
apply choice_axiom; trivial.
Qed.

Lemma repl_ax:
    forall a (R:set->set->Prop),
    (forall x x' y y', in_set x a ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x y y', in_set x a -> R x y -> R x y' -> eq_set y y') ->
    exists b, forall x, in_set x b <->
     (exists2 y, in_set y a & R y x).
intros.
elim (ttrepl_axiom (subset a (fun x=>exists y, R x y))
        (fun p y => R (proj1_sig p) y)); intros.
pose (a' := {x|in_set x (subset a (fun x => exists y, R x y))}).
fold a' in x,H1.
exists (repl1 _ x).
intros.
elim (repl1_ax _ x x0); intros.
 fold a' in H2,H3|-.
 split; intros.
  elim H2; trivial; intros.
  exists (proj1_sig x1).
   apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x1))).

   apply H with (4:=H1 x1).
    apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x1))).
    apply eq_set_refl.
    apply eq_set_sym; trivial.

  apply H3.
  destruct H4.
  assert (in_set x1 (subset a (fun x => exists y, R x y))).
   apply (proj2 (subset_ax a (fun x => exists y, R x y) x1)).
   split; trivial.
   exists x1.
    apply eq_set_refl.
    exists x0; trivial.
  pose (x' := exist _ x1 H6 : a').
  exists x'.
  apply H0 with x1; trivial.
  apply (H1 x').

 apply H0 with (proj1_sig z); trivial.
  apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig z))).
  apply H with (proj1_sig z') (x z'); trivial.
   apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig z'))).
   apply eq_set_sym; trivial.
   apply eq_set_refl.

(* side conditions *)
 elim (proj2 (proj1 (subset_ax _ _ _) (proj2_sig x))); intros. 
 destruct H2.
 exists x1; apply H with (4:=H2).
  apply in_reg with (proj1_sig x); trivial.
  apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x))).

  apply eq_set_sym; trivial.

  apply eq_set_refl.

 assert (in_set (proj1_sig x) a).
  apply (proj1 (proj1 (subset_ax _ _ _) (proj2_sig x))).
 split; intros.
  apply H0 with (proj1_sig x); trivial.

  revert H1; apply H; trivial.
  apply eq_set_refl.
Qed.

Definition repl_ex := repl_ax.

(* Attempt to prove that choice is necessary for replacement, by deriving
   choice from replacement. Works only for relations that are morphisms for
   set equality... *)
Lemma ttrepl_needed_for_repl :
  forall a:set,
  let A := {x|in_set x a} in
  let eqA (x y:A) := eq_set (proj1_sig x) (proj1_sig y) in
  let B := set in
  let eqB := eq_set in
  forall (R:A->B->Prop),
  Proper (eqA==>eqB==>iff) R ->
  (forall x:A, exists y:B, R x y) ->
  (forall x y y', R x y -> R x y' -> eqB y y') ->
  exists f:A->B, forall x:A, R x (f x).
intros a A eqA B eqB R Rext Rex Runiq.
destruct repl_ax with
  (a:=a) (R:=fun x y => exists h:in_set x a, R (exist _ x h) y).
 intros.
 destruct H2.
 exists (in_reg _ _ _ H0 x0).
 revert H2; apply Rext; apply eq_set_sym; assumption.

 intros x y y' _ (h,Rxy) (h',Rxy').
 apply Runiq with (1:=Rxy).
 revert Rxy'; apply Rext.
  apply eq_set_refl.
  apply eq_set_refl.

 exists (fun y => union (subset x (fun z => R y z))).
 intro.
 destruct Rex with x0.
 apply Rext with (3:=H0);[apply eq_set_refl|].
 apply eq_set_sym.
 apply eq_set_ax; split; intros.
  rewrite union_ax; exists x1; trivial.
  rewrite subset_ax.
  split.
   apply H.
   exists (proj1_sig x0); [apply proj2_sig|].
   exists (proj2_sig x0).
   destruct x0; trivial.

   exists x1; trivial; apply eq_set_refl.

  rewrite union_ax in H1; destruct H1.
  rewrite subset_ax in H2; destruct H2.
  destruct H3.
  apply eq_elim with x2; trivial.
  apply eq_set_trans with (1:=H3).
  apply Runiq with (1:=H4); trivial.
Qed.

Notation "x ∈ y" := (in_set x y).
Notation "x == y" := (eq_set x y).

(* Collection *)
Section Collection.

Section FromTTColl.

(* TTColl is a consequence of choice *)
Lemma ttcoll0 :
  forall (A:Tlo) (R:A->set->Prop),
  (forall x:A, exists y:set, R x y) ->
  exists X:Tlo, exists f : X->set,
    forall x:A, exists i:X, R x (f i).
intros.
destruct (choice_axiom A set R) as (f,Hf); trivial.
(* X is A because choice "chooses" just one y for each x *)
exists A; exists f; eauto.
Qed.

Lemma ttcoll' :
  forall (A:Tlo) R,
  (forall x:A, exists y:set, R x y) ->
  exists B, forall x:A, exists2 y, y ∈ B & R x y.
intros.
destruct ttcoll0 with (1:=H) as (X,(f,Hf)).
exists (sup X f).
intro.
destruct Hf with x.
exists (f x0); trivial.
exists x0; apply eq_set_refl.
Qed.

Lemma coll_ax_ttcoll : forall A (R:set->set->Prop), 
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x, in_set x A -> exists y, R x y) ->
    exists B, forall x, in_set x A -> exists2 y, in_set y B & R x y.
intros.
destruct (ttcoll0 (idx A) (fun i y => R (elts A i) y)) as (X,(f,Hf)).
 intro i.
 apply H0.
 exists i; apply eq_set_refl.

 exists (sup X f); intros.
 destruct H1 as (i,?).
 destruct (Hf i) as (j,?).
 exists (f j).
  exists j; apply eq_set_refl.

  revert H2; apply H.
   exists i; apply eq_set_refl.
   apply eq_set_sym; assumption.
   apply eq_set_refl.
Qed.

(* Proving collection requires the specialized version of ttcoll *)
Lemma ttcoll'' : forall A (R:set->set->Prop),
  (forall x x' y y', in_set x A ->
   eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
  (forall x, x ∈ A -> exists y:set, R x y) ->
  exists f : {x|x∈ A} -> {X:Tlo & X->set},
    forall x, exists i:projT1 (f x), R (proj1_sig x) (projT2 (f x) i).
intros.
destruct (coll_ax_ttcoll A R H H0) as (B,HB).
exists (fun _ => let (X,f) := B in existT (fun X => X->set) X f).
destruct B; simpl.
destruct x; simpl; intros.
destruct HB with x; trivial.
destruct H1.
exists x1.
apply H with (4:=H2); auto with *.
apply eq_set_refl.
Qed.

End FromTTColl.

Section FromChoice.

Lemma coll_ax_choice : forall A (R:set->set->Prop), 
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x, in_set x A -> exists y, R x y) ->
    exists B, forall x, in_set x A -> exists y, in_set y B /\ R x y.
intros.
elim (choice_axiom {x|x ∈ A} set (fun p y => R (proj1_sig p) y)); trivial; intros.
 exists (repl1 A x).
 intros.
 destruct H2.
 exists (x (elts' _ x1)); split.
  exists x1; apply eq_set_refl.

  apply H with (proj1_sig (elts' _ x1)) (x (elts' _ x1)); trivial.
   apply (proj2_sig (elts' _ x1)).
   apply eq_set_sym; trivial.
   apply eq_set_refl.

 apply H0.
 apply (proj2_sig x).
Qed.

End FromChoice.

Section FromReplClassic.

Hypothesis EM : forall A:Prop, A \/ ~A.

Lemma coll_ax : forall A (R:set->set->Prop), 
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (forall x, in_set x A -> exists y, R x y) ->
    exists B, forall x, in_set x A -> exists y, in_set y B /\ R x y.
intros.
pose (P := fun x y => x ∈ A /\ exists z, z ∈ y /\ R x z).
assert (Pm : forall x x', x ∈ A -> x == x' -> forall y y', y == y' -> P x y -> P x' y').
 intros.
 destruct H4.
 destruct H5; destruct H5.
 split; [|exists x0;split].
  apply in_reg with x; trivial.

  apply eq_elim with y; trivial.

  apply H with x x0; trivial.
  apply eq_set_refl.
assert (Pwit : forall x, x ∈ A -> exists y, P x (V y)). 
 intros.
 destruct (H0 x); trivial.
 exists (singl x0); split; trivial.
 exists x0; split; trivial.
 apply V_sub with (V x0).
  apply V_mono; exists tt; apply eq_set_refl.
  apply V_intro.
destruct (@repl_ax A (fun x y => lst_rk (P x) y)); eauto using lst_rk_uniq, lst_rk_ex.
 intros.
 apply lst_rk_morph with (P x) y; trivial.
 intros.
 split; intros; eauto.
  apply Pm with x' x'0; trivial.
   apply in_reg with x; trivial.
   apply eq_set_sym; trivial.
   apply eq_set_sym; trivial.

 exists (union x); intros.
 destruct lst_rk_ex with (P x0); auto.
  split; apply Pm; trivial; auto using eq_set_refl, eq_set_sym.

  specialize lst_incl with (1:=H3).
  destruct 1 as (_,(?,(?,?))).
  exists x2; split; trivial.
  rewrite union_ax.
  exists x1; trivial.
  rewrite H1.
  exists x0; auto.
Qed.

Lemma coll2_ax : forall A (R:set->set->Prop) x,
    (forall x x' y y', in_set x A ->
     eq_set x x' -> eq_set y y' -> R x y -> R x' y') ->
    (exists y, R x y) ->
    in_set x A ->
    exists B, exists y, in_set y B /\ R x y.
intros.
assert (forall z, z ∈ singl x -> z ∈ A).
 intros.
 destruct H2; simpl in *.
 apply in_reg with x; trivial.
 apply eq_set_sym; trivial.
destruct (coll_ax (singl x) R); intros; eauto.
 destruct H0.
 exists x1.
 apply H with x x1; trivial.
  destruct H3; simpl in *.
  apply eq_set_sym; trivial.

  apply eq_set_refl.

 exists x0.
 apply H3.
 exists tt; apply eq_set_refl.
Qed.
 
End FromReplClassic.

End Collection.

(* Rk: decision of membership implies excluded-middle *)
Lemma set_dec_EM :
  (forall x y, in_set x y \/ ~ in_set x y) ->
  (forall P, P \/ ~ P).
intros.
destruct (H empty (subset (power empty) (fun _ => P))).
 left.
 rewrite subset_ax in H0; destruct H0.
 destruct H1; trivial.
 right; red; intros; apply H0.
 rewrite subset_ax.
 split.
  rewrite power_ax; intros.
  elim empty_ax with y; trivial.

  exists empty; trivial.
  apply eq_set_refl.
Qed.

(* Failed attempt to build (set-theoretical) choice axiom. *)

Section Choice.

Hypothesis C : forall X:Type, X + (X->False).

Lemma impl_choice_ax : forall A B, choice A B.
red; intros.
exists (fun x =>
  match C ({y:B|R x y}) with
  | inl y => proj1_sig y
  | inr h =>
    False_rect B (let (y,r) := H x in h (exist _ y r))
  end).
intros.
destruct (C {y:B|R x y}).
 destruct s; trivial.

 destruct (H x).
 destruct (f (exist (fun y => R x y) x0 r)).
Qed.

Definition choose (x:set) :=
  match C (idx x) with
  | inl i => elts x i
  | _ => empty
  end.

Lemma choose_ax : forall a, (exists x, x ∈ a) -> choose a ∈ a.
intros.
unfold choose.
destruct (C (idx a)).
 exists i; apply eq_set_refl.

 destruct H.
 destruct H.
 elim (f x0).
Qed.

(* ... but choose is not a morphism! *)
Lemma choose_not_morph : ~ forall x x', x == x' -> choose x == choose x'.
unfold choose; red; intros.
generalize (H (sup bool (fun b => if b then empty else singl empty))
              (sup bool (fun b => if b then singl empty else empty))).
simpl idx; simpl elts; intros.
assert (singl empty == empty).
 lapply H0.
  destruct (C bool); trivial.
   destruct b; auto with *.
   apply eq_set_sym; trivial.

   destruct (f true).

  split; intros.
   exists (negb i).
   destruct i; apply eq_set_refl.

   exists (negb j).
   destruct j; apply eq_set_refl.
elim empty_ax with empty.
apply eq_elim with (singl empty); trivial.
exists tt; apply eq_set_refl.
Qed.

End Choice.

(* Regularity is classical *)

Section Regularity.

Definition regularity :=
  forall a a0, a0 ∈ a ->
  exists2 b, b ∈ a & ~(exists2 c, c ∈ a & c ∈ b).

Lemma regularity_ax (EM:forall P,P\/~P): regularity.
red.
induction a0; intros.
destruct (EM (exists i:X, f i ∈ a)).
 destruct H1; eauto.

 exists (sup X f); trivial.
 red; intros; apply H1.
 destruct H2.
 destruct H3; simpl in *.
 exists x0.
 apply in_reg with x; trivial.
Qed.

Lemma regularity_is_classical (reg : regularity) : forall P, P \/ ~P.
intros.
destruct (reg (subset (pair empty (power empty))
           (fun x => x == power empty \/ x == empty /\ P)) (power empty)).
 rewrite subset_ax.
 split.
  rewrite pair_ax; right ;apply eq_set_refl.
  exists (power empty).
   apply eq_set_refl.
   left; apply eq_set_refl.

 rewrite subset_ax in H; destruct H.
 destruct H1.
 destruct H2.
  right ;red; intros.
  apply H0.
  exists empty.
   rewrite subset_ax.
   split.
    rewrite pair_ax; left; apply eq_set_refl.
    exists empty.
     apply eq_set_refl.
     right; split; trivial.
     apply eq_set_refl.

    apply eq_elim with x0.
    2:apply eq_set_sym; trivial.
    apply eq_elim with (power empty).
    2:apply eq_set_sym; trivial.
    rewrite power_ax; trivial.

  destruct H2; auto.
Qed.

End Regularity.

End IZF_R.
