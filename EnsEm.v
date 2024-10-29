Require Export basic.
Require Import Choice. (* Axiom *)
Require Import Sublogic.
Require Import ZFdef.

(** In this file, we build a model of both intuitionistic and
   classical ZF in Coq extended with the Type-Theoretical Collection
   Axiom (TTColl).
 *)

Module RawEnsembles (L:SublogicTheory).

Import L.

(* Statement of choice principles in the given logic *) 
Definition Tchoice A B :=
  forall (R:A->B->Prop),
  (forall x:A, #exists y:B, R x y) ->
  #exists f:A->B, forall x:A, #R x (f x).
Definition Tunique_choice A B (E:B->B->Prop) :=
  forall (R:A->B->Prop),
  (forall x:A, #exists y:B, R x y) ->
  (forall x y y', R x y -> (R x y' <-> E y y')) ->
  #exists f:A->B, forall x:A, #R x (f x).

(** The level of sets *)
Definition Thi := Type.

(** The level of indexes *)
Definition Tlo : Thi := Type.

Inductive set_ : Thi :=
  sup (X:Tlo) (f:X->set_).
Definition set := set_.

Definition idx (x:set) := let (X,_) := x in X.
Definition elts (x:set) : idx x -> set :=
  match x return idx x -> set with
  | sup X f => f
  end.

(** Equality and membership *)

Fixpoint eq_set (x y:set) {struct x} :=
  (forall i, #exists j, eq_set (elts x i) (elts y j)) /\
  (forall j, #exists i, eq_set (elts x i) (elts y j)).

Lemma eq_set_def x y :
  eq_set x y <->
  (forall i, #exists j, eq_set (elts x i) (elts y j)) /\
  (forall j, #exists i, eq_set (elts x i) (elts y j)).
destruct x; destruct y; simpl; intros.
reflexivity.
Qed.

Lemma eq_set_isL : forall x y, isL(eq_set x y).
intros; rewrite eq_set_def; auto.
Qed.
Global Hint Resolve eq_set_isL : core.

Lemma eq_set_intro x y :
  (forall i, exists j, eq_set (elts x i) (elts y j)) ->
  (forall j, exists i, eq_set (elts x i) (elts y j)) ->
  eq_set x y.
intros.
rewrite eq_set_def; split; intros; Tin; auto.
Qed.

Lemma eq_set_refl : forall x, eq_set x x.
induction x.
apply eq_set_intro; simpl; intros i; exists i; trivial.
Qed.

Lemma eq_set_sym : forall x y,
  eq_set x y -> eq_set y x.
induction x; intros.
rewrite eq_set_def in H0|-*.
destruct H0; split; intros i.
 Tdestruct (H1 i).
 Texists x; auto.

 Tdestruct (H0 i).
 Texists x; auto.
Qed.

Lemma eq_set_trans : forall x y z,
  eq_set x y -> eq_set y z -> eq_set x z.
induction x; destruct y; destruct z; intros.
rewrite eq_set_def in H0,H1|-*.
destruct H0; destruct H1; split; intros i.
 Tdestruct (H0 i).
 Tdestruct (H1 x).
 Texists x0; eauto.

 Tdestruct (H3 i).
 Tdestruct (H2 x).
 Texists x0; eauto.
Qed.

Definition in_set x y :=
  #exists j, eq_set x (elts y j).

Lemma in_set_isL : forall x y, isL (in_set x y).
intros; apply Tr_isL.
Qed.
Global Hint Resolve in_set_isL : core.

Notation "x ∈ y" := (in_set x y) (at level 60).
Notation "x == y" := (eq_set x y) (at level 70).

Lemma eq_set_ax : forall x y,
  x == y <-> (forall z, z ∈ x <-> z ∈ y).
intros.
rewrite eq_set_def.
split; intros.
 destruct H; split; intros.
  Tdestruct H1.
  Tdestruct (H x0).
  Texists x1.
  apply eq_set_trans with (elts x x0); trivial.

  Tdestruct H1.
  Tdestruct (H0 x0).
  Texists x1.
  apply eq_set_trans with (elts y x0); trivial.
  apply eq_set_sym; trivial.

 split; intros.
  apply H.
  Texists i; apply eq_set_refl.

  assert (elts y j ∈ y).
   Texists j; apply eq_set_refl.
  apply H in H0.
  Tdestruct H0; intros.
  Texists x0.
  apply eq_set_sym; trivial.
Qed.

Lemma in_reg : forall x x' y,
  x == x' -> x ∈ y -> x' ∈ y.
intros.
Tdestruct H0.
Texists x0.
apply eq_set_trans with x; trivial.
apply eq_set_sym; trivial.
Qed.

Lemma eq_intro : forall x y,
  (forall z, z ∈ x -> z ∈ y) ->
  (forall z, z ∈ y -> z ∈ x) ->
  x == y.
intros.
rewrite eq_set_ax.
split; intros; eauto.
Qed.

Lemma eq_elim : forall x y y',
  x ∈ y ->
  y == y' ->
  x ∈ y'.
intros.
rewrite eq_set_ax in H0.
destruct (H0 x); auto.
Qed.

Instance in_set_morph : Proper (eq_set ==> eq_set ==> iff) in_set.
do 3 red; intros.
split; intros.
 apply in_reg with x; trivial.
 apply eq_elim with x0; trivial.

 apply eq_set_sym in H.
 apply eq_set_sym in H0.
 apply in_reg with y; trivial.
 apply eq_elim with y0; trivial.
Qed.

Definition el (x:set) := {z|z ∈ x}.
Definition eli x y (h:y ∈ x): el x := exist (fun z=>z∈ x) y h.

Definition elts' (x:set) (i:idx x) : el x.
exists (elts x i).
abstract (Texists i; apply eq_set_refl).
Defined.

Lemma eq_elim1 x y : el x -> x == y -> el y.
intros z eqxy.
exists (proj1_sig z).
apply eq_elim with x; trivial.
apply proj2_sig.
Defined.

Lemma incl_elim1 x y :
  el x -> (forall z, z ∈ x -> z ∈ y) -> el y.
intros z eqxy.
exists (proj1_sig z).
apply eqxy.
apply proj2_sig.
Defined.

(** Set induction *)

Lemma wf_ax0 :
  forall (P:set->Prop),
  (forall x, isL (P x)) ->
  (forall x, (forall y, y ∈ x -> P y) -> P x) ->
  forall x, P x.
intros P PisL H x.
cut (forall x', x == x' -> P x');[auto using eq_set_refl|].
induction x; intros.
apply H; intros.
apply eq_set_sym in H1.
apply eq_elim with (2:=H1) in H2.
Tdestruct H2.
apply H0 with x.
apply eq_set_sym; trivial.
Qed.

Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, (forall y, y ∈ x -> #P y) -> #P x) ->
  forall x, #P x.
intros P H x.
cut (forall x', x == x' -> #P x');[auto using eq_set_refl|].
induction x; intros.
apply H; intros.
apply eq_set_sym in H1.
apply eq_elim with (2:=H1) in H2.
Tdestruct H2.
apply H0 with x.
apply eq_set_sym; trivial.
Qed.

(***********************************************************)
(** Empty set *)

Definition empty :=
  sup False (fun x => match x with end).

Lemma empty_ax : forall x, x ∈ empty -> #False.
intros.
Tdestruct H.
Tin; trivial.
Qed.

(** Singleton and pairs *)

Definition singl x := sup unit (fun _ => x).

Definition pair x y :=
  sup bool (fun b => if b then x else y).

Lemma pair_ax : forall a b z,
  z ∈ pair a b <-> #(z == a \/ z == b).
split; intros.
 Tdestruct H.
 Tin; destruct x; auto.

 Tdestruct H.
  Texists true; trivial.
  Texists false; trivial.
Qed.

Lemma pair_morph :
  forall a a', a == a' -> forall b b', b == b' ->
  pair a b == pair a' b'.
intros.
rewrite eq_set_ax; intros.
do 2 rewrite pair_ax.
split; intros.
 Tdestruct H1.
  Tleft; apply eq_set_trans with a; trivial.
  Tright; apply eq_set_trans with b; trivial.

 apply eq_set_sym in H.
 apply eq_set_sym in H0.
 Tdestruct H1.
  Tleft; apply eq_set_trans with a'; trivial.
  Tright; apply eq_set_trans with b'; trivial.
Qed.

(** Union *)

Record union_idx x := mkUi {
  un_i : idx x;
  un_j : idx(elts x un_i)
}.

Definition union (x:set) :=
  sup (union_idx x)
    (fun p => elts (elts x (un_i _ p)) (un_j _ p)).

Lemma union_ax : forall a z,
  z ∈ union a <-> #exists2 b, z ∈ b & b ∈ a.
split; intros.
 Tdestruct H.
 destruct x as (i,j); simpl in *.
 Texists (elts a i).
  Texists j; trivial.

  Texists i; apply eq_set_refl.

 Tdestruct H.
 Tdestruct H0.
 specialize eq_elim with (1:=H) (2:=H0); intro.
 Tdestruct H1.
 unfold union.
 Texists (mkUi _ x0 x1); simpl; trivial.
Qed.

Lemma union_morph :
  forall a a', a == a' -> union a == union a'.
intros.
rewrite eq_set_ax; intros.
rewrite union_ax; rewrite union_ax.
split; intros.
 Tdestruct H0.
 Texists x; trivial.
 apply eq_elim with a; trivial.

 apply eq_set_sym in H.
 Tdestruct H0.
 Texists x; trivial.
 apply eq_elim with a'; trivial.
Qed.

(** Separation axiom *)

Record subset_idx x (P:set->Prop) := mkSi {
  sb_i : idx x;
  sb_spec : #exists2 x', elts x sb_i == x' & P x'
}.

Definition subset (x:set) (P:set->Prop) :=
  sup (subset_idx x P) (fun y => elts x (sb_i _ _ y)).

Lemma subset_ax : forall x P z,
  z ∈ subset x P <->
  z ∈ x /\ #exists2 z', z == z' & P z'.
intros x P z.
split; intros.
 Tdestruct H.
 destruct x0 as (i,h); simpl in *.
 split.
  Texists i; trivial.

  Tdestruct h as (x',?,?).
  Texists x'; trivial.
  apply eq_set_trans with (elts x i); trivial.

 destruct H.
 Tdestruct H0.
 Tdestruct H.
 assert (#exists2 x', elts x x1 == x' & P x').
  Texists x0; trivial.
  apply eq_set_trans with z; trivial.
  apply eq_set_sym; trivial.
 Texists (mkSi x P x1 H2); trivial.
Qed.

(** Power-set axiom *)

Definition power (x:set) :=
  sup (idx x->Prop)
   (fun P => subset x
         (fun y => #exists2 i, y == elts x i & P i)).

Lemma power_ax : forall x z,
  z ∈ power x <->
  (forall y, y ∈ z -> y ∈ x).
split; intros.
 Tdestruct H.
 specialize eq_elim with (1:=H0)(2:=H); intro.
 simpl in H1; rewrite subset_ax in H1.
 destruct H1; trivial.

 Texists (fun i => elts x i ∈ z).
 apply eq_intro; intros.
  simpl; rewrite subset_ax.
  split; auto.
  Texists z0;[apply eq_set_refl|].
  specialize H with (1:=H0).
  Tdestruct H.
  Texists x0; trivial.
  apply in_reg with z0; trivial.

  simpl in H0; rewrite subset_ax in H0.
  destruct H0.
  Tdestruct H1.
  Tdestruct H2.
  apply in_reg with (elts x x1); trivial.
  apply eq_set_sym.
  apply eq_set_trans with x0; trivial.
Qed.

Lemma power_morph : forall x x', x == x' -> power x == power x'.
intros.
rewrite eq_set_ax; intros.
do 2 rewrite power_ax.
apply fa_morph; intro y.
apply fa_morph; intros _.
assert (H' := eq_set_sym _ _ H).
split; intros; eapply eq_elim; eassumption.
Qed.

(** Infinity *)

Fixpoint num (n:nat) : set :=
  match n with
  | 0 => empty
  | S k => union (pair (num k) (pair (num k) (num k)))
  end.

Definition infinite := sup _ num.

Lemma infinity_ax1 : empty ∈ infinite.
Texists 0.
apply eq_set_refl.
Qed.

Lemma infinity_ax2 : forall x, x ∈ infinite ->
  union (pair x (pair x x)) ∈ infinite.
intros.
Tdestruct H.
Texists (S x0); simpl elts.
apply union_morph.
apply pair_morph; trivial.
apply pair_morph; trivial.
Qed.


(** Functional Replacement *)

Definition replf (x:set) (F:set->set) :=
  sup _ (fun i => F (elts x i)).

Lemma replf_ax : forall x F z,
  (forall z z', z ∈ x -> z == z' -> F z == F z') ->
  (z ∈ replf x F <-> #exists2 y, y ∈ x & z == F y).
split; intros.
 Tdestruct H0.
 Texists (elts x x0); trivial.
 Texists x0; apply eq_set_refl.

 Tdestruct H0.
 assert (h:=H0); Tdestruct h.
 Texists x1.
 apply eq_set_trans with (F x0); trivial.
 apply H; trivial.
Qed.

(** Functional replacement with domain information *)

Definition repl1 (x:set) (F:el x->set) :=
  sup _ (fun i => F (elts' x i)).

Lemma repl1_ax : forall x F z,
  (forall z z', proj1_sig z == proj1_sig z' -> F z == F z') ->
  (z ∈ repl1 x F <-> #exists y, z == F y).
split; intros.
 Tdestruct H0.
 Texists (elts' x x0); trivial.

 Tdestruct H0.
 destruct x0.
 Tdestruct i.
 Texists x1.
 apply eq_set_trans with (1:=H0).
 apply H; trivial.
Qed.

Lemma repl1_mono x y F G :
  (forall z, z ∈ x -> z ∈ y) ->
  (forall x' y', proj1_sig x' == proj1_sig y' -> F x' == G y') ->
  (forall z, z ∈ repl1 x F -> z ∈ repl1 y G).
intros inclxy eqFG.
assert (forall x' y', proj1_sig x' == proj1_sig y' -> F x' == F y').
 intros z z' eqz.
 apply eq_set_trans with (G (incl_elim1 _ _ z' inclxy)).
  apply eqFG; simpl; trivial.

  apply eq_set_sym; apply eqFG; simpl; apply eq_set_refl.
intros.
rewrite repl1_ax in H0; trivial.
Tdestruct H0 as (w,e).
Tdestruct (inclxy _ (proj2_sig w)) as (j, e').
Texists j; simpl.
apply eq_set_trans with (1:=e).
apply eqFG; simpl; trivial.
Qed.

Lemma repl1_morph : forall x y F G,
  x == y ->
  (forall x' y', proj1_sig x' == proj1_sig y' -> F x' == G y') ->
  repl1 x F == repl1 y G.
intros; rewrite eq_set_ax; split; apply repl1_mono; intros; auto.
 apply eq_elim with x; trivial.

 apply eq_elim with y; trivial.
 apply eq_set_sym; trivial.

 apply eq_set_sym; apply H0.
 apply eq_set_sym; trivial.
Qed.

Section WellFoundedRecursion.
Variable f : set -> set.
Hypothesis fm : Proper (eq_set==>eq_set) f.

Fixpoint WFR (x:set) (p:Acc in_set x) {struct p} : set :=
  f (repl1 x (fun (y:el x) =>
               WFR (proj1_sig y) (Acc_inv p (proj2_sig y)))).

Lemma WFR_eqn x p : WFR x p == f (repl1 x (fun y => WFR _ (Acc_inv p (proj2_sig y)))).
destruct p; simpl.
apply eq_set_refl.
Qed.

Lemma WFR_irrel x p x' p' : x==x' -> WFR x p == WFR x' p'.
revert x p x' p'.
fix WFRi 2.
destruct p; simpl; intros.
apply eq_set_trans with (2:=eq_set_sym _ _ (WFR_eqn x' p')).
apply fm; apply repl1_morph; intros; trivial.
apply WFRi; trivial.
Qed.

End WellFoundedRecursion.

(***********************************************************************)

(** Statement of useful axioms (independently of the logic used):
    - TTRepl
    - TTColl
    They are both consequence of [choice] *)

(** TTColl *)
Definition ttcoll (E:set->set->Prop) :=
  forall (X:Tlo) (R:X->set->Prop),
  (forall i, Proper (E==>iff) (R i)) ->
  #exists (Y:Tlo) (g:Y->set),
    forall i, (#exists w, R i w) -> #exists j:Y, R i (g j).

Lemma ttcoll_mono (E E':set->set->Prop) :
  (forall x y, E x y -> E' x y) ->
  ttcoll E -> ttcoll E'.
unfold ttcoll; intros.
apply H0; intros; auto.
do 2 red; intros.
apply H1; auto.
Qed.

Module OtherCollectionAxioms.

Definition streicher_ttcoll :=
  forall (A:Tlo) (X:Thi) (e:X->A),
  (forall y:A, #exists x:X, e x = y) ->
  #exists (C:Tlo) (f:C->X),
    forall y:A, #exists x:C, e (f x) = y.

Lemma ttcoll_impl1 E :
  streicher_ttcoll -> ttcoll E.
red; intros.
clear E H0.
red in H.
pose (X':= {x:X|exists y:set, R x y}).
pose (Y := { a:X' & { y:set | R (proj1_sig a) y}}).
assert (tot : forall y : X', #exists x : Y, projT1 x = y).
{destruct y as (x,(y,?)); simpl.
 Texists (existT (fun a:X'=>{y:set|R(proj1_sig a) y}) (exist _ x (ex_intro _ y r)) (exist (fun y => R x y) y r)).
 simpl.
 reflexivity. }
Tdestruct (H X' Y (fun y => projT1 y) tot) as (C,(f,Hf)).
Texists C.
exists (fun c => proj1_sig (projT2 (f c))).
intros.
Telim H0; intros H0.
Tdestruct (Hf (exist (fun x => exists y, _) i H0)) as (c,?).
Texists c.
assert (h := proj2_sig (projT2 (f c))).
simpl in h.
pattern (projT1 (f c)) in h at 1.
rewrite H1 in h.
simpl in h.
trivial.
Qed.

Definition miquel_dom A (P:A->Prop) (R:A->Type->Prop) :=
  (forall x B B' (f:B->B'),
   (forall b1 b2, f b1 = f b2 -> b1 = b2) ->
   R x B -> R x B') ->
  (forall x, P x -> exists B, R x B) ->
  exists B, forall x, P x -> R x B.

End OtherCollectionAxioms.


(** TTColl is a consequence of choice *)

Record ttcoll_dom (X:Tlo) (R:X->set->Prop) : Tlo := mkCi {
  cd_i:X;
  cd_dom : exists y, R cd_i y
}.

(** We show that all instances of [ttcoll] are a consequence of [choice]. *)
Lemma ttcoll_from_choice E :
  (forall (X:Tlo), choice X set) -> ttcoll E.
red; intros choice_ax X R _Rm; clear _Rm. (* We don't need that R is a morphism *)
destruct (choice_ax (ttcoll_dom X R) (fun i y => R (cd_i _ _ i) y)) as (f,Hf).
 intros; apply (cd_dom _ _ x).

 Texists (ttcoll_dom X R).
 exists f.
 intros.
 Telim H; intros H.
 Texists (mkCi _ _ i H).
 apply (Hf (mkCi _ _ i H)).
Qed.

(** TTRepl *)
Definition ttrepl (E:set->set->Prop) :=
  forall X:Tlo, Tunique_choice X set E.

(** We show that all instances of [ttrepl] are a consequence of [choice]. *)
Lemma ttrepl_from_choice E :
  (forall X:Tlo, Tchoice X set) -> ttrepl E.
red; red; intros choice_ax X R Rex _Runiq; clear _Runiq. (* unicity not needed *)
apply choice_ax; trivial.
Qed.


(** TTColl is stronger than TTRepl *)
Lemma ttrepl_from_ttcoll : ttcoll eq_set -> ttrepl eq_set.
red; red; intros ttcoll_ax X R Rex Runiq.
assert (Rm : forall i : X, Proper (eq_set ==> iff) (R i)).
{do 2 red; intros.
 split; intros.
  apply Runiq with x; trivial.
  apply Runiq with y; trivial.
  apply eq_set_sym; trivial. }
Tdestruct (ttcoll_ax X R Rm) as (Y,(g,HB)).
Texists (fun i => union (subset (sup Y g) (fun y => R i y))).
intros i.
Tdestruct (Rex i) as (y,Hy).
Tin.
assert (y == union (subset (sup Y g) (fun y => R i y))).
{apply eq_intro; intros.
  rewrite union_ax.
  Texists y; trivial.
  rewrite subset_ax.
  split.
  assert (exR : #exists w, R i w) by (Texists y; trivial).
  Tdestruct (HB i exR) as (j,?); trivial.
   Texists j; simpl.
   apply Runiq with i; trivial.

   Texists y; trivial.
   apply eq_set_refl.

 rewrite union_ax in H.
 Tdestruct H as (b, ?, ?).
 rewrite subset_ax in H0; destruct H0.
 Tdestruct H1 as (b', ?, ?).
 apply eq_elim with b; trivial.
 apply eq_set_trans with b'; trivial.
 apply Runiq with i; trivial. }
apply Runiq with y; trivial.
Qed.


(** Relation between ttrepl/ttcoll and replacement/collection,
    intuitionistically and classically. *)

Section ReplacementFromTTRepl.
  
Record repl_dom a (R:set->set->Prop) := mkRi {
  rd_i : idx a;
  rd_dom : #exists y, R (elts a rd_i) y
}.

(** Showing that TTRepl implies Replacement.
    This proofs requires that we are in the intuitionistic fragment.
    If L is classical logic, we would have a model of ZF in Coq+TTRepl.
 *)

Lemma weak_uniq_R : forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    (forall x x' y y', x ∈ a -> R x y -> R x' y' -> x == x' -> y == y').
intros.
apply H0 with x; trivial.
revert H3; apply H.
 apply in_reg with x; trivial.

 apply eq_set_sym; trivial.

 apply eq_set_refl.
Qed.

Hypothesis ttrepl_axiom : ttrepl eq_set.

Lemma ttrepl_implies_repl_ex (a:set) (R:set->set->Prop) :
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    #exists b, forall x, x ∈ b <-> #exists2 y, y ∈ a & R y x.
intros.
assert (exR : forall x : repl_dom a R, # (exists y : set, R (elts a (rd_i a R x)) y)).
{destruct x as (i,h); simpl; trivial. }
assert (uniqR : forall x y y',
            R (elts a (rd_i a R x)) y -> R (elts a (rd_i a R x)) y' <-> y == y').
{split; intros.
  apply H0 with (elts a (rd_i _ _ x)); trivial.
  red; simpl.
  Texists (rd_i _ _ x); apply eq_set_refl.

  revert H1; apply H; trivial.
   Texists (rd_i _ _ x); apply eq_set_refl.

   apply eq_set_refl. }
Tdestruct (ttrepl_axiom (repl_dom a R)
        (fun i y => R (elts a (rd_i _ _ i)) y) exR uniqR) as (f,?); intros.
Texists (sup _ f).
unfold in_set at 1; simpl.
split; intros.
 Tdestruct H2 as (j,?).
 Telim (H1 j); intro.
 Texists (elts a (rd_i _ _ j)).
  apply (proj2_sig (elts' a _)).

  revert H3; apply H.
   apply (proj2_sig (elts' a _)).

   apply eq_set_refl.

   apply eq_set_sym; trivial.

  Tdestruct H2.
  assert (h:=H2); Tdestruct h as (i,?).
  assert (R (elts a i) x).
  {revert H3; apply H; trivial.
   apply eq_set_refl. }
  assert (#exists y, R (elts a i) y).
  {Texists x; trivial. }
  Texists (mkRi _ _ i H6).
  Telim (H1 (mkRi _ _ i H6)); simpl; intro.
  apply H0 with (elts a i); trivial.
  Texists i; apply eq_set_refl.
Qed.
End ReplacementFromTTRepl.

Module Type HasTTReplacement.
  Parameter ttrepl_ax : ttrepl eq_set.
End HasTTReplacement.

Module MakeRepl (R : HasTTReplacement).

  Lemma repl_ex a (R:set->set->Prop) :
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    #exists b, forall x, x ∈ b <-> #exists2 y, y ∈ a & R y x.
Proof.
apply ttrepl_implies_repl_ex.
exact R.ttrepl_ax.
Qed.

End MakeRepl.

(** Collection *)
Section Collection.

  (** We now show that TTColl implies (set-theoretical) collection *)
Hypothesis ttcoll_axiom : ttcoll eq_set.

(* ttcoll rephrased on sets: *)
Lemma ttcoll_set A (R:set->set->Prop) :
  Proper (eq_set==>eq_set==>iff) R ->
  #exists z, forall i, (#exists w, R (elts A i) w) ->
             #exists j, R (elts A i) (elts z j).
intros.
assert (Rm : forall i, Proper (eq_set ==> iff) (fun y : set => R (elts A i) y)).
{intros; apply H; apply eq_set_refl. }
Tdestruct (ttcoll_axiom (idx A) (fun i y => R (elts A i) y) Rm) as (Y,(g,Hg)).
Texists (sup Y g); trivial.
Qed.

(* Collection axiom out of TTColl: *)
Lemma collection_ax : forall A (R:set->set->Prop), 
    Proper (eq_set==>eq_set==>iff) R ->
    #exists B, forall x, x ∈ A ->
      (#exists y, R x y) ->
      (#exists2 y, y ∈ B & R x y).
intros A R Rm.
Tdestruct (ttcoll_set A R Rm) as (B,HB); trivial.
Texists B; intros x inA H0.
Tdestruct H0 as (w, Rxw).
assert (h:=inA); Tdestruct h as (i, eqx).
assert (wit : # exists w, R (elts A i) w).
{Texists w.
 revert Rxw; apply Rm; trivial.
  apply eq_set_sym; trivial.
  apply eq_set_refl. }
Tdestruct (HB i wit) as (j,Rxy).
Texists (elts B j).
 apply (proj2_sig (elts' B j)).

 revert Rxy; apply Rm; trivial.
 apply eq_set_refl.
Qed.

Lemma collection_ax_total : forall A (R:set->set->Prop), 
    Proper (eq_set==>eq_set==>iff) R ->
    (forall x, x ∈ A -> (#exists y, R x y)) ->
    #exists B, forall x, x ∈ A -> #exists2 y, y ∈ B & R x y.
intros.
Tdestruct (collection_ax A R H) as (B,HB); trivial.
Texists B; auto.
Qed.

(** Comparison of replacement and collection *)


(* Replacement as a weaker form of collection.
   This is stronger than combining ttrepl_from_ttcoll with intuit_repl_ax because
   we would need to be intuitionistic
 *)

Definition mkRel (R:set->set->Prop) x y :=
  exists2 x', x==x' & exists2 y', y==y' & R x' y'.

Instance mkRel_morph R : Proper (eq_set==>eq_set==>iff) (mkRel R).
unfold mkRel; do 3 red; intros.
apply ex2_morph; red; intros.
 split; intros.
  apply eq_set_trans with x; trivial.
  apply eq_set_sym; trivial.

  apply eq_set_trans with y; trivial.
apply ex2_morph; red; intros; auto with *.
split; intros.
 apply eq_set_trans with x0; trivial.
 apply eq_set_sym; trivial.

 apply eq_set_trans with y0; trivial.
Qed.

Lemma repl_from_collection : forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    #exists b, forall x, x ∈ b <-> #exists2 y, y ∈ a & R y x.
intros a R Rm Ru.
assert (Rfun : forall x x' y y', x ∈ a -> R x y -> R x' y' -> x == x' -> y == y').
 apply weak_uniq_R; trivial.
Tdestruct (collection_ax a (mkRel R) (mkRel_morph R)) as (B,HB).
Texists (subset B (fun y => exists2 x, x ∈ a & R x y)); split; intros.
 rewrite subset_ax in H; destruct H.
 Tdestruct H0 as (y,?,(x',?,?)).
 Texists x'; trivial.
 revert H2; apply Rm; trivial.
  apply eq_set_refl.
  apply eq_set_sym; trivial.

 Tdestruct H as (x',?,?).
 rewrite subset_ax; split.
  elim HB with x' using Tr_ind; clear HB; trivial.
   intros (y',?,(x'',?,(y'',?,?))).
   apply in_reg with y'; trivial.
   apply eq_set_trans with y''; trivial.
   apply Rfun with x'' x'; trivial.
    apply in_reg with x'; trivial.
    apply eq_set_sym; trivial.

   Texists x.
   exists x'; [apply eq_set_refl|].
   exists x; auto using eq_set_refl.

 Texists x; trivial.
  apply eq_set_refl.
 exists x'; auto.
Qed.

End Collection.

(* Deriving the existentially quantified sets *)

Lemma empty_ex: #exists empty, forall x, x ∈ empty -> Tr False.
Texists empty.
exact empty_ax.
Qed.

Lemma pair_ex: forall a b,
  #exists c, forall x, x ∈ c <-> Tr(x == a \/ x == b).
intros.
Texists (pair a b).
apply pair_ax.
Qed.

Lemma union_ex: forall a, #exists b,
    forall x, x ∈ b <-> #exists2 y, x ∈ y & y ∈ a.
intros.
Texists (union a).
apply union_ax.
Qed.

Lemma subset_ex : forall a P, #exists b,
    forall x, x ∈ b <-> x ∈ a /\ #exists2 x', x == x' & P x'.
intros.
Texists (subset a P).
apply subset_ax.
Qed.

Lemma power_ex: forall a, #exists b,
     forall x, x ∈ b <-> (forall y, y ∈ x -> y ∈ a).
intros.
Texists (power a).
apply power_ax.
Qed.

(* Infinity *)

Lemma infinity_ex: #exists2 infinite,
    (#exists2 empty, (forall x, x ∈ empty -> Tr False) & empty ∈ infinite) &
    (forall x, x ∈ infinite ->
     #exists2 y,
       (forall z, z ∈ y <-> #(z == x \/ z ∈ x)) &
       y ∈ infinite).
Texists infinite.
 Texists empty.
  exact empty_ax.
  exact infinity_ax1.

 intros.
 Texists (union (pair x (pair x x))); intros.
  rewrite union_ax.
  split; intros.
   Tdestruct H0.
   rewrite pair_ax in H1.
   Tdestruct H1.
    Tright; apply eq_elim with x0; trivial.

    specialize eq_elim with (1:=H0) (2:=H1); intro.
    rewrite pair_ax in H2.
    Tdestruct H2; Tin; auto.

   Tdestruct H0.
    Texists (pair x x).
     rewrite pair_ax; Tleft; auto.

     rewrite pair_ax; Tright; apply eq_set_refl.

    Texists x; trivial.
    rewrite pair_ax; Tleft; apply eq_set_refl.

  apply infinity_ax2; trivial.
Qed.

(** Showing that in classical logic, collection can be made
   deterministic, by building the smallest element of
   Veblen hierarchy containing the images *)

Section ClassicalCollectionFromReplacement.

(** Veblen cumulative hierarchy (applied to any set) *)
Fixpoint V (x:set) := union (replf x (fun x' => power (V x'))).

Lemma V_morph : forall x x', x == x' -> V x == V x'.
induction x; destruct x'; intros.
simpl V; unfold replf; simpl union.
apply union_morph.
rewrite eq_set_def in H0; simpl in H0.
destruct H0.
apply eq_intro; intros.
 Tdestruct H2.
 Tdestruct (H0 x).
 Texists x0; simpl.
 apply eq_set_trans with (1:=H2).
 apply power_morph.
 auto.

 Tdestruct H2.
 Tdestruct (H1 x).
 simpl in *.
 Texists x0; simpl.
 apply eq_set_trans with (1:=H2).
 apply eq_set_sym.
 apply power_morph.
 auto.
Qed.

Lemma V_def : forall x z,
  z ∈ V x <-> #exists2 y, y ∈ x & z ∈ power (V y).
destruct x; simpl; intros.
rewrite union_ax.
unfold replf; simpl.
split; intros.
 Tdestruct H.
 Tdestruct H0; simpl in *.
 Texists (f x0).
  Texists x0; apply eq_set_refl.

  specialize eq_elim with (1:=H) (2:=H0); intro; trivial.

 Tdestruct H.
 Tdestruct H; simpl in *.
 Texists (power (V x)); trivial.
 Texists x0; simpl elts.
 apply power_morph.
 apply V_morph; trivial.
Qed.


Lemma V_trans : forall x y z,
  z ∈ y -> y ∈ V x -> z ∈ V x.
intros x.
(*apply (fun h => @Tr_ind _ _ h (fun x=>x)); auto.*)
apply wf_ax0 with (P:=fun x => forall y z, z ∈ y -> y ∈ V x -> z ∈ V x) (x:=x); auto.
clear x; intros.
rewrite V_def in H1|-*.
Tdestruct H1.
Texists x0; trivial.
rewrite power_ax in H2|-*; eauto.
Qed.

Lemma V_pow : forall x, power (V x) == V (singl x).
intros.
apply eq_intro; intros.
 rewrite V_def.
 Texists x; trivial.
 Texists tt; apply eq_set_refl.

 rewrite V_def in H.
 Tdestruct H.
 Tdestruct H; simpl in *.
 apply eq_elim with (power (V x0)); auto.
 apply power_morph.
 apply V_morph; trivial.
Qed.

Lemma V_mono : forall x x',
  x ∈ x' -> V x ∈ V x'.
intros.
rewrite (V_def x').
Texists x; trivial.
rewrite power_ax; auto.
Qed.

Lemma V_sub : forall x y y',
  y ∈ V x -> y' ∈ power y -> y' ∈ V x.
intros.
rewrite V_def in H|-*.
Tdestruct H.
Texists x0; trivial.
rewrite power_ax in H0,H1|-*; auto.
Qed.

Lemma V_compl : forall x z, z ∈ V x <-> V z ∈ V x. 
intros x.
pattern x; apply wf_ax0; clear x; intros; auto.
repeat rewrite V_def.
split; intros.
 Tdestruct H0.
 Texists x0; trivial.
 rewrite power_ax in H1|-*; intros.
 rewrite V_def in H2.
 Tdestruct H2.
 apply H1 in H2.
 rewrite H in H2; trivial.
 apply V_sub with (V x1); trivial.

 Tdestruct H0.
 Texists x0; trivial.
 rewrite power_ax in H1|-*; intros.
 rewrite H; trivial.
 apply H1.
 apply V_mono; trivial.
Qed.

Lemma V_comp2 x y : x ∈ power (V y) -> V x ∈ power (V y).
intros.
apply eq_elim with (V (singl y)).
2:apply eq_set_sym; apply V_pow.
apply -> V_compl.
apply eq_elim with (1:=H).
apply V_pow.
Qed.

Lemma V_intro : forall x, x ∈ power (V x).
intros x.
rewrite power_ax; intros.
rewrite V_compl; apply V_mono; trivial.
Qed.

Lemma V_idem : forall x, V (V x) == V x.
intros.
apply eq_intro; intros.
 rewrite V_def in H.
 Tdestruct H.
 apply V_sub with (V x0); trivial.
 rewrite <- V_compl; trivial.

 apply V_sub with (V z).
  apply V_mono; trivial.
  apply V_intro.
Qed.

Lemma rk_induc :
  forall P:set->Prop,
  (forall x, isL (P x)) ->
  (forall x, (forall y, y ∈ V x -> P y) -> P x) ->
  forall x, P x.
intros.
cut (forall y, V y ∈ power (V x) -> P y).
 intros.
 apply H1.
 rewrite power_ax; auto.
apply wf_ax0 with (x:=x); intros; auto.
apply H0; intros.
rewrite power_ax in H2; specialize H2 with (1:=H3).
rewrite V_def in H2.
Tdestruct H2.
apply H1 with x1; trivial.
apply V_comp2; trivial.
Qed.

Hypothesis EM : forall A, #(A \/ #¬A).

(** Classical proof that the rank of a set is totally ordered:
     rk(x) < rk(y) \/ rk(y) <= rk(x) *)
Lemma V_total : forall x y, #(V x ∈ V y \/ V y ∈ power (V x)).
intros x y.
revert x.
apply wf_ax0 with (x:=y); clear y; auto.
intros y Hy x.
Tdestruct (EM (#exists2 y', y' ∈ V y & V x ∈ power y')).
*Tleft.
 Tdestruct H.
 apply V_sub with x0; trivial.

*Tright; rewrite power_ax; intros.
 rewrite V_def in H0.
 Tdestruct H0.
 assert (#exists2 w, w ∈ V x & #¬ w ∈ V x0).
 {Tdestruct (EM (#(exists2 w, w ∈ V x & #¬ w ∈ V x0))); trivial.
  assert (V x ∈ power (V x0) -> #False).
  {intros; apply H.
   Texists (V x0); trivial.
   apply V_mono; trivial. }
  Tabsurd; apply H3; rewrite power_ax; intros.
  Tdestruct (EM (y1 ∈ V x0)); trivial.
  Tabsurd; apply H2.
  Texists y1; trivial. }
 Tdestruct H2.
 Tdestruct (Hy _ H0 x1).
  Tabsurd; apply H3.
  apply V_sub with (V x1); trivial.
  apply V_intro.

  apply V_sub with (V x1).
   apply -> V_compl; trivial.

   rewrite power_ax in H1,H4|-*; auto.
Qed.

Definition lst_rk (P:set->Prop) (y:set) :=
  P y /\
  y == V y /\
  forall x, x == V x -> P x -> y ∈ power x.

Lemma lst_rk_uniq P x y :
  lst_rk P x -> lst_rk P y -> x == y.
Proof.
intros (Px&rkx&lstx)(Py&rky&lsty).
apply eq_set_ax; split; apply power_ax; [apply lstx|apply lsty]; trivial.
Qed.

Lemma lst_rk_morph :
  forall (P P':set->Prop),
  (forall x x', x == x' -> (P x <-> P' x')) ->
  forall y y', y == y' -> lst_rk P y -> lst_rk P' y'.
intros.
unfold lst_rk in H1|-*.
destruct H1.
destruct H2.
split; [|split].
*revert H1; apply H; trivial.

*apply eq_set_trans with y;[apply eq_set_sym; trivial|].
 apply eq_set_trans with (V y); trivial.
 apply V_morph; trivial.

*intros.
 rewrite <-H with (x:=x) in H5;[|apply eq_set_refl].
 apply H3 in H5; [|trivial].
 apply in_reg with y; trivial.
Qed.

Lemma lst_incl : forall P y, lst_rk P y -> P y. 
intros.
destruct H as (?,_); trivial.
Qed.

(** Proof that if P is true for some Veblen universe, then
    we can find the least rank satisfying P. *)
Lemma lst_rk_ex : forall (P:set->Prop),
   Proper (eq_set==>iff) P ->
   (#exists x, P (V x)) ->
   (#exists x, lst_rk P x).
intros P Pm Pex.
Telim Pex; destruct 1.
revert H; apply rk_induc with (x:=x); clear x; intros; auto.
Tdestruct (EM (#exists2 z, z ∈ V x & P (V z))).
  Tdestruct H1; eauto.
 
  Texists (V x).
  unfold lst_rk; split; [trivial|split].
   apply eq_set_sym; apply V_idem.
 
   intros y ? ?.
   Tdestruct (V_total y x); auto.
    Tabsurd; apply H1.
    Texists y.
     apply in_reg with (V y); trivial.
     apply eq_set_sym; trivial.
     rewrite <- H2; trivial.

     rewrite power_ax in H4.
     rewrite power_ax; intros.
     apply eq_set_sym in H2.
     apply eq_elim with (V y); auto.
Qed.

(* We could also try to prove that B grows when A and R do. *)

Definition coll_unique_rel R (x v:set) :=
  lst_rk (fun v => exists2 y, R x y & y ∈ v) v.

Lemma coll_rel_morph A R (Rm:Proper (eq_set==>eq_set==>iff) R)(x x' y y' : set) :
  x ∈ A -> x == x' -> y == y' -> coll_unique_rel R x y -> coll_unique_rel R x' y'.
Proof.
unfold coll_unique_rel.
intros _ eqx; apply lst_rk_morph.
intros v v' eqv.
apply ex2_morph.
*red; intros; apply Rm;[trivial|apply eq_set_refl].
*red; intros; apply in_set_morph;[apply eq_set_refl|trivial].
Qed.

Lemma coll_rel_uniq A R (x y y' : set) :
  x ∈ A -> coll_unique_rel R x y -> coll_unique_rel R x y' -> y == y'.
Proof.
unfold coll_unique_rel.
intros _.
apply lst_rk_uniq.
Qed.

Lemma coll_rel_ex R x :
  (#exists y, R x y) ->
  #exists v, coll_unique_rel R x v.
Proof.
intros img.
Tdestruct img as (y,img).  
apply lst_rk_ex.
*do 2 red; intros.
 apply ex2_morph; red; intros; [reflexivity|].
 apply in_set_morph; [apply eq_set_refl|trivial].
*Texists (singl y); exists y; trivial.
 apply eq_elim with (power (V y)).
 +apply V_intro.
 +apply V_pow.
Qed.

Lemma coll_from_repl_gen A R coll x :
  x ∈ A ->
  # (exists y : set, R x y) ->
  (forall z x : set, x ∈ A -> coll_unique_rel R x z -> z ∈ coll) ->
  #exists2 y, y ∈ union coll & R x y.
Proof.
intros tyx img Hrepl.
Tdestruct (coll_rel_ex R x img) as (v, is_rk).
destruct (is_rk) as ((y',rel',inv),_).
Texists y';[|trivial].
apply union_ax.
Texists v; trivial.
apply Hrepl with x; trivial.
Qed.


Section Skolemized.

Variable repl : set -> (set->set->Prop) -> set.
Hypothesis repl_ax :
  forall a R,
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    forall z, z ∈ repl a R <-> #exists2 y, y ∈ a & R y z.


Definition coll_from_repl A R :=
  union (repl A (coll_unique_rel R)).

Lemma coll_ax_from_repl A R :
    Proper (eq_set==>eq_set==>iff) R ->
    forall x, x ∈ A ->
      (#exists y, R x y) -> #exists2 y, y ∈ coll_from_repl A R & R x y.
Proof.
intros Rm x tyx wit.
apply coll_from_repl_gen with (1:=tyx)(2:=wit).
clear x tyx wit; intros z x tyx img.
apply repl_ax.
*apply coll_rel_morph; trivial.
*apply coll_rel_uniq.
*Texists x; trivial.
Qed.

End Skolemized.

Section Existential.

Hypothesis repl_ex : forall a (R:set->set->Prop),
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    #exists b, forall x, x ∈ b <-> #exists2 y, y ∈ a & R y x.

Lemma coll_ex_from_repl A R :
    Proper (eq_set==>eq_set==>iff) R ->
    #exists B, forall x, x ∈ A ->
      (#exists y, R x y) -> #exists2 y, y ∈ B & R x y.
Proof.
intros Rm.
Tdestruct (repl_ex A (coll_unique_rel R) (coll_rel_morph A R Rm) (coll_rel_uniq A R))
  as (coll, Hcoll).
Texists (union coll).
intros x tyx wit.
apply coll_from_repl_gen with (1:=tyx)(2:=wit).
clear x tyx wit; intros z x tyx img.
apply Hcoll.
Texists x; trivial.
Qed.

End Existential.

End ClassicalCollectionFromReplacement.

End RawEnsembles.


(** This functor assumes ttrepl and provides an instance
    of IZF_R set theory (replacement not skolemized) *)
Module EnsZFRepl (L:SublogicTheory) <: IZF_R_HalfEx_sig L.
  Import L.
  Module E := RawEnsembles L.
  Include E.

  Axiom ttrepl_axiom : ttrepl eq_set.

  Lemma repl_ex a (R:set->set->Prop) :
    (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') ->
    (forall x y y', x ∈ a -> R x y -> R x y' -> y == y') ->
    #exists b, forall x, x ∈ b <-> #exists2 y, y ∈ a & R y x.
Proof.
apply ttrepl_implies_repl_ex.
exact ttrepl_axiom.
Qed.
End EnsZFRepl.

(** This functor assumes ttcoll and provides an instance
    of IZF_C set theory (collection not skolemized) *)
Module EnsZFColl (L:SublogicTheory) <: IZF_C_sig L.
  Import L.
  Module E := RawEnsembles L.
  Include E.

  Axiom ttcoll_axiom : ttcoll eq_set.

  Lemma coll_ex A (R:set->set->Prop) :
    Proper (eq_set ==> eq_set ==> iff) R ->
    #exists B, forall x, x ∈ A ->
         (#exists y, R x y) -> #exists2 y, y ∈ B & R x y.
Proof.
apply collection_ax.
exact ttcoll_axiom.
Qed.
End EnsZFColl.

Module IZFR_Axioms := EnsZFRepl CoqSublogicThms.

Import IZFR_Axioms.

(** Proving that ttrepl + EM => ttcoll
    If we could avoid EM, we would have that ttrepl
    gives Coq the strength of ZF
 *)
Lemma ttcoll_from_ttrepl_em : (forall P,P\/~P) -> ttrepl eq_set -> ttcoll eq_set.
intros EM ttrepl_ax X R Rm.
pose (P i v := exists2 x, x ∈ v & R i x).
destruct (@ttrepl_ax (ttcoll_dom X R)
  (fun i y => lst_rk (P (cd_i _ _ i)) y)) as (f,?).
{destruct x as (i,e); simpl.
 assert (exists x, P i (V x)).
 {destruct e.
  exists (singl x).
  red.
  exists x; trivial.
  apply eq_elim with (power (V x)).
  2:apply V_pow.
  apply V_intro. }
 apply lst_rk_ex with (1:=EM); trivial.
 do 2 red; intros.
 unfold P.
 apply ex2_morph; red; intros; auto with *.
 apply in_set_morph; [apply eq_set_refl|trivial]. }
{split; intros.
  apply lst_rk_uniq with (1:=H) (2:=H0).

  revert H; apply lst_rk_morph; intros; trivial.
  unfold P.
  apply ex2_morph; red; intros; auto with *.
  apply in_set_morph; [apply eq_set_refl|trivial]. }
(* main *)
pose (B := union (sup _ f)).
exists (idx B); exists (elts B).
intros.
specialize H with (mkCi _ _ i H0); simpl in H.
apply lst_incl in H.
red in H.
destruct H.
assert (x ∈ B).
 simpl.
 unfold B; rewrite union_ax.
 econstructor;[eexact H|].
 econstructor; eapply eq_set_refl.
destruct H2 as (j,?).
exists j.
revert H1; apply Rm.
apply eq_set_sym; trivial.
Qed.
