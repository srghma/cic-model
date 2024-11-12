
Require Import ZF.

Instance repl_mono_raw :
  Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl.
Proof repl_mono.

Instance repl_morph_raw :
  Proper (eq_set ==> (eq_set ==> eq_set ==> iff) ==> eq_set) repl.
do 3 red; intros.
apply eq_intro.
 apply repl_mono; auto; intros.
 rewrite <- H; trivial.

 symmetry in H0.
 apply repl_mono; auto; intros.
 rewrite H; trivial.
Qed.

Definition repl_rel a (R:set->set->Prop) :=
  (forall x x' y y', x ∈ a -> x == x' -> y == y' -> R x y -> R x' y') /\
  (forall x y y', x ∈ a -> R x y -> R x y' -> y == y').

Lemma repl_rel_fun : forall x f,
  ext_fun x f -> repl_rel x (fun a b => b == f a).
split; intros.
 rewrite <- H2; rewrite H3; auto.
 rewrite H1; rewrite H2; reflexivity.
Qed.

Lemma repl_intro : forall a R y x,
  repl_rel a R -> y ∈ a -> R y x -> x ∈ repl a R.
Proof.
intros a R y x (Rm,Rfun) H1 H2.
elim repl_ax with (1:=Rm) (2:=Rfun) (a := a) (x := x); intros.
apply H0.
exists y; trivial.
Qed.

Lemma repl_elim : forall a R x,
  repl_rel a R -> x ∈ repl a R -> exists2 y, y ∈ a & R y x.
Proof.
intros a R x (Rm,Rfun) H1.
elim repl_ax with (1:=Rm) (2:=Rfun) (a:=a) (x:=x); intros.
apply H in H1; clear H H0.
destruct H1.
exists x0; trivial.
Qed.

Lemma repl_ext : forall p a R,
  repl_rel a R ->
  (forall x y, x ∈ a -> R x y -> y ∈ p) ->
  (forall y, y ∈ p -> exists2 x, x ∈ a & R x y) ->
  p == repl a R.
Proof.
intros; apply eq_intro; intros.
 elim H1 with (1:=H2); intros.
 apply repl_intro with x; trivial.

 elim repl_elim with (1:=H) (2:=H2); intros; eauto.
Qed.

Lemma repl_mono2 : forall x y R,
  repl_rel y R ->
  x ⊆ y ->
  repl x R ⊆ repl y R.
red; intros.
assert (repl_rel x R).
 destruct H; split; intros; eauto.
apply repl_elim in H1; trivial.
destruct H1.
apply repl_intro with x0; auto.
Qed.


Lemma repl_empty : forall R, repl empty R == empty.
Proof.
intros.
apply empty_ext.
red; intros.
elim repl_elim with (2:=H); intros.
 elim empty_ax with x0; trivial.

 split; intros.
  elim empty_ax with x0; trivial.
  elim empty_ax with x0; trivial.
Qed.

(* unique choice *)
Definition uchoice (P : set -> Prop) : set :=
  union (repl (singl empty) (fun _ => P)).

Instance uchoice_morph_raw : Proper ((eq_set ==> iff) ==> eq_set) uchoice.
do 2 red; intros.
unfold uchoice.
apply union_morph.
apply repl_morph_raw; auto with *.
red; auto.
Qed.

Definition uchoice_pred (P:set->Prop) :=
  (forall x x', x == x' -> P x -> P x') /\
  (exists x, P x) /\
  (forall x x', P x -> P x' -> x == x').

Instance uchoice_pred_morph : Proper ((eq_set ==> iff) ==> iff) uchoice_pred.
apply morph_impl_iff1; auto with *.
do 3 red; intros.
destruct H0 as (?,(?,?)); split;[|split]; intros.
 assert (x x0).
  revert H4; apply H; auto with *.
 revert H5; apply H; trivial.

 destruct H1; exists x0.
 revert H1; apply H; auto with *.

 apply H2; [revert H3|revert H4]; apply H; auto with *.
Qed.


Lemma uchoice_ext : forall P x, uchoice_pred P -> P x -> x == uchoice P.
intros.
assert (repl_rel (singl empty) (fun _ => P)).
 destruct H.
 destruct H1.
 split; eauto.
unfold uchoice.
apply union_ext; intros.
 elim repl_elim with (2:=H3); clear H3; trivial; intros.
 rewrite (proj2 (proj2 H) _ _ H0 H4); trivial.

 exists x; trivial.
 apply repl_intro with empty; trivial.
 apply singl_intro.
Qed.

Lemma uchoice_def : forall P, uchoice_pred P -> P (uchoice P).
intros.
elim (proj1 (proj2 H)); intros.
apply (proj1 H x); trivial.
apply uchoice_ext; trivial.
Qed.

Lemma uchoice_morph : forall P P',
  uchoice_pred P ->
  (forall x, P x <-> P' x) ->
  uchoice P == uchoice P'.
intros.
elim (proj1 (proj2 H)); intros.
assert (P' x).
 elim (H0 x); auto.
assert (uchoice_pred P').
 destruct H.
 split; intros.
  apply (proj1 (H0 x')).
  apply H with x0; trivial.
  apply (proj2 (H0 x0)); auto.

  destruct H3.
  split; intros.
   destruct H3.
   exists x; trivial.

   apply H4.
    apply (proj2 (H0 x0)); trivial.
    apply (proj2 (H0 x')); trivial.
rewrite <- (uchoice_ext _ _ H H1).
apply uchoice_ext; trivial.
Qed.

Lemma uchoice_ax : forall P x,
  uchoice_pred P ->
  (x ∈ uchoice P <-> exists2 z, P z & x ∈ z).
intros.
specialize (uchoice_def _ H); intro.
split; intros.
 exists (uchoice P); trivial.

 destruct H1.
 destruct H.
 destruct H3.
 rewrite (H4 _ _ H0 H1); trivial.
Qed.


(* Relations between repl and uchoice *)
(*Lemma repl_rel_uchoice_pred A R :
  (forall x, x ∈ A -> uchoice_pred (R x)) ->
  repl_rel A R.
split; intros.
 destruct (H _ H0) as (?,_); eauto with *.

 destruct H as (?,?).
 split; [|split]; intros.
  destruct H; eauto with *.

  exists 
*)

(*
Lemma repl_is_choice A R :
  repl_rel A R ->
  repl A R == replf A (fun x => uchoice (R x)).
intros.
assert (ext_fun A (fun x => uchoice (R x))).
 destruct H as (?,_).
 do 2 red; intros.
 apply uchoice_morph_raw.
 red; intros.
 split; intros.
  apply H with x x0; auto with *.
  
  apply H with x' y; auto with *.
  rewrite <- H1; trivial.
apply eq_intro; intros.
 apply repl_elim in H1; trivial; destruct H1.
 rewrite replf_ax; trivial.
 exists x; trivial.
 apply uchoice_ext; trivial.
 destruct H as (?,?).
 split; [|split]; intros; eauto.
 apply H with x x0; auto with *.

 rewrite replf_ax in H1; trivial.
 destruct H1.
 rewrite H2; clear z H2.
 apply repl_intro with x; trivial.
 apply uchoice_def.
*)

(** Building well-founded recursor using uchoice *)

Section PolymorphicWellFoundedRecursion.

  Context {A : Type} (Aeq : relation A) {Arefl : Equivalence Aeq}.
  
Section WellFoundedRecursion.

  Variable Rsub : set -> set.
  Hypothesis Rsubm : morph1 Rsub.

  Let R x y := x ∈ Rsub y.
  Local Instance Rm : Proper (eq_set==>eq_set==>iff) R.
do 3 red; intros.
unfold R; rewrite H,H0; reflexivity.
Qed.

  Variable F : (set -> A -> set) -> set -> A -> set.
  Hypothesis Fm :
      Proper ((eq_set ==> Aeq ==> eq_set) ==> eq_set ==> Aeq ==> eq_set) F.

  Let F' f x a := F (fun y a => cond_set (R y x) (f y a)) x a.

  Local Instance Fm' :
      Proper ((eq_set ==> Aeq ==> eq_set) ==> eq_set ==> Aeq ==> eq_set) F'.
do 4 red; intros.   
unfold F'.
apply Fm; trivial.
do 2 red; intros.
apply cond_set_morph; auto.
 apply Rm; trivial.
 apply H; trivial.
Qed.

  Let Fext' x a f f' :
    (forall y y' a a', R y x -> y==y' -> Aeq a a' -> f y a == f' y' a') -> F' f x a == F' f' x a.
unfold F'; intros.
apply Fm; auto with *.
do 2 red; intros.
apply cond_set_morph2; intros; auto.
apply Rm; auto with *.
Qed.

  Definition WFR_rel x a y :=
    forall (P:set->A->set->Prop),
    Proper (eq_set ==> Aeq ==> eq_set ==> iff) P ->
    (forall x' a' f, Proper (eq_set==>Aeq==>eq_set) f ->
     (forall x'' a'', R x'' x' -> P x'' a'' (f x'' a'')) ->
     P x' a' (F' f x' a')) ->
    P x a y.

  Instance WFR_rel_morph :
      Proper (eq_set ==> Aeq ==> eq_set ==> iff) WFR_rel.
do 4 red; intros.
unfold WFR_rel.
apply fa_morph; intros P.
apply fa_morph; intros Pm.
apply fa_morph; intros _.
apply Pm; trivial.
Qed.

  Lemma WFR_rel_intro x a f :
    Proper (eq_set==>Aeq==>eq_set) f ->
    (forall y a, R y x -> WFR_rel y a (f y a)) ->
    WFR_rel x a (F' f x a).
red; intros.
apply H2; auto with *.
intros.
apply H0; trivial.
Qed.

  Lemma WFR_rel_inv x a y :
    WFR_rel x a y ->
    exists2 f, Proper (eq_set==>Aeq==>eq_set) f &
      (forall y a, R y x -> WFR_rel y a (f y a)) /\
      y == F' f x a.
intros.
apply (@proj2 (WFR_rel x a y)).
apply H; intros.
 do 4 red; intros.
 apply and_iff_morphism.
  apply WFR_rel_morph; auto with *.

  apply ex2_morph'; intros; auto with *.
  apply and_iff_morphism.
   apply fa_morph; intros y3.
   apply fa_morph; intros z3.
   rewrite H0; reflexivity.
   apply eq_set_morph; trivial.
   apply Fm; trivial.
   do 2 red; intros.
   apply cond_set_morph; intros; auto.
    apply Rm; trivial.
    apply H3; trivial.
assert (WFR_relsub := fun x z h => proj1 (H1 x z h)); clear H1.
split.
 apply WFR_rel_intro; trivial.

 exists f; auto with *.
Qed.

  (** Particular case of bottom values (do not rely on Fm) *)
  Lemma WFR_rel_inv_norec x a y f0 :
    WFR_rel x a y ->
    (forall f' x' a', x==x' -> Aeq a a' -> F f0 x a == F f' x' a') ->
    y == F f0 x a.
intros r Fext.
generalize (@reflexivity _ eq_set _ x) (@reflexivity _ Aeq _ a).
pattern x at 1, a at 1, y.
apply r; intros.
 do 4 red; intros.
 rewrite H,H0,H1; reflexivity.
symmetry; apply Fext; auto with *.
Qed.
  
  Lemma WFR_rel_fun :
    forall x a y, WFR_rel x a y -> forall y', WFR_rel x a y' -> y == y'.
intros x a y H.
apply H; intros.
 do 4 red; intros.
 apply fa_morph; intros y'.
 rewrite H0,H1,H2; reflexivity.
apply WFR_rel_inv in H2; destruct H2 as (f',fm',(?,?)).
rewrite H3; clear y' H3.
apply Fext'; intros; auto with *.
apply H1; trivial.
rewrite H4 in H3|-*; rewrite H5; auto with *.
Qed.

  Lemma WFR_rel_repl_rel :
    forall x a, repl_rel x (fun x' y => WFR_rel x' a y).
split; intros.
 rewrite <-H0,<-H1; trivial.

 apply WFR_rel_fun with x0 a; trivial.
Qed.

  Lemma WFR_rel_def x a: Acc R x -> exists y, WFR_rel x a y.
intros kx; revert a; generalize kx.
induction kx; intros.
assert (forall x' a', R x' x -> uchoice_pred (fun y => WFR_rel x' a' y)).
{intros.
 destruct H0 with x' a'; eauto.
 split; intros.
  rewrite <- H3; trivial.
 split; intros.
  exists x0; trivial.
 apply WFR_rel_fun with x' a'; trivial. }
exists (F' (fun x' a' => uchoice (fun y => WFR_rel x' a' y)) x a).
apply WFR_rel_intro; intros; trivial.
 do 3 red; intros.
 apply uchoice_morph_raw; red; intros.
 apply WFR_rel_morph; trivial.
apply uchoice_def; auto.
Qed.

  Lemma WFR_rel_choice_pred : forall x a, Acc R x ->
    uchoice_pred (fun y => WFR_rel x a y).
split; intros.
 rewrite <- H0; trivial.
split; intros.
apply WFR_rel_def; trivial.
apply WFR_rel_fun with x a; trivial.
Qed.

  Definition WFR x a := uchoice (fun y => WFR_rel x a y).

  Global Instance WFR_morph0 : Proper (eq_set ==> Aeq ==> eq_set) WFR.
do 3 red; intros.
unfold WFR.
apply uchoice_morph_raw.
red; intros.
apply WFR_rel_morph; trivial.
Qed.

  (** Particular case of bottom values: needs less assumptions... *)
  Lemma WFR_eqn_norec x a :
    (forall y, ~ R y x) ->
    (forall f' x' a', x==x' -> Aeq a a' -> F (fun _ _ => empty) x a == F f' x' a') ->
    WFR x a == F (fun _ _ => empty) x a.
clear Rsubm Fm.
intros bot Fext.
assert (WFR_rel x a (F (fun _ _ => empty) x a)).
{red; intros.
 setoid_replace (F (fun _ _ => empty) x a) with (F' (fun _ _ => empty) x a).
 apply H0; [do 3 red; reflexivity|].
  intros.
  elim bot with (1:=H1).
 apply Fext; reflexivity. }
assert (u: forall y y', WFR_rel x a y -> WFR_rel x a y' -> y==y').
{intros.
 transitivity (F (fun _ _ => empty) x a).
  apply WFR_rel_inv_norec with (1:=H0); trivial.
  symmetry; eapply WFR_rel_inv_norec with (1:=H1); trivial. }
symmetry; apply ZFrepl.uchoice_ext; trivial.
split;[|split];trivial; intros.
 revert H1; apply WFR_rel_morph; auto with *.
 econstructor; apply H.
Qed.

  Lemma WFR_eqn0 x a : Acc R x -> WFR x a == F' WFR x a.
intros.
specialize WFR_rel_choice_pred with (1:=H)(a:=a); intro.
apply uchoice_def in H0.
apply WFR_rel_inv in H0.
destruct H0 as (f,fm,(?,?)).
unfold WFR at 1; rewrite H1.
apply Fext'; intros; auto with *.
eapply WFR_rel_fun with y a0; auto.
rewrite H3.
unfold WFR.
rewrite H4.
apply uchoice_def.
apply WFR_rel_choice_pred.
apply Acc_inv with x; trivial.
rewrite <- H3; trivial.
Qed.

  Lemma WFR_eqn x a :
    (forall f f',
     (forall y y' a a', R y x -> y==y' -> Aeq a a' -> f y a == f' y' a') ->
     F f x a == F f' x a) ->
    Acc R x -> WFR x a == F WFR x a.
intros Fext wfx.
rewrite WFR_eqn0; trivial.
unfold F'; apply Fext; trivial.
intros.
rewrite cond_set_ok; trivial.
apply WFR_morph0; auto with *.
Qed.

End WellFoundedRecursion.

Local Notation E:=eq_set (only parsing).

Global Instance WFR_morph :
    Proper ((E==>E)==>((E==>Aeq==>E)==>E==>Aeq==>E)==>E==>Aeq==>E) WFR.
do 5 red; intros.
apply uchoice_morph_raw.
red; intros.
unfold WFR_rel.
apply fa_morph; intros P.
apply fa_morph; intros Pm.
apply impl_morph.
2:intros; apply Pm; trivial.
apply fa_morph; intros x'.
apply fa_morph; intros a'.
apply fa_morph; intros f.
apply fa_morph; intros fm.
apply impl_morph.
 apply fa_morph; intros x''.
 apply fa_morph; intros a''.
 apply impl_morph; auto with *.
 apply in_set_morph; [reflexivity|].
 apply H; auto with *.
intros _.
apply Pm; auto with *.
apply H0; auto with *.
do 2 red; intros.
apply cond_set_morph; [|apply fm; trivial].
apply in_set_morph; [trivial|].
 apply H; auto with *.
Qed.
  
Global Instance WFR_morph_gen2 R : Proper
  (pointwise_relation _ (pointwise_relation set (pointwise_relation A eq_set)) ==> E==>pointwise_relation A E) (WFR R).
intros F F' eqF x y e a.
apply uchoice_morph_raw.
red; intros.
unfold WFR_rel. 
apply fa_morph; intros P.
apply fa_morph; intros Pm.
apply impl_morph; auto with *.
2:intros; apply Pm; auto with *.
apply fa_morph; intros x'.
apply fa_morph; intros a'.
apply fa_morph; intros f.
apply fa_morph; intros _.
apply fa_morph; intros _.
apply Pm; auto with *.
apply eqF. 
Qed.

  Lemma WFR_ext (R R':set->set) F F' x x' a a':
  pointwise_relation _ E R R' ->
  (forall f f' y a,
   Proper (eq_set==>Aeq==>eq_set) f ->
   Proper (eq_set==>Aeq==>eq_set) f' ->
(*   clos_refl_trans _ R y x ->*)
   (forall z a, z ∈ R y -> f z a == f' z a) ->
   F f y a == F' f' y a) ->
  x == x' ->
  a = a' ->
  WFR R F x a == WFR R' F' x' a'.
intros eqR eqF eqx eqa.
subst a'.
apply ZFrepl.uchoice_morph_raw.
red; intros x1 x1' eqx1.
unfold WFR_rel.
apply fa_morph; intro P.
apply fa_morph; intro Pm.
apply impl_morph; intros.
2:apply Pm; auto with *.
apply fa_morph; intro x'0.
apply fa_morph; intro a'.
apply fa_morph; intro f.
apply fa_morph; intro fm.
apply impl_morph; intros.
 apply fa_morph; intros x''.
 apply fa_morph; intros a''.
 apply impl_morph; auto with *.
 apply in_set_morph; [reflexivity|].
 apply eqR; auto with *.
apply Pm; auto with *.
apply eqF; auto with *.
*do 3 red; intros.
 apply cond_set_morph; auto.
  rewrite H0; reflexivity.
  apply fm; trivial.
*do 3 red; intros.
 apply cond_set_morph; auto.
  rewrite H0; reflexivity.
  apply fm; trivial.
*intros.
 apply cond_set_morph2; auto with *.
apply in_set_morph; [reflexivity|].
 apply eqR; reflexivity.
Qed.
  
End PolymorphicWellFoundedRecursion.
