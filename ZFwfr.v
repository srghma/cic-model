Require Import ZF.
Require ZFrepl.

(* Instance of ZFrepl.WFR when there is no need for an auxiliary fixpoint parameter *)

Section WellFoundedRecursion.

  Variable Rsub : set -> set.
  Hypothesis Rsubm : morph1 Rsub.

  Let R x y := x ∈ Rsub y.
  Local Instance Rm : Proper (eq_set==>eq_set==>iff) R.
do 3 red; intros.
unfold R; rewrite H,H0; reflexivity.
Qed.

  Variable F : (set -> set) -> set -> set.
  Hypothesis Fm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) F.

  Let F' := fun f x (_:unit) => F (fun x=>f x tt) x.
  Let F'm : Proper ((eq_set ==> eq ==> eq_set) ==> eq_set ==> eq ==> eq_set) F'.
do 4 red; intros.
unfold F'.    
apply Fm; trivial.
red; intros.
apply H; trivial.
Qed.

  Definition WFR x := ZFrepl.WFR eq Rsub F' x tt.

  Instance WFR_morph0 : morph1 WFR.
do 2 red; intros.
apply ZFrepl.WFR_morph0; trivial.
Qed.
  
  Lemma WFR_eqn x :
    (forall f f',
     (forall y y', R y x -> y==y' -> f y == f' y') ->
     F f x == F f' x) ->
    Acc R x -> WFR x == F WFR x.
intros.
unfold WFR; rewrite ZFrepl.WFR_eqn; auto with *.
*unfold F'; reflexivity.
*intros.
 apply H; auto.
Qed.

  Lemma WFR_ind : forall x (P:set->set->Prop),
    (forall y f f', Acc R y ->
     (forall z z', R z y -> z==z' -> f z == f' z') ->
     F f y == F f' y) ->
    Proper (eq_set ==> eq_set ==> iff) P ->
    Acc R x ->
    (forall y, Acc R y ->
     (forall x, R x y -> P x (WFR x)) ->
     P y (F WFR y)) ->
    P x (WFR x).
intros x P Fextx Pm wfx Hrec.
elim wfx; intros.
rewrite WFR_eqn; trivial.
*apply Hrec; [constructor; trivial|intros].
 apply H0; trivial.
*intros.
 apply Fextx; auto with *.
 constructor; trivial.
*constructor; trivial.
Qed.

  Lemma WFR_eqn_norec x :
    (forall y, ~ R y x) ->
    (forall f' x', x==x' -> F (fun _ => empty) x == F f' x') ->
    WFR x == F (fun x => empty) x.
intros.
apply ZFrepl.WFR_eqn_norec; intros; auto with *.
*apply H.
*apply H0; trivial.
Qed.

End WellFoundedRecursion.

Local Notation E:=eq_set (only parsing).

Global Instance WFR_morph :
    Proper ((E==>E)==>((E ==> E) ==> E ==> E) ==> E ==> E) WFR.
do 4 red; intros.
apply ZFrepl.WFR_morph; auto with *.
do 3 red; intros.
apply H0; trivial.
red; intros; apply H2; auto.
Qed.
  
Global Instance WFR_morph_gen2 R : Proper
  (pointwise_relation _ (pointwise_relation _ E) ==> E ==> E) (WFR R).
do 3 red; intros.
apply ZFrepl.WFR_morph_gen2; auto with *.
do 3 red; intros.
apply H; trivial.
Qed.

Lemma WFR_ext R R' F F' x x' :
  pointwise_relation _ E R R' ->
  (forall f f' y,
   morph1 f ->
   morph1 f' ->
   (forall z, z ∈ R y -> f z == f' z) ->
   F f y == F' f' y) ->
  x == x' ->
  WFR R F x == WFR R' F' x'.
intros.
apply ZFrepl.WFR_ext; auto with *.
intros.
apply H0; auto.
*do 2 red; intros; apply H2; trivial.
*do 2 red; intros; apply H3; trivial.
Qed.
