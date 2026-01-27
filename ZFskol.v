
(* In this file, we show the equivalence between the Skolemized
   and existentially quantified presentations of ZF.
 *)

Require Import basic.
Require Export ZFdef.
Require Import Sublogic.
Require Zskol.

Module Skolem (Z : IZF_R_Ex_sig CoqSublogicThms) <: IZF_R_sig CoqSublogicThms.

(* We skolemize all of Zermelo set theory *)
Include Zskol.Skolem CoqSublogicThms Z.

(* replacement *)

Definition funDom (R:set -> set -> Prop) x :=
  forall x' y y', R x y -> R x' y' -> x == x' -> y == y'.
Definition downR (R:set -> set -> Prop) x' y' :=
  exists2 x, x == Z2set x' /\ funDom R x & exists2 y, y == Z2set y' & R x y.

Lemma downR_morph : Proper
  ((eq_set ==> eq_set ==> iff) ==> Z.eq_set ==> Z.eq_set ==> iff) downR.
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
  Z.eq_set x x' ->
  Z.eq_set y y' ->
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
  Z.eq_set y y'.
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
exists
 (fun a' => forall x,
  Z.in_set x a' <-> exists2 y, Z2set y ∈ a & downR R y x).
split; intros.
 destruct (Z2set_surj a).
 assert (R'm := fun x0 x' y y' (_:Z.in_set x0 x) => downRm R x0 x' y y').
 assert (R'fun := fun x0 y y' (_:Z.in_set x0 x) => downR_fun R x0 y y').
 destruct (Z.repl_ex x (downR R) R'm R'fun); intros.
 exists x0; intros.
 rewrite H0.
 apply ex2_morph; red; intros.
 2:reflexivity.
 split; intros.
  rewrite H.
  apply inZ_in; trivial.

  apply in_inZ.
  rewrite <- H; trivial.

 rewrite Z.eq_set_ax; intros.
 rewrite H.
 rewrite H0.
 reflexivity.
Defined.

Definition incl_set x y := forall z, z ∈ x -> z ∈ y.

Lemma repl0_mono :
  Proper (incl_set ==> (eq_set ==> eq_set ==> iff) ==> incl_set) repl0.
do 4 red; simpl; intros.
rewrite in_set_elim in *.
destruct H1.
destruct H2.
simpl in *; intros.
destruct (Z2set_surj y).
assert (R'm := fun x x' y y' (_:Z.in_set x x3) => downRm y0 x x' y y').
assert (R'fun := fun x y y' (_:Z.in_set x x3) => downR_fun y0 x y y').
destruct (Z.repl_ex x3 (downR y0) R'm R'fun).
exists x1; trivial.
exists x4; trivial.
 intro; rewrite H5.
 apply ex2_morph; red; intros; auto with *.
 rewrite H4.
 symmetry; apply in_equiv.

 rewrite H5.
 rewrite H2 in H3.
 clear x2 H1 H2 x4 H5.
 destruct H3.
 exists x2.
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
    forall x, x ∈ repl a R <-> exists2 y, y ∈ a & R y x }.
exists repl0; split.
 exact repl0_mono.
split; intros.
 rewrite in_set_elim in H1.
 destruct H1.
 destruct H2; simpl in *.
 rewrite H2 in H3.
 destruct H3.
 destruct H4.
 destruct H5.
 destruct H4.
 exists x3.
  rewrite H4; trivial.
 revert H6; apply H; auto with *.
  rewrite H4; trivial.

  apply Eq_proj in H1.
  rewrite H1; trivial.

 destruct H1.
 apply In_intro; simpl; intros.
 rewrite H4; clear H4.
 destruct (Z2set_surj x0).
 exists x1.
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
    forall x, x ∈ repl a R <-> exists2 y, y ∈ a & R y x.
Proof proj2 (proj2_sig repl_sig).


(* Proving that collection can be skolemized in classical ZF:
   we need excluded-middle to prove coll_ax_uniq (see EnsEm)
 *)

Section Collection.

(* A predicate transformer that is true for the least element of
   the Veblen hierarchy that satisfies the input predicate. If there
   is no unique solution, the returned predicate is empty. No
   excluded-middle needed here.
 *)
Hypothesis lst_rk : (Z.set->Prop) -> Z.set -> Prop.
Hypothesis lst_rk_morph : forall (P P':Z.set->Prop),
  (forall x x', Z.eq_set x x' -> (P x <-> P' x')) ->
  forall y y', Z.eq_set y y' -> lst_rk P y -> lst_rk P' y'.
Hypothesis lst_incl : forall P y, lst_rk P y -> P y.
Hypothesis lst_fun : forall P y y', lst_rk P y -> lst_rk P y' -> Z.eq_set y y'.

(* The modification of the collection axiom that return the least Veblen universe
   that collects all the images of A. This can exist only when the Veblen hierarchy
   is totally ordered, which requires excluded-middle. See EnsEm for the
   construction.
 *)
Hypothesis coll_ax_uniq : forall A (R:Z.set->Z.set->Prop), 
    (forall x x' y y', Z.in_set x A -> Z.eq_set x x' -> Z.eq_set y y' ->
     R x y -> R x' y') ->
    exists B, lst_rk(fun B =>
      forall x, Z.in_set x A ->
      (exists y, R x y) ->
      exists2 y, Z.in_set y B & R x y) B.
(* We could also try to prove that B grows when A and R do. *)

Lemma coll_sig : forall A (R:set->set->Prop), 
  {coll| Proper (eq_set==>eq_set==>iff) R ->
     forall x, x ∈ A -> (exists y, R x y) ->
     exists2 y, y ∈ coll & R x y }.
intros A R.
pose (R' x y := exists2 x', Z2set x == x' & exists2 y', Z2set y == y' & R x' y').
assert (R'm : forall x x' y y', Z.eq_set x x' -> Z.eq_set y y' ->
     R' x y -> R' x' y').
 destruct 3 as (x'',?,(y'',?,?)).
 exists x'';[|exists y'';trivial].
  transitivity (Z2set x); trivial.
  apply Zeq_eq.
  symmetry; trivial.

  transitivity (Z2set y); trivial.
  apply Zeq_eq.
  symmetry; trivial.
apply set_intro with
  (lst_rk(fun B => exists2 A', Z2set A' == A & forall x, Z.in_set x A' ->
      (exists y, R' x y) ->
      exists2 y, Z.in_set y B & R' x y)); intros.
 destruct (Z2set_surj A) as (A',e).
 destruct coll_ax_uniq with A' R' as (B,HB); eauto.
 exists B.
 revert HB; apply lst_rk_morph; auto with *.
 intros.
 split; intros.
  exists A'; intros; auto with *.
  destruct H0 with x0 as (y,?,?); trivial.
  exists y; trivial.
  revert H3; apply Zin_morph; auto with *.

  destruct H0 as (A'',e',?).
  rewrite e in e'.
  apply eq_Zeq in e'.
  rewrite <- e' in H1.
  destruct H0 with x0 as (y,?,?); trivial.
  exists y; trivial.
  revert H3; apply Zin_morph; auto with *.

 apply lst_fun with (1:=H) (2:=H0).

 destruct Hex as (B,HB).
 assert (Bok := lst_incl _ _ HB).
 destruct Bok as (A',eA,Bok).
 destruct (Z2set_surj x) as (x',ex).
 destruct Bok with x' as (y,?,?).
  apply in_inZ.
  rewrite eA; rewrite <- ex; trivial.

  destruct H1 as (y,Rxy).
  destruct (Z2set_surj y) as (y',ey).
  exists y'; exists x; [|exists y]; auto with *.

  exists (Z2set y).
   apply In_intro; simpl; intros.
   specialize Huniq with (1:=HB) (2:=H5).
   rewrite <- Huniq.
   rewrite H4; trivial.

   destruct H3 as (x'',?,(y',?,?)).
   revert H5; apply H; trivial.
   rewrite ex; rewrite <- H3; auto with *.
Qed.

Definition coll A R := proj1_sig (coll_sig A R).
Lemma coll_ax : forall A (R:set->set->Prop), 
  Proper (eq_set==>eq_set==>iff) R ->
  forall x, x ∈ A -> (exists y, R x y) ->
  exists2 y, y ∈ coll A R & R x y.
Proof (fun A R => proj2_sig (coll_sig A R)).

End Collection.

End Skolem.
