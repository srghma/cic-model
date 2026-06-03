
Require Import ZF.

(** Natural numbers *)

Definition zero := empty.
Definition succ n := n ∪ singl n.

Instance succ_morph : morph1 succ.
Proof.
unfold succ; do 2 red; intros; rewrite H; reflexivity.
Qed.

Definition pred := union.

Instance pred_morph : morph1 pred.
exact union_morph.
Qed.

Lemma discr : forall k, ~ succ k == zero.
Proof.
red; intros.
elim (empty_ax k).
rewrite <- H.
unfold succ.
apply union2_intro2.
apply singl_intro.
Qed.

Definition lt := in_set.
Definition le m n := lt m (succ n).
Infix "<" := lt.
Infix "<=" := le.

Instance lt_morph : Proper (eq_set ==> eq_set ==> iff) lt.
exact in_set_morph.
Qed.

Instance le_morph : Proper (eq_set ==> eq_set ==> iff) le.
Proof.
unfold le; do 3 red; intros; rewrite H; rewrite H0; reflexivity.
Qed.


Lemma le_case : forall m n, m <= n -> m == n \/ m < n.
Proof.
unfold le, lt, succ in |- *; intros.
elim union2_elim with (1 := H); intros; auto.
left.
apply singl_elim; trivial.
Qed.

Lemma succ_intro1 : forall x n, x == n -> x < succ n.
red; intros.
unfold succ.
apply union2_intro2.
apply singl_intro_eq.
trivial.
Qed.

Lemma succ_intro2 : forall x n, x < n -> x < succ n.
red; intros.
unfold succ.
apply union2_intro1.
trivial.
Qed.

Lemma lt_is_le : forall x y, x < y -> x <= y.
Proof succ_intro2.

Lemma le_refl : forall n, n <= n.
intros.
apply succ_intro1; reflexivity.
Qed.
Hint Resolve lt_is_le le_refl : core.


(* building the set of natural numbers *)

Definition is_nat n : Prop :=
  forall nat:set,
  nat ⊆ infinite ->
  zero ∈ nat ->
  (forall k, k ∈ nat -> succ k ∈ nat) ->
  n ∈ nat.

Lemma is_nat_zero : is_nat zero.
Proof.
red in |- *; intros; auto.
Qed.

Lemma is_nat_succ : forall n, is_nat n -> is_nat (succ n).
Proof.
unfold is_nat in |- *; intros.
apply H2.
apply H; auto.
Qed.

Definition N := subset infinite is_nat.

Lemma zero_typ: zero ∈ N.
Proof.
unfold N in |- *.
apply subset_intro.
 unfold zero in |- *; apply infinity_ax1.
 exact is_nat_zero.
Qed.

Lemma succ_typ: forall n, n ∈ N -> succ n ∈ N.
Proof.
unfold N; intros.
apply subset_intro.
 unfold succ, union2, singl; apply infinity_ax2;
  apply subset_elim1 with is_nat; trivial.
 apply is_nat_succ.
  elim subset_elim2 with (1:=H); intros; trivial.
  unfold is_nat.
  intros; rewrite H0.
  auto.
Qed.

Lemma N_ind : forall (P: set->Prop),
  (forall n n', n ∈ N -> n == n' -> P n -> P n') ->
  P zero ->
  (forall n, n ∈ N -> P n -> P (succ n)) ->
  forall n, n ∈ N -> P n.
Proof.
intros.
assert (n ∈ subset N P).
{unfold N in H2.
 elim subset_elim2 with (1 := H2); intros.
 rewrite H3.
 red in H4; apply H4; intros; auto.
 *transitivity N; red; apply subset_elim1.
 *apply subset_intro; trivial.
  apply zero_typ.
 *apply subset_intro.
   apply succ_typ.
   apply subset_elim1 with (1 := H5).

   apply H1.
    apply subset_elim1 with (1 := H5).

    elim subset_elim2 with (1 := H5); intros.
    apply H with x0; auto.
    rewrite <- H6.
    apply subset_elim1 with (1 := H5).
    symmetry; trivial. }
elim subset_elim2 with (1 := H3); intros.
apply H with x; auto.
rewrite <- H4; trivial.
symmetry; trivial.
Qed.
 
Lemma Nle_ind m P :
  Proper (eq_set==>iff) P ->
  P m ->
  (forall n, n ∈ N -> P n -> P (succ n)) ->
  forall n, m ∈ N -> n ∈ N -> le m n -> P n.
intros Pm Hm HS n tym tyn Hle.
revert m tym Hm Hle; elim tyn using N_ind; intros.
*rewrite <- H0 in Hle|-*; eauto.
*revert Hm Hle; elim tym using N_ind; intros; trivial.
 +rewrite <- H0 in Hm, Hle; auto.
 +apply le_case in Hle; destruct Hle as [Hle|Hle];
    [apply discr in Hle|apply empty_ax in Hle]; contradiction.
*apply le_case in Hle; destruct Hle.
 +rewrite H1 in Hm; trivial.
 +apply HS; trivial.
  apply H0 with m; trivial.
Qed.

Lemma N_trans x y : x ∈ y -> y ∈ N -> x ∈ N.
 intros.
 revert H; elim H0 using N_ind; intros. 
  rewrite <- H1 in H3; auto.

  apply empty_ax in H; contradiction.
  apply union2_elim in H2; destruct H2; auto.
  apply singl_elim in H2.
  rewrite H2; trivial.
Qed.

Lemma lt_trans : forall m n p, p ∈ N -> m < n -> n < p -> m < p.
Proof.
intros m n p ty_p.
unfold lt in |- *.
elim ty_p using N_ind; intros.
 rewrite <- H0 in H3|-*; auto.
 elim empty_ax with (1 := H0).
 elim le_case with (1 := H2); intros.
   rewrite <- H3; trivial.
    unfold succ in |- *.
    apply union2_intro1; trivial.
  unfold succ in |- *.
    apply union2_intro1; auto.
Qed.

Lemma le_trans m n p :
  p ∈ N -> le m n -> le n p -> le m p.
intros.
apply le_case in H0; destruct H0.
 rewrite H0; trivial.

 apply lt_is_le.
 apply le_case in H1; destruct H1.
 rewrite <-H1; trivial.

 apply lt_trans with n; trivial.
Qed.

Lemma le_lt_trans : forall m n p, p ∈ N -> m <= n -> n < p -> m < p.
intros.
apply le_case in H0; trivial.
destruct H0.
*rewrite H0; trivial.
*apply lt_trans with n; trivial.
Qed.

Lemma pred_succ_eq : forall n, n ∈ N -> pred (succ n) == n.
Proof.
unfold pred, succ in |- *; intros.
apply eq_intro; intros.
 elim union_elim with (1 := H0); intros.
   elim union2_elim with (1 := H2); intros.
  apply lt_trans with x; trivial.
   rewrite (singl_elim _ _ H3) in H1.
    trivial.
 apply union_intro with n; trivial.
   apply union2_intro2.
   apply singl_intro.
Qed.

Lemma pred_typ : forall n, n ∈ N -> pred n ∈ N.
Proof.
intros.
elim H using N_ind; intros.
 rewrite <- H1; trivial.

 unfold pred, zero in |- *.
 rewrite union_empty_eq.
 exact zero_typ.

 rewrite pred_succ_eq; trivial.
Qed.

Lemma succ_inj : forall m n, m ∈ N -> n ∈ N -> succ m == succ n -> m == n.
Proof.
intros.
 rewrite <- (pred_succ_eq _ H).
 rewrite <- (pred_succ_eq _ H0).
 rewrite H1; reflexivity.
Qed.

Lemma N_case n :
  n ∈ N -> n==zero \/ n==succ(pred n).
intros tyn.
elim tyn using N_ind; intros.
*rewrite <-H0; trivial.
*auto with *.
*right; rewrite pred_succ_eq; auto with *.
Qed.

Lemma lt_0_succ : forall n, n ∈ N -> zero < succ n.
intros.
elim H using N_ind; intros.
 rewrite <- H1; trivial.

 apply succ_intro1; reflexivity.

 apply lt_trans with (succ n0); trivial.
  apply succ_typ; apply succ_typ; trivial.
  apply succ_intro1; reflexivity.
Qed.

Lemma lt_mono : forall m n, m ∈ N -> n ∈ N -> 
  m < n -> succ m < succ n.
intros m n Hm Hn.
elim Hn using N_ind; intros. rewrite H0 in H1; auto.
 elim empty_ax with m; trivial.
 elim le_case with (1:=H1); intros.
  rewrite H2; apply succ_intro1; reflexivity.
  apply succ_intro2; auto.
Qed.

Lemma lt_inv m n :
  n ∈ N -> succ m < succ n -> m < n.
intros tyn H.
apply le_case in H;destruct H.
*rewrite <- H; apply succ_intro1; reflexivity.
*apply lt_trans with (succ m); trivial.
 apply succ_intro1; reflexivity.
Qed.

Lemma le_total : forall m, m ∈ N -> forall n, n ∈ N ->
  m < n \/ m == n \/ n < m.
intros m Hm.
elim Hm using N_ind; intros. rewrite <- H0; auto.
 elim H using N_ind; intros. rewrite <- H1; auto.
  right; left; reflexivity.

  left.
  apply lt_0_succ; trivial.

 elim H1 using N_ind; intros. rewrite <- H3; auto.
  right;right.
  apply lt_0_succ; trivial.

  elim H0 with n1; intros; auto.
   left.
   apply lt_mono; trivial.

   right.
   destruct H4.
    left; rewrite H4; reflexivity.

    right.
    apply lt_mono; trivial.
Qed.

Lemma N_strong_ind (P:set->Prop) n :
  (forall n, n ∈ N -> (forall k, k < n -> P k) -> P n) ->
  n ∈ N -> P n.
intros Hrec tyn.
cut (forall n', n' ∈ N -> n' ⊆ n -> P n'); eauto with *.
elim tyn using N_ind; intros.
*apply H1; trivial.
 rewrite H0; trivial.
*apply Hrec; trivial.
 intros.
 apply H0 in H1; apply empty_ax in H1; contradiction.
*apply Hrec; trivial.
 intros.
 apply H0; [apply N_trans with n'; trivial|].
 red; intros.
 apply H2 in H3.
 apply le_case in H3; destruct H3.
 rewrite <-H3; trivial.
 apply lt_trans with k; trivial.
Qed.

(** definition by case on N *)
Definition natcase n f g :=
    cond_set (n==zero) f ∪ cond_set (exists2 m, m ∈ N & n==succ m) g.

Lemma natcase_0 n f g :
  n == zero ->
  natcase n f g == f.
intros.
unfold natcase.
rewrite cond_set_ok with (x:=f); trivial.
rewrite cond_set_mt with (x:=g).
+apply eq_set_ax; intros z.
 rewrite union2_ax.
 split; [destruct 1|]; auto.
 apply empty_ax in H0; contradiction.
+intros (m,_,?).
 rewrite H0 in H; apply discr in H; trivial.
Qed.

Lemma natcase_succ n m f g :
  m ∈ N ->
  n == succ m ->
  natcase n f g == g.
intros.
unfold natcase.
rewrite cond_set_ok with (x:=g); eauto.
rewrite cond_set_mt with (x:=f).
+apply eq_set_ax; intros z.
 rewrite union2_ax.
 split; [destruct 1|]; auto.
 apply empty_ax in H1; contradiction.
+intros e.
 rewrite H0 in e; apply discr in e; trivial.
Qed.

#[global]Instance natcase_morph :
  Proper (eq_set==>eq_set==>eq_set==>eq_set) natcase.
do 4 red; intros.
apply union2_morph;[rewrite H,H0;reflexivity|].
apply cond_set_morph;[|trivial].
apply ex2_morph; intro; auto with *.
rewrite H; reflexivity.
Qed.

(** Bounded Recursive definitions *)
(*
Section BoundedNatRec.

  (* Set of return values *)
  Variable P : set -> set.
  Hypothesis Pext : ext_fun N P.

  Variable F : set -> set -> set.
  Hypothesis Ftyp : forall n x,
    n ∈ N -> x ∈ P n -> F n x ∈ P (succ n).

  Definition natrec_spec n x :=
    forall 


End BoundedNatRec.
*)

(** max *)

Definition max := union2.

Instance max_morph : morph2 max.
exact union2_morph.
Qed.

Lemma max_sym : forall m n, max m n == max n m.
unfold max; intros.
apply union2_commut.
Qed.


Lemma max_eq : forall m n, m == n -> max m n == m.
unfold max; intros.
rewrite H.
apply eq_intro; intros.
 elim union2_elim with (1:=H0); auto.
 apply union2_intro1; trivial.
Qed.

Lemma max_lt : forall m n, n ∈ N -> m < n -> max m n == n.
intros m n H.
generalize m; clear m.
elim H using N_ind; intros.
 unfold max; rewrite <- H1 in H3|-*; auto.

 elim empty_ax with m; trivial.

 elim le_case with (1:=H2); intros.
  unfold max; rewrite H3.
  apply eq_intro; intros.
   elim union2_elim with (1:=H4); intros; auto.
   apply succ_intro2; trivial.

   apply union2_intro2; trivial.

 unfold max.
 apply eq_intro; intros.
  elim union2_elim with (1:=H4); intros; auto.
  rewrite <- (H1 _ H3).
  apply succ_intro2.
  apply union2_intro1; trivial.

  apply union2_intro2; trivial.
Qed.

Lemma max_le_l n m : n ∈ N -> m ∈ N -> le n (max n m).
intros.
destruct le_total with n m as [?|[?|?]]; trivial.
 rewrite max_lt; trivial.
 apply lt_is_le; trivial.

 rewrite max_eq; trivial.

 rewrite max_sym,max_lt; trivial.
Qed.

Lemma max_le_r n m : n ∈ N -> m ∈ N -> le m (max n m).
intros.
rewrite max_sym; apply max_le_l; trivial.
Qed.

Lemma max_typ : forall m n, m ∈ N -> n ∈ N -> max m n ∈ N.
intros.
elim le_total with m n; trivial; intros.
 rewrite (max_lt m n); trivial.

 destruct H1.
  rewrite H1; rewrite max_eq; trivial; reflexivity.

  rewrite (max_sym m n).
  rewrite (max_lt n m); trivial.
Qed.
Hint Resolve max_le_l max_le_r max_typ : core.

(* nat -> set *)
Fixpoint nat2set (n:nat) : set :=
  match n with
  | 0 => zero
  | S k => succ (nat2set k)
  end.

Lemma nat2set_typ : forall n, nat2set n ∈ N.
induction n; simpl.
 apply zero_typ.
 apply succ_typ; trivial.
Qed.

Lemma nat2set_inj : forall n m, nat2set n == nat2set m -> n = m.
induction n; destruct m; simpl; intros; trivial.
 elim (discr (nat2set m)); symmetry; trivial.

 elim (discr (nat2set n)); trivial.

 replace m with n; auto.
 apply IHn.
 apply succ_inj; trivial; apply nat2set_typ.
Qed.

Lemma nat2set_reflect : forall x, x ∈ N -> exists n, x == nat2set n.
intros.
elim H using N_ind; intros.
 destruct H2.
 exists x0.
 rewrite <- H1; trivial.

 exists 0; reflexivity.

 destruct H1.
 exists (S x0); rewrite H1; reflexivity.
Qed.

Lemma nat2set_le_intro m n :
  (m <= n)%nat ->
  nat2set m <= nat2set n.
induction 1; [apply succ_intro1;reflexivity|simpl].
apply le_trans with (2:=IHle).
*apply succ_typ; apply nat2set_typ.
*apply succ_intro2; apply succ_intro1; reflexivity.
Qed.

Lemma nat2set_le_elim m n :
  nat2set m <= nat2set n ->
  (m <= n)%nat.
intros lemn.
cut (forall n', nat2set n == nat2set n' -> (m<=n')%nat); [auto with *|].
elim lemn using Nle_ind; auto using nat2set_typ with *.
*do 2 red; intros.
 apply fa_morph; intros n'.
 rewrite H; reflexivity.
*intros.
 apply nat2set_inj in H; subst n'; auto with arith.
*intros.
 destruct n'; simpl in *.
 +apply discr in H1; contradiction.
 +apply succ_inj in H1; auto using nat2set_typ with arith.  
Qed.

Lemma nat2set_le_reflect m n :
  nat2set m <= nat2set n <-> (m <= n)%nat.
split.
apply nat2set_le_elim.
apply nat2set_le_intro.
Qed.

(** Binary operations: Addition, etc. *)

Section BinaryOperation.

  Variable f : nat->nat->nat.

Definition isBinop m n p :=
  exists m':nat, nat2set m' == m /\
  exists n':nat, nat2set n' == n /\ nat2set (f m' n') == p.

Instance isBinop_morph : Proper (eq_set==>eq_set==>eq_set==>iff) isBinop.
do 4 red; intros.
apply ex_morph; intros m'.
apply and_iff_morphism; [rewrite H; reflexivity|].
apply ex_morph; intros n'.
apply and_iff_morphism; [rewrite H0; reflexivity|].
rewrite H1; reflexivity.
Qed.

Lemma isBinop_typ m n p : isBinop m n p -> m ∈ N /\ n ∈ N /\ p ∈ N.
intros (m'&eqm&n'&eqn&eqp).
rewrite <-eqm,<-eqn,<-eqp.
auto using nat2set_typ.
Qed.

Lemma isBinop_uniq m n p p' : isBinop m n p -> isBinop m n p' -> p==p'.
intros (m1&em1&n1&en1&ep) (m2&em2&n2&en2&ep').
rewrite <-em2 in em1; apply nat2set_inj in em1; subst m2.
rewrite <-en2 in en1; apply nat2set_inj in en1; subst n2.
rewrite <-ep,<-ep'; reflexivity.
Qed.

Lemma isBinop_ex m n :
  m ∈ N -> n ∈ N -> exists p, isBinop m n p.
intros tym tyn.
apply nat2set_reflect in tym; destruct tym as (m',eqm).
apply nat2set_reflect in tyn; destruct tyn as (n',eqn).
exists (nat2set(f m' n')).
exists m'; split;[ auto with *|].
exists n'; split; auto with *.
Qed.

Definition binop m n := union (subset N (isBinop m n)).

Instance binop_morph : morph2 binop.
do 3 red; intros.
unfold binop.
apply union_morph.
apply subset_morph; [reflexivity|red; intros].
rewrite H,H0; reflexivity.
Qed.

Lemma binop_ax m n p :
  m ∈ N -> n ∈ N ->
  binop m n == p <-> isBinop m n p.
intros tym tyn.
destruct isBinop_ex with (1:=tym)(2:=tyn) as (p',p'def).
unfold binop; rewrite union_subset_singl with (y:=p')(y':=p'); auto with *.
*split; intros.
 +rewrite <-H; trivial.
 +apply isBinop_uniq with (1:=p'def)(2:=H).
*apply isBinop_typ with (1:=p'def).
*intros; apply isBinop_uniq with m n; trivial.
Qed.

Lemma binop_typ m n :
  m ∈ N -> n ∈ N -> binop m n ∈ N.
intros tym tyn.
destruct isBinop_ex with (1:=tym)(2:=tyn) as (p,pdef).
destruct isBinop_typ with (1:=pdef) as (_&_&typ).
apply binop_ax in pdef; trivial.
rewrite pdef; trivial.
Qed.

Lemma binop_reflect m n :
  binop (nat2set m) (nat2set n) == nat2set (f m n).
apply binop_ax; auto using nat2set_typ.
eexists; split; [reflexivity| eexists; split; reflexivity].
Qed.

End BinaryOperation.
Existing Instance binop_morph.

Definition add := binop plus.

Instance add_morph : morph2 add.
apply binop_morph.
Qed.

Lemma add_typ m n :
  m ∈ N -> n ∈ N -> add m n ∈ N.
apply binop_typ.
Qed.

Lemma add0 n : n ∈ N -> add n zero == n.
intros tyn.
unfold add.
apply binop_ax; auto using zero_typ.
apply nat2set_reflect in tyn; destruct tyn as (n',eqn').
exists n'; split; [auto with *|].
exists 0; split; [reflexivity|].
replace (n'+0) with n'; auto with *.
Qed.
  
Lemma addS n m : n ∈ N -> m ∈ N -> add n (succ m) == succ (add n m).
intros tyn tym.
apply nat2set_reflect in tyn; destruct tyn as (n',eqn).
apply nat2set_reflect in tym; destruct tym as (m',eqm).
rewrite eqn, eqm.
unfold add; rewrite (binop_reflect plus n' m').
rewrite (binop_reflect plus n' (S m')).
replace (n'+S m') with (S(n'+m')); simpl; auto with *.
Qed.

Lemma add1 n : n ∈ N -> add n (succ zero) == succ n.
intros; rewrite addS; trivial.
 rewrite add0; trivial; reflexivity.  

 apply zero_typ.
Qed.

Lemma addS_l m n : m ∈ N -> n ∈ N -> add (succ m) n == succ (add m n).
intros.
elim H0 using N_ind; intros.
*rewrite <-H2; trivial.
*rewrite !add0; auto using zero_typ, succ_typ.
 reflexivity.
*rewrite !addS,H2; auto using zero_typ, succ_typ.
 reflexivity.
Qed.

Lemma discr_even_odd m n :
  m ∈ N -> n ∈ N ->
  ~ add m m == succ (add n n).
intros mty; revert n; elim mty using N_ind; intros.
*rewrite <-H0; auto.
*rewrite add0; [|apply zero_typ].
 intros h; symmetry in h; apply discr in h; trivial. 
*rewrite addS; [|apply succ_typ;trivial|trivial].
 rewrite addS_l; trivial.
 elim H1 using N_ind; intros.
 +rewrite <-H3; trivial.
 +rewrite add0; [|apply zero_typ].
  intro h.
  apply succ_inj in h; auto using zero_typ, succ_typ, add_typ.
  apply discr in h; trivial.
 +rewrite addS; [|apply succ_typ|]; trivial.
  rewrite addS_l; trivial.
  intro h.
  apply succ_inj in h; auto using zero_typ, succ_typ, add_typ.
  apply succ_inj in h; auto using zero_typ, succ_typ, add_typ.
  apply H0 in h; auto.
Qed.

Lemma mult2_inj m n : m ∈ N -> n ∈ N -> add m m == add n n -> m==n.
intros mty; revert n; elim mty using N_ind; intros.
*rewrite <-H0 in H3|-*; auto.
*rewrite add0 in H0; [|apply zero_typ].
 revert H0; elim H using N_ind; intros.
 +rewrite <-H1 in H3|-*; auto.
 +reflexivity.
 +rewrite addS in H2; [|apply succ_typ|]; trivial.
  symmetry in H2; apply discr in H2; contradiction.  
*rewrite addS in H2; [|apply succ_typ|]; trivial.
 rewrite addS_l in H2; trivial.
 revert H2; elim H1 using N_ind; intros.
 +rewrite <-H3 in H5|-*; auto.
 +rewrite add0 in H2; [|apply zero_typ].
  apply discr in H2; contradiction.
 +rewrite addS in H4; [|apply succ_typ|]; trivial.
  rewrite addS_l in H4; trivial.
  apply succ_inj in H4; auto using zero_typ, succ_typ, add_typ.
  apply succ_inj in H4; auto using zero_typ, succ_typ, add_typ.
  apply succ_morph; auto.
Qed.

Lemma mult2_incr n : n ∈ N -> n <= add n n.
intros.
elim H using N_ind; intros.
*rewrite <-H1; trivial.
*rewrite add0; [apply succ_intro1; reflexivity|apply zero_typ].
*rewrite addS; [|apply succ_typ|]; trivial.
 rewrite addS_l; trivial.
 red in H1|-*.
 apply lt_mono; auto using succ_typ, add_typ.
 apply succ_intro2; trivial.
Qed.

(* Bijection NxN = N *)
From Stdlib Require Import Arith Lia.

Require Import Zpairs.

Definition NN2N xy := binop nn2n (fst xy) (snd xy).

Instance NN2N_morph : morph1 NN2N.
do 2 red; intros; unfold NN2N.
apply binop_morph; rewrite H; reflexivity.
Qed.

Lemma NN2N_def x y :
  NN2N (couple (nat2set x) (nat2set y)) == nat2set(nn2n x y).
unfold NN2N.
rewrite fst_def, snd_def.
apply binop_reflect.
Qed.

Lemma NN2N_typ : typ_fun NN2N (prodcart N N) N.
red; intros.
apply binop_typ.
apply fst_typ in H; trivial.
apply snd_typ in H; trivial.
Qed.

Lemma NN2N_inj xy1 xy2 :
  xy1 ∈ prodcart N N -> xy2 ∈ prodcart N N -> NN2N xy1 == NN2N xy2 -> xy1 == xy2.
intros.
rewrite surj_pair with (1:=H) in H1|-*.
rewrite surj_pair with (1:=H0) in H1|-*.
destruct (nat2set_reflect (fst xy1)); [apply fst_typ in H; trivial|].
destruct (nat2set_reflect (snd xy1)); [apply snd_typ in H; trivial|].
destruct (nat2set_reflect (fst xy2)); [apply fst_typ in H0; trivial|].
destruct (nat2set_reflect (snd xy2)); [apply snd_typ in H0; trivial|].
rewrite H2,H3,H4,H5 in H1|-*.
rewrite !NN2N_def in H1.
apply nat2set_inj in H1.
apply nn2n_inj in H1.
destruct H1; subst x1 x2; reflexivity.
Qed.

Lemma NN2N_surj n : n ∈ N -> exists xy, xy ∈ prodcart N N /\ n == NN2N xy.
intros.
destruct (nat2set_reflect n) as (k,?); [trivial|].
destruct (nn2n_surj k) as (x & y & e).
exists (couple (nat2set x)(nat2set y)); split.
apply couple_intro; apply nat2set_typ.
rewrite H0; subst k.
symmetry; apply NN2N_def.
Qed.
