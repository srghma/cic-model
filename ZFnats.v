
Require Export ZF ZFwfr.
Require Export Znats.

 (** * Well-foundation results *)

Require Import ZFwf.

Lemma isWf_succ : forall n, isWf n -> isWf (succ n).
intros.
apply isWf_intro; intros.
elim le_case with (1:=H0); clear H0; intros.
 apply isWf_ext with n; trivial.
 symmetry; trivial.

 apply isWf_inv with n; trivial.
Qed.

Lemma isWf_N : isWf N.
apply isWf_intro; intros.
elim H using N_ind; intros.
 apply isWf_ext with n; trivial.
 apply isWf_zero.
 apply isWf_succ; trivial.
Qed.

(** Recursor (as in G""odel's T) *)

Section Natrec.

Let natrec_body f g (F:set->set) n :=
  cond_set (n==zero) f ∪
  cond_set (exists2 k, k ∈ N & n==succ k) (g (pred n) (F (pred n))).

Local Instance natrec_body_morph :
  Proper (eq_set==>(eq_set==>eq_set==>eq_set)==>
                (eq_set==>eq_set)==>eq_set==>eq_set) natrec_body.
do 5 red; intros.
apply union2_morph.
 rewrite H,H2; reflexivity.

 apply cond_set_morph; auto with *.
  apply ex2_morph; auto with *.
  red; intros.
  rewrite H2; reflexivity.

  apply H0.
   rewrite H2; reflexivity.

   apply H1.
   rewrite H2; reflexivity.
Qed.

Lemma natrec_body_ext  f g :
  morph2 g ->
  forall (x x' : set) (F F' : set -> set),
  (forall y y' : set, y ∈ x -> y == y' -> F y == F' y') ->
  x == x' ->
  natrec_body f g F x == natrec_body f g F' x'.
intros gm x x' F F' eqF eqx.
apply union2_morph.
*apply cond_set_morph2; auto with *.
 rewrite eqx; reflexivity.
*apply cond_set_morph2; auto with *.
 +apply ex2_morph; [red; reflexivity| intro; rewrite eqx; reflexivity].
 +intros (k,tyk,xsuc).
  apply gm; [rewrite eqx; reflexivity|].
  apply eqF; [|rewrite eqx; reflexivity].
  rewrite xsuc.
  rewrite pred_succ_eq; auto.
  apply succ_intro1.
  reflexivity.
Qed.

Lemma natrec_body0 f g F n :
  n==zero -> natrec_body f g F n == f.
unfold natrec_body.
intros eqn.
rewrite cond_set_ok; auto with *.
rewrite cond_set_mt.
 apply union2_mt_r.

 intros (k,_,e).
 rewrite e in eqn; apply discr in eqn; trivial.
Qed.

Definition natrec (f:set) (g:set->set->set) (n:set) : set :=
  WFR (fun m => m) (natrec_body f g) n.

Global Instance natrec_morph :
  Proper (eq_set ==> (eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set) natrec.
do 4 red; intros.
apply WFR_morph; [red; auto| |trivial].
do 2 red; intros.
apply natrec_body_morph; trivial.
Qed.

Lemma N_acc n :
  n ∈ N -> Acc in_set n.
apply isWf_acc.
apply isWf_N.
Qed.

Lemma zero_min x y : ZFrepl.WFRle (fun x=>x) x y -> y==zero -> x==zero.
induction 1; intros;auto.
destruct H; [rewrite H; trivial|].  
rewrite H0 in H.
apply empty_ax in H; contradiction.
Qed.

Lemma natrec_0_eq f g n :
  n == zero ->
  natrec f g n == f.
intros eqn.
unfold natrec; rewrite WFR_eqn; auto with *.
*apply natrec_body0; auto with *.

*intros.
 apply zero_min in H; [|trivial].
 rewrite natrec_body0; trivial.
 rewrite H1 in H.
 rewrite natrec_body0; trivial.
 reflexivity.

*apply N_acc; trivial.
 rewrite eqn; apply zero_typ.
Qed.

Lemma natrec_0 f g :
  natrec f g zero == f.
apply natrec_0_eq; reflexivity.
Qed.

Lemma natrec_S_eq f g n k :
  morph2 g ->
  k ∈ N ->
  n == succ k ->
  natrec f g n == g k (natrec f g k).
intros.
unfold natrec.
rewrite WFR_eqn.
*unfold natrec_body at 1.
 rewrite cond_set_mt.
 rewrite cond_set_ok.
 rewrite union2_mt_l.
 apply pred_morph in H1; rewrite pred_succ_eq in H1; trivial.
 apply H; trivial.
 apply WFR_ext; auto with *.
 +rewrite <- H1 in H0.
  intros; apply natrec_body_ext; trivial.
 +rewrite <- H1 in H0.
  apply N_acc; trivial.
 +exists k; auto with *.
 +rewrite H1; apply discr.

*auto with *.
 
*intros.
 apply natrec_body_ext; trivial.

*apply N_acc; trivial.
 rewrite H1; apply succ_typ; trivial.
Qed.

Lemma natrec_S f g n :
  morph2 g ->
  n ∈ N ->
  natrec f g (succ n) == g n (natrec f g n).
intros; apply natrec_S_eq; auto with *.
Qed.

Lemma natrec_typ P f g n :
  morph1 P ->
  morph2 g ->
  n ∈ N ->
  f ∈ P zero ->
  (forall k h, k ∈ N -> h ∈ P k -> g k h ∈ P (succ k)) ->
  natrec f g n ∈ P n.
intros.
elim H1 using N_ind; intros.
 rewrite <- H5.
 trivial.

 rewrite natrec_0; trivial.
 rewrite natrec_S; auto.
Qed.

End Natrec.
