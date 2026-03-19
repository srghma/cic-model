From Stdlib Require Import Setoid Compare_dec Lia.
Require Import basic.
Require Import Lambda.
Require Import ZF Zpairs Zsum Znats Ziso.
Require Import Ztarski Zfix.
Require Import Sat.

(** * The set of lambda-terms *)

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

Lemma le_lt_trans : forall m n p, p ∈ N -> m <= n -> n < p -> m < p.
intros.
apply le_case in H0; trivial.
destruct H0.
*rewrite H0; trivial.
*apply lt_trans with n; trivial.
Qed.

(* N+N iso N *)
Definition Cnn : set -> set :=
  sum_case (fun n => add n n) (fun n => succ (add n n)).

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

Lemma Cnn_iso : iso_fun (sum N N) N Cnn.
unfold Cnn; split; intros.
*do 2 red; intros.
 apply sum_case_morph; trivial.
 +red; intros.
  rewrite H0; reflexivity.
 +red; intros.
  rewrite H0; reflexivity.
*red; intros.
 elim H using sum_ind; intros.
 +rewrite sum_case_inl0;[|eauto].
  apply add_typ; rewrite H1,dest_sum_inl; trivial.
 +rewrite sum_case_inr0;[|eauto].
  apply succ_typ; apply add_typ; rewrite H1,dest_sum_inr; trivial.
*elim H using sum_ind; intros; elim H0 using sum_ind; intros.
 +rewrite !sum_case_inl0 in H1; eauto.
  rewrite H3, H5, !dest_sum_inl in H1.
  rewrite H3,H5; apply inl_morph.
  apply mult2_inj in H1; trivial.
 +rewrite sum_case_inl0,sum_case_inr0 in H1; eauto.
  rewrite H3, H5, dest_sum_inl,dest_sum_inr in H1.
  apply discr_even_odd in H1; trivial; contradiction.  
 +rewrite sum_case_inr0,sum_case_inl0 in H1; eauto.
  rewrite H3, H5, dest_sum_inl,dest_sum_inr in H1.
  symmetry in H1; apply discr_even_odd in H1; trivial; contradiction.  
 +rewrite !sum_case_inr0 in H1; eauto.
  rewrite H3, H5, !dest_sum_inr in H1.
  rewrite H3,H5; apply inr_morph.
  apply mult2_inj; trivial.
  apply succ_inj; auto using add_typ.
*elim H using N_ind; intros.
 +revert H2; apply ex2_morph; intros x; [reflexivity|].
  rewrite H1; reflexivity.
 +exists (inl zero); [apply inl_typ; apply zero_typ|].
  rewrite sum_case_inl; [apply add0;apply zero_typ|].
  intros ?? h; rewrite h; reflexivity.
 +destruct H1 as (s,tys,eqn).
  elim tys using sum_ind; intros.
  ++exists (inr x); [apply inr_typ; trivial|].
    rewrite sum_case_inl0 in eqn;[|eauto].
    rewrite H2, dest_sum_inl in eqn.
    rewrite sum_case_inr; [rewrite eqn; reflexivity|].
    intros ?? h; rewrite h; reflexivity.
  ++exists (inl (succ y0)); [auto using inl_typ, succ_typ|].
    rewrite sum_case_inr0 in eqn;[|eauto].
    rewrite H2, dest_sum_inr in eqn.
    rewrite <- eqn.
    rewrite sum_case_inl; [|intros ?? h; rewrite h; reflexivity].
    rewrite addS; [|apply succ_typ|]; trivial.
    rewrite addS_l; auto with *.
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
 
  Lemma Cnn_order : forall n, n ∈ N -> n <= Cnn (inl n) /\ n <= Cnn (inr n).
intros.
unfold Cnn.
rewrite sum_case_inl, sum_case_inr;
  [|intros ?? h;rewrite h; reflexivity|intros ?? h;rewrite h; reflexivity].
split; [apply mult2_incr;trivial|].
apply succ_intro2;apply mult2_incr;trivial.
Qed.
  Lemma Cnn_order_lt : forall n, n ∈ N -> n < Cnn (inr n).
intros.
unfold Cnn.
rewrite sum_case_inr; [|intros ?? h;rewrite h; reflexivity].
apply mult2_incr; trivial.
Qed.

(* NxN iso N *)
Definition Cnxn := NN2N.
Lemma Cnxn_iso : iso_fun (prodcart N N) N Cnxn.
unfold Cnxn.
split.
*apply NN2N_morph.
*apply NN2N_typ.
*apply NN2N_inj.
*intros; destruct NN2N_surj with (1:=H) as (p,(?,?)); exists p; trivial.
 symmetry; trivial.
Qed.

Lemma nat2set_le_intro m n :
  (m <= n)%nat ->
  nat2set m ⊆ nat2set n.
induction 1; [reflexivity|simpl].
rewrite IHle.
red; intros.
apply lt_trans with (2:=H0).
*apply succ_typ; apply nat2set_typ.
*apply succ_intro1; reflexivity.
Qed.
Lemma nat2set_le_intro' m n :
  (m <= n)%nat ->
  nat2set m <= nat2set n.
induction 1; [apply succ_intro1;reflexivity|simpl].
apply le_trans with (2:=IHle).
*apply succ_typ; apply nat2set_typ.
*apply succ_intro2; apply succ_intro1; reflexivity.
Qed.

Lemma nn2n_order n m :
  (n <= nn2n n m /\ m <= nn2n n m)%nat.
unfold nn2n.
unfold nn2n1, nn2n2; simpl.
lia.
Qed.

  Lemma Cnxn_order : forall n m, n ∈ N -> m ∈ N -> n <= Cnxn (couple n m) /\ m <= Cnxn (couple n m).
unfold Cnxn; intros.
destruct (nat2set_reflect n) as (n',?); [trivial|].
destruct (nat2set_reflect m) as (m',?); [trivial|].
rewrite H1,H2.
rewrite NN2N_def.
split; apply nat2set_le_intro'; apply nn2n_order.
Qed.
  
(* f iso A ->N  yields iso  1+A -> N*)
Definition compCnn f g x :=
  Cnn (sum_isomap f g x).
Definition compCnxn f g x :=
  Cnxn (sigma_isomap f (fun _ =>g) x).
Lemma compCnn_iso A B f g :
  iso_fun A N f -> iso_fun B N g -> iso_fun (sum A B) N (compCnn f g).
intros.
unfold compCnn.
apply iso_fun_trans with (2:=Cnn_iso).
apply sum_iso_fun_morph;trivial.
Qed.
Lemma compCnxn_iso A B f g :
  iso_fun A N f -> iso_fun B N g -> iso_fun (prodcart A B) N (compCnxn f g).
intros.
unfold compCnxn.
apply iso_fun_trans with (2:=Cnxn_iso).
apply prodcart_iso_fun_morph;trivial.
Qed.

(** Now the construction of the set of lambda terms *)

Module Lam.
Section LambdaTerms.

  Definition LAMf (X:set) :=
    sum N (* dB *)
      (sum (prodcart X X) (* App *)
         X). (* Lam *)

Instance LAMf_mono : Proper (incl_set ==> incl_set) LAMf.
do 2 red; intros.
unfold LAMf.
apply sum_mono; [reflexivity|].
apply sum_mono; [|trivial].
apply prodcart_mono; trivial.
Qed.

Instance LAMf_morph : Proper (eq_set ==> eq_set) LAMf.
apply Fmono_morph; apply LAMf_mono.
Qed.

  Hint Resolve LAMf_mono LAMf_morph : core.

  Definition mkLam :=
    compCnn (fun x => x) (* dB *)
       (compCnn Cnxn (* App *)
          (fun x => x)). (* Lam *)

  Lemma mkLam_iso : iso_fun (LAMf N) N mkLam.
unfold mkLam.
apply compCnn_iso; [apply id_iso_fun|].
apply compCnn_iso; [apply Cnxn_iso|].
apply id_iso_fun.
Qed.

  Let mkLam_morph := iso_funm mkLam_iso.
  
  Definition Lambda := N.
  Definition Var n   := mkLam (inl n).
  Definition App a b := mkLam (inr (inl (couple a b))).
  Definition Abs a   := mkLam (inr (inr a)).

  Lemma Var_typ : forall n,
    n ∈ N -> Var n ∈ Lambda.
intros.
unfold Lambda, Var.
apply mkLam_iso.
apply inl_typ; trivial.
Qed.

  Lemma App_typ : forall a b,
    a ∈ Lambda -> b ∈ Lambda -> App a b ∈ Lambda.
intros.
unfold Lambda, App.
apply mkLam_iso.
apply inr_typ; apply inl_typ.
apply couple_intro; trivial.
Qed.

Lemma App_sub a b : a ∈ Lambda -> b ∈ Lambda -> a ∈ App a b /\ b ∈ App a b.
intros tya tyb.
assert (ty1 : Cnxn (couple a b) ∈ N).
{apply Cnxn_iso; apply couple_intro; trivial. }
assert (ty2 : Cnn (inl (Cnxn (couple a b))) ∈ N).
{apply Cnn_iso; apply inl_typ; trivial. }
assert (ty3 : Cnn (inr (Cnn (inl (Cnxn (couple a b))))) ∈ N).
{apply Cnn_iso; apply inr_typ; trivial. }
unfold App, mkLam.
unfold compCnn.
assert (h := iso_funm Cnn_iso).
assert (h' := iso_funm Cnxn_iso).
rewrite sum_isomap_inr; [| |reflexivity].
2:intros ? e; apply h; apply sum_isomap_morph; auto with *.
2:red; trivial.
rewrite sum_isomap_inl; [| |reflexivity].
2:intros ? e; apply h'; trivial.
split.
*eapply le_lt_trans; [trivial| |].
 2:apply Cnn_order_lt; trivial.
 eapply le_trans; [trivial| |].
 2:apply Cnn_order; trivial.
 apply Cnxn_order; trivial.
*eapply le_lt_trans; [trivial| |].
 2:apply Cnn_order_lt; trivial.
 eapply le_trans; [trivial| |].
 2:apply Cnn_order; trivial.
 apply Cnxn_order; trivial.
Qed.
  
Lemma Abs_sub a : a ∈ Lambda -> a ∈ Abs a.
intros tya.
assert (ty1 : Cnn (inr a) ∈ N).
{apply Cnn_iso; apply inr_typ; trivial. }
assert (ty2 : Cnn (inr (Cnn (inr a))) ∈ N).
{apply Cnn_iso; apply inr_typ; trivial. }
unfold Abs, mkLam.
unfold compCnn.
assert (h := iso_funm Cnn_iso).
assert (h' := iso_funm Cnxn_iso).
rewrite sum_isomap_inr; [| |reflexivity].
2:intros ? e; apply h; apply sum_isomap_morph; auto with *.
2:red; trivial.
rewrite sum_isomap_inr; [|trivial|reflexivity].
eapply le_lt_trans; [trivial| |].
2:apply Cnn_order_lt; trivial.
apply Cnn_order; trivial.
Qed.

  Lemma Abs_typ : forall a,
    a ∈ Lambda -> Abs a ∈ Lambda.
intros.
unfold Lambda, Abs.
apply mkLam_iso.
apply inr_typ; apply inr_typ; trivial.
Qed.

  Definition F X := replf (LAMf X) mkLam.

(*  Lemma N_LAMf_case X l (P:Prop) :
    (forall n, n ∈ N -> l==Var n -> P) ->
    (forall a b, a ∈ N -> b ∈ N -> l==App a b -> P) ->
    (forall b, b ∈ N -> l==Abs b -> P) ->
    l ∈ F X -> P.
intros PV PA PL tyl.
assert (m := iso_funm mkLam_iso).
apply replf_ax in tyl; destruct tyl as (z,tyz,(_,?)).
apply iso_typ with (1:=mkLam_iso) in tyz.
generalize (iso_inv_eq _ mkLam_iso tyz); intros eql.
symmetry in eql.
set (a:=iso_inv (LAMf N) mkLam l) in eql.
assert (tya : a ∈ LAMf N).
{apply iso_inv_typ with (1:=mkLam_iso); trivial. }
elim tya using sum_ind; intros.
{rewrite H0 in eql; eauto. }
rewrite H0 in eql.
elim H using sum_ind; intros.
{apply prodcart_ax in H1; destruct H1 as (xc & ty1 & ty2).
 red in xc; rewrite xc in H2.
 rewrite H2 in eql; apply PA with (fst x)(snd x); trivial. }
{rewrite H2 in eql.
 apply PL with y0; trivial. }
Qed.*)
  Lemma N_LAMf_case l (P:Prop) :
    (forall n, n ∈ N -> l==Var n -> P) ->
    (forall a b, a ∈ N -> b ∈ N -> l==App a b -> P) ->
    (forall b, b ∈ N -> l==Abs b -> P) ->
    l ∈ N -> P.
intros PV PA PL tyl.
assert (m := iso_funm mkLam_iso).
generalize (iso_inv_eq _ mkLam_iso tyl); intros eql.
symmetry in eql.
set (a:=iso_inv (LAMf N) mkLam l) in eql.
assert (tya : a ∈ LAMf N).
{apply iso_inv_typ with (1:=mkLam_iso); trivial. }
elim tya using sum_ind; intros.
{rewrite H0 in eql; eauto. }
rewrite H0 in eql.
elim H using sum_ind; intros.
{apply prodcart_ax in H1; destruct H1 as (xc & ty1 & ty2).
 red in xc; rewrite xc in H2.
 rewrite H2 in eql; apply PA with (fst x)(snd x); trivial. }
{rewrite H2 in eql.
 apply PL with y0; trivial. }
Qed.

  Lemma LAMf_ind : forall X (P : set -> Prop),
    Proper (eq_set ==> iff) P ->
    (forall n, n ∈ N -> P (Var n)) ->
    (forall a b, a ∈ X -> b ∈ X -> P (App a b)) ->
    (forall a, a ∈ X -> P (Abs a)) ->
    forall a, a ∈ LAMf X -> P (mkLam a).
unfold LAMf; intros X P Pm PV PA PL a tya.
elim tya using sum_ind; intros.
{rewrite (Pm _ _ (mkLam_morph _ _ H0)).
 apply PV; trivial. }
rewrite (Pm _ _ (mkLam_morph _ _ H0)).
elim H using sum_ind; intros.
{apply prodcart_ax in H1; destruct H1 as (xc & ty1 & ty2).
 red in xc; rewrite xc in H2.
 rewrite (Pm _ _ (mkLam_morph _ _ (inr_morph _ _ H2))).
 apply PA; trivial. }
{rewrite (Pm _ _ (mkLam_morph _ _ (inr_morph _ _ H2))).
 apply PL; trivial. }
Qed.


  Lemma Fmono : Proper (incl_set ==> incl_set) F.
do 2 red; intros.
unfold F.
intros z.
rewrite !replf_def; auto with *.
intros (a,?,?); exists a; trivial.
revert H0; apply LAMf_mono; trivial.
Qed.

  Instance Fm : morph1 F.
auto using Fmono with *.
Qed.
  
  Lemma Fbound X : X ⊆ N -> F X ⊆ N.
red; intros.
apply replf_ax in H0.
destruct H0 as (a,tya,(_,eqz)).
rewrite eqz.
apply iso_typ with (1:=mkLam_iso).
revert tya; apply LAMf_mono; trivial.
Qed.
  Hint Resolve Fmono Fbound : core.  

  Definition L := FIX incl_set inter N (power N) F.

  Lemma L_eqn : L == F L.
symmetry; apply FIX_eqn; auto with *.
Qed.
  
  Lemma NinclL : N ⊆ L.
red; intros.
elim H using N_strong_ind; intros.
rewrite L_eqn.
apply replf_def; auto.
elim H0 using N_LAMf_case; intros.
*econstructor;[|exact H3].
 apply inl_typ; trivial.
*econstructor;[|exact H4].
 apply inr_typ; trivial.
 apply inl_typ; trivial.
 destruct App_sub with (1:=H2)(2:=H3).
 rewrite <-H4 in H5, H6.
 apply couple_intro; auto.
*econstructor;[|exact H3].
 apply inr_typ; trivial.
 apply inr_typ; trivial.
 apply Abs_sub in H2.
 rewrite <- H3 in H2.
 auto.
Qed.
  Lemma L_least X : F X ⊆ X -> L ⊆ X.
apply knaster_tarski; auto with *.
Qed.

  Lemma L_N : L == Lambda.
apply incl_eq.
*apply L_least; apply Fbound; reflexivity.
*apply NinclL.
Qed.

  Lemma Lambda_eqn : Lambda == F Lambda.
rewrite <-L_N; exact L_eqn.
  Qed.

  Lemma Lambda_ind : forall P : set -> Prop,
    Proper (eq_set ==> iff) P ->
    (forall n, n ∈ N -> P (Var n)) ->
    (forall a b, a ∈ Lambda -> b ∈ Lambda -> P a -> P b -> P (App a b)) ->
    (forall a, a ∈ Lambda -> P a -> P (Abs a)) ->
    forall a, a ∈ Lambda -> P a.
intros P Pm PV PA PL a tya.
assert (Pax : forall z, z ∈ subset Lambda P <-> z ∈ Lambda /\ P z).
{intros; rewrite subset_ax.
 apply and_iff_morphism; [reflexivity|].
 split; [destruct 1 as (z',eqz,?)|exists z; auto with *].
 rewrite eqz; trivial. }
cut (a ∈ subset Lambda P).
{intro h; apply Pax in h; apply h. }
apply NinclL in tya.
revert a tya; apply FIX_ind with (le:=incl_set); auto with *.
red; intros.
apply replf_ax in H1.
destruct H1 as (a,tya,(_,eqz)); rewrite eqz; clear z eqz.
elim tya using LAMf_ind.
*do 2 red; intros.
 rewrite H1; reflexivity.
*intros; apply subset_intro; auto.
 apply Var_typ; trivial.
*intros.
 apply H0 in H1; apply Pax in H1; destruct H1. 
 apply H0 in H2; apply Pax in H2; destruct H2. 
 apply subset_intro; auto.
 apply App_typ; trivial.
*intros.
 apply H0 in H1; apply Pax in H1; destruct H1. 
 apply subset_intro; auto.
 apply Abs_typ; trivial.
Qed.


End LambdaTerms.
End Lam.

Import Lam.
Import Lambda.

(** * Pure lambda-terms: no constants *) 
Definition CCLam := Lambda.

Fixpoint iLAM (t:term) :=
  match t with
  | Ref n => Lam.Var (nat2set n)
  | Abs M => Lam.Abs (iLAM M)
  | App u v => Lam.App (iLAM u) (iLAM v)
  end.

Lemma iLAM_typ : forall t, iLAM t ∈ CCLam.
  unfold CCLam; induction t; try destruct s; simpl;
  repeat
  (apply Var_typ || apply App_typ || apply Abs_typ ||
   (apply succ_intro1; reflexivity) || apply succ_intro2 || apply nat2set_typ);
 trivial.
Qed. 
(*
Ltac inj_pre H :=
  unfold Var, Lam.App, Lam.Abs in H;
  change (succ (succ (succ zero))) with (nat2set 3) in H;
  change (succ (succ zero)) with (nat2set 2) in H;
  change (succ zero) with (nat2set 1) in H;
  change zero with (nat2set 0) in H.

Ltac inj_lam H :=
  (apply nat2set_inj in H; try discriminate H) ||
  (apply couple_injection in H;
   let H2 := fresh "H" in
   destruct H as (H,H2); inj_lam H; inj_lam H2) ||
  idtac.

Ltac injl H := inj_pre H; inj_lam H.
*)

Ltac typ_tac :=
  repeat (apply inl_typ||apply inr_typ||
            apply couple_intro||apply nat2set_typ||apply iLAM_typ).

Ltac inj_tac H :=
  repeat (apply inl_inj in H||apply inr_inj in H||apply nat2set_inj in H
         || (apply discr_sum in H;contradiction)
         || (symmetry in H;apply discr_sum in H; contradiction)).
  
Lemma iLAM_inj : forall t u,
  iLAM t == iLAM u -> t=u.
fix IH 1.
destruct t; destruct u; simpl;
  intro H;
  (apply iso_inj with (1:=mkLam_iso) in H; [inj_tac H|typ_tac|typ_tac]).
*subst n; trivial.
*rewrite IH with (1:=H); trivial.
*apply couple_injection in H; destruct H; f_equal; auto.
Qed.

(** Embedding saturated sets in a set *)
Definition iSAT S :=
  subset CCLam (fun x => exists2 t, inSAT t S & x == iLAM t).

Instance iSAT_morph : Proper (eqSAT ==> eq_set) iSAT.
do 2 red; intros.
rewrite eqSAT_def in H.
unfold iSAT.
apply subset_ext; intros.
 apply subset_intro; trivial.
 destruct H1.
 exists x1; trivial.
 rewrite H; trivial.

 apply subset_elim1 in H0; trivial.

 apply subset_elim2 in H0.
 destruct H0.
 destruct H1.
 exists x1; trivial.
 exists x2; trivial.
 rewrite <- H; trivial.
Qed.

Definition complSAT (P:term->Prop) :=
  interSAT (fun p:{S|forall t, sn t -> P t -> inSAT t S} => proj1_sig p).

Definition sSAT x :=
  complSAT (fun t => iLAM t ∈ x).

Instance sSAT_morph : Proper (eq_set ==> eqSAT) sSAT.
do 2 red; intros.
unfold sSAT, complSAT.
apply interSAT_morph_subset; simpl; intros.
 split; intros.
  rewrite <- H in H2; auto.
  rewrite H in H2; auto.

 reflexivity.
Qed.

Lemma iSAT_id : forall S, eqSAT (sSAT (iSAT S)) S.
intros.
rewrite eqSAT_def.
unfold sSAT, complSAT.
intros.
rewrite <- interSAT_ax.
split; intros.
 assert (forall t, sn t -> iLAM t ∈ iSAT S -> inSAT t S).
  intros.
  unfold iSAT in H1.
  rewrite subset_ax in H1.
  destruct H1 as (_,(x,eq_x,(u,inS,eq_u))).
  rewrite eq_u in eq_x; apply iLAM_inj in eq_x.
  rewrite eq_x; trivial.
 exact (H (exist _ S H0)). 

 destruct x; simpl.
 apply i.
  apply sat_sn in H; trivial.

  unfold iSAT.
  apply subset_intro.
   apply iLAM_typ.

   exists t; trivial; reflexivity.

 exists snSAT; intros.
 apply snSAT_intro; trivial.
Qed.

Lemma sSAT_mt : eqSAT (sSAT empty) neuSAT.
unfold sSAT,complSAT.
apply neuSAT_ext.
red; intros.
assert (h : forall t, sn t -> iLAM t ∈ empty -> inSAT t neuSAT).
 intros.
 apply empty_ax in H1; contradiction.
assert (H' := fun h => interSAT_elim H (exist _ neuSAT h));
   clear H; simpl in H'.
auto.
Qed.


Definition SATset :=
  subset (power CCLam) (fun S => iSAT(sSAT S)==S).

Definition replSAT F :=
  replf (power CCLam) (fun P => F (sSAT P)).

Lemma replSAT_ax : forall f z,
  Proper (eqSAT ==> eq_set) f ->
  (z ∈ replSAT f <-> exists A, z == f A).
unfold replSAT.
intros.
rewrite replf_def.
 split; intros.
  destruct H0 as (y,isSet,img).
  exists (sSAT y); trivial.

  destruct H0 as (S,eqz).
  exists (iSAT S).
   apply power_intro; intros.
   unfold iSAT in H0.
   apply subset_elim1 in H0; trivial.

   rewrite iSAT_id; trivial.

 do 2 red; intros.
 rewrite <- H1; reflexivity.
Qed.
(*
Lemma G_CCLam U :
  grot_univ U ->
  N ∈ U ->
  CCLam ∈ U.
trivial.
Qed.
Hint Resolve G_CCLam : core.
*)
