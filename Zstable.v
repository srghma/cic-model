
Require Export ZF.

(** Warning: uses unbounded quantifications *)

(** Stable functions *)

Definition stable_set (K:set) (F:set->set) :=
  forall X, X ⊆ K -> inter (replf X F) ⊆ F (inter X).

#[global]Instance stable_set_morph :
  Proper (eq_set==>(eq_set==>eq_set)==>iff) stable_set.
Proof.
do 3 red; intros.
apply fa_morph; intros X.
apply impl_morph;[|intros].
+apply incl_set_morph; auto with *.
+apply incl_set_morph.
 *apply inter_morph.
  apply replf_morph;[reflexivity|].
  red; intros; apply H0; trivial.
 *apply H0; reflexivity.
Qed.

(* Could be generalized with eq_index *)
#[global]Instance stable_set_mono :
  Proper (incl_set-->(eq_set==>eq_set)==>impl) stable_set.
Proof.
intros K1 K2 eqK F1 F2 eqF stbl X Xok.
rewrite <- (eqF (inter X) (inter X));[|reflexivity].
rewrite <- (stbl X).
+apply eq_incl.
 apply inter_morph.
 apply replf_morph; auto with *.
 red; intros; symmetry; apply eqF; auto with *.
+intros; rewrite Xok; auto.
Qed.

Lemma cst_stable_set A K : stable_set K (fun _ => A).
red; red; intros.
apply inter_elim with (1:=H0) (y:=A).
destruct inter_wit with (1:=H0).
rewrite replf_ax; auto.
exists x; auto with *.
Qed.

Lemma id_stable_set K : stable_set K (fun x => x).
red; red; intros.
destruct inter_wit with (1:=H0).
apply inter_intro; eauto.
intros.
apply inter_elim with (1:=H0).
rewrite replf_ax.
exists y;auto with *.
Qed.


Lemma compose_stable_set K1 K2 F G :
  Proper (incl_set ==> incl_set) F ->
  morph1 G ->
  stable_set K1 F ->
  stable_set K2 G ->
  typ_fun G K2 K1 ->
  stable_set K2 (fun o => F (G o)).
intros Fm Gm Fs Gs Gty.
red; intros.
transitivity (F (inter (replf X G))).
*red; intros.
 apply Fs.
 +red; intros.
  rewrite replf_ax in H1; auto with *.
  destruct H1 as (x,?,(?,?)).
  rewrite H3; auto.
 +rewrite compose_replf; trivial.
   red; red; intros; apply Gm; trivial.
  apply Fmono_morph in Fm.
  red; red; intros; apply Fm; trivial.
*apply Fm.
 apply Gs; trivial.
Qed.

Lemma power_stable K : stable_set K power.
red; red; intros.
apply power_intro; intros.
destruct inter_non_empty with (1:=H0).
rewrite replf_ax in H2.
destruct H2.
apply inter_intro; eauto.
clear H3 H4 H2 x0 x.
intros.
assert (z ∈ power y).
 apply inter_elim with (1:=H0).
 rewrite replf_ax.
 exists y; auto with *.
rewrite power_ax in H3; auto.
Qed.

Lemma union2_stable_disjoint K F G :
  morph1 F ->
  morph1 G ->
  stable_set K F ->
  stable_set K G ->
  (forall X Y z, X ∈ K -> Y ∈ K -> z ∈ F X -> z ∈ G Y -> False) ->
  stable_set K (fun X => F X ∪ G X).
intros Fm Gm Fs Gs disj.
intros X KX z zty.
destruct inter_wit with (1:=zty) as (w,winX).
assert (forall x, x ∈ X -> z ∈ F x ∪ G x).
{intros.
 apply inter_elim with (1:=zty).
 rewrite replf_ax.
 exists x; [|split]; auto with *.
 red; intros; rewrite H0; reflexivity. }
clear zty.
assert (z ∈ F w ∪ G w) by auto.
apply union2_elim in H0; destruct H0.
 apply union2_intro1.
 apply Fs; auto.
 apply inter_intro.
  intros.
  rewrite replf_ax in H1.
  destruct H1 as (?,?,(_,?)).
  rewrite H2; clear H2 y.
  assert (z ∈ F x ∪ G x) by auto.
  apply union2_elim in H2; destruct H2; trivial.
  elim disj with (3:=H0) (4:=H2); auto.

  exists (F w).
  rewrite replf_ax.
  exists w; auto with *.

 apply union2_intro2.
 apply Gs; auto.
 apply inter_intro.
  intros.
  rewrite replf_ax in H1.
  destruct H1 as (?,?,(_,?)).
  rewrite H2; clear H2 y.
  assert (z ∈ F x ∪ G x) by auto.
  apply union2_elim in H2; destruct H2; trivial.
  elim disj with (3:=H2) (4:=H0); auto.

  exists (G w).
  rewrite replf_ax.
  exists w; auto with *.
Qed.


Definition stable_class (K:set->Prop) (F:set->set) :=
  forall X, (forall x, x∈X -> K x) -> inter (replf X F) ⊆ F (inter X).

Lemma stable_class_eqv K F :
  stable_class K F <->
    forall X, (forall x, x ∈ X -> K x) -> stable_set X F.
Proof.
unfold stable_set, stable_class.
split; intros; eauto.
apply H with X; auto with *.
Qed.
  
Definition stable := stable_class (fun _ => True).
