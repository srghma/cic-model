
Require Export basic ZF Zstable Zpairs Zrelations Ziso.

(** * Impredicativity of props *)

Definition prf_trm := empty.
Definition props := power (singl prf_trm).

Lemma empty_in_props : empty ∈ props.
apply power_intro; intros.
apply empty_ax in H; contradiction.
Qed.

Lemma one_in_props : singl prf_trm ∈ props.
apply power_intro; auto.
Qed.
Hint Resolve empty_in_props one_in_props : core.

Lemma props_proof_irrelevance x P :
  P ∈ props -> x ∈ P -> x == empty.
intros.
apply singl_elim.
apply power_elim with (1:=H); trivial.
Qed.

Lemma props_are_hprop P Q p q :
  P ∈ props -> Q ∈ props -> p ∈ P -> q ∈ Q -> p==q.
intros tyP tyQ typ tyq.
apply props_proof_irrelevance in typ; trivial.
apply props_proof_irrelevance in tyq; trivial.
rewrite tyq; trivial.
Qed.

Lemma cc_impredicative_prod : forall dom F,
  (forall x, x ∈ dom -> F x ∈ props) ->
  cc_prod dom F ∈ props.
Proof.
intros.
unfold props, prf_trm.
apply power_intro; intros.
apply singl_intro_eq.
rewrite cc_eta_eq with (1:=H0).
apply cc_impredicative_lam.
intros.
apply props_proof_irrelevance with (F x); auto.
apply cc_prod_elim with (1:=H0); trivial.
Qed.

Lemma cc_impredicative_arr : forall A B,
  B ∈ props ->
  cc_arr A B ∈ props.
intros.
apply cc_impredicative_prod; auto.
Qed.


Lemma cc_forall_intro A B :
  ext_fun A B ->
  (forall x, x ∈ A -> empty ∈ B x) ->
  empty ∈ cc_prod A B.
intros.
rewrite <- cc_impredicative_lam with (dom:=A) (F:= fun _ => empty); auto with *.
apply cc_prod_intro; auto with *.
Qed.

Lemma cc_forall_elim A B x :
  empty ∈ cc_prod A B ->
  x ∈ A ->
  empty ∈ B x.
intros.
setoid_replace empty with (cc_app empty x).
 apply cc_prod_elim with (1:=H); trivial.

 symmetry; apply empty_ext; red; intros.
 rewrite <- couple_in_app in H1.
 apply empty_ax in H1; trivial.
Qed.

Definition cc_exists := sup. 
Hint Unfold cc_exists : core.


Lemma cc_exists_typ A B :
  ext_fun A B ->
  (forall x, x ∈ A -> B x ∈ props) ->
  cc_exists A B ∈ props.
unfold cc_exists; intros.
apply power_intro; intros.
rewrite sup_ax in H1.
destruct H1 as (?,?,(_,?)).
apply singl_intro_eq.
apply props_proof_irrelevance with (B x); auto.
Qed.

Lemma cc_exists_intro A B x :
  ext_fun A B -> 
  x ∈ A ->
  empty ∈ B x ->
  empty ∈ cc_exists A B.
unfold cc_exists; intros.
rewrite sup_ax; eauto.
Qed.

Lemma cc_exists_elim A B :
  ext_fun A B ->
  empty ∈ cc_exists A B ->
  exists2 x, x ∈ A & empty ∈ B x.
unfold cc_exists; intros.
rewrite sup_def in H0; auto.
Qed.


(** * mapping (meta-level) propositions to props back and forth *)

Definition P2p (P:Prop) := cond_set P (singl prf_trm).
Definition p2P p := prf_trm ∈ p.

Instance P2p_morph : Proper (iff ==> eq_set) P2p.
do 2 red; intros; unfold P2p.
apply cond_set_morph; auto with *.
Qed.

Instance p2P_morph : Proper (eq_set ==> iff) p2P.
do 2 red; intros; apply in_set_morph; auto with *.
Qed.

Lemma P2p_ax P x :
   x ∈ P2p P <-> x == empty /\ P.
unfold P2p.
rewrite cond_set_ax.
apply and_iff_morphism; auto with *.
split; intros.
 apply singl_elim in H; auto with *.

 apply singl_intro_eq; trivial.
Qed.

Lemma P2p_typ : forall P, P2p P ∈ props.
unfold P2p; intros.
apply power_intro; intros.
rewrite cond_set_ax in H; destruct H; trivial.
Qed.

Lemma P2p2P : forall P, p2P (P2p P) <-> P.
unfold P2p, p2P; intros.
rewrite cond_set_ax.
split; intros.
 destruct H; trivial.

 split; trivial; apply singl_intro.
Qed.

Lemma p2P2p : forall p, p ∈ props -> P2p (p2P p) == p.
intros.
apply eq_set_ax; intros.
rewrite P2p_ax.
split; intros.
 destruct H0.
 rewrite H0; trivial.

 rewrite props_proof_irrelevance with (2:=H0) in H0|-*; auto with *.
Qed.

Lemma P2p_forall A (B:set->Prop) :
   (forall x x', x ∈ A -> x == x' -> (B x <-> B x')) ->
   P2p (forall x, x ∈ A -> B x) == cc_prod A (fun x => P2p (B x)).
intros.
unfold P2p.
apply eq_intro; intros.
 rewrite cond_set_ax in H0; destruct H0.
 apply singl_elim in H0.
 rewrite H0.
 apply cc_forall_intro; intros.
  do 2 red; intros.
  apply cond_set_morph; auto with *.

  rewrite cond_set_ax; split; auto; apply singl_intro.
  
 rewrite cond_set_ax; split; intros.
  apply singl_intro_eq.
  apply props_proof_irrelevance with (2:=H0).
  apply cc_impredicative_prod; intros.
  apply P2p_typ.

  specialize cc_prod_elim with (1:=H0) (2:=H1); intro.
  rewrite cond_set_ax in H2; destruct H2; trivial.
Qed.

Lemma cc_prod_forall A B :
   ext_fun A B ->
   (forall x, x ∈ A -> B x ∈ props) ->
   cc_prod A B == P2p (forall x, x ∈ A -> p2P (B x)).
intros.
rewrite P2p_forall.
 apply cc_prod_ext; auto with *.
 red; intros.
 rewrite p2P2p; auto.
 apply H0; rewrite <- H2; trivial.

 intros.
 apply in_set_morph; auto with *.
Qed.

Lemma cc_arr_imp A B :
   B ∈ props ->
   cc_arr A B == P2p ((exists x, x ∈ A) -> p2P B).
intros; unfold cc_arr; rewrite cc_prod_forall; intros; auto.
apply P2p_morph.
split; intros; eauto with *.
destruct H1; eauto.
Qed.

Lemma predicate_ext P Q f g :
  P ∈ props ->
  Q ∈ props ->
  f ∈ cc_arr P Q ->
  g ∈ cc_arr Q P ->
  P == Q.
intros.
rewrite <- (p2P2p P); trivial.  
rewrite <- (p2P2p Q); trivial.  
apply P2p_morph.
split; intros.
 specialize cc_prod_elim with (1:=H1) (2:=H3); intros.
 rewrite props_proof_irrelevance with (2:=H4) in H4; trivial.

 specialize cc_prod_elim with (1:=H2) (2:=H3); intros.
 rewrite props_proof_irrelevance with (2:=H4) in H4; trivial.
Qed.

(** * Prop-Truncation *)

Definition trunc (x:set) := P2p (exists w, w ∈ x).

Instance trunc_morph : morph1 trunc.
do 2 red; intros.
apply P2p_morph.
apply ex_morph; intros w.
rewrite H; reflexivity.
Qed.

Lemma trunc_prop x : trunc x ∈ props.
apply P2p_typ.
Qed.

Definition trunc_descr P : set := union P.

Instance trunc_descr_morph : morph1 trunc_descr.
Proof union_morph.

Lemma trunc_ind X P F p :
  (forall x y, x ∈ P -> y ∈ P -> x==y) ->
  typ_fun F X P ->
  p ∈ trunc X ->
  trunc_descr P ∈ P.
intros Pp tyF wit.
apply P2p_ax in wit.
destruct wit as (_,(x,tyx)).
assert (witP : F x ∈ P) by auto.
unfold trunc_descr.
apply in_reg with (F x); auto.
apply union_ext; intros.
 rewrite (Pp (F x) y); trivial.  

 exists (F x); trivial.
Qed.
  
(** * Classical propositions: we also have a model for classical logic *)

Definition cl_props := subset props (fun P => ~~p2P P -> p2P P).

Lemma cc_cl_impredicative_prod : forall dom F,
  ext_fun dom F ->
  (forall x, x ∈ dom -> F x ∈ cl_props) ->
  cc_prod dom F ∈ cl_props.
Proof.
intros dom F eF H.
rewrite cc_prod_forall; intros; trivial.
 apply subset_intro; intros.
  apply P2p_typ.

  rewrite P2p2P in H0|-*; intros.
  specialize H with (1:=H1).
  apply subset_elim2 in H; destruct H.
  rewrite H; apply H2.
  intro nx; apply H0; intro h; apply nx.
  rewrite <- H; auto.

 specialize H with (1:=H0); apply subset_elim1 in H; trivial.
Qed.

Lemma cl_props_classical P :
  P ∈ cl_props ->
  cc_arr (cc_arr P empty) empty ⊆ P.
red; intros.
unfold cl_props in H; rewrite subset_ax in H.
destruct H as (Pty,(P',eqP,clP)).
rewrite <- eqP in clP; clear P' eqP.
assert (z == empty).
 apply props_proof_irrelevance with (2:=H0).
 apply cc_impredicative_arr.
 apply power_intro; intros.
 apply empty_ax in H; contradiction.
rewrite H; apply clP.
intro nP.
assert (empty ∈ cc_arr P empty).
 apply cc_forall_intro; intros; auto with *.
 elim nP.
 rewrite props_proof_irrelevance with (1:=Pty) (2:=H1) in H1; trivial.
apply empty_ax with (cc_app z empty).
apply cc_arr_elim with (2:=H1); trivial.
Qed.

(** Auxiliary stuff for strong normalization proof: every type
   contains the empty set. 
 *)

(* The operator that adds the empty set to a type. *)
Definition cc_bot x := singl empty ∪ x.

Lemma cc_bot_bot x : empty ∈ cc_bot x. 
apply union2_intro1; apply singl_intro.
Qed.
Lemma cc_bot_intro x z : z ∈ x -> z ∈ cc_bot x.
intros.
apply union2_intro2; trivial.
Qed.
Hint Resolve cc_bot_bot cc_bot_intro : core.

Instance cc_bot_mono : Proper (incl_set==>incl_set) cc_bot.
do 3 red; intros.
apply union2_elim in H0; destruct H0.
 apply union2_intro1; trivial.
 apply union2_intro2; auto.
Qed.

Instance cc_bot_morph : morph1 cc_bot.
unfold cc_bot; do 2 red; intros.
rewrite H; reflexivity.
Qed.

Lemma cc_bot_ax : forall x z,
  z ∈ cc_bot x <-> z == empty \/ z ∈ x.
unfold cc_bot; intros.
split; intros.
 apply union2_elim in H; destruct H; auto.
 apply singl_elim in H; auto.

 destruct H.
  apply union2_intro1; rewrite H; apply singl_intro.

  apply union2_intro2; trivial.
Qed.

Lemma cc_bot_prop :
    forall P, P ∈ props -> cc_bot P ∈ props.
intros.
apply power_intro; intros.
rewrite cc_bot_ax in H0.
destruct H0;[rewrite H0;apply singl_intro|].
apply power_elim with (1:=H); trivial.
Qed.

Lemma cc_bot_nop x :
  empty ∈ x -> cc_bot x == x.
intros.
apply eq_set_ax; split; intros; auto.
apply cc_bot_ax in H0; destruct H0; auto.
rewrite H0; trivial.
Qed.

Lemma cc_bot_cl_prop :
    forall P, P ∈ cl_props -> cc_bot P ∈ cl_props.
intros.
apply subset_intro.
 apply cc_bot_prop.
 apply subset_elim1 in H; auto.

 intros _.
 red; rewrite cc_bot_ax; left; reflexivity.
Qed.

Lemma cc_prod_mt U V :
  ext_fun U V ->
  (forall x, x ∈ U -> empty ∈ V x) ->
  cc_bot (cc_prod U V) == cc_prod U V.
intros Vm Vmt.
unfold cc_bot.
apply eq_intro; intros; auto.
rewrite cc_bot_ax in H; destruct H; trivial.
rewrite H.
assert (cc_lam U (fun _ => empty) == empty).
 apply cc_impredicative_lam; auto with *.
rewrite <- H0.
apply cc_prod_intro; auto with *.
Qed.

Lemma cc_prod_ext_mt U V f :
  ext_fun (cc_bot U) V ->
  empty ∈ V empty ->
  ~ empty ∈ U ->
  f ∈ cc_prod U V ->
  f ∈ cc_prod (cc_bot U) V.
intros.
rewrite cc_prod_def; [|trivial].
split.
*apply cc_prod_is_cc_fun in H2.
 destruct H2; split; [trivial|].
 rewrite H3; red; auto.
*intros x tyx.
 rewrite cc_bot_ax in tyx; destruct tyx.
 +rewrite cc_app_outside_domain.
  2:apply cc_prod_is_cc_fun in H2; eexact H2.
  ++apply eq_elim with (V empty); trivial.
    apply H; auto with *.
  ++rewrite H3; trivial.
 +apply cc_prod_elim with (1:=H2); trivial.
Qed.

Lemma cc_bot_stable_set X :
  (forall z x, z ∈ X ->  x ∈ z -> x==empty \/ ~x==empty) ->
  stable_set X cc_bot.
intros empty_dec Y YX.
red; intros.
destruct inter_wit with (1:=H).
assert (forall x, x ∈ Y -> z ∈ cc_bot x).
{intros.
 apply inter_elim with (1:=H).
 apply replf_ax; auto with *.
 exists x0; auto with *. }
assert (zcase:=H1 _ H0).
apply cc_bot_ax in zcase; destruct zcase.
*rewrite H2; auto.
*destruct (empty_dec x z) as [is_mt|not_mt]; auto.
 +rewrite is_mt; auto.
 +apply cc_bot_intro. 
  apply inter_intro;[|eauto].
  intros. 
  apply H1 in H3.
  apply cc_bot_ax in H3; destruct H3; [contradiction|trivial].
Qed.

Definition fbot f x := cond_set (~x==empty) (f x).

Lemma eqf_fbot X f f' :
  ~ empty ∈ X ->
  eq_fun X f f' ->
  eq_fun (cc_bot X) (fbot f) (fbot f').
red; intros.
rewrite cc_bot_ax in H1; destruct H1.
 unfold fbot; rewrite cond_set_mt;[|unfold Tnot;tauto].
 rewrite H2 in H1; rewrite cond_set_mt;[|unfold Tnot; tauto].
 reflexivity.

 assert (~x==empty).
  intro h; rewrite h in H1; contradiction.
 unfold fbot; rewrite cond_set_ok; trivial.
 rewrite H2 in H3; rewrite cond_set_ok; trivial.
 apply H0; trivial.
Qed.

Lemma iso_cc_bot X Y f :
  iso_fun X Y f ->
  ~ empty ∈ X ->
  ~ empty ∈ Y ->
  iso_fun (cc_bot X) (cc_bot Y) (fbot f).
unfold fbot.
intros.
assert (fm := iso_funm H).
split; intros.
 do 2 red; intros.
 rewrite H2; reflexivity.

 red; intros.
 apply cc_bot_ax in H2; destruct H2.
 rewrite cond_set_mt; auto.

  rewrite cond_set_ok.
   apply cc_bot_intro.
   apply (iso_typ H); trivial.

   intro h; rewrite h in H2; contradiction.

 rewrite cc_bot_ax in H2,H3.
 destruct H2; [rewrite H2|]; (destruct H3;[rewrite H3|]); try reflexivity.
  rewrite cond_set_mt in H4;[|unfold Tnot; tauto].
  rewrite cond_set_ok in H4.
   elim H1.
   rewrite H4.
   apply (iso_typ H); trivial.

   intro h; rewrite h in H3; contradiction.

  rewrite cond_set_ok in H4.
   rewrite cond_set_mt in H4;[|unfold Tnot; tauto].
   elim H1.
   rewrite <- H4.
   apply (iso_typ H); trivial.

   intro h; rewrite h in H2; contradiction.

  rewrite cond_set_ok in H4.
   rewrite cond_set_ok in H4.
    apply (iso_inj H) in H4; trivial.

    intro h; rewrite h in H3; contradiction.
   intro h; rewrite h in H2; contradiction.

 rewrite cc_bot_ax in H2; destruct H2.
  exists empty; auto.
  rewrite cond_set_mt; auto with *.

  destruct (iso_surj H) with y; trivial.
  exists x; auto.
  rewrite cond_set_ok; trivial.
  intro h; rewrite h in H3; contradiction.
Qed.

(** Taking the bottom value out of the domain of a function *)
Require Import Zbot.
Definition squash f := squ (singl empty) f.

#[global]Instance squash_morph : morph1 squash.
do 2 red; intros.
apply subset_morph; auto with *.
Qed.
(*
Lemma squash_ax f z :
  z ∈ squash f <-> z ∈ f /\ ~ fst z == empty.
unfold squash; rewrite subset_ax.
apply and_iff_morphism; auto with *.
split; intros.
 destruct H.
 rewrite H; trivial.

 exists z; auto with *.
Qed.

Lemma squash_nmt f x :
  ~ x == empty ->
  cc_app (squash f) x == cc_app f x.
intros Hnmt.
apply eq_set_ax; intros z.
rewrite <- couple_in_app.
rewrite squash_ax, fst_def.
rewrite couple_in_app.
split;[destruct 1; trivial|auto].
Qed.

Lemma squash_mt f :
  cc_app (squash f) empty == empty.
apply empty_ext.
red; intros.  
rewrite <- couple_in_app in H.
rewrite squash_ax, fst_def in H.
destruct H.
apply H0; reflexivity.
Qed.

Lemma squash_eq  A B f :
  ~ empty ∈ A ->
  f ∈ cc_prod (cc_bot A) B ->
  squash f == cc_lam A (cc_app f).
intros.
apply eq_set_ax; intros z.
rewrite squash_ax.
rewrite cc_lam_def.
2:do 2 red; intros; apply cc_app_morph; auto with *.
split; intros.
 destruct H1.
 destruct cc_prod_is_cc_fun with (1:=H0)(2:=H1).
 apply union2_elim in H4; destruct H4.
  apply singl_elim in H4; contradiction.
 exists (fst z); trivial.
 exists (snd z); trivial.
 rewrite <- couple_in_app.
 rewrite H3 in H1; trivial.

 destruct H1 as (x,xty,(y,yty,eqc)).
 rewrite <- couple_in_app in yty.
 rewrite eqc; split; trivial.
 rewrite fst_def; intro h; rewrite h in xty; auto.
Qed.

Lemma squash_typ A B f :
  ext_fun (cc_bot A) B ->
  ~ empty ∈ A ->
  f ∈ cc_prod (cc_bot A) B ->
  squash f ∈ cc_prod A B.
intros.
rewrite squash_eq with (2:=H1); trivial.
apply cc_prod_intro; intros.
 do 2 red; intros; apply cc_app_morph; auto with *.

 do 2 red; intros; apply H; trivial.
 apply cc_bot_intro; trivial.

 apply cc_prod_elim with (1:=H1).
 apply cc_bot_intro; trivial.
Qed.
*)
