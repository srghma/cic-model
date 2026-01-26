Require Import ZF.

(** We show that replf is derivable in Z.
    [replf a f] is defined by induction on the syntax of f.
    Termination is ensured by lexico order on (1) the number
    of occurences of replf in f, and (2) the size of f 
 *)

(* First we show it is enough to find an upper bound [b].
   Then [replf a f] can be derived by separation *)
Lemma replf_der_ub a f b :
  ext_fun a f ->
  replf a f ⊆ b ->
  replf a f == subset b (fun y => exists2 x, x ∈ a & y == f x).
Proof.
intros fext ub.
apply eq_set_ax; intros z.
rewrite replf_ax; trivial.
rewrite subset_ax.
split.
*intros (x,tyx,eqz).
 split.
 +apply ub.
  apply replf_intro with x; trivial.
 +exists z; [reflexivity|exists x; trivial].
*intros (_,(z',eqz,(x,tyx,eqz'))).
 rewrite <- eqz in eqz'; eauto.
Qed.

(* Projection case (variable) *)
Lemma replf_der_proj a :
  replf a (fun x => x) == a.
Proof.
apply replf_id.
Qed.

(* Constant case: deals with empty, infity, and global variables *)
Lemma replf_der_cst a b :
  replf a (fun _ => b) ⊆ singl b.
Proof.
red; intros.
rewrite replf_ax in H; [| auto with *].
destruct H as (x,tyx,eqz).
apply singl_intro_eq; trivial.
Qed.

Lemma replf_der_pair a F G :
  ext_fun a F ->
  ext_fun a G ->
  replf a (fun x => pair (F x) (G x)) ⊆ power (replf a F ∪ replf a G).
intros Fext Gext z.
rewrite replf_ax; [|do 2 red; intros; apply pair_morph; auto].
intros (x,tyx,eqz).
rewrite eqz. clear z eqz.
rewrite power_ax; intros z tyz.
rewrite pair_ax in tyz; destruct tyz as [eqz|eqz].
*apply union2_intro1.
 rewrite replf_ax; eauto.
*apply union2_intro2.
 rewrite replf_ax; eauto.
Qed.

Lemma replf_der_union a F :
  ext_fun a F ->
  replf a (fun x => union (F x)) ⊆ power (union (union (replf a F))).
intros Fext z.
rewrite replf_ax; [|do 2 red; intros; apply union_morph; auto].
intros (x,tyx,eqz).
rewrite eqz. clear z eqz.
rewrite power_ax; intros z tyz.
rewrite union_ax in tyz; destruct tyz as (y,tyz,img).
rewrite union_ax.
exists y; trivial.
rewrite union_ax.
exists (F x); trivial.
apply replf_intro with x; auto with *.
Qed.

Lemma replf_der_power a F :
  ext_fun a F ->
  replf a (fun x => power (F x)) ⊆ power (power (union (replf a F))).
intros Fext z.
rewrite replf_ax; [|do 2 red; intros; apply power_morph; auto].
intros (x,tyx,eqz).
rewrite eqz. clear z eqz.
rewrite power_ax; intros z tyz.
rewrite power_ax in tyz.
rewrite power_ax; intros y tyy.
rewrite union_ax.
exists (F x); [auto|].
apply replf_intro with x; auto with *.
Qed.

Lemma replf_der_subset a F P :
  ext_fun a F ->
  (forall x x' y, x ∈ a -> x==x' -> y ∈ F x -> (P x y <-> P x' y)) ->
  replf a (fun x => subset (F x) (P x)) ⊆ power (union (replf a F)).
intros Fext Pext z.
rewrite replf_ax.
2:{do 2 red; intros.
   apply subset_morph; auto.
   red; auto. }
intros (x,tyx,eqz).
rewrite eqz. clear z eqz.
rewrite power_ax; intros z tyz.
rewrite subset_ax in tyz.
destruct tyz as (tyz,_).
rewrite union_ax.
exists (F x); [auto|].
apply replf_intro with x; auto with *.
Qed.

Require Import ZFpairs.
(* NB: prodcart, fst and snd are defined in Zermelo *)

Lemma replf_der_replf a F G :
  ext_fun a F ->
  (forall x x' y y', x ∈ a -> x==x' -> y==y' -> G x y == G x' y') ->
  replf a (fun x => replf (F x) (G x)) ⊆ 
    power (replf (prodcart a (union (replf a F))) (fun p => G (fst p) (snd p))).
intros Fext Gext z.
rewrite replf_ax.
2:{do 2 red; intros.
   apply replf_morph; auto.
   red; auto. }
intros (x,tyx,eqz).
rewrite eqz. clear z eqz.
rewrite power_ax; intros z tyz.
rewrite replf_ax in tyz; auto.
2:do 2 red; intros; auto with *.
destruct tyz as (y,tyy,eqz).
assert (y ∈ union (replf a F)).
{apply union_intro with (F x); trivial.
 apply replf_intro with x; auto with *. }
rewrite replf_ax.
*exists (couple x y); [apply couple_intro; trivial|].
 rewrite eqz.
 apply Gext; trivial.
 +symmetry; apply fst_def.
 +symmetry; apply snd_def.
*do 2 red; intros.
 apply Gext.
 +apply fst_typ in H0; trivial.
 +apply fst_morph; trivial.
 +apply snd_morph; trivial.
Qed.
