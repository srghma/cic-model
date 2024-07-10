Require Import Inverse_Image.
Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFord.
Require Import ZFgrothendieck.
Require Import ZFlist ZFfixfun.

Section EncodeBigParameter.

Variable Arg : set.
Variable A : set -> set.
Variable B : set -> set -> set.
Variable f : set -> set -> set -> set.
Hypothesis Am : morph1 A.
Hypothesis Bm : morph2 B.
Hypothesis fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) f.
Hypothesis ftyp : forall a x y,
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  f a x y ∈ Arg.

(** Encoding big parameters as (small) paths from a fixed parameter [a].
    First, the type operator. *)
Let L X a :=
  singl empty ∪ Σ x ∈ A a, Σ y ∈ B a x, X (f a x y).

Instance Lmorph : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) L.
do 3 red; intros.
apply union2_morph;[reflexivity|].
apply sigma_morph; auto.
red; intros.
apply sigma_morph.
 apply Bm; auto.

 red; intros.
 apply H; apply fm; trivial.
Qed.
Hint Resolve Lmorph : core.

Lemma L_intro1 X a : empty ∈ L X a.
apply union2_intro1.
apply singl_intro.
Qed.

Lemma L_intro2 a x y q X :
  morph1 X ->
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  q ∈ X (f a x y) ->
  couple x (couple y q) ∈ L X a.
unfold L; intros.
apply union2_intro2.
apply couple_intro_sigma; trivial.
 do 2 red; intros; apply sigma_morph.
  apply Bm; auto with *.

  red; intros; apply H; apply fm; auto with *.

 apply couple_intro_sigma; trivial.
 do 2 red; intros; apply H; apply fm; auto with *.
Qed.

Definition L_match q f g :=
  if_prop (exists x y q', q == couple x (couple y q'))
          (g (fst q) (fst (snd q)) (snd (snd q)))
          f.

Lemma L_match_mt l f0 g :
  l==empty ->
  L_match l f0 g == f0.
intros; unfold L_match.
apply if_right; trivial.
intros (x,(y,(q,eql))).
rewrite eql in H; apply couple_mt_discr in H; trivial.
Qed.

Lemma L_match_cons l f0 g x y q :
  Proper (eq_set==>eq_set==>eq_set==>eq_set) g ->
  l==couple x (couple y q) ->
  L_match l f0 g == g x y q.
intros; unfold L_match.
rewrite if_left.
 rewrite H0,!snd_def,!fst_def; reflexivity.

 exists x; exists y;exists q; trivial.
Qed.

Lemma L_elim a q X :
  morph1 X ->
  a ∈ Arg ->
  q ∈ L X a ->
  q == empty \/
  exists2 x, x ∈ A a &
  exists2 y, y ∈ B a x &
  exists2 q', q' ∈ X (f a x y) &
  q == couple x (couple y q').
intros.
destruct union2_elim with (1:=H1);[left|right].
 apply singl_elim in H2; trivial.

 clear H1.
 assert (fst q ∈ A a).
  apply fst_typ_sigma in H2; auto.
 exists (fst q); trivial.
 assert (q == couple (fst q) (snd q)).
  apply surj_pair with (1:=subset_elim1 _ _ _ H2).
 apply snd_typ_sigma with (y:=fst q) in H2; auto with *.
  2:do 2 red; intros; apply sigma_morph.
  2: apply Bm; auto with *.
  2: red; intros; apply H; apply fm; auto with *.
 assert (fst (snd q) ∈ B a (fst q)).
  apply fst_typ_sigma in  H2; trivial.
 exists (fst (snd q)); trivial.
 exists (snd (snd q)).
  apply snd_typ_sigma with (y:=fst (snd q)) in H2; auto with *.
  do 2 red; intros; apply H; apply fm; auto with *.

  apply transitivity with (1:=H3).
  apply couple_morph; [reflexivity|].
  apply surj_pair with (1:=subset_elim1 _ _ _ H2).
Qed.


Lemma Lmono : mono_fam Arg L.
do 3 red; intros.
destruct L_elim with (3:=H3) as [znil|(x,xty,(y,yty,(q,qty,zcons)))]; trivial.
 rewrite znil; apply L_intro1.

 rewrite zcons; apply L_intro2; trivial.
 revert qty; apply H1.
 apply ftyp; auto.
Qed.
Hint Resolve Lmono : core.

(** The fixpoint: paths
    Arg' a == 1 + { x : A a ; y : B a x ; l : Arg' (f a x y) } *)
Definition Arg' : set -> set := TIF Arg L omega.

Instance Arg'_morph : morph1 Arg'.
apply TIF_morph; reflexivity.
Qed.

Lemma Arg'_ind P :
  Proper (eq_set ==> eq_set ==> iff) P ->
  (forall a, a∈ Arg -> P a empty) ->
  (forall a x y q,
   a ∈ Arg ->
   x ∈ A a ->
   y ∈ B a x ->
   q ∈ Arg' (f a x y) ->
   P (f a x y) q ->
   P a (couple x (couple y q))) ->
  forall a q,
  a ∈ Arg -> 
  q ∈ Arg' a ->
  P a q.
unfold Arg'; intros.
revert a q H2 H3; elim isOrd_omega using isOrd_ind; intros.
rename y into o.
apply TIF_elim in H6; trivial.
destruct H6 as (o',?,?); trivial.
destruct L_elim with (3:=H7) as [qnil|(x,xty,(y,yty,(q',q'ty,qcons)))]; trivial.
 apply TIF_morph; reflexivity.

 rewrite qnil; auto.

 rewrite qcons.
 apply H1; trivial.
  revert q'ty; apply TIF_mono; auto.
  apply isOrd_inv with o; trivial.

  apply H4 with o'; trivial.
  apply ftyp; trivial.
Qed.

Lemma Arg'_eqn a :
  a ∈ Arg ->
  Arg' a == L Arg' a.
intros.
apply eq_intro; intros.
 apply Arg'_ind with (5:=H0); intros; trivial.
  apply morph_impl_iff2; auto with *.
  do 4 red; intros.
  rewrite <- H2; rewrite <- H1; trivial.

  apply L_intro1.

  apply L_intro2; trivial with *.

 destruct L_elim with (3:=H0) as [qnil|(x,xty,(y,yty,(q,qty,qcons)))];
   trivial with *.
  apply TIF_intro with (osucc zero); auto with *.
  rewrite qnil; apply L_intro1.

  apply TIF_elim in qty; auto.
  destruct qty as (o,oo,qty).
  apply TIF_intro with (osucc o); auto.
  rewrite qcons; apply L_intro2; auto.
   apply TIF_morph; reflexivity.

   rewrite TIF_mono_succ; auto.
   eauto using isOrd_inv.
Qed.

Lemma Arg'_intro1 a :
  a ∈ Arg ->
  empty ∈ Arg' a.
intros.
rewrite Arg'_eqn; trivial.
apply L_intro1.
Qed.

Lemma Arg'_intro2 a x y q :
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  q ∈ Arg' (f a x y) ->
  couple x (couple y q) ∈ Arg' a.
intros.
rewrite Arg'_eqn; trivial.
apply L_intro2; trivial with *.
Qed.

(** Auxiliary result to build recursive function over an Arg' *)

Definition Arg'lt q q' :=
  exists x y, q' == couple x (couple y q).
Definition Arg'K q := Acc Arg'lt q.


Instance Arg'ltm : Proper (eq_set ==> eq_set ==> iff) Arg'lt.
do 3 red; intros.
unfold Arg'lt.
apply ex_morph; intro x1.
apply ex_morph; intro y1.
rewrite H,H0; reflexivity.
Qed.

Instance Arg'Km : Proper (eq_set ==> iff) Arg'K.
do 2 red; intros.
apply wf_morph with (eqA := eq_set); auto with *.
apply Arg'ltm.
Qed.

Lemma Arg'K_intro : forall a q, a ∈ Arg -> q ∈ Arg' a -> Arg'K q.
intros.
pattern a, q; apply Arg'_ind with (a:=a) (q:=q); trivial.
 do 3 red; intros.
 apply Arg'Km; trivial.

 intros; constructor; intros.
 destruct H2 as (x1,(y1,h)).
 symmetry in h; apply couple_mt_discr in h; contradiction.

 intros.
 constructor; intros.
 destruct H6 as (x1,(y1,h)).
 apply couple_injection in h; destruct h as (_,h).
 apply couple_injection in h; destruct h as (_,h).
 rewrite <- h; trivial.
Qed.

Hint Resolve Arg'ltm Arg'Km Arg'K_intro : core.
     
Section DecodePath.

  Let K aq :=  exists a q, aq == couple a q /\ Arg'K q.

  Let R aq aq' := (*Arg'K (snd aq) /\*) Arg'lt (snd aq) (snd aq').


  Let F Frec aq :=
    L_match (snd aq)
            (*q=[]:*)(fst aq)
            (*q=[x:y:q']:*)(fun x y q' => Frec (couple (f (fst aq) x y) q')).

  Definition Dec a(**∈Arg*) q(**∈Arg' a*) : set(*∈ Arg*) :=
    WFR R F (couple a q).

  Let Km : Proper (eq_set ==> iff) K.
do 2 red; intros.
apply ex_morph; intros a.
apply ex_morph; intros q.
rewrite H; reflexivity.
Qed.

  Let Rm : Proper (eq_set ==> eq_set ==> iff) R.
unfold R; do 3 red; intros.
rewrite H,H0; reflexivity.
Qed.

  Let AccR aq : K aq -> Acc R aq.
destruct 1 as (x,(y,(qeq,h))); trivial.
red in h.
(*apply Acc_incl with (fun aq aq' => Arg'lt (snd aq) (snd aq')).
 red; destruct 1; trivial.*)

 apply Acc_inverse_image with (f:=snd).
 rewrite qeq, snd_def; trivial.
Qed.

  Let Fm : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) F.
unfold F; do 3 red; intros.
apply if_prop_morph.
 apply ex_morph; intros x1.
 apply ex_morph; intros y1.
 apply ex_morph; intros q'.
 rewrite H0; reflexivity.

 apply H; rewrite H0; reflexivity.

 rewrite H0; reflexivity.
Qed.

  Let Fext x g g' :
    K x ->
    (forall y y', R y x -> y==y' -> g y == g' y') ->
    F g x == F g' x.
unfold F; intros.
apply union2_morph; apply cond_set_morph2; intros; auto with *.
apply H0; auto with *.
red; rewrite snd_def.
red in H.
destruct H as (a,(q,(h,_))).
destruct H1 as (x',(y',(q',h'))).
rewrite h, snd_def in h'|-*.
rewrite h',!snd_def.
exists x';exists y'; reflexivity.
Qed.
  
  Let KArg : forall a q, a ∈ Arg -> q ∈ Arg' a -> K (couple a q).
red; intros.
apply Arg'K_intro in H0; trivial.
exists a; exists q; split;[reflexivity|trivial].
Qed.

  Hint Resolve Km Rm AccR Fm Fext : core.


  Global Instance Dec_morph : morph2 Dec.
do 3 red; intros.
apply WFR_morph_gen2.
 reflexivity.
 apply couple_morph; trivial.
Qed.

  Lemma Dec_mt a : a ∈ Arg -> Dec a empty == a.
unfold Dec; intros.
rewrite WFR_eqn_gen; auto.
 unfold F; rewrite L_match_mt.
  apply fst_def.
  apply snd_def.

  intros; apply Fext; auto.
  exists a; exists empty; split;[reflexivity|].
  apply Arg'K_intro with a; trivial.
  apply Arg'_intro1; trivial.

  apply AccR.
  apply KArg; trivial.
 apply Arg'_intro1; trivial.
Qed.

Lemma Dec_cons a x y q :
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  q ∈ Arg' (f a x y) ->
  Dec a (couple x (couple y q)) == Dec (f a x y) q.
intros.
unfold Dec at 1.
rewrite WFR_eqn_gen; auto.
 unfold F; rewrite L_match_cons with (x:=x)(y:=y) (q:=q).
  apply Dec_morph; auto with *.
  rewrite fst_def; reflexivity.

  clear -fm; do 4 red; intros.
  apply WFR_morph0.
  rewrite H,H0,H1; reflexivity.

  apply snd_def.

  intros; apply Fext; trivial.
  exists a; exists (couple x (couple y q));split;[reflexivity|].
  apply Arg'K_intro with a; trivial.
  apply Arg'_intro2; trivial.

 apply AccR.
 apply KArg; trivial.
 apply Arg'_intro2; trivial.
Qed.
End DecodePath.


Lemma Dec_typ a q :
  a ∈ Arg ->
  q ∈ Arg' a ->
  Dec a q ∈ Arg.
intros.
apply Arg'_ind with (5:=H0); intros; auto with *.
 do 3 red; intros.
 rewrite H1; rewrite H2; reflexivity.

 rewrite Dec_mt; auto.

 rewrite Dec_cons; auto.
Qed.

(** Extending a path *)

Section ExtendPath.

  Let F x y g q :=
    L_match q
             (*q=[]:*)(couple x (couple y empty))
             (*q=[x:y:q']:*)(fun x' y' q' => couple x' (couple y' (g q'))).

  Let Fm : Proper (eq_set==>eq_set==>(eq_set ==> eq_set) ==> eq_set ==> eq_set) F.
unfold F; do 5 red; intros.
apply if_prop_morph; auto with *.
 apply ex_morph; intros x'.
 apply ex_morph; intros y'.
 apply ex_morph; intros q'.
 rewrite H2; reflexivity.

 apply couple_morph; [rewrite H2;reflexivity|].
 apply couple_morph; [rewrite H2;reflexivity|].
 apply H1; rewrite H2; reflexivity.

 rewrite H,H0; reflexivity.
Qed.

  Let Fext x0 y0 x g g' :
    Arg'K x ->
    (forall y y', Arg'lt y x -> y==y' -> g y == g' y') ->
    F x0 y0 g x == F x0 y0 g' x.
unfold F; intros.
apply union2_morph; apply cond_set_morph2; intros; auto with *.
 apply couple_morph; [reflexivity|].
 apply couple_morph; [reflexivity|].
 apply H0; auto with *.
 red.
 destruct H1 as (x1,(y1,(q1,h))).
 exists x1; exists y1.
 apply transitivity with (1:=h).
 rewrite h,!snd_def; reflexivity.
Qed. 
  
  Definition extln q x y : set := WFR Arg'lt (F x y) q.

Global Instance extln_morph : Proper (eq_set==>eq_set==>eq_set==>eq_set) extln.
do 4 red; intros.
apply WFR_morph; auto with *.
 apply Arg'ltm.
 apply Fm; trivial.
Qed.

Lemma extln_cons a x y q x' y' :
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  q ∈ Arg' (f a x y) ->
  x' ∈ A (Dec (f a x y) q) ->
  y' ∈ B (Dec (f a x y) q) x' ->
  extln (couple x (couple y q)) x' y' == couple x (couple y (extln q x' y')).
intros.
unfold extln at 1.
rewrite WFR_eqn_gen; auto with *.
 apply L_match_cons with (x:=x) (y:=y) (q:=q); auto with *.
 clear; do 4 red; intros.
 rewrite H,H0,H1; reflexivity.

 apply Fm; reflexivity.

 intros; apply Fext; trivial.
 apply Arg'K_intro with a; trivial.
 eapply Arg'_intro2; eauto.

 eapply Arg'K_intro; eauto.
 eapply Arg'_intro2; eauto.
Qed.

Lemma extln_nil a x y :
  a ∈ Arg ->
  x ∈ A a ->
  y ∈ B a x ->
  extln empty x y == couple x (couple y empty).
intros.
unfold extln at 1.
rewrite WFR_eqn_gen; auto with *.
 apply L_match_mt; auto with *.

 apply Fm; reflexivity.

 intros; apply Fext; trivial.
 eapply Arg'K_intro; eauto.
 eapply Arg'_intro1; trivial.
 
 eapply Arg'K_intro; eauto.
 eapply Arg'_intro1; trivial.
Qed.

End ExtendPath.

Lemma extln_typ : forall a q x y,
  a ∈ Arg ->
  q ∈ Arg' a ->
  x ∈ A (Dec a q) ->
  y ∈ B (Dec a q) x ->
  extln q x y ∈ Arg' a.
intros a q x y aty qty; revert x y; apply Arg'_ind with (5:=qty); trivial; intros.
 do 3 red; intros.
 apply fa_morph; intros x1.
 apply fa_morph; intros y1.
 rewrite H,H0; reflexivity.

 rewrite Dec_mt in H0,H1; trivial.
 rewrite extln_nil with (a:=a0); trivial.
 apply Arg'_intro2; auto.
 apply Arg'_intro1; trivial.
 apply ftyp; auto.

 rewrite Dec_cons in H4,H5; auto.
 rewrite extln_cons with (a:=a0); auto.
 apply Arg'_intro2; auto.
Qed.

Lemma Dec_extln a p x y :
  a ∈ Arg ->
  p ∈ Arg' a ->
  x ∈ A (Dec a p) ->
  y ∈ B (Dec a p) x ->
  Dec a (extln p x y) == f (Dec a p) x y.
intros.
revert x y H1 H2.
apply Arg'_ind with (4:=H) (5:=H0). 
 apply morph_impl_iff2; auto with *.
 do 4 red; intros.
  rewrite <- H1,<- H2 in H4,H5|-*.
  auto.

 intros.
 rewrite Dec_mt in H2,H3|-*; trivial.
 rewrite extln_nil; eauto.
 rewrite Dec_cons; trivial.
  apply Dec_mt; auto.
  apply Arg'_intro1; auto.

 intros.
 rewrite Dec_cons in H6,H7|-*; trivial.
 rewrite extln_cons with (a:=a0); auto.
 rewrite Dec_cons; auto.
 apply extln_typ; auto.
Qed.

Section UniverseFacts.
  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega ∈ U.  

  (** We don't assume Arg is in U... *)
  Hypothesis aU : forall a, a ∈ Arg -> A a ∈ U.
  Hypothesis bU : forall a x, a ∈ Arg -> x ∈ A a -> B a x ∈ U.


  (* ... but Arg' is in U *)
  Lemma G_Arg' : forall a, a ∈ Arg -> Arg' a ∈ U.
unfold Arg'.
elim isOrd_omega using isOrd_ind; intros.
rewrite TIF_eq; auto.
apply G_sup; trivial.
 do 2 red; intros; apply Lmorph; auto with *.
 apply TIF_morph; trivial.

 apply G_incl with omega; trivial.

 intros.
 apply G_union2; trivial.
  apply G_singl; trivial.
  apply G_trans with omega; auto.
  apply zero_omega.

  apply G_sigma; auto.
   do 2 red; intros; apply sigma_morph.
    apply Bm; auto with *.

    red; intros.
    apply TIF_morph; auto with *.
    apply fm; auto with *.

   intros.
   apply G_sigma; auto.
   do 2 red; intros.
   apply TIF_morph; auto with *.
   apply fm; auto with *.
Qed.

End UniverseFacts.
  
End EncodeBigParameter.

Existing Instance Arg'ltm.
Instance Dec_morph_gen :
  Proper ((eq_set==>eq_set==>eq_set==>eq_set)==>eq_set==>eq_set==>eq_set) Dec.
do 4 red; intros.
unfold Dec.
apply WFR_morph.
 do 2 red; intros.
 rewrite H2,H3; reflexivity.

 do 3 red; intros.
 apply if_prop_morph.
  apply ex_morph; intros x'.
  apply ex_morph; intros y'.
  apply ex_morph; intros q'.
  rewrite H3; reflexivity.

  apply H2.
  apply couple_morph.
   apply H; rewrite H3; reflexivity.

   rewrite H3; reflexivity.

  rewrite H3; reflexivity.

 rewrite H0,H1; reflexivity.
Qed.
