Require Import ZF ZFpairs ZFrelations ZFord ZFstable.
Require Import ZFgrothendieck.
Require Import ZFfunext ZFfix ZFfixrec.
Require Import ZFw.
Require Import ZFiso.

(** In this file we develop the theory of W-types:
    - typing
    - existence of a fixpoint
    - recursor
 *)

Section W_theory.

(** * Definition and properties of the W-type operator *)

Variable A : set.
Variable B : set -> set.
Hypothesis Bm : morph1 B.

(* The intended type operator *)
Definition W_F X := Σ x ∈ A, cc_arr (B x) X.

Lemma wfm1 : forall X, ext_fun A (fun x => cc_arr (B x) X).
do 2 red; intros.
apply cc_arr_morph; auto with *.
Qed.
Hint Resolve wfm1 : core.

Lemma W_F_intro X a f :
  ext_fun (B a) f ->
  a ∈ A ->
  (forall i, i ∈ B a -> f i ∈ X) ->
  couple a (cc_lam (B a) f) ∈ W_F X.
intros.
apply couple_intro_sigma; auto with *.
apply cc_arr_intro; intros; auto with *.
Qed.

Lemma W_F_elim X x :
  x ∈ W_F X ->
  fst x ∈ A /\
  (forall i, i ∈ B (fst x) -> cc_app (snd x) i ∈ X) /\
  x ==couple (fst x) (cc_lam (B (fst x)) (cc_app (snd x))). 
intros.
assert (ty1 := fst_typ_sigma _ _ _ H).
assert (eq1 := surj_pair _ _ _ (subset_elim1 _ _ _ H)).
apply snd_typ_sigma with (y:=fst x) in H; auto with *.
split; trivial.
split; intros.
 apply cc_arr_elim with (1:=H); trivial.

 rewrite cc_eta_eq with (1:=H) in eq1; trivial.
Qed.

Instance W_F_mono : Proper (incl_set ==> incl_set) W_F.
do 3 red; intros.
apply W_F_elim in H0; destruct H0 as (?,(?,?)).
rewrite H2.
apply W_F_intro; auto.
do 2 red; intros; apply cc_app_morph; auto with *.
Qed.

Instance W_F_morph : morph1 W_F.
apply Fmono_morph; auto with *.
Qed.

Lemma W_F_stable : stable W_F.
unfold W_F.
apply sigma2_stable_class; auto with *.
 intros; apply cc_prod_ext; auto with *.
 red; trivial.

 intros.
 apply cc_prod_stable_class; intros; auto.
 apply id_stable_class.
Qed.

Lemma WFi_ext a a' f f' :
  a ∈ A ->
  a == a' ->
  (a == a' -> eq_fun (B a) f f') ->
  couple a (cc_lam (B a) f) == couple a' (cc_lam (B a') f').
intros.
apply couple_morph; trivial.
apply cc_lam_ext; auto.
Qed.

Lemma WFi_inv a a' Y Y' f f' :
  couple a (cc_lam Y f) == couple a' (cc_lam Y' f') ->
  ext_fun Y f ->
  ext_fun Y' f' ->
  (a == a' -> Y == Y') ->
  a == a' /\ eq_fun Y f f'.
intros.
apply couple_injection in H; destruct H; split; trivial.
red; intros.
assert (eqr := cc_app_morph _ _ H3 _ _ H5).
rewrite cc_beta_eq in eqr; trivial.
rewrite cc_beta_eq in eqr; trivial.
rewrite <- H2; trivial; rewrite <- H5; trivial.
Qed.

  (** Applying [f] to the recursive subterms of [x] *)
  Definition WFmap f x :=
    couple (fst x) (λ i ∈ B (fst x), f (cc_app (snd x) i)).

  Lemma WFmap_ext : forall f f' x x',
    fst x ∈ A ->
    fst x == fst x' ->
    (forall i i', i ∈ B (fst x) -> i == i' ->
     f (cc_app (snd x) i) == f' (cc_app (snd x') i')) ->
    WFmap f x == WFmap f' x'.
intros.
apply WFi_ext; auto.
Qed.

  Instance WFmap_morph : Proper ((eq_set==>eq_set)==>eq_set==>eq_set) WFmap.
do 3 red; intros.
apply couple_morph.
 apply fst_morph; trivial.

 apply cc_lam_ext; intros.
  rewrite H0; reflexivity.

  red; intros.
  apply H.
  rewrite H0; rewrite H2; reflexivity.
Qed.

Lemma WFmap_comp : forall f g X Y x,
  morph1 g ->
  morph1 f ->
  (forall x, x ∈ X -> g x ∈ Y) ->
  x ∈ W_F X ->
  WFmap f (WFmap g x) == WFmap (fun x => f (g x)) x.
intros.
unfold WFmap.
apply W_F_elim in H2; destruct H2 as (?,(?,_)).
symmetry; apply WFi_ext; intros; auto.
 rewrite fst_def; reflexivity.

 red; intros.
 apply H0; auto.
 rewrite snd_def.
 rewrite <- H6.
 rewrite cc_beta_eq; auto with *.
 do 2 red; intros; apply H; auto.
 rewrite H8; reflexivity.
Qed.

Lemma WF_eta : forall X x,
  x ∈ W_F X ->
  x == WFmap (fun x => x) x.
intros.
apply W_F_elim in H; destruct H as (_,(_,?)); assumption.
Qed.

  Lemma WFmap_inj : forall X Y g g' x x',
    x ∈ W_F X -> x' ∈ W_F Y ->
    ext_fun X g -> ext_fun Y g' ->
    (forall a a', a ∈ X -> a' ∈ Y -> g a == g' a' -> a == a') ->
    WFmap g x == WFmap g' x' -> x == x'.
unfold WFmap; intros.
apply W_F_elim in H; destruct H as (?,(?,?)).
apply W_F_elim in H0; destruct H0 as (?,(?,?)).
apply WFi_inv in H4; auto.
 destruct H4.
 red in H9.
 rewrite H6; rewrite H8; apply WFi_ext; intros; auto.
 red; intros.
 apply H3; auto.
 apply H7.
 rewrite <- H12; revert H11; apply eq_elim; apply Bm; trivial.

 do 2 red; intros; apply H1; auto.
 rewrite H10; reflexivity.

 do 2 red; intros; apply H2; auto.
 rewrite H10; reflexivity.
Qed.

  Lemma WFmap_typ : forall X Y f x,
    ext_fun X f ->
    x ∈ W_F X ->
    (forall a, a ∈ X -> f a ∈ Y) ->
    WFmap f x ∈ W_F Y.
intros.
apply W_F_elim in H0; destruct H0 as (?,(?,_)).
apply W_F_intro; auto.
do 2 red; intros.
apply H; auto.
rewrite H4; reflexivity.
Qed.

(** If [f] is as iso between [X] and [Y},
    then [WFmap f] is an iso between [W_F X] and [W_F Y] *)
Lemma WFmap_iso X Y f :
  iso_fun X Y f ->
  iso_fun (W_F X) (W_F Y) (WFmap f).
intros isof.
assert (fm := iso_funm isof).
assert (fext : ext_fun X f).
 apply morph_is_ext; trivial.
constructor; intros.
 apply WFmap_morph; trivial.

 red; intros.
 eapply WFmap_typ with (2:=H); intros; trivial.
 apply (iso_typ isof); trivial.

 apply WFmap_inj with (1:=H)(2:=H0) in H1; intros; trivial.
 apply (iso_inj isof) in H4; trivial.

 exists (WFmap (iso_inv X f) y).
  apply WFmap_typ with (2:=H); intros; trivial.
   apply morph_is_ext; apply (iso_funm (iso_fun_sym isof)).

   apply iso_inv_typ with (1:=isof); trivial.

  rewrite WFmap_comp with (1:=iso_funm (iso_fun_sym isof)) (2:=fm) (4:=H); intros; trivial.
   transitivity (WFmap (fun x => x) y).
   2:symmetry; apply WF_eta with (1:=H); trivial.
   apply WFmap_ext; intros; auto with *.
    apply W_F_elim with (1:=H).

    rewrite <- H1.
    apply iso_inv_eq with (1:=isof); trivial.
    apply W_F_elim with (1:=H); trivial.

   apply iso_inv_typ with (1:=isof); trivial.
Qed.

(** The iso between [W_F X] and [Wf X]. *)

Section WfIso. Import ZFwdom.
  
Definition Wintro x := Wsup (fst x) (snd x).
Instance Wintro_morph : morph1 Wintro.
do 2 red; intros.
apply Wsup_morph; [apply fst_morph|apply snd_morph]; trivial.
Qed.

Lemma Wintro_ext : forall X, ext_fun (W_F X) Wintro.
do 2 red; intros; apply Wintro_morph; trivial.
Qed.

Hint Resolve Wintro_morph : core.

Lemma Wf_intro : forall x X,
  x ∈ W_F X ->
  Wintro x ∈ Wf A B X.
intros.
apply W_F_elim in H.
destruct H as (tyx,(tyy,eqx)).
apply snd_morph in eqx.
rewrite snd_def in eqx.
apply Wf_intro; trivial.
rewrite eqx.
apply cc_prod_intro; auto.
do 2 red; intros; apply cc_app_morph; auto with *.
Qed.

Lemma Wf_elim a X :
  a ∈ Wf A B X ->
  exists2 x, x ∈ W_F X &
  a == Wintro x.
intros.
apply Wf_elim in H;[|trivial].
destruct H as (x,tyx,(f,tyf,eqa)).
exists (couple x f).
+rewrite cc_eta_eq with (1:=tyf).
 apply W_F_intro; intros; trivial.
  do 2 red; intros; apply cc_app_morph; auto with *.
 apply cc_prod_elim with (1:=tyf); trivial.
+unfold Wintro; rewrite fst_def, snd_def; trivial.
Qed.

(*Hint Resolve Wf_mono Wf_morph : core.*)

Lemma Wintro_inj X X' x x' :
  X ⊆ Wdom A B ->
  X' ⊆ Wdom A B ->
  x ∈ W_F X ->
  x' ∈ W_F X' ->
  Wintro x == Wintro x' ->
  x==x'.
intros tyX tyX' tyx tyx' eqWi.
apply W_F_elim in tyx.
destruct tyx as (tyx1,(tyx2,eqx)).
apply W_F_elim in tyx'.
destruct tyx' as (tyx'1,(tyx'2,eqx')).
apply Wsup_inj with (A:=A)(B:=B) in eqWi; trivial.
destruct eqWi as (eq1,eq2).
+rewrite eqx, eqx'; apply couple_morph; [trivial|].
 apply cc_lam_ext; [rewrite eq1;reflexivity|].
 red; intros.
 rewrite (eq2 x0); trivial.
 apply cc_app_morph;[reflexivity|trivial].
+intros.
 apply tyX; apply tyx2; trivial.
+intros.
 apply tyX'; apply tyx'2; trivial.
Qed.
 
 Lemma W_F_Wf_iso X :
  X ⊆ Wdom A B ->
  iso_fun (W_F X) (Wf A B X) Wintro.
split; intros.
 apply Wintro_morph.

 red; intros.
 apply Wf_intro; trivial.

 apply Wintro_inj with X X; auto.

 destruct Wf_elim with (1:=H0); eauto with *.
Qed.

End WfIso.
 
(** The iso between [W_F X] and [Wf Y], given an iso [f] between [X] and [Y]. *)
Definition wiso f := comp_iso (WFmap f) Wintro.

Lemma W_F_Wf_mapiso o f :
  isOrd o ->
  iso_fun (TI W_F o) (Wi A B o) f ->
  iso_fun (W_F (TI W_F o)) (ZFwdom.Wf A B (Wi A B o)) (wiso f).
intros.
apply iso_fun_trans with (W_F (Wi A B o)).
 apply WFmap_iso; trivial.

 apply W_F_Wf_iso.
 apply Wi_typ; trivial.
Qed.

Instance wisom  : Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set) wiso.
do 3 red; intros.
unfold wiso.
apply comp_iso_morph; trivial.
 apply WFmap_morph; trivial.

 apply Wintro_morph.
Qed.

Lemma wiso_ext : forall X f f',
  eq_fun X f f' -> eq_fun (W_F X) (wiso f) (wiso f').
red; intros.
apply Wintro_morph.
apply WFmap_ext.
 apply W_F_elim with (1:=H0).

 rewrite H1; reflexivity.

 intros.
 apply H.
  apply W_F_elim with (1:=H0); trivial.

  rewrite H1; rewrite H3; reflexivity.
Qed.
Hint Resolve wiso_ext : core.

(** The iso between [TI W_F o] and [TI Wf o]. *)
Lemma TI_W_F_Wf_iso o :
  isOrd o ->
  iso_fun (TI W_F o) (Wi A B o) (TI_iso W_F wiso o).
intros.
apply TI_iso_fun; intros; auto with *.
apply W_F_Wf_mapiso; trivial.
Qed.

(** * The fixpoint of the W_type operator *)

(** We get W the fixpoint of W_F by isomorphism *)

  Definition W_ord := ZFw.W_ord A B.
  Definition W := TI W_F W_ord.

  Lemma W_ord_o : isOrd W_ord.
apply ZFw.W_ord_o; trivial.
Qed.
Hint Resolve W_ord_o : core.

  Lemma W_eqn : W == W_F W.
unfold W.
apply TI_iso_fixpoint with (5:=W_F_Wf_mapiso); auto with *.
unfold W_ord. fold (Wi A B).
rewrite <- ZFw.W_clos; trivial.
apply ZFw.W_eqn; trivial.
Qed.

  Lemma W_post : forall o, isOrd o -> TI W_F o ⊆ W.
intros.
apply TI_pre_fix; auto with *.
rewrite <- W_eqn; reflexivity.
Qed.

  Lemma W_eta w : w ∈ W -> w == couple (fst w) (snd w).
intros.
rewrite W_eqn in H.
apply surj_pair with (1:=subset_elim1 _ _ _ H).
Qed.

(** Recursor on W *)

Section Recursor.

  Hint Resolve W_F_mono : core.

  Lemma Wi_fix :
    forall (P:set->Prop) o,
    isOrd o ->
    (forall i, isOrd i -> i ⊆ o ->
     (forall i' m, i' ∈ i -> m ∈ TI W_F i' -> P m) ->
     forall n, n ∈ TI W_F i -> P n) ->
    forall n, n ∈ TI W_F o -> P n.
intros P o is_ord Prec.
induction is_ord using isOrd_ind; intros; eauto.
Qed.

  Variable ord : set.
  Hypothesis oord : isOrd ord.

  Variable F : set -> set -> set.
  Hypothesis Fm : morph2 F.

  Variable U : set -> set -> set.
  Hypothesis Umono : forall o o' x x',
    isOrd o' -> o' ⊆ ord -> isOrd o -> o ⊆ o' ->
    x ∈ TI W_F o -> x == x' ->
    U o x ⊆ U o' x'.

  Let Ty o := cc_prod (TI W_F o) (U o).
  Hypothesis Ftyp : forall o f, isOrd o -> o ∈ ord ->
    f ∈ Ty o -> F o f ∈ Ty (osucc o).

  Definition Wi_ord_irrel :=
    forall o o' f g,
    isOrd o' -> o' ⊆ ord -> isOrd o -> o ⊆ o' ->
    f ∈ Ty o -> g ∈ Ty o' ->
    fcompat (TI W_F o) f g ->
    fcompat (TI W_F (osucc o)) (F o f) (F o' g).

  Hypothesis Firrel : Wi_ord_irrel.

  Definition WREC := REC F.

  Lemma WREC_recursor_hyps : typed_recursor_hyps (TI W_F) U F ord.
apply mkTypedRec; auto.
 apply TI_morph.

 red; intros; apply TI_mono_eq; auto.

 intros.
 apply Umono; auto. 
  eauto using isOrd_inv.
  apply olts_le; auto. 

 intros.
 apply Ftyp; auto. 
 eauto using isOrd_inv.

 intros.
 apply Firrel; auto. 
  eauto using isOrd_inv.
  apply olts_le; auto. 
Qed.

  Lemma WREC_recursor : typed_recursor_spec (TI W_F) U F WREC ord.
apply typed_recursor; auto.
apply WREC_recursor_hyps.
Qed.

End Recursor.

Section RecursorProperties.

  (* Main properties of WREC: typing and equation *)

  Variable ord : set.
  Hypothesis oord : isOrd ord.

  Variable F : set -> set -> set.
  Variable U : set -> set -> set.
  Hypothesis Uext : ext_fun (TI W_F ord) (U ord).
  Let Ty o := cc_prod (TI W_F o) (U o).
  Hypothesis isrec : typed_recursor_spec (TI W_F) U F (WREC F) ord.

  Lemma WREC_wt : WREC F ord ∈ Ty ord.
intros.
apply typed_rec_typ with (1:=isrec); auto with *.
Qed.

  Lemma WREC_expand : forall n,
    n ∈ TI W_F ord -> cc_app (WREC F ord) n == cc_app (F ord (WREC F ord)) n.
intros.
apply typed_rec_eqn with (1:=isrec); auto with *.
Qed.

End RecursorProperties.

Section SimpleRecursor.

  Variable F : set -> set.
  Hypothesis Fm : morph1 F.
  
  Variable U : set -> set.
  Hypothesis Um : morph1 U.

  Hypothesis Ftyp : forall o f, isOrd o ->
    (forall w, w ∈ TI W_F o -> cc_app f w ∈ U w) ->
    (forall w, w ∈ TI W_F (osucc o) -> cc_app (F f) w ∈ U w).

  Hypothesis Firr : forall o f g, isOrd o ->
    fcompat (TI W_F o) f g ->
    fcompat (TI W_F (osucc o)) (F f) (F g).
    
  Let F' := fun o fct => λ w ∈ TI W_F (osucc o), cc_app (F fct) w.

  Definition W_REC := WREC F' W_ord.

  Lemma W_REC_recursor_hyps : typed_recursor_hyps (TI W_F) (fun o => U) F' W_ord.
apply mkTypedRec; auto with *.
 red; intros; apply TI_mono_eq; auto with *.

 intros.
 rewrite H3; reflexivity.

 do 3 red; intros.
 apply cc_lam_morph; intros.
  rewrite H; reflexivity.

  red; intros.
  rewrite H0, H1; reflexivity.

 intros.
 apply cc_prod_intro.
  do 2 red; intros; apply cc_app_morph; auto with *.
  do 2 red; intros; auto.
  intros.
  apply Ftyp with o; trivial.
   apply isOrd_inv with W_ord; auto.  
  intros.
  apply cc_prod_elim with (1:=H0); trivial.

 red; red; intros.
 assert (oo' : isOrd o') by eauto using isOrd_inv.
 unfold F'.
 rewrite cc_beta_eq; trivial.
  rewrite cc_beta_eq. 
  red in Firr.
  eapply Firr with o; trivial.

  do 2 red; intros.
  rewrite H7; reflexivity.

 revert H5; apply TI_mono; eauto with *.
 apply osucc_mono; auto.

 do 2 red; intros.
 rewrite H7; reflexivity.
Qed.


  Lemma W_REC_recursor : typed_recursor_spec (TI W_F) (fun o => U) F' (REC F') W_ord.
apply typed_recursor with (2:=W_REC_recursor_hyps); auto.
Qed.
  
 Lemma W_REC_eqn w :
    w ∈ W ->
    cc_app W_REC w == cc_app (F W_REC) w.
intros.
unfold W_REC.
rewrite WREC_expand with (2:=W_REC_recursor); auto.
unfold F' at 1.
rewrite cc_beta_eq; trivial.
 reflexivity.

 do 2 red; intros.
 rewrite H1; reflexivity.

 rewrite TI_mono_succ; auto with *.
 fold W.
 rewrite <- W_eqn; trivial.
Qed.

  Lemma W_REC_typ : W_REC ∈ cc_prod W U.
apply WREC_wt with (3:=W_REC_recursor); auto.
Qed.

  Lemma W_REC_unicity :
    forall f,
    f ∈ (Π w ∈ W, U w) ->
    fcompat W f (F f) ->
    f == W_REC.
    intros.
assert (forall w, w ∈ W -> cc_app f w ∈ U w).
 intros.
 apply cc_prod_elim with (1:=H); trivial.
rename H into fty.
assert (fcompat W f W_REC).
revert H1 H0; unfold W.
apply isOrd_ind with (2:=W_ord_o).
intros.
red; intros.
rewrite W_REC_eqn.
red in H3.
rewrite H3; trivial.
red in Firr.
apply TI_elim in H4; auto with *.
destruct H4 as (o',o'o,H4).
assert (isOrd o').
 apply isOrd_inv with y; trivial.
rewrite <- TI_mono_succ in H4; auto with *.
assert (TI W_F o' ⊆ TI W_F y).
 apply TI_mono; auto with *.
apply Firr with (o:=o'); trivial.
apply H1; trivial.
 intros.
 apply H2; auto.

 red; intros.
 apply H3; auto.

 revert H4; apply TI_mono; auto with *.

rewrite cc_eta_eq with (1:=fty).
rewrite cc_eta_eq with (1:=W_REC_typ).
apply cc_lam_ext.
reflexivity.
red; intros.
red in H.
rewrite <- H3.
apply H.
trivial.
Qed.
    
End SimpleRecursor.

Section PrimRecursor.

  Variable P : set -> set.
  Hypothesis Pm : morph1 P.
  
  Variable F : set -> set -> set -> set.
  Hypothesis Fm : Proper (eq_set==>eq_set==>eq_set==>eq_set) F.

  Hypothesis Ftyp : forall x y recy,
    x ∈ A ->
    y ∈ (Π i ∈ B x, W) ->
    recy ∈ (Π i ∈ B x, P (cc_app y i)) ->
    F x y recy ∈ P (couple x y).

  Definition WPREC : set :=
    W_REC (fun f =>
             λ w ∈ W, F (fst w) (snd w) (λ i ∈ B (fst w), cc_app f (cc_app (snd w) i))).

  Let lam_m1 : forall f f' w w', f==f' -> w ∈ W -> w==w' ->
    F (fst w) (snd w) (λ i ∈ B (fst w), cc_app f (cc_app (snd w) i)) ==
    F (fst w') (snd w') (λ i ∈ B (fst w'), cc_app f' (cc_app (snd w') i)).
intros.
apply Fm.
 apply fst_morph; trivial.
 apply snd_morph; trivial.
apply cc_lam_ext.
 apply Bm.
 apply fst_morph; trivial.

 red; intros.
 rewrite H,H1,H3; reflexivity.
Qed.

  Let lam_m :
    morph1
     (fun f : set =>
      λ w ∈ W,
      F (fst w) (snd w) (λ i ∈ B (fst w), cc_app f (cc_app (snd w) i))).
do 2 red; intros.
apply cc_lam_ext.
 reflexivity.
red; intros.
apply lam_m1; trivial.
Qed.
  
Let lam_typ :
 forall o f : set,
 isOrd o ->
 (forall w : set, w ∈ TI W_F o -> cc_app f w ∈ P w) ->
 forall w : set,
 w ∈ TI W_F (osucc o) ->
 cc_app
   (λ w0 ∈ W,
    F (fst w0) (snd w0) (λ i ∈ B (fst w0), cc_app f (cc_app (snd w0) i))) w
   ∈ P w.
intros.
rewrite cc_beta_eq.
rewrite TI_mono_succ in H1; auto with *.
  setoid_replace (P w) with (P (couple (fst w) (snd w))).
 apply Ftyp.
  apply fst_typ_sigma in H1; trivial.

  eapply snd_typ_sigma in H1.
  3:reflexivity.
  revert H1; apply cc_prod_covariant.   
  do 2 red; reflexivity.
  reflexivity.   
  intros.
  apply W_post; trivial.
  do 2 red; intros.
  apply cc_arr_morph.
  auto.
  reflexivity.

  apply cc_prod_intro.
   do 2 red; intros.
   rewrite H3; reflexivity.
   do 2 red; intros.
   rewrite H3; reflexivity.
   intros.
   apply H0.
   eapply snd_typ_sigma in H1.
   3:reflexivity.
   apply cc_prod_elim with (1:=H1); trivial.
   do 2 red; intros.
   apply cc_arr_morph.
   auto.
   reflexivity.

 apply Pm.
 apply surj_pair with (1:=subset_elim1 _ _ _ H1).

 do 2 red; intros.
 apply lam_m1; trivial.
 reflexivity. 

 revert H1; apply W_post; auto.
Qed.

Let lam_irr :
 forall o f f',
 isOrd o ->
 fcompat (TI W_F o) f f' ->
 fcompat (TI W_F (osucc o))
   (λ w ∈ W, F (fst w) (snd w) (λ i ∈ B (fst w), cc_app f (cc_app (snd w) i)))
   (λ w ∈ W, F (fst w) (snd w) (λ i ∈ B (fst w), cc_app f' (cc_app (snd w) i))).
red; intros.
rewrite cc_beta_eq.
rewrite cc_beta_eq.
apply Fm.
reflexivity.
reflexivity.
apply cc_lam_ext.
reflexivity.
red; intros.
rewrite <- H3.
apply H0.
rewrite TI_mono_succ in H1; auto with *.
eapply snd_typ_sigma in H1.
3:reflexivity.
apply cc_prod_elim with (1:=H1); trivial.
do 2 red; intros.
apply cc_arr_morph.
auto.
reflexivity.

do 2 red; intros.
apply lam_m1; trivial.
reflexivity. 

revert H1; apply W_post; auto.

do 2 red; intros.
apply lam_m1; trivial.
reflexivity. 

revert H1; apply W_post; auto.
Qed.

Lemma WPREC_typ : WPREC ∈ Π w ∈ W, P w.
intros.
unfold WPREC.
apply W_REC_typ with (U:=P); trivial.
Qed.

  Lemma WPREC_eqn x y :
    couple x y ∈ W ->
    cc_app WPREC (couple x y) == F x y (λ i ∈ B x, cc_app WPREC (cc_app y i)).
intros.
unfold WPREC.
rewrite W_REC_eqn with (U:=P); trivial.
rewrite cc_beta_eq; trivial.
apply Fm.
 apply fst_def.
 apply snd_def.

 apply cc_lam_ext.
 apply Bm.
 apply fst_def.
 red; intros.
 rewrite snd_def.
 rewrite H1.
 reflexivity.

do 2 red; intros.
apply lam_m1; trivial.
reflexivity.
Qed.
  


End PrimRecursor.

 (** * Universe facts: when A and B belong to a given (infinite) universe, then so does W(A,B). *)

Section W_Univ.

(* Universe facts *)
  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : omega ∈ U.  

  Hypothesis aU : A ∈ U.
  Hypothesis bU : forall a, a ∈ A -> B a ∈ U.

  Lemma G_W_F X : X ∈ U -> W_F X ∈ U.
intros.
unfold W_F.
apply G_sigma; intros; trivial.
apply G_cc_prod; auto.
Qed.
  Lemma G_W_ord : W_ord ∈ U.
unfold W_ord.
apply G_clos_ord; auto.
apply ZFwdom.G_Wdom; trivial.
Qed.

  Lemma G_W : W ∈ U.
apply G_TI; intros; trivial.
 apply W_F_morph.

 apply G_W_ord.

 apply G_W_F; trivial.
Qed.

  Lemma G_Wi o : isOrd o -> TI W_F o ∈ U.
intros.
apply G_incl with W; trivial.
 apply G_W.

 apply W_post; trivial.
Qed.

End W_Univ.

End W_theory.

#[global]Hint Resolve W_ord_o : core.

(* Discharged morphism results *)

Instance W_F_morph_gen :
  Proper (eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) W_F.
do 4 red; intros.
unfold W_F.
apply sigma_ext; trivial.
intros.
rewrite (H0 _ _ H3),H1; reflexivity.
Qed.

Lemma W_F_ext : forall A A' B B' X X',
  A == A' ->
  eq_fun A B B' ->
  X == X' ->
  W_F A B X == W_F A' B' X'.
unfold W_F; intros.
apply sigma_ext; trivial.
intros.
apply cc_prod_ext; auto with *.
red; auto.
Qed.

Lemma W_ord_morph : Proper (eq_set==>(eq_set==>eq_set)==>eq_set) W_ord.
apply ZFw.W_ord_morph.
Qed.

Lemma WREC_morph_gen : Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) WREC.
do 3 red; intros.
unfold WREC.
unfold ZFfixrec.REC.
apply TR_morph; trivial.
do 2 red; intros.
apply sup_morph; trivial.
red; intros.
apply H; auto.
Qed.

Hint Resolve wfm1 : core.

(** A specific instance of W-type: the type of sets (cf Ens.set) *)

Section Sets.

Hypothesis U : set.
Hypothesis Ugrot : grot_univ U.

  Definition sets := W U (fun X =>X).

  Let sm : morph1 (fun X => X).
do 2 red; trivial.
Qed.

  Lemma sets_ind :
    forall P : set -> Prop,
    (forall y X f, morph1 f ->
     (* y ∈ sigma X:U. U->Ens.set *)
     y == couple X (cc_lam X f) ->
     X ∈ U ->
     (forall x, x ∈ X -> f x ∈ sets) ->
     (* induction hypothesis *)
     (forall x, x ∈ X -> P (f x)) ->
     P y) ->
    forall x, x ∈ sets -> P x.
unfold sets,W;intros.
assert (isOrd (W_ord U (fun X => X))).
 apply W_ord_o; trivial.
revert x H0; elim H1 using isOrd_ind; intros.
apply TI_elim in H4; auto with *.
2:apply W_F_morph; trivial.
destruct H4 as (o',?,?).
apply W_F_elim in H5; auto with *.
destruct H5 as (?,(?,?)).
apply H with (fst x) (cc_app (snd x)); intros; trivial.
 apply cc_app_morph; reflexivity.

 generalize (H6 _ H8); apply TI_incl; auto with *.
  apply W_F_morph; trivial.

  apply H2; trivial.

 apply H3 with o'; auto.
Qed.

  Lemma sets_incl_U : sets ⊆ U.
red; intros.
apply sets_ind with (2:=H); intros.
rewrite H1; clear H1 y.
apply G_couple; trivial.
apply G_cc_lam; auto.
Qed.

End Sets.
