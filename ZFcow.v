Require Import ZF Zpairs Znats Zrelations ZFord Zcoc.
Require Import ZFgrothendieck.
Require Import ZFfix ZFcofix.
Require Import ZFfixfun.
Require Import ZFwdom.


(* Ordinal interval [o'; o[ *)
Definition ord_intv o' o  :=
  subset o (fun o'' => o' ⊆ o'').

Lemma ord_intv_def o' o z :
  z ∈ ord_intv o' o <-> o' ⊆ z /\ z ∈ o.
Proof.
unfold ord_intv; rewrite subset_ax.
split.
*intros (?,(z',eqz,?)).
 rewrite eqz in H|-*; auto.
*intros (?,?); split;[|exists z]; auto with *.
Qed.

Lemma ord_intv_intro1 o o' :
  isOrd o ->
  o' ∈ o ->
  o' ∈ ord_intv o' o.
Proof.
intros; rewrite ord_intv_def; auto with *.
Qed.
  Hint Resolve ord_intv_intro1 : core.

Lemma ord_intv_dir o o' i j :
  isOrd o ->
  i ∈ ord_intv o' o ->
  j ∈ o ->
  exists2 k, k ∈ ord_intv o' o & i ⊆ k /\ j ⊆ k.
Proof.
intros oo tyi tyj.
rewrite ord_intv_def in tyi; trivial.
destruct tyi.
exists (i ⊔ j);[|split].
*rewrite ord_intv_def; split.
 +rewrite H; apply osup2_incl1; eauto using isOrd_inv.
 +apply osup2_lt; trivial.
*apply osup2_incl1; eauto using isOrd_inv.
*apply osup2_incl2; eauto using isOrd_inv.
Qed.

Lemma ord_intv_sup o o' f :
  increasing_bounded o f ->
  isOrd o  ->
  o' ∈ o ->
  sup o f == sup (ord_intv o' o) f.
Proof.
intros fincr oo lto.
assert (oo' : isOrd o') by eauto using isOrd_inv.
apply eq_set_ax; intros z.
rewrite !sup_def; auto.
*split.
 +intros (y,?,?). 
  destruct (ord_intv_dir o o' o' y) as (k,?,(?,?)); auto.
  exists k; auto.
  rewrite ord_intv_def in H1; destruct H1.
  revert H0; apply fincr; trivial.
 +intros (y,?,?); exists y; trivial.
  rewrite ord_intv_def in H; apply H.
*do 2 red; intros.
 apply increasing_bounded_is_ext in fincr.
 rewrite ord_intv_def in H; destruct H; auto.
Qed.


Section CoW.

(* The first parameter of W-types (aka the payload) *)
Variable A : set.
(* The subterm index type *)
Variable B : set -> set.
Hypothesis Bm : morph1 B.

Notation Wdom := (Zwdom.Wdom A B).
Notation Wf := (Zwdom.Wf A B).
Notation Wsup := Zwdom.Wsup.
Notation Wfst := Zwdom.Wfst.
Notation Wsnd_fun := Zwdom.Wsnd_fun.
Existing Instance Zwdom.Wf_mono.

Let Wdom_compl I f :
  ext_fun I f -> (forall i : set, i ∈ I -> f i ∈ Wdom) -> sup I f ∈ Wdom.
intros.  
apply power_intro.
intros.
apply sup_ax in H1; trivial.
destruct H1 as (?,?,(_,?)).
apply power_elim with (2:=H2); auto.
Qed.

(*******************************************************************************************)
Section CoFixpointByIteration.

  (* Co-Iteration of Wf *)

  Definition COWi := COTI Wdom Wf.

  Lemma COWi_typ o : isOrd o -> COWi o ⊆ Wdom.
apply COTI_bound; auto with *.
Qed.

  Lemma COWi_succ o : isOrd o -> COWi (osucc o) == Wf (COWi o).
intros.
unfold COWi; apply COTI_mono_succ; auto with *.
Qed.

  Lemma COWi_zero : COWi zero == Wdom.
apply COTI_initial; auto.
Qed.

  Lemma COWi_one : COWi (osucc zero) == Wf Wdom.
rewrite COWi_succ; auto.
rewrite COWi_zero; reflexivity.
Qed.

  Lemma COWi_decreasing : decreasing COWi.
apply COTI_mono; auto with *.
Qed.

  Lemma COWi_incl o: isOrd o -> COWi (osucc o) ⊆ COWi o.
intros; apply COWi_decreasing; auto.
red; intros; apply isOrd_trans with o; auto.
Qed.
  
  (** Coinductive *)

(* Proving the fixpoint is reached at omega *)

  Definition co_ord := omega.
  Lemma co_ordo : isOrd co_ord. 
trivial.
Qed.

  Definition COW := COWi co_ord.

  Lemma COW_typ : COW ⊆ Wdom.
apply COWi_typ; trivial.
Qed.
  
  Lemma Wf_stable_COWi : stable_class (fun X => exists2 o, isOrd o & X == COWi o) Wf.
red; intros; apply Zwdom.Wf_stable; trivial.
red; intros.
apply H in H0; destruct H0 as (o,oo,eqX); rewrite eqX.
apply power_def; apply COWi_typ; trivial.
Qed.
  
  Lemma COWi_closure : COW ⊆ Wf COW.
apply COTI_closure_stable; auto with *.
apply Wf_stable_COWi.
Qed.
Opaque co_ord.
  
Lemma COW_eqn : COW == Wf COW.
apply incl_eq.
 apply COWi_closure.

 unfold COW.
 rewrite <- COWi_succ; trivial.
 apply COWi_incl; trivial.
Qed.

(* It is the greatest fixpoint (in Wdom) *)
Lemma COW_gfp X : X ⊆ Wdom -> X ⊆ Wf X -> X ⊆ COW.
intros.
apply COTI_post_fix; auto with *.
Qed.

Lemma COW_COWi o : isOrd o -> COW ⊆ COWi o.
intros.
apply COTI_post_fix; auto with *.
 apply COW_typ.
 apply COWi_closure.
Qed. 

End CoFixpointByIteration.

(* We do not need more properties about COW beyond this point *)
Lemma COW_def : COW == COWi co_ord.
reflexivity.
Qed.
Opaque COW.
Hint Resolve co_ordo : core.

Lemma COW_Wf1 : COW ⊆ Wf Wdom.
rewrite COW_eqn; apply Wf_mono; trivial.
apply COW_typ.  
Qed.
Lemma Wf1_Wdom : Wf Wdom ⊆ Wdom.
apply Zwdom.Wf_typ; [trivial|reflexivity].
Qed.
Hint Resolve COW_typ COW_eqn COW_Wf1 Wf1_Wdom : core.


(*******************************************************************************************)
(* Universe facts *)

Section W_Univ.

  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : N ∈ U.  

  Hypothesis aU : A ∈ U.
  Hypothesis bU : forall a, a ∈ A -> B a ∈ U.

  Let Gdom : Wdom ∈ U.
apply ZFwdom.G_Wdom; auto.
Qed.
    
  Lemma G_COWi o : isOrd o -> COWi o ∈ U.
intros oo.
apply G_incl with Wdom; trivial.
apply COWi_typ; trivial.
Qed.

  Lemma G_COW : COW ∈ U.
apply G_incl with Wdom; trivial.
Qed.

End W_Univ.

(*******************************************************************************************)
(* Co-recursion... *)

Lemma COWi_complete o I i0 :
  i0 ∈ I ->
  (forall i j : set, i ∈ I -> j ∈ I -> exists2 k : set, k ∈ I & i ⊆ k /\ j ⊆ k) ->
  isOrd o ->
  complete I (COWi o).
Proof.
intros tyi0 dirI oo.
elim oo using isOrd_ind; intros.
red.
assert (aux := fun o => isOrd_inv _ o H).
intros f tyf fincr.
apply COTI_intro; intros; auto with *.
*apply Wdom_complete; auto.
 red; intros.
 apply COWi_typ with (o:=y); auto. 
*apply Wf_complete with i0; auto.
 +apply COTI_bound; auto with *.
 +red; intros.
  rewrite <- COTI_mono_succ; auto with *.
  generalize (tyf _ H3).
  apply COTI_mono; auto with *.
  apply olts_le; apply lt_osucc_compat; trivial.
Qed.

(*Lemma COWi_sup_intro f o o' :
  increasing_bounded o f ->
  isOrd o ->
  o' ∈ o ->
  (forall o'', o' ⊆ o'' -> o'' ∈ o -> f o'' ∈ X) ->
  complete I 
  sup o f ∈ COWi o'.
Proof.
intros fincr oo lto Hrec.
assert (oo' : isOrd o') by eauto using isOrd_inv.
rewrite (ord_intv_sup o o' f); trivial.
apply COWi_complete with o'; auto.
*intros.
 apply ord_intv_def in H0; destruct H0.
 apply ord_intv_dir; trivial.
*red; intros.
 rewrite ord_intv_def in H; destruct H; auto.
*red; intros.
 rewrite ord_intv_def in H; destruct H.
 rewrite ord_intv_def in H0; destruct H0.
 apply fincr; auto.
Qed.


Lemma COWi_sup_intro f o o' :
  increasing_bounded o f ->
  isOrd o ->
  o' ∈ o ->
  (forall o'', o' ⊆ o'' -> o'' ∈ o -> f o'' ∈ X) ->
  compl
  sup o f ∈ X.
Proof.
intros fincr oo lto Hrec.
assert (oo' : isOrd o') by eauto using isOrd_inv.
rewrite (ord_intv_sup o o' f); trivial.
apply COWi_complete with o'; auto.
*intros.
 apply ord_intv_def in H0; destruct H0.
 apply ord_intv_dir; trivial.
*red; intros.
 rewrite ord_intv_def in H; destruct H; auto.
*red; intros.
 rewrite ord_intv_def in H; destruct H.
 rewrite ord_intv_def in H0; destruct H0.
 apply fincr; auto.
Qed.*)

Lemma COWi_sup_intro f o o' x :
  isOrd x ->
  increasing_bounded o f ->
  isOrd o ->
  o' ∈ o ->
  (forall o'', o' ⊆ o'' -> o'' ∈ o -> f o'' ∈ COWi x) ->
  sup o f ∈ COWi x.
Proof.
intros xo fincr oo lto Hrec.
assert (oo' : isOrd o') by eauto using isOrd_inv.
rewrite (ord_intv_sup o o' f); trivial.
apply COWi_complete with o'; auto.
*intros.
 apply ord_intv_def in H0; destruct H0.
 apply ord_intv_dir; trivial.
*red; intros.
 rewrite ord_intv_def in H; destruct H; auto.
*red; intros.
 rewrite ord_intv_def in H; destruct H.
 rewrite ord_intv_def in H0; destruct H0.
 apply fincr; auto.
Qed.

Lemma COWi_sup_intro_succ f o o' :
  increasing_bounded o f ->
  isOrd o ->
  o' ∈ o ->
  (forall o'', o' ⊆ o'' -> o'' ∈ o -> f o'' ∈ Wf (COWi o')) ->
  sup o f ∈ Wf (COWi o').
Proof.
intros fincr oo lto Hrec.
assert (oo' : isOrd o') by eauto using isOrd_inv.
rewrite <- COWi_succ; auto with *.
apply COWi_sup_intro with o'; auto.
intros.
 rewrite COWi_succ; auto with *.
Qed.

(* Simple co-recursion *)
Section SimpleCorecursion.

(* The body of the cofixpoint *)
Hypothesis F:set->set.
Hypothesis Fm:morph1 F.
(* The body produces a constructor each time it is applied *)
Hypothesis Fty :
  forall o w, isOrd o -> w ∈ COWi o -> F w ∈ COWi (osucc o).

Let Fty_simple : typ_fun F Wdom Wdom.
red; intros.
rewrite <- COWi_zero in H.
apply Fty in H; trivial.
rewrite COWi_one in H; auto.
Qed.

(**)
  
Hypothesis Fmono : mono_bounded Wdom F.

Let TI_WF_step o : isOrd o ->
  TI F o ⊆ F (TI F o).
red; intros.
apply TI_elim in H0; trivial.
destruct H0 as (o',?,?).
revert H1; apply Fmono; auto.
 apply TI_mono_bound; eauto using isOrd_inv.
 apply TI_mono_bound; eauto using isOrd_inv.
 apply TI_incl; trivial.
Qed.

  Lemma TI_WF_typ_gen o o' : isOrd o -> isOrd o' -> o' ⊆ o -> TI F o ∈ COWi o'.
Proof.
intros; eapply TI_typ_COTI_gen; auto.
*red; intros.
 apply Fty; trivial.
*intros.
 destruct H6.
 apply COWi_sup_intro with x; trivial.
Qed.
  
Lemma TI_WF_typ o : isOrd o -> TI F o ∈ COWi o.
intros; apply TI_WF_typ_gen; auto with *.
Qed.


Definition COREC := TI F co_ord.

Lemma COREC_typ : COREC ∈ COW.
rewrite COW_def.
apply TI_WF_typ; trivial.
Qed.

Lemma COREC_eqn : COREC == F COREC.  
symmetry.
apply pre_incl_eq with (A:=A)(B:=B)(X:=COW); auto.
+apply COWi_closure.
+apply COREC_typ.
+rewrite COW_eqn.
 rewrite COW_def.
 rewrite <- COWi_succ; auto.
 apply Fty; trivial.
 rewrite <- COW_def.
 apply COREC_typ.
+apply TI_WF_step; trivial.
Qed.

Lemma corec_COWi w :
  w ∈ Wdom ->
  w == F w ->
  forall o, isOrd o -> w ∈ COWi o.
intros tyw wfx o oo.
elim oo using isOrd_ind; intros.
apply COTI_intro; intros; auto with *.
fold (COWi o').
assert (oo' : isOrd o') by eauto using isOrd_inv.
rewrite <- COWi_succ; trivial.
rewrite wfx.
apply Fty; auto.
Qed.

Lemma corec_typ w :
  w ∈ Wdom ->
  w == F w ->
  w ∈ COW.
intros.
rewrite COW_def.
apply corec_COWi; trivial.
Qed.

  
Lemma COREC_unique w :
  w ∈ Wdom ->
  w == F w ->
  w == COREC.
intros.
apply pre_incl_eq with (A:=A)(B:=B)(X:=COW); auto.
 rewrite <- COW_eqn; reflexivity.

 apply COREC_typ.

 apply corec_typ; trivial.

 apply TI_pre_fix_bounded with (A:=Wdom); trivial.
 rewrite <- H0; reflexivity.
Qed.

(* Mono_Bounded functions : includes constructors *)

 
Lemma mono_bounded_id X : mono_bounded X (fun w => w).
  red; trivial.
Qed.

Lemma mono_bounded_comp X Y F0 G :
  (forall w, w ∈ X -> F0 w ∈ Y) ->
  mono_bounded X F0 ->
  mono_bounded Y G ->
  mono_bounded X (fun x => G (F0 x)).
unfold mono_bounded; auto.
Qed.

Lemma mono_bounded_cst X w : mono_bounded X (fun _ => w).
red; reflexivity.
Qed.

Lemma mono_bounded_cstr X x f :
  (forall w, w ∈ X -> isWfun (f w)) ->
  (forall w, w ∈ X -> rel_domain (f w) ⊆ B x) ->
  (forall i, i ∈ B x -> mono_bounded X (fun w => cc_app (f w) i)) ->
  mono_bounded X (fun w => Wsup x (f w)).
unfold mono_bounded; intros fty fdom fprod; intros.
apply Zwdom.Wsup_mono; auto with *.
intros.
assert (i ∈ B x).
{apply fdom with (1:=H).
 rewrite rel_domain_ax; eauto. }
rewrite couple_in_app in H2|-*.
revert H2; apply fprod; auto.
Qed.

End SimpleCorecursion.

Let test := (COREC_typ,COREC_eqn,COREC_unique).
Print Assumptions test.


(* Indexed-corec *)

Section IndexedCoRecursion.
  
Variable I:set.
Variable F:(set->set)->set->set.
Hypothesis Fm:Proper((eq_set==>eq_set)==>eq_set==>eq_set) F.
Existing Instance Fm.
Hypothesis Fty :
  forall X f, X ⊆ Wdom -> COW ⊆ X -> Wf X ⊆ X ->
  morph1 f ->
  typ_fun f I X ->
  typ_fun (F f) I (Wf X).
Hint Resolve Fm : core.

Definition imono_bounded I X F :=
  forall w w0,
  morph1 w -> morph1 w0 ->
  typ_fun w0 I X -> (* w0 = observation *)
  typ_fun w I X ->
  incl_fam I w0 w -> (* obs of w0 are the same in w *)
  incl_fam I (F w0) (F w). (* F w0 can be observed both in F w *)
  
Hypothesis Fmono : imono_bounded I Wdom F.

Lemma TIF_WF_dom o :
  isOrd o ->
  typ_fun (TIF I F o) I Wdom.
intros oo; induction oo using isOrd_ind; red; intros.
rewrite TIF_eq; auto with *.
apply power_intro.
intros.
apply sup_ax in H2.
 destruct H2 as (?,?,(_,?)).
 apply power_elim with (2:=H3).
 apply Wf_typ with (X:=Wdom); auto with *.
 apply Fty with (X:=Wdom); auto with *.
 apply TIF_morph; reflexivity.
Qed.

Lemma FTIF_typ o w (wm:morph1 w) :
  isOrd o ->
  typ_fun w I (COWi o) ->
  typ_fun (F w) I (Wf (COWi o)).
intros.
apply Fty; trivial.
+apply COTI_bound; auto.
+apply COW_COWi; trivial.
+rewrite <- COWi_succ; auto with *.
 apply COTI_incl; auto with *.
Qed.


Lemma FTIF_mono a : a ∈ I -> increasing (fun o => F (TIF I F o) a).
red; intros.
apply Fmono; auto.
 apply TIF_morph; auto with *.
 apply TIF_morph; auto with *.

 apply TIF_WF_dom; trivial.

 apply TIF_WF_dom; trivial.

 red; intros.
 apply TIF_mono; trivial.
Qed.

Lemma TIF_WF_step o : isOrd o ->
  incl_fam I (TIF I F o) (F (TIF I F o)).
do 2 red; intros.
apply TIF_elim in H1; trivial.
destruct H1 as (o',?,?).
revert H2; apply FTIF_mono; eauto using isOrd_inv.
Qed.

Lemma TIF_WF_typ_gen o o' : isOrd o -> isOrd o' -> o' ⊆ o -> typ_fun (TIF I F o) I (COWi o').
intros oo; revert o'; elim oo using isOrd_ind; red; intros.
apply COTI_intro; auto with *.
 apply TIF_WF_dom; trivial.

 intros o''; intros.
 assert (oo'':isOrd o'') by eauto using isOrd_inv.
 assert (eqC: Wf (COWi o'') == COWi (osucc o'')).
  symmetry; apply COTI_mono_succ; auto with *.
 rewrite TIF_eq; auto.
 rewrite eqC.
 apply COWi_sup_intro with o''; auto.
  apply increasing_bounded_weaker; trivial.
  apply FTIF_mono; trivial.

  intros.
  rewrite <- eqC.
  apply FTIF_typ; auto.
  apply TIF_morph; auto with *.
Qed.

Lemma TIF_WF_typ o : isOrd o -> typ_fun (TIF I F o) I (COWi o).
intros; apply TIF_WF_typ_gen; auto with *.
Qed.


Definition ICOREC := TIF I F co_ord.

Instance ICOREC_morph : morph1 ICOREC.
apply TIF_morph; reflexivity.
Qed.


Lemma ICOREC_typ : typ_fun ICOREC I COW.
red; intros.
rewrite COW_def.
apply TIF_WF_typ; trivial.
Qed.

Lemma ICOREC_eqn : eq_fun I ICOREC (F ICOREC).
red; intros.
symmetry.
apply pre_incl_eq with (A:=A)(B:=B)(X:=COWi co_ord); auto.
 apply COWi_closure.

 rewrite <- COW_def.
 apply ICOREC_typ; trivial.

 rewrite <- COW_def, COW_eqn, COW_def.
 apply FTIF_typ; auto with *.
  apply ICOREC_typ.
  rewrite <- H0; trivial.

 rewrite H0.
 apply TIF_WF_step; trivial.
 rewrite <- H0; trivial.
Qed.


Lemma icorec_typ w :
  morph1 w ->
  typ_fun w I Wdom ->
  eq_fun I w (F w) ->
  typ_fun w I COW.
intros wm; intros.
rewrite COW_def.
elim co_ordo using isOrd_ind; intros.
red; intros.
apply COTI_intro; intros; auto with *.
red in H0; rewrite H0;[|trivial|reflexivity].
apply FTIF_typ; eauto using isOrd_inv.
Qed.

Lemma ICOREC_unique w :
  morph1 w ->
  typ_fun w I Wdom ->
  eq_fun I w (F w) ->
  eq_fun I w ICOREC.
intros wm; intros.
red; intros.
rewrite <- H2.
clear x' H2.
apply pre_incl_eq with (A:=A)(B:=B)(X:=COW); auto.
 rewrite <- COW_eqn; reflexivity.

 apply ICOREC_typ; trivial.

 apply icorec_typ; trivial.

 unfold ICOREC.
 revert x H1; elim co_ordo using isOrd_ind; intros.
 red; intros.
 elim TIF_elim with (4:=H5); intros; auto with *.
 red in H0; rewrite H0; [|trivial|reflexivity].
 revert H7; apply Fmono; auto.
  apply TIF_morph; reflexivity.

  apply TIF_WF_dom; eauto using isOrd_inv.

  red; intros; apply H3; trivial.
Qed.

End IndexedCoRecursion.

Let itest := (ICOREC_typ,ICOREC_eqn,COREC_unique).
Print Assumptions itest.

End CoW.

