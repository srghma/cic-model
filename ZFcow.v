Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFtarski ZFstable.
Require Import ZFgrothendieck.
Require Import ZFlist.
Require Import ZFcoc.
Require Import ZFord.
Require Import ZFfix ZFcofix.
Require Import ZFfixfun.
Require Import ZFwdom.

Import ZFrepl.

Section CoW.

(* The first parameter of W-types (aka the payload) *)
Variable A : set.
(* The subterm index type *)
Variable B : set -> set.
Hypothesis Bm : morph1 B.

Notation Wdom := (ZFwdom.Wdom A B).
Notation Wf := (ZFwdom.Wf A B).
Notation Wsup := ZFwdom.Wsup.
Notation Wfst := ZFwdom.Wfst.
Notation Wsnd_fun := ZFwdom.Wsnd_fun.
Existing Instance ZFwdom.Wf_mono.

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
apply ZFwdom.Wf_typ; trivial.
reflexivity.
Qed.

  Lemma COWi_decreasing : decreasing COWi.
apply COTI_mono; auto with *.
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

  Lemma COWi_closure : COW ⊆ Wf COW.
red; intros.
assert (z ∈ Wf Wdom).
{assert (z ∈ Wf (COWi zero)).
 {apply COTI_elim with (3:=H); auto with *. }
 unfold COWi in H0; rewrite COTI_initial in H0; auto with *. }
apply Wf_elim in H0;[|trivial];
  destruct H0 as (a,tya,(f,tyf,eqz)).
rewrite eqz.
apply Wf_intro; trivial. 
rewrite cc_eta_eq with (1:=tyf).
apply cc_prod_intro; intros; auto with *.
 do 2 red; intros; apply cc_app_morph; auto with *.
apply COTI_intro; auto with *.
 apply cc_prod_elim with (1:=tyf); trivial.

 intros.
 assert (oo':isOrd o') by eauto using isOrd_inv.
 rewrite <- COTI_mono_succ; auto with *.
 2:apply ZFwdom.Wf_typ; [trivial|reflexivity].
 assert (z ∈ Wf (COWi (osucc o'))).
 {apply COTI_elim with (3:=H); auto with *. }
 rewrite eqz in H2.
 apply ZFwdom.Wf_elim' with (A:=A)(B:=B)(x:=a); trivial.
  intros; apply cc_prod_elim with (1:=tyf); trivial.

  apply COTI_bound; auto with *.
Qed.
Opaque co_ord.
  
Lemma COW_eqn : COW == Wf COW.
apply incl_eq.
 apply COWi_closure.

 unfold COW.
 rewrite <- COWi_succ; trivial.
 apply COWi_decreasing; auto with *.
 red; intros.
 apply isOrd_trans with co_ord; auto.
Qed.

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
(* We rediscover after the fact that COW is the iteration at omega *)
Lemma COW_def : COW == COWi co_ord.
reflexivity.
(*apply incl_eq.
 apply COW_COWi; trivial.

 apply COW_gfp.
  apply COTI_bound; auto.
  apply COWi_closure.*)
Qed.
Opaque COW.
Hint Resolve co_ordo : core.

Lemma COW_Wf1 : COW ⊆ Wf Wdom.
rewrite COW_eqn; apply Wf_mono; trivial.
apply COW_typ.  
Qed.
Lemma Wf1_Wdom : Wf Wdom ⊆ Wdom.
apply ZFwdom.Wf_typ; [trivial|reflexivity].
Qed.
Hint Resolve COW_typ COW_eqn COW_Wf1 Wf1_Wdom : core.


(*******************************************************************************************)
(* Universe facts *)

Section W_Univ.

  Variable U : set.
  Hypothesis Ugrot : grot_univ U.
  Hypothesis Unontriv : ZFord.omega ∈ U.  

  Hypothesis aU : A ∈ U.
  Hypothesis bU : forall a, a ∈ A -> B a ∈ U.

  Let Gdom : Wdom ∈ U.
apply ZFwdom.G_Wdom; trivial.
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


Lemma COWi_complete I o : (exists i, i ∈ I) -> isOrd o -> complete I (COWi o).
intros wit oo; elim oo using isOrd_ind; intros.
assert (aux := fun o => isOrd_inv _ o H).
intros f fext fdir.
apply COTI_intro; intros; auto with *.
+apply Wdom_sup_closed; trivial.
 revert fdir; apply directed_covariant.
 apply COTI_bound; auto with *.

+apply Wf_complete; auto.
  apply COTI_bound; auto with *.

  revert fdir; apply directed_covariant.
  rewrite <- COTI_mono_succ; auto with *.
   apply COTI_mono; auto with *.
   apply olts_le; apply lt_osucc_compat; trivial.
Qed.

Lemma COWi_sup_intro f o o' :
  ext_fun o f ->
  increasing f ->
  isOrd o ->
  o' ∈ o ->
  (forall o'', o' ⊆ o'' -> o'' ∈ o -> f o'' ∈ Wf (COWi o')) ->
  sup o f ∈ Wf (COWi o').
intros fext fmono oo lto Hrec.
intros; apply complete_sup_intro with (F:=fun o => Wf(COWi o)); trivial.
apply Wf_complete; eauto.
 apply COTI_bound; auto with *.
 apply isOrd_inv with o; trivial.

 apply COWi_complete; eauto.
 apply isOrd_inv with o; trivial.
Qed.

(* Simple co-recursion *)
Section SimpleCorecursion.

Hypothesis F:set->set.
Hypothesis Fm:morph1 F.
(*Existing Instance Fm.*)
Hypothesis Fty :
  forall X w, COW ⊆ Wf X -> Wf X ⊆ X ->
            w ∈ X -> F w ∈ Wf X.
(*Hint Resolve Fm.*)

Lemma TI_WF_dom o :
  isOrd o ->
  TI F o ∈ Wdom.
induction 1 using isOrd_ind; intros.
rewrite TI_eq; auto with *.
apply power_intro.
intros.
apply sup_ax in H2. 2:do 2 red; intros; apply Fm; apply TI_morph; trivial.
destruct H2.
apply power_elim with (2:=H3).
apply Wf_typ with (X:=Wdom); auto with *.
Qed.


Lemma FTI_typ o w :
  isOrd o ->
  w ∈ COWi o ->
  F w ∈ Wf (COWi o).
intros.
apply Fty; trivial.
 rewrite COW_eqn; apply Wf_mono; [trivial|].
 apply COW_COWi; trivial.

 unfold COWi; rewrite <- COTI_mono_succ; auto with *.
 apply COTI_incl; auto with *.
Qed.

(**)

Definition productive X F :=
  forall w w0,
  w0 ∈ X -> (* w0 = observation *)
  w ∈ X -> w0 ⊆ w -> (* obs of w0 are the same in w *)
  F w0 ⊆ F w. (* F w0 can be observed both in F w *)
  
Hypothesis Fprod : productive Wdom F.
(*  forall X, X ⊆ Wdom -> COW ⊆ Wf X -> Wf X ⊆ X -> (* = K X *)
  productive X F.*)
         
Lemma FTI_mono : increasing (fun o => F (TI F o)).
red; intros.
apply Fprod.
 apply TI_WF_dom; trivial.

 apply TI_WF_dom; trivial.

 apply TI_mono; trivial.
Qed.
Lemma TI_WF_step o : isOrd o ->
  TI F o ⊆ F (TI F o).
red; intros.
apply TI_elim in H0; trivial.
destruct H0 as (o',?,?).
revert H1; apply FTI_mono; eauto using isOrd_inv.
Qed.


Lemma TI_WF_typ_gen o o' : isOrd o -> isOrd o' -> o' ⊆ o -> TI F o ∈ COWi o'.
intros oo; revert o'; elim oo using isOrd_ind; intros.
apply COTI_intro; auto with *.
 apply TI_WF_dom; trivial.

 intros o''; intros.
 assert (oo'':isOrd o'') by eauto using isOrd_inv.
 assert (eqC: Wf (COWi o'') == COWi (osucc o'')).
  symmetry; apply COTI_mono_succ; auto with *.
 rewrite TI_eq; auto.
 apply COWi_sup_intro; auto.
  apply FTI_mono.

  intros.
  apply FTI_typ; auto.
Qed.

Lemma TI_WF_typ o : isOrd o -> TI F o ∈ COWi o.
intros; apply TI_WF_typ_gen; auto with *.
Qed.



Definition K X :=
  COW ⊆ X /\ X ⊆ Wdom /\ Wf X ⊆ X.
Definition K' X :=
  COW ⊆ X /\ X ⊆ Wdom /\ X ⊆ Wf X.

Definition Fcfx X := subset X (fun w => F w ⊆ w).

Lemma Fcxf_cofix w :
  w ∈ Fcfx COW ->
  w ∈ COW /\ w == F w.
intros.
apply subset_ax' in H.
destruct H.
split; trivial.
apply pre_incl_eq with (A:=A)(B:=B)(X:=COW); auto.
 rewrite <-COW_eqn; reflexivity.

 rewrite COW_eqn; apply Fty; auto.
  rewrite <-COW_eqn; reflexivity.
  rewrite <-COW_eqn; reflexivity.
do 2 red; intros.
rewrite H1.
reflexivity.
Qed.

Definition COREC := TI F co_ord.

Lemma COREC_typ : COREC ∈ COW.
rewrite COW_def.
apply TI_WF_typ; trivial.
Qed.

Lemma COREC_eqn : COREC == F COREC.  
symmetry.
apply pre_incl_eq with (A:=A)(B:=B)(X:=COWi co_ord); auto.
 apply COWi_closure.

 rewrite <- COW_def.
 apply COREC_typ.

 rewrite <- COW_def, COW_eqn, COW_def.
 apply FTI_typ; trivial.
 apply COREC_typ.

 apply TI_WF_step; trivial.
Qed.


Lemma corec_typ w :
  w ∈ Wdom ->
  w == F w ->
  w ∈ COW.
intros.
rewrite COW_def.
elim co_ordo using isOrd_ind; intros.
apply COTI_intro; intros; auto with *.
rewrite H0.
apply FTI_typ; eauto using isOrd_inv.
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

 unfold COREC.
 elim co_ordo using isOrd_ind; intros.
 red; intros.
 elim TI_elim with (3:=H4); intros; auto with *.
 rewrite H0; revert H6; apply Fprod; auto.
 apply TI_WF_dom; eauto using isOrd_inv.
Qed.

(* Productive functions : includes constructors *)

 
Lemma productive_id X : productive X (fun w => w).
  red; trivial.
Qed.

Lemma productive_comp X Y F0 G :
  (forall w, w ∈ X -> F0 w ∈ Y) ->
  productive X F0 ->
  productive Y G ->
  productive X (fun x => G (F0 x)).
unfold productive; auto.
Qed.

Lemma productive_cst X w : productive X (fun _ => w).
red; reflexivity.
Qed.

Lemma productive_cstr X x f :
  (forall w, w ∈ X -> is_cc_fun (B x) (f w)) ->
  (forall i, i ∈ B x -> productive X (fun w => cc_app (f w) i)) ->
  productive X (fun w => Wsup x (f w)).
unfold productive; intros fty fprod; intros.
apply ZFwdom.Wsup_mono with (B:=B); auto with *.
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
  forall X f, COW ⊆ Wf X -> Wf X ⊆ X ->
  morph1 f ->
  typ_fun f I X ->
  typ_fun (F f) I (Wf X).
Hint Resolve Fm : core.

Definition iproductive I X F :=
  forall w w0,
  morph1 w -> morph1 w0 ->
  typ_fun w0 I X -> (* w0 = observation *)
  typ_fun w I X ->
  incl_fam I w0 w -> (* obs of w0 are the same in w *)
  incl_fam I (F w0) (F w). (* F w0 can be observed both in F w *)
  
Hypothesis Fprod : iproductive I Wdom F.

Lemma TIF_WF_dom o :
  isOrd o ->
  typ_fun (TIF I F o) I Wdom.
intros oo; induction oo using isOrd_ind; red; intros.
rewrite TIF_eq; auto with *.
apply power_intro.
intros.
apply sup_ax in H2. 2:do 2 red; intros; apply Fm; auto with *; apply TIF_morph; trivial.
 destruct H2.
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
 rewrite COW_eqn; apply Wf_mono; auto with *.
 apply COW_COWi; trivial.

 unfold COWi; rewrite <- COTI_mono_succ; auto with *.
 apply COTI_incl; auto with *.
Qed.


Lemma FTIF_mono a : a ∈ I -> increasing (fun o => F (TIF I F o) a).
red; intros.
apply Fprod; auto.
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
 apply COWi_sup_intro; auto.
  do 2 red; intros.
  apply Fm; auto with *.
  apply TIF_morph; trivial.
  
  apply FTIF_mono; trivial.

  intros.
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
 revert H7; apply Fprod; auto.
  apply TIF_morph; reflexivity.

  apply TIF_WF_dom; eauto using isOrd_inv.

  red; intros; apply H3; trivial.
Qed.

End IndexedCoRecursion.

Let itest := (ICOREC_typ,ICOREC_eqn,COREC_unique).
Print Assumptions itest.

End CoW.

