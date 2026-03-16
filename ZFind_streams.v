Require Import ZF Znats ZFord Zcoc ZFwdom ZFcow.
Require Import ZFwsimul.
Import ZFcofix.


Lemma imono_bounded_inst I X g : typ_fun g I I -> imono_bounded I X (fun f i => f (g i)).
red; red; intros.
apply H4.
auto.
Qed.


Existing Instance Wfmap_morph.

Section Streams.

  Variable A : set.
  
  Definition Bstrm (a:set) := succ zero.

  Let Bstrmm : morph1 Bstrm.
unfold Bstrm; do 2 red; auto with *.
Qed.

  Definition sdom := Wdom A Bstrm.
  
  Definition streami o := COWi A Bstrm o.
  Definition stream := COW A Bstrm.
  
  Definition Scons (x:set) (s:set) : set :=
    Wsup x (cc_lam (succ zero) (fun _ => s)).

  Instance Scons_morph : morph2 Scons.
do 3 red; intros.  
apply Wsup_morph; trivial.
apply cc_lam_ext; [reflexivity|red; auto with *].
Qed.

  Lemma Scons_typ_gen X x s :
    X ⊆ sdom -> stream ⊆ X -> Wf A Bstrm X ⊆ X ->
    x ∈ A -> s ∈ X -> Scons x s ∈ Wf A Bstrm X.
intros.
apply Wf_intro; trivial.
apply cc_prod_intro; auto with *.
Qed.

  Lemma Scons_typ_stage o x s : isOrd o -> x ∈ A -> s ∈ streami o -> Scons x s ∈ streami (osucc o).
intros oo tyx tys.
unfold streami; rewrite COWi_succ; auto.
apply Scons_typ_gen; auto.
+apply COWi_typ; trivial.
+apply COW_COWi; trivial.
+rewrite <- COWi_succ; auto.
 apply COWi_incl; trivial.
Qed.

  Lemma Scons_typ x s : x ∈ A -> s ∈ stream -> Scons x s ∈ stream.
intros tyx tys.
unfold stream; rewrite COW_eqn; trivial.
apply Scons_typ_gen; auto with *.
+apply COW_typ; trivial.
+reflexivity.
+rewrite <- COW_eqn; trivial.
 reflexivity.
Qed.

  Lemma Scons_mono_raw x x' s s' :
    isWobj s ->
    isWobj s' ->
    x == x' ->
    s ⊆ s' ->
    Scons x s ⊆ Scons x' s'.
intros sw sw' eqx incls.
apply Zwdom.Wsup_mono; auto with *.
*apply isWfun_cc_lam;auto.
*apply isWfun_cc_lam;auto.
*intros.
 rewrite cc_lam_def in H|-*; auto with *.
 destruct H as (n,?,(y,?,?)).
 exists n;[|exists y]; auto.
Qed.
  
  Lemma Scons_mono X x s :
    (forall x, x ∈ X -> isWobj (s x)) ->
    mono_bounded X s ->
    mono_bounded X (fun i => Scons x (s i)).
unfold mono_bounded; intros sw smono; intros.
apply Scons_mono_raw; auto with *.
Qed.

  Lemma Scons_imono I X x s :
    (forall f i, i ∈ I -> typ_fun f I X -> isWobj (s f i)) ->
    (forall w, w ∈ X -> isWobj w) ->
    imono_bounded I X s ->
    imono_bounded I X (fun f i => Scons (x i) (s f i)).
unfold imono_bounded; intros sw Xw smono; red; intros.
apply Scons_mono_raw; auto with *.
apply smono; auto.
Qed.

  Definition hd s := Wfst s.

  Instance hd_morph : morph1 hd.
exact Wfst_morph.
Qed.

  Lemma hd_def x s : hd (Scons x s) == x.
apply Wfst_def.  
Qed.
  
  Definition tl s := Wsnd s zero.

  Instance tl_morph : morph1 tl.
do 2 red; intros.
apply Wsnd_morph; [trivial|reflexivity].
Qed.
  
  Lemma tl_def_gen o x s : isOrd o -> s ∈ streami o -> tl (Scons x s) == s. 
intros oo tys.
assert (e : cc_app (cc_lam (succ zero) (fun _ => s)) zero == s).
{rewrite cc_beta_eq; auto with *. apply succ_intro1; reflexivity. }
unfold tl, Scons; rewrite Wsnd_def; trivial.
apply isWfun_cc_lam; intros; auto.
eapply Wdom_Wobj; apply COWi_typ with (3:=tys); trivial.
Qed.


  Lemma tl_def x s : s ∈ stream -> tl (Scons x s) == s. 
apply tl_def_gen; trivial.
Qed.

  Lemma stream_elim_gen o s :
    isOrd o ->
    s ∈ streami (osucc o) ->
    hd s ∈ A /\ tl s ∈ streami o /\ s == Scons (hd s) (tl s).
intros oo tys.
unfold streami in tys; rewrite COWi_succ in tys; auto.
apply Wf_elim in tys; auto.
destruct tys as (x,tyx,(g,tyg,eqs)).
assert (eqg : g == λ __∈succ zero, (cc_app g zero)).
{rewrite cc_eta_eq with (1:=tyg).
 apply cc_lam_ext; auto with *;[reflexivity|].
  red; intros.
  apply cc_app_morph; [reflexivity|].
  apply union2_elim in H; destruct H.
    apply empty_ax in H; contradiction.
   apply singl_elim in H; auto. }
rewrite eqg in eqs.
assert (eq1 : hd s == x).
{rewrite eqs; apply hd_def. }
assert (eq2 : tl s == cc_app g zero).
{rewrite eqs.
 unfold tl. 
 apply tl_def_gen with (o:=o); auto.
 apply cc_prod_elim with (1:=tyg); trivial.
 apply succ_intro1; reflexivity. }
split;[|split]. 
*rewrite eq1; trivial.
*rewrite eq2.
 apply cc_prod_elim with (1:=tyg); trivial.
 apply succ_intro1; reflexivity.
*rewrite eq1, eq2.
 assumption.
Qed.
    

Section Repeat.
(* Parameterized cofix:
   CoFixpoint repeat x := Scons x (repeat x) *)

  Variable x : set.
  Hypothesis tyx : x ∈ A.
  
  Definition repeat := COREC (fun s => Scons x s).

  Instance rpt_m : morph1 (fun s : set => Scons x s).
do 2 red; intros; apply Scons_morph; auto with *.
Qed.

  Lemma rpt_typ o w :
    isOrd o ->
    w ∈ streami o -> Scons x w ∈ streami (osucc o).
intros.
apply Scons_typ_stage; trivial.
Qed.
  
  Lemma mono_rpt : mono_bounded sdom (fun s => Scons x s).
apply Scons_mono with (s:=fun s=>s).
*intros.
 apply Wdom_Wobj with (1:=H).
*apply mono_bounded_id.
Qed.

Hint Resolve rpt_m rpt_typ mono_rpt : core.
  
  Lemma repeat_typ : repeat ∈ stream.
apply COREC_typ; auto.
Qed.
  
  Lemma repeat_eqn : repeat == Scons x repeat.
apply COREC_eqn with (A:=A)(B:=Bstrm); auto.
Qed.

End Repeat.


Section From.

  Variable f : set -> set.
  Hypothesis fm : morph1 f.
  Hypothesis ftyp : typ_fun f A A.

  (* Indexed cofix:
  CoFixpoint from x := Scons x (from (f x)) *)

  Definition from := ICOREC A (fun frm x => Scons x (frm (f x))).

  Instance frm_m :  Proper ((eq_set ==> eq_set) ==> eq_set ==> eq_set)
                      (fun frm x => Scons x (frm (f x))).
do 3 red; intros; apply Scons_morph; auto with *.
Qed.

  Lemma frm_typ X frm :
  X ⊆ sdom -> stream ⊆ X -> Wf A Bstrm X ⊆ X ->
  morph1 frm ->
  typ_fun frm A X ->
  typ_fun (fun x => Scons x (frm (f x))) A (Wf A Bstrm X).
red; intros.
apply Scons_typ_gen; trivial.
apply H3.
apply ftyp; trivial.
Qed.
  
  Lemma frm_mono : imono_bounded A sdom (fun frm x => Scons x (frm (f x))).
apply Scons_imono.
*intros.
 eapply Wdom_Wobj; apply H0; auto.
*intros.
 apply Wdom_Wobj with (1:=H).
*apply imono_bounded_inst; trivial.
Qed.

  Hint Resolve frm_m frm_typ frm_mono : core.
  
  Lemma from_typ x : x ∈ A -> from x ∈ stream.
intros tyx.
unfold from; apply ICOREC_typ; auto with *.
Qed.
  
  Lemma from_eqn x : x ∈ A -> from x == Scons x (from (f x)).
intros tyx.
unfold from.
apply ICOREC_eqn with (A:=A)(B:=Bstrm)(F:=fun frm x => Scons x (frm (f x))); auto with *.
Qed.

End From.


Section Map.
  Variable f : set->set.
  Hypothesis ftyp : typ_fun f A A.
  Hypothesis fm : morph1 f.

  Definition map := Wfmap f.

  Lemma map_typ o : isOrd o -> typ_fun map (streami o) (streami o).
intros oo w tyw.
revert w tyw; elim oo using isOrd_ind; intros.
rename y into o'.
apply COTI_intro; auto.
apply Wfmap_typ with (A:=A)(B:=Bstrm); auto.
+reflexivity.
+apply COWi_typ in tyw; auto.
+intros o'' lto'.
 assert (o''o : isOrd o'') by eauto using isOrd_inv.
 assert (tyw' : w ∈ Wf A Bstrm (streami o'')).
 {apply COTI_elim with (3:=tyw); auto. }
 apply Wf_elim in tyw'; trivial.
 destruct tyw' as (x,tyx,(g,tyg,eqw)).
 unfold map.
 rewrite eqw.
 rewrite Wfmap_sup with (B':=Bstrm)(B:=Bstrm)(4:=tyx)(5:=tyg); auto.
 2:reflexivity. 
 2:apply COWi_typ; auto.
 apply Wf_intro; auto.
 apply cc_prod_intro; auto.
 *do 2 red; intros.
  rewrite H3; reflexivity.
 *intros i tyi.
  apply H1; trivial.
  apply cc_prod_elim with (1:=tyg); trivial.
Qed.

  Lemma map_cons o x s :
    isOrd o ->
    x ∈ A ->
    s ∈ streami o ->
    map (Scons x s) == Scons (f x) (map s).
intros oo tyx tys.    
unfold map,Scons.
rewrite Wfmap_sup with (B':=Bstrm)(B:=Bstrm)(X:=streami o)(4:=tyx); auto.
2:reflexivity.
2:apply COWi_typ; auto.
2:apply cc_prod_intro; auto with *.
apply Wsup_morph; trivial;[reflexivity|].
apply cc_lam_ext; [reflexivity|].
red; intros.
apply Wfmap_morph; trivial.
rewrite cc_beta_eq; auto.
reflexivity.
Qed.
  
  Lemma map_codef o s :
    isOrd o ->
    s ∈ streami (osucc o) ->
    hd (map s) == f (hd s) /\ tl (map s) == map (tl s).
intros oo tys.
destruct stream_elim_gen with (2:=tys) as (hdty&tlty&eqs); trivial.
rewrite eqs.
rewrite map_cons with (o:=o); trivial.
split.
+rewrite !hd_def; reflexivity.
+rewrite !tl_def_gen with (o:=o); auto.
 reflexivity.
 apply map_typ; trivial.
Qed.
  
  Lemma map_mono :
    mono_bounded sdom map.
red; intros.
intros z.
unfold map.
rewrite Wfmap_def with (2:=Wdom_Wobj _ _ _ H); trivial.
rewrite Wfmap_def with (2:=Wdom_Wobj _ _ _ H0); trivial.
intros (w,?,?); exists w;[trivial|].
apply H1; trivial.
Qed.

  (** Allows for a definition of from without index (but a parameter instead)
      CoFixpoint from x := Scons x (map f (from x). *)
  Definition alt_from x := COREC (fun s => Scons x (map s)).

  Lemma altfrmm x : morph1 (fun s : set => Scons x (map s)).
do 2 red; intros.
rewrite H; reflexivity.
Qed.

  Lemma altfrm_typ x :
    x ∈ A ->
    forall o w, isOrd o -> w ∈ streami o -> Scons x (map w) ∈ streami (osucc o).
intros.
apply Scons_typ_stage; auto.
apply map_typ; trivial.
Qed.

    Lemma altfrm_mono x :
    x ∈ A ->
    mono_bounded sdom (fun s => Scons x (map s)).
intros tyx.
apply Scons_mono.
*intros.
 apply Wfmap_Wobj; trivial.
 eapply Wdom_Wobj with (1:=H).
*apply map_mono.
Qed.

Hint Resolve altfrmm altfrm_typ altfrm_mono : core.

  Instance alt_from_morph : morph1 alt_from.
do 2 red; intros.
unfold alt_from.
unfold COREC.
apply TI_morph_gen;[|reflexivity].
red; intros.
rewrite H,H0; reflexivity.
Qed.
  
  Lemma alt_from_typ x :
    x ∈ A -> alt_from x ∈ stream.
intros tyx.
apply COREC_typ with (A:=A)(B:=Bstrm); eauto.
Qed.
  
  Lemma alt_from_eqn x :
    x ∈ A -> alt_from x == Scons x (map (alt_from x)).
intros tyx.
apply COREC_eqn with (A:=A)(B:=Bstrm); auto.
Qed.

  Lemma alt_from_map x :
    x ∈ A ->
    map (alt_from x) == alt_from (f x).
intros tyx.
apply COREC_unique with (A:=A)(B:=Bstrm); auto.
+apply COW_typ; auto.
 apply map_typ; auto.
 apply alt_from_typ; trivial.
+transitivity (map (Scons x (map (alt_from x)))).
 apply Wfmap_morph; auto.
 apply alt_from_eqn; trivial.

 rewrite map_cons with (o:=co_ord); auto.
 reflexivity. 
 apply map_typ; auto.
 apply alt_from_typ; trivial.
Qed.

  Lemma alt_from_eq x :
    x ∈ A ->
    alt_from x == from f x.
intros tyx.
apply ICOREC_unique with (A:=A)(B:=Bstrm); auto with *.
+apply frm_m; trivial.
+apply frm_typ; trivial.
+apply frm_mono; trivial.

+red; intros; apply COW_typ; auto.
 apply alt_from_typ; trivial.
+red; intros.
 rewrite alt_from_eqn with (1:=H).
 apply Scons_morph; trivial.
 rewrite alt_from_map; trivial.
 rewrite H0; reflexivity.
Qed.

End Map.
  
End Streams.
