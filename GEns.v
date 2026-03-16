Require Import ZFskol.
Require Import Choice.
Require Import Sublogic.

(** In this file, we give an attempt to build a model of IZF
   in Coq using pointed graphs. An attempt is made to separate
   the construction of the node type and data at the object level
   (head and membership relation). This is to avoid resorting to an
   extra sort above Ti.
 *)

(*Module IZF_R <: IZF_R_Ex_sig CoqSublogicThms.*)
Import CoqSublogicThms.

(* The level of indexes *)
Definition Ti := Type.

Record set_ : Type(* > Ti *) :=
  mkS {
      pts : Ti;
      head : pts;
      mem : pts -> pts -> Prop }.

Definition set := set_.

Definition wfs (x:set) : Prop :=
  Acc (mem x) (head x).

Definition wset := {x:set | wfs x}.

Definition sim_step {X Y:Ti} Rx Ry (R:X->Y->Prop) (i:X) (j:Y) :=
  (forall i', Rx i' i -> exists j', Ry j' j /\ R i' j') /\
  (forall j', Ry j' j -> exists i', Rx i' i /\ R i' j').

Definition sim {X Y:Ti} Rx Ry (R:X->Y->Prop) :=
  (forall i i' j, Rx i' i -> R i j -> exists j', Ry j' j /\ R i' j') /\
  (forall j j' i, Ry j' j -> R i j -> exists i', Rx i' i /\ R i' j').

Definition eq_set (x y:set) : Prop :=
  exists R:pts x -> pts y -> Prop,
    R (head x) (head y) /\ sim (mem x) (mem y) R.

Definition eq_wset (x y:wset) := eq_set (proj1_sig x) (proj1_sig y).

Definition eq_set_isL x y : isL (eq_set x y) := fun h => h.

Lemma eq_set_map X Y hx mx my (f:X->Y) :
  (forall i j, mx i j -> my (f i) (f j)) ->
  (forall i j, my i (f j) -> exists i', mx i' j /\ i = f i') ->
  eq_set (mkS X hx mx) (mkS Y (f hx) my).
exists (fun i j => j = f i); simpl; split; [trivial|].
split; simpl; intros.
*subst j.
 exists (f i'); split;auto.
*subst j; auto.
Qed.



Lemma eq_set_refl : forall x, eq_set x x.
intros x.
apply eq_set_map with (f:=fun i=>i); eauto.
Qed.

Lemma eq_set_sym : forall x y, eq_set x y -> eq_set y x.
intros.
destruct H as (R & ? & ? & ?).
exists (fun j i => R i j); split; [trivial|].
split; intros.
*apply H1 with i; trivial.
*apply H0 with j; trivial.
Qed.

Lemma eq_set_trans : forall x y z,
  eq_set x y -> eq_set y z -> eq_set x z.
intros.
destruct H as (Rxy & ? & ? & ?).
destruct H0 as (Ryz & ? & ? & ?).
exists (fun i k => exists j, Rxy i j /\ Ryz j k).
split; [|split]; intros.
*exists (head y); auto.
*destruct H6 as (iy & ? & ?).
 destruct H1 with (1:=H5)(2:=H6) as (iy' & ? & ?).
 destruct H3 with (1:=H8)(2:=H7) as (j' & ? & ?).
 exists j'; split; [trivial|].
 exists iy'; auto.
*destruct H6 as (iy & ? & ?).
 destruct H4 with (1:=H5)(2:=H7) as (iy' & ? & ?).
 destruct H2 with (1:=H8)(2:=H6) as (i' & ? & ?).
 exists i'; split; [trivial|].
 exists iy'; auto.
Qed.

(*
Lemma eq_set_def : forall x y,
  (forall i, exists j, eq_set (elts x i) (elts y j)) /\
  (forall j, exists i, eq_set (elts x i) (elts y j)) <->
  eq_set x y.
destruct x; simpl; reflexivity.
Qed.
*)
Definition move (x:set) : pts x -> set :=
  fun h => mkS (pts x) h (mem x).

Definition idx (x:set) := {i : pts x | mem x i (head x)}.

Definition elts (x:set) (i:idx x) : set :=
  move x (proj1_sig i).

Definition in_set x y :=
  exists j, eq_set x (elts y j).

Definition in_wset (x y:wset) := in_set (proj1_sig x) (proj1_sig y).


Definition in_set_isL x y : isL (in_set x y) := fun h => h.

Definition incl_set x y := forall z, in_set z x -> in_set z y.

Lemma eq_elim0 : forall x y i,
  eq_set x y ->
  exists j, eq_set (elts x i) (elts y j).
intros x y i (R & Rh & sim1 & sim2).
destruct sim1 with (1:=proj2_sig i)(2:=Rh) as (j&?&?).
exists (exist _ j H).
exists R; split; auto.
split; auto.
Qed.

Lemma eq_set_ax : forall x y,
  eq_set x y <-> (forall z, in_set z x <-> in_set z y).
unfold in_set; split; intros.
*split; intros; destruct H0 as (i&?).
 +destruct (eq_elim0 x y i) as (j&?); trivial.
  exists j.
  apply eq_set_trans with (elts x i); trivial.
 +apply eq_set_sym in H.
  destruct (eq_elim0 y x i) as (j&?); trivial.
  exists j.
  apply eq_set_trans with (elts y i); trivial.
*exists (sim_step (mem x) (mem y) (fun i' j' => eq_set (move x i') (move y j'))).
 split.
 +split; intros.
  ++destruct (H (move x i')) as (e1,_).
    destruct e1 as (j',?); [exists (exist _ i' H0); apply eq_set_refl|].
    exists (proj1_sig j');split; [apply (proj2_sig j')|trivial].
  ++destruct (H (move y j')) as (_,e2).
    destruct e2 as (i',?); [exists (exist _ j' H0); apply eq_set_refl|].
    exists (proj1_sig i'); split; [apply (proj2_sig i')|].
    apply eq_set_sym;trivial.
 +split; intros.
  ++destruct H1 as (H1,_).
    destruct H1 with (1:=H0) as (j',(?,?)).
    exists j'; split; [trivial|].
    split; intros.
    +++destruct eq_elim0 with (1:=H3)(i:=exist _ i'0 H4 : idx (move x i'))
         as ((j'0,?),?).
       exists j'0; auto.
    +++destruct eq_elim0 with (1:=eq_set_sym _ _ H3)
                              (i:=exist _ j'0 H4:idx(move y j')) as ((i'0,?),?).
       exists i'0; split; [trivial|].
       apply eq_set_sym; trivial.
  ++destruct H1 as (_,H1).
    destruct H1 with (1:=H0) as (i',(?,?)).
    exists i'; split; [trivial|].
    split; intros.
    +++destruct eq_elim0 with (1:=H3)(i:=exist _ i'0 H4:idx(move x i'))
         as ((j'0,?),?).
       exists j'0; split; trivial.
    +++destruct eq_elim0 with (1:=eq_set_sym _ _ H3)
                              (i:=exist _ j'0 H4:idx(move y j')) as ((i'0,?),?).
       exists i'0; split; trivial.
       apply eq_set_sym; trivial.
Qed.

Lemma eq_set_incl : forall x y,
  eq_set x y <-> (incl_set x y /\ incl_set y x).
intros.
unfold incl_set.
rewrite eq_set_ax.
split; try destruct 1; split; auto.
intros; apply H; auto.
intros; apply H; auto.
Qed.


Definition in_set_intro (x:set) (i:idx x) : in_set (elts x i) x :=
  ex_intro _ i (eq_set_refl _).
(*
Definition elts' (x:set) (i:pts x) : {y|in_set y x}.
exists (elts x i).
abstract (exists i; apply eq_set_refl).
Defined.
*)

Lemma in_reg : forall x x' y,
  eq_set x x' -> in_set x y -> in_set x' y.
destruct 2 as (i&?); intros.
exists i.
apply eq_set_trans with x; trivial.
apply eq_set_sym; trivial.
Qed.

Lemma eq_intro : forall x y,
  (forall z, in_set z x -> in_set z y) ->
  (forall z, in_set z y -> in_set z x) ->
  eq_set x y.
intros.
rewrite eq_set_ax.
split; intros; eauto.
Qed.

Lemma eq_elim : forall x y y',
  in_set x y ->
  eq_set y y' ->
  in_set x y'.
intros.
rewrite eq_set_ax in H0.
destruct (H0 x); auto.
Qed.

(* Set induction *)

Lemma Acc_in_set : forall x:wset, Acc in_set (proj1_sig x).
destruct x as (x,wfx).
cut (forall i (h:Acc (mem x) i), Acc in_set (move x i)).
{destruct x as (A,h,m); simpl; intros H; apply H; trivial. }
clear wfx; induction 1; simpl; intros.
constructor; intros.
destruct H1 as ((j,?),?); simpl in *.
unfold elts in H1; simpl in H1.
apply H0 in m.
constructor; intros.
apply Acc_inv with (move x j); [trivial|].
apply eq_elim with y; trivial.
Qed.

From Stdlib Require Import Inverse_Image.
Lemma Acc_in_wset : forall x:wset, Acc in_wset x.
intros.
apply Acc_inverse_image with (f:=@proj1_sig _ _).
apply Acc_in_set.
Qed.

Lemma wf_rec :
  forall P : wset -> Type,
  (forall x, (forall y, in_wset y x -> P y) -> P x) -> forall x, P x.
intros.
elim (Acc_in_wset x); intros.
apply X; apply X0.
Defined.


Lemma wf_ax :
  forall (P:wset->Prop),
  (forall x, (forall y, in_wset y x -> P y) -> P x) -> forall x, P x.
intros P.
apply wf_rec.
Qed.

(* *)

Definition supX (X:Ti) (f:X->Ti) : Ti :=
  option {i:X & f i}.

Definition supm (X:Ti) (f:X->set) (i j:supX X (fun i => pts(f i))) :=
       match i, j with
         Some(existT _ i' x), None => x = head (f i')
       | Some(existT _ i' x), Some(existT _ j' y) =>
           exists e: i' = j',
             mem (f j') (eq_rect _ (fun i=>_) x _ e) y
       | None, _ => False
       end.

Definition sup (X:Ti) (f:X->set) : set :=
  mkS (supX X (fun i => pts (f i))) None (supm X f).

Lemma eq_set_elts X f (i:X) :
  eq_set (move (sup X f) (Some(existT _ i (head (f i))))) (f i).
apply eq_set_sym.
apply eq_set_map with (f:=fun j => Some(existT (fun _=>_) i j)); simpl; intros.
*exists eq_refl; simpl; trivial.
*destruct i0 as [(i',j')|];[simpl in H|contradiction].
 destruct H as (e,H).
 subst i'; simpl in H.
 exists j'; auto.
Qed.

Lemma idx_sup X f (i:idx(sup X f)) :
  exists i':X, eq_set (elts (sup X f) i) (f i').
destruct i as ([(i',x)|],?); [|contradiction].
simpl in m; subst x.
exists i'.
apply eq_set_elts.
Qed.

Lemma in_set_def z X f :
  in_set z (sup X f) <-> exists i:X, eq_set z (f i).
unfold in_set; simpl.
split; intros.
*destruct H as (i, e).
 destruct idx_sup with (i:=i) as (j,?).
 exists j; apply eq_set_trans with (1:=e); trivial.
*destruct H as (i,e).
 eexists (exist _ (Some(existT _ i (head (f i)))) eq_refl).
 apply eq_set_trans with (1:=e).
 apply eq_set_sym.
 apply eq_set_elts.
Qed.

Lemma Acc_supm X f i p :
  Acc (mem (f i)) p ->
  Acc (supm X f) (Some (existT _ i p)).
induction 1.
constructor; intros.
destruct y as [(j,y)|]; [|contradiction].
simpl in H1.
destruct H1 as (e,H1).
destruct e; simpl in H1; auto.
Qed.

(* sup preserves well-foundation *)
Lemma sup_wf X f :
   (forall i:X, wfs (f i)) -> wfs (sup X f).
constructor; simpl; intros.
destruct y as [(i,y)|]; [|contradiction].
red in H0; subst y.
apply Acc_supm; apply H.
Qed.

Lemma subsingleton_morph X f Y g :
  (X -> forall P:Prop, (Y->P) -> P) ->
  (Y -> forall P:Prop, (X->P) -> P) ->
  (forall (i:X) (j:Y), eq_set (f i) (g j)) ->
  eq_set (sup X f) (sup Y g).
intros F G e; apply eq_set_ax; intros z.
rewrite !in_set_def.
split; destruct 1 as (i,?).
*apply (F i); intros j; exists j.
 apply eq_set_trans with (1:=H); trivial.
*apply (G i); intros j; exists j.
 apply eq_set_trans with (1:=H); apply eq_set_sym; trivial.
Qed.

(* *)
Definition emptyX : Ti := unit.

Definition empty :=
  mkS unit tt (fun _ _ => False).

Lemma empty_ax : forall x, ~ in_set x empty.
unfold in_set, empty; simpl.
red; intros.
destruct H as ((j,[ ]),_).
Qed.

(*Definition singl x := sup unit (fun _ => x).*)

(*Definition pairX (x y:Ti) : Ti :=
  supX bool (fun b => if b then x else y).*)
Definition pairX (x y:Ti) : Ti :=
  option(x+y).
Definition pairm (x y:set) (i j:pairX (pts x)(pts y)) : Prop :=
  match i, j with
  | Some (inl i), Some (inl j) => mem x i j
  | Some (inr i), Some (inr j) => mem y i j
  | Some (inl i), None => i = head x
  | Some (inr j), None => j = head y
  | _, _ => False
  end.
Definition pair0 (x y:set) :=
  mkS (pairX (pts x) (pts y)) None (pairm x y).

Definition pairX' (x y:Ti) : Ti :=
  supX bool (fun b => if b then x else y).

Definition pair x y :=
  sup bool (fun b => if b then x else y).

Lemma pair_ax a b z :
  in_set z (pair a b) <-> eq_set z a \/ eq_set z b.
unfold pair; rewrite in_set_def.
split; intros.
*destruct H as ([|],e); auto.
*destruct H; [exists true|exists false]; trivial.
Qed.

Lemma pair_morph :
  forall a a', eq_set a a' -> forall b b', eq_set b b' ->
  eq_set (pair a b) (pair a' b').
intros.
apply eq_set_ax; intros z.
rewrite !pair_ax.
split; destruct 1; eauto using eq_set_trans, eq_set_sym.
Qed.

Definition unionX (x:Ti) : Ti :=
  option x.

Definition unionm (x:set) (i j:unionX (pts x)) : Prop :=
  match i, j with
  | Some i, Some j => mem x i j
  | Some i, None => exists2 i', mem x i' (head x) & mem x i i'
  | None, _ => False
  end.
Definition union0 (x:set) := mkS (unionX (pts x)) None (unionm x).
Lemma union0_ax a z :
  in_set z (union0 a) <-> exists2 b, in_set z b & in_set b a.
unfold union0, in_set, elts, move; simpl.
split; intros.
*destruct H as ((j,jh),e); simpl in *.
 destruct j as [j|]; [|contradiction].
 red in jh; simpl in jh.
 destruct jh as (i,?,?).
 exists (move a i).
 +exists (exist _ j H0); simpl.
  apply eq_set_trans with (1:=e).
  exists (fun i j => i = Some j); simpl; split; [trivial|].
  split; simpl; intros.
  ++subst i0.
    destruct i' as [i'|]; [|contradiction].
    exists i'; auto.
  ++subst i0.
    exists (Some j'); simpl; auto.
 +exists (exist _ i H); simpl.
  apply eq_set_refl.
*destruct H as (b,inb,((i,ih),eqb)); simpl in eqb.
 change (in_set z b) in inb.
 apply eq_elim with (2:=eqb) in inb.
 destruct inb as ((j,jh),eqz); simpl in eqz.
 eexists (exist _ (Some j) _); simpl.
 apply eq_set_trans with (1:=eqz).
 exists (fun i j => j = Some i); simpl; split; [trivial|].
 split; simpl; intros.
 ++subst j0.
   exists (Some i'); simpl; auto.
 ++subst j0.
   destruct j' as [j'|]; [|contradiction].
   exists j'; auto.
Unshelve.
simpl.
exists i; trivial.
Qed.

Definition union (x:set) :=
  sup {i:idx x & idx (elts x i)}
    (fun p => elts (elts x (projT1 p)) (projT2 p)).

Lemma union_ax a z :
  in_set z (union a) <-> exists2 b, in_set z b & in_set b a.
unfold union; rewrite in_set_def.
split; intros.
*destruct H as ((i,j),e); simpl in e.
 exists (elts a i); [|apply in_set_intro].
 exists j; trivial.
*destruct H as (b,inb,ina).
 destruct ina as (i,eqb).
 apply eq_elim with (2:=eqb) in inb.
 destruct inb as (j,eqz).
 exists (existT _ i j); trivial.
Qed.

Lemma union_morph :
  forall a a', eq_set a a' -> eq_set (union a) (union a').
intros.
apply eq_set_ax; intros z.
rewrite !union_ax.
apply ex2_morph; intros w; [reflexivity|].
apply eq_set_ax; trivial.
Qed.

(* A useful tool to hide some logical information in a set *)
Lemma union_sup_eq X f x (d:forall P:Prop,(X->P)->P):
  (forall i:X, eq_set (f i) x) ->
  eq_set (union (sup X f)) x.
intros; apply eq_set_ax; intros z.
rewrite union_ax.
split.
*intros (b, inb, (i,ei)); simpl in *.
 destruct idx_sup with (i:=i) as (j,?).
 apply eq_elim with b; trivial.
 apply eq_set_trans with (1:=ei).
 apply eq_set_trans with (1:=H0); trivial.
*intros.
 apply d; intros i. 
 exists x; trivial.
 apply in_set_def.
exists i; simpl.
 apply eq_set_sym; trivial.
Qed.


Definition subsetX (x:Ti) : Ti :=
  option x.
Definition subsetm (x:set) (P:pts x->Prop) (i j:subsetX (pts x)) : Prop :=
  match i, j with
  | Some i, Some j => mem x i j
  | Some i, None => mem x i (head x) /\ P i
  | None, _ => False
  end.
Definition subset0 (x:set) (P:set->Prop) :=
  mkS (subsetX (pts x)) None (subsetm x (fun i => P (move x i))).

Definition subset (x:set) (P:set->Prop) :=
  sup {a|exists2 x', eq_set (elts x a) x' & P x'}
    (fun y => elts x (proj1_sig y)).

Lemma subset_ax x P z :
  in_set z (subset x P) <->
  in_set z x /\ exists2 z', eq_set z z' & P z'.
unfold subset; rewrite in_set_def.
split; intros.
*destruct H as ((a,(x',eqx',p)),eqz); simpl in eqz.
 split; [exists a; trivial|].
 exists x'; [|trivial].
 apply eq_set_trans with (elts x a); trivial.
*destruct H as ((a,eqz),(z',eqz',p)).
 assert (e := eq_set_trans _ _ _ (eq_set_sym _ _ eqz) eqz').
 exists (exist _ a (ex_intro2 _ _ z' e p)); simpl; trivial.
Qed.

  Lemma subset_morph : Proper (eq_set ==> (eq_set==>iff) ==> eq_set) subset.
Proof.
do 3 red; intros.
apply eq_set_ax; intros z.
do 2 rewrite subset_ax.
apply and_iff_morphism. 
*split; intros; apply eq_elim with (1:=H1); trivial.
 apply eq_set_sym; trivial.
*apply ex2_morph; red; intros.
 +reflexivity.
 +apply H0; apply eq_set_refl.
Qed.

Definition powerX (x:Ti) : Ti :=
  option ((x -> Prop) + x).

Definition powerm (x:set) (i j:powerX (pts x)) : Prop :=
  match i, j with
  | Some (inr i), Some (inr j) => mem x i j
  | Some (inr i), Some (inl P) => mem x i (head x) /\ P i
  | Some (inl _), None => True
  | _, _ => False
  end.

Definition power0 (x:set) (P:set->Prop) :=
  mkS (powerX (pts x)) None (powerm x).


Definition power (x:set) :=
  sup (idx x->Prop)
   (fun P => subset x (fun y => exists2 i, eq_set y (elts x i) & P i)).

Lemma power_ax x z :
  in_set z (power x) <->
  (forall y, in_set y z -> in_set y x).
unfold power; rewrite in_set_def.
split; intros.
*destruct H as (P,eqs).
 specialize eq_elim with (1:=H0)(2:=eqs); intro.
 apply (proj1 (proj1 (subset_ax _ _ _) H)).
*exists (fun i => in_set (elts x i) z).
 apply eq_intro; intros.
 +rewrite subset_ax.
  split; auto.
  exists z0;[apply eq_set_refl|].
  destruct H with (1:=H0) as (i,?).
  exists i; trivial.
  apply in_reg with z0; trivial.
 +rewrite subset_ax in H0.
  destruct H0 as (?,(z',?,(i,?,?))).
  apply in_reg with (elts x i); trivial.
  apply eq_set_sym;
    apply eq_set_trans with z'; trivial.
Qed.

Lemma power_morph : forall x y,
  eq_set x y -> eq_set (power x) (power y).
intros.
apply eq_intro; intros.
 rewrite power_ax in H0|-*; intros.
 apply eq_elim with x; auto.

 apply eq_set_sym in H.
 rewrite power_ax in H0|-*; intros.
 apply eq_elim with y; auto.
Qed.

Definition infX : Ti :=
  option nat.

Definition infr (i j: infX) :=
  match i, j with
  | Some n, Some m => n<m
  | Some _, None => True
  | _, _ => False
  end.

Definition infinity0 := mkS infX None infr.

Fixpoint num (n:nat) : set :=
  match n with
  | 0 => empty
  | S k => union (pair (num k) (pair (num k) (num k)))
  end.

Definition infinity := sup _ num.

Lemma infty_ax1 : in_set empty infinity.
apply in_set_def.
exists 0.
unfold elts, infinity, num.
apply eq_set_refl.
Qed.

Lemma infty_ax2 : forall x, in_set x infinity ->
  in_set (union (pair x (pair x x))) infinity.
intros.
unfold infinity in H.
rewrite in_set_def in H.
destruct H as (n,?).
apply in_set_def.
exists (S n); simpl.
apply union_morph.
apply pair_morph; trivial.
apply pair_morph; trivial.
Qed.


Definition replfX (x:Ti) (F:x->Ti) : Ti :=
  option {i:x & F i}.

Definition replfm (x:set) (F:set->set)
  (i j:replfX (pts x) (fun i=>pts (F (move x i)))) :=
  match i, j with
  | Some(existT _ i a), Some(existT _ j b) =>
      exists e:i=j, mem (F (move x j)) (eq_rect _ (fun _ => pts _) a _ e) b  
  | Some(existT _ i a), None =>
      a = head (F (move x i))
  | _, _ => False
  end.


Definition replf (x:set) (F:set->set) :=
  sup _ (fun i => F (elts x i)).

Lemma replf_ax : forall x F z,
  (forall z z', in_set z x ->
   eq_set z z' -> eq_set (F z) (F z')) ->
  (in_set z (replf x F) <->
   exists2 y, in_set y x & eq_set z (F y)).
intros. 
unfold replf; rewrite in_set_def.
split; intros.
*destruct H0 as (i,eqz).
 exists (elts x i); trivial.
 apply in_set_intro.
*destruct H0 as (y,(i,eqy),eqz).
 exists i.
 apply eq_set_trans with (F y); trivial.
 apply H; [|trivial].
 exists i; trivial.
Qed.


Lemma replf_morph : Proper (eq_set ==> (eq_set==>eq_set) ==> eq_set) replf.
do 3 red; intros.
apply eq_set_ax; intros z.
rewrite !replf_ax.
*apply ex2_morph; red; intros.
 +split; intros; apply eq_elim with (1:=H1); trivial.
  apply eq_set_sym; trivial.
 +split; intros; apply eq_set_trans with (1:=H1);[|apply eq_set_sym]; apply H0;
    apply eq_set_refl.
*intros.
 apply eq_set_trans with (x0 z0);[apply eq_set_sym|];apply H0; trivial.
 apply eq_set_refl.
*intros.
 apply eq_set_trans with (y0 z0);[|apply eq_set_sym];apply H0; trivial.
  apply eq_set_refl.
  apply eq_set_sym; trivial.
Qed.


(* Well-founded recursion *)

Module weakerWFR.

  Section Unpacked.

    Hypothesis A : Ti.

    Hypothesis R : A -> A -> Prop.

    Hypothesis F : (A -> Ti) -> A -> Ti.

    Definition cond_ty (P:Prop) (f:P->Ti) : Ti :=
      { h:P & f h }. 

    Fixpoint WFRX (x:A) (h:Acc R x) {struct h} : Ti :=
      F (fun y => option {r:R y x & WFRX y (Acc_inv h r)}) x.

    Hypothesis Fh : forall (f:A->set) (x:A), F (fun y => pts(f y)) x.
    Hypothesis Fm : forall (f:A->set) (x:A), F (fun y => pts(f y)) x -> F (fun y => pts (f y)) x -> Prop.

    Lemma WFRm (x:A) (h:Acc R x) : WFRX x h * forall(i j:WFRX x h),Prop.
revert x h; fix WFRm 2; intros.
destruct h; simpl.
pose (f := fun y =>
             let wfrh r := fst (WFRm y (a y r)) in
             let wfrm r := snd (WFRm y (a y r)) in
             mkS (option {r:R y x & WFRX y (a y r)}) None
               (fun i j =>
                  match i,j with
                  | Some(existT _ r i), None => 
                      wfrm r i (wfrh r)
                  | Some(existT _ r i), Some(existT _ r' j) => 
                      exists e:r=r', wfrm r' (eq_rect _ (fun r => WFRX y (a y r)) i _ e) j
                  | None,_ => False
                  end)).
split.
apply (Fh f).
apply (Fm f).
Defined.

  Definition WFR_aux (x:A) (h:Acc R x) : set :=
    mkS (WFRX x h) (fst (WFRm x h)) (snd (WFRm x h)).
  End Unpacked.

(*

  Definition WFR (x:set) :=
    union (sup (Acc R x) (fun h => WFR_aux x a h)).

  Fixpoint WFR_aux (x:set) (a:A) (h:Acc R' x) : set :=

  End Unpacked.

  Variable A:Ti.
  Hypothesis R : set -> set -> Prop.
  Hypothesis FX : (A -> Ti) -> A -> Ti.
  Hypothesis Fm : forall (f:A->set) (x:A), FX f x -> FX f x -> Prop.


Ti) (fm:forall x, fX x -> fX x -> Prop) (set -> set) -> set -> set.

Let y' := fun y
  Let FX := fun (f:pts A->Ti)(x:pts A) =>
              pts (F (fun (y:set) => ...) (move A x)).

 
  Fixpoint WFRm (x:set) (h:Acc R x) (i j:WFRX x h): Prop :=
      F (fun y =>
         union (sup {i:idx (R x)|eq_set y (elts (R x) i)}
                  (fun i => WFR_aux (elts (R x) (proj1_sig i)) a
                              (Acc_inv h (in_set_intro (R x) (proj1_sig i))))))
      x a.
*)
End weakerWFR.

Section WellFoundedRecursion.
  Context {A : Type} (Aeq : relation A) {Arefl : Equivalence Aeq}.


  Hypothesis R : set -> set.
  Hypothesis Rm : Proper (eq_set==>eq_set) R.
  Let R' x y := in_set x (R y).
  Hypothesis F : (set -> A -> set) -> set -> A -> set.
  Variable xx : set.

  Let Rle := clos_trans _ (fun x y => eq_set x y\/R' x y).

  Hypothesis Fext : forall x x' a a' f f',
    Rle x xx ->
    (forall y y' a a',
        R' y x -> eq_set y y' -> Aeq a a' -> eq_set (f y a) (f' y' a')) ->
    eq_set x x' ->
    Aeq a a' ->
    eq_set (F f x a) (F f' x' a').

  Fixpoint WFR_aux (x:set) (a:A) (h:Acc R' x) : set :=
    F (fun y a =>
         union (sup {i:idx (R x)|eq_set y (elts (R x) i)}
                  (fun i => WFR_aux (elts (R x) (proj1_sig i)) a
                              (Acc_inv h (in_set_intro (R x) (proj1_sig i))))))
      x a.

  Definition WFR (x:set)(a:A) :=
    union (sup (Acc R' x) (fun h => WFR_aux x a h)).
  
  Lemma WFR_auxm x x' a a' (h:Acc R' x) (h':Acc R' x') (r:Rle x xx) :
    eq_set x x' -> Aeq a a' ->
    eq_set (WFR_aux x a h) (WFR_aux x' a' h').
revert x x' a a' h h' r.
fix aux 5.
destruct h; destruct h'; simpl.
intros lexx eqx eqa.
assert (eR := Rm _ _ eqx).
rewrite eq_set_ax in eR.
apply Fext; [trivial| |trivial|trivial].
clear a a' eqa.
intros.
apply union_morph.
apply subsingleton_morph.
{destruct 1; intros.
 destruct (proj1 (eR _) (ex_intro _ x0 e)).
 apply eq_set_trans with (1:=eq_set_sym _ _ H0) in H3.
 eauto. }
{destruct 1; intros.
 destruct (proj2 (eR _) (ex_intro _ x0 e)).
 apply eq_set_trans with (1:=H0) in H3.
 eauto. }
intros (i,Ryx); simpl.
intros (j,Ryx'); simpl.
apply aux; [| |trivial].
{apply t_trans with x; [|trivial].
 apply t_step; right; exists i; apply eq_set_refl. }
apply eq_set_trans with (2:=Ryx'). 
apply eq_set_trans with (2:=H0). 
apply eq_set_sym; trivial.
Qed.

Lemma WFR_unfold x a (h:Acc R' x) (r:Rle x xx) : eq_set (WFR_aux x a h) (WFR x a).
unfold WFR.
apply eq_set_sym; apply union_sup_eq; [auto|].
intros.
apply WFR_auxm; [trivial|apply eq_set_refl | reflexivity].
Qed.

Lemma WFR_eqn a :
  Acc R' xx ->
  eq_set (WFR xx a) (F WFR xx a).
intros h.
assert (r:Rle xx xx) by (apply t_step; left; apply eq_set_refl).
apply eq_set_trans with (1:=eq_set_sym _ _ (WFR_unfold _ _ h r)).  
clear r.
destruct h as (acc); simpl.
apply Fext;[apply t_step;left;apply eq_set_refl| |apply eq_set_refl|reflexivity].
clear a; intros.
assert (r' : R' y' xx).
{apply in_reg with y; trivial. }
assert (r: Rle y' xx) by (apply t_step;right; trivial).
apply eq_set_trans with (2:=WFR_unfold _ _ (acc _ r') r).
destruct H as (i,?).
apply union_sup_eq; [eauto|].
intros; apply WFR_auxm; trivial.
{destruct i0 as (i',ei'); simpl.
 apply t_step; right; exists i'; apply eq_set_refl. }
apply eq_set_trans with y; trivial. 
apply eq_set_sym.
apply (proj2_sig i0).
Qed.

End WellFoundedRecursion.

Local Notation E:=eq_set (only parsing).

Lemma WFR_morph {A} (Aeq:relation A) {Aeqv : Equivalence Aeq} :
    Proper ((E==>E)==>((E==>Aeq==>E)==>E==>Aeq==>E)==>E==>Aeq==>E) WFR.
intros Rs Rs' eqRs F F' eqF x x' eqx a a' eqa.
pose (R:= fun x y => in_set x (Rs y)).
pose (R':= fun x y => in_set x (Rs' y)).
assert (accm : (eq_set ==> iff)%signature (Acc R) (Acc R')). 
{intros y y' eqy.
 split; intros acc.
 *revert y' eqy; induction acc; constructor; intros.
  apply H0 with y; [|apply eq_set_refl].
  apply eq_elim with (Rs' y'); trivial.
  apply eq_set_sym; apply eqRs; trivial.
 *revert y eqy; induction acc; constructor; intros.
  apply H0 with y0; [|apply eq_set_refl].
  apply eq_elim with (Rs y); trivial.
  apply eqRs; trivial. }
assert (aux : forall h h', eq_set (WFR_aux Rs F x a h) (WFR_aux Rs' F' x' a' h')).
{revert x x' eqx a a' eqa; fix aux 7; destruct h; destruct h'; simpl.
 apply eqF; trivial.
 clear a a' eqa.
 intros y y' eqy a a' eqa.
 apply union_morph.
 apply subsingleton_morph.
 {intros (i,?) P h.
  destruct eq_elim0 with (1:=eqRs _ _ eqx) (i:=i) as (j,?).
  apply h; clear h.
  exists j.
  apply eq_set_trans with (2:=H).
  apply eq_set_trans with (2:=e).
  apply eq_set_sym; trivial. }
 {intros (i,?) P h.
  destruct eq_elim0 with (1:=eq_set_sym _ _ (eqRs _ _ eqx)) (i:=i) as (j,?).
  apply h; clear h.
  exists j.
  apply eq_set_trans with (1:=eqy).
  apply eq_set_trans with (1:=e); trivial. }
 intros (i,ei) (j,ej); simpl.
 apply aux; [|trivial].
 apply eq_set_trans with (2:=ej).
 apply eq_set_trans with (2:=eqy).
 apply eq_set_sym; trivial. }
unfold WFR.
apply union_morph.
simpl.
apply subsingleton_morph; [| |apply aux].
*intros.
 apply H0.
 revert H; apply accm; trivial.
*intros.
 apply H0.
 revert H; apply accm; trivial.
Qed.

Notation "x ∈ y" := (in_set x y).
Notation "x == y" := (eq_set x y).

(* Deriving the existentially quantified sets *)

Lemma empty_ex: exists empty, forall x, ~ x ∈ empty.
exists empty.
exact empty_ax.
Qed.

Lemma pair_ex: forall a b, exists c, forall x, x ∈ c <-> (x == a \/ x == b).
intros.
exists (pair a b).
apply pair_ax.
Qed.

Lemma union_ex: forall a, exists b,
    forall x, x ∈ b <-> (exists2 y, x ∈ y & y ∈ a).
intros.
exists (union a).
apply union_ax.
Qed.

Lemma subset_ex : forall x P, exists b,
  forall z, z ∈ b <->
  (z ∈ x /\ exists2 z', z == z' & P z').
intros.
exists (subset x P).
apply subset_ax.
Qed.

Lemma power_ex: forall a, exists b,
     forall x, x ∈ b <-> (forall y, y ∈ x -> y ∈ a).
intros.
exists (power a).
apply power_ax.
Qed.

(* Infinity *)

Lemma infinity_ex: exists2 infinite,
    (exists2 empty, (forall x, ~ x ∈ empty) & empty ∈ infinite) &
    (forall x, x ∈ infinite ->
     exists2 y, (forall z, z ∈ y <-> (z == x \/ z ∈ x)) &
       y ∈ infinite).
exists infinity.
 exists empty.
  exact empty_ax.
  exact infty_ax1.

 intros.
 exists (union (pair x (pair x x))); intros.
  rewrite union_ax.
  split; intros.
   destruct H0.
   rewrite pair_ax in H1; destruct H1.
    right.
    unfold in_set.
    apply eq_elim with x0; trivial.

    left.
    specialize eq_elim with (1:=H0) (2:=H1); intro.
    rewrite pair_ax in H2; destruct H2; trivial.

   destruct H0.
    exists (pair x x).
     rewrite pair_ax; auto.

     rewrite pair_ax; right; apply eq_set_refl.

    exists x; trivial.
    rewrite pair_ax; left; apply eq_set_refl.

  apply infty_ax2; trivial.
Qed.

(*Require Import IntMap.*)

Definition icons {A:Type} (x:A) (i:nat->A) (k:nat) : A :=
  match k with 
  | 0 => x
  | S k => i k
  end.
Definition idcons {B}{A:nat->Type} (x:B) (i:forall n,A n) (k:nat) : icons B A k :=
  match k with 
  | 0 => x
  | S k => i k
  end.


Inductive zform :=
| In : zterm -> zterm -> zform
| Fa : zform
| And : zform -> zform -> zform
| Or : zform -> zform -> zform
| Imp : zform -> zform -> zform
| Allb : zterm -> zform -> zform
| Exb : zterm -> zform -> zform

with zterm :=
| Var : nat-> zterm
| Pair : zterm -> zterm -> zterm
| Union : zterm -> zterm
| Power : zterm -> zterm
| Subset : zterm -> zform -> zterm 
| Nat : zterm.

Definition ilift l k :=
  match k with
  | 0 => 0
  | S k => S (l k)
  end.

Fixpoint ren (l:nat->nat) t : zterm :=
  match t with
  | Var k => Var (l k)
  | Pair x y => Pair (ren l x) (ren l y)
  | Union x => Union (ren l x)
  | Power x => Power (ren l x)
  | Subset x P => Subset (ren l x) (ren_f (ilift l) P)
  | Nat => Nat
  end
with ren_f l f : zform :=
  match f with
  | In x y => In (ren l x) (ren l y)
  | Fa => Fa
  | And A B => And (ren_f l A) (ren_f l B)
  | Or A B => Or (ren_f l A) (ren_f l B)
  | Imp A B => Imp (ren_f l A) (ren_f l B)
  | Allb x A => Allb (ren l x) (ren_f (ilift l) A)
  | Exb x A => Exb (ren l x) (ren_f (ilift l) A)
end.

Definition lift k := ren (fun n=>k+n).
Definition lift_f k := ren_f (fun n=>k+n).
Definition lift1_f k := ren_f (ilift(fun n=>k+n)).

Definition slift l k :=
  match k with
  | 0 => Var 0
  | S k => lift 1 (l k)
  end.
Fixpoint sub (l:nat->zterm) t : zterm :=
  match t with
  | Var k => l k
  | Pair x y => Pair (sub l x) (sub l y)
  | Union x => Union (sub l x)
  | Power x => Power (sub l x)
  | Subset x P => Subset (sub l x) (sub_f (slift l) P)
  | Nat => Nat
  end
with sub_f l f : zform :=
  match f with
  | In x y => In (sub l x) (sub l y)
  | Fa => Fa
  | And A B => And (sub_f l A) (sub_f l B)
  | Or A B => Or (sub_f l A) (sub_f l B)
  | Imp A B => Imp (sub_f l A) (sub_f l B)
  | Allb x A => Allb (sub l x) (sub_f (slift l) A)
  | Exb x A => Exb (sub l x) (sub_f (slift l) A)
end.
Definition subst_f f t :=
  sub_f (icons t Var) f.

Definition Iff A B := And (Imp A B) (Imp B A).

Definition Incl a b :=
  Allb a (In (Var 0) (lift 1 b)).

Definition Eq a b :=
  And (Incl a b) (Incl b a).

Definition Pair_ax : zform :=
  let a := Var 0 in
  let b := Var 1 in 
  And
    (And (In a (Pair a b)) (In b (Pair a b)))
    (Allb (Pair a b) (Or (Eq (Var 0) (lift 1 a)) (Eq (Var 0) (lift 1 b)))).

Definition Union_ax :=
  let a := Var 0 in
  And (Allb a (Allb (Var 0) (In (Var 0) (Union (lift 2 a)))))
      (Allb (Union a) (Exb (lift 1 a) (In (Var 1) (Var 0)))).

(* If we want z to be bounded, then we should also 
   include forall x \incl y... as bounded *)
Definition Power_ax :=
  let a := Var 1 in
  let z := Var 0 in (* z not bounded *)
  Iff (Incl z a) (In z (Power a)).
 
Definition Subset_ax P :=
  let a := Var 0 in
  And (Allb a (Imp (subst_f (lift1_f 1 P) (Var 0)) (In (Var 0) (lift 1 (Subset a P)))))
      (Allb (Subset a P) (And (In (Var 0) (lift 1 a)) (subst_f (lift1_f 1 P) (Var 0)))).


Module SetInterp.

Fixpoint int_f (f:zform) (i:nat->set) : Prop :=
  match f with
  | In x y => in_set (int x i) (int y i)
  | Fa => False
  | And A B => int_f A i /\ int_f B i
  | Or A B => int_f A i \/ int_f B i
  | Imp A B => int_f A i -> int_f B i
  | Allb x A => forall a, in_set a (int x i) -> int_f A (icons a i)
  | Exb x A => exists a, in_set a (int x i) /\ int_f A (icons a i)
  end
with int (t:zterm) (i:nat->set) : set :=
  match t with
  | Var n => i n
  | Pair x y => pair (int x i) (int y i)
  | Union x => union (int x i)
  | Power x => power (int x i)
  | Subset x P => subset (int x i) (fun a => int_f P (icons a i))
  | Nat => infinity
end.

(* Showing axioms of Z *)
 
Lemma pair_sound i : int_f Pair_ax i.
simpl.
split;[split|].
*apply pair_ax; left; apply eq_set_refl.
*apply pair_ax; right; apply eq_set_refl.
*intros.
 apply pair_ax in H; destruct H;[left|right].
 apply eq_set_incl;trivial.
 apply eq_set_incl;trivial.
Qed.


End SetInterp.

Module CICInterp.
(* Interp in CIC *)

(* We need: option, +, X->Prop, nat *)
Fixpoint intTi (t:zterm) (i:nat->Ti) : Ti :=
  match t with
  | Var n => i n
  | Pair x y => pairX (intTi x i) (intTi y i)
  | Union x => unionX (intTi x i)
  | Power x => powerX (intTi x i)
  | Subset x P => subsetX (intTi x i)
  | Nat => infX
end.

Definition setm (X:Ti) := (X * (X->X->Prop))%type.
Definition mks (X:Ti)(m:setm X) : set := mkS X (fst m) (snd m).

Definition eqs (X Y:Ti) (mx:setm X) (my:setm Y) : Prop :=
  exists R:X->Y->Prop, R (fst mx) (fst my) /\ sim (snd mx) (snd my) R.

Lemma eqs_ok X Y mx my : eqs X Y mx my <-> eq_set (mks _ mx) (mks _ my).
unfold eqs, eq_set; simpl; reflexivity.
Qed.

Definition ins (X Y:Ti) (mx:setm X) (my:setm Y) : Prop :=
  exists j:Y, snd my j (fst my) /\ eqs X Y mx (j,snd my).

Lemma ins_ok X Y mx my : ins X Y mx my <-> in_set (mks _ mx) (mks _ my).
unfold ins, in_set; simpl.
split; intros.
*destruct H as (j&?&?).
 exists (exist _ j H); simpl.
 exact H0.
*destruct H as ((j,?),?).
 exists j; split; trivial.
Qed.


Fixpoint int_f (f:zform) (i:nat->Ti) (j:forall n, setm(i n)) : Prop :=
  match f with
  | In x y => ins (intTi x i) (intTi y i) (intm x i j) (intm y i j)
  | Fa => False
  | And A B => int_f A i j /\ int_f B i j
  | Or A B => int_f A i j \/ int_f B i j
  | Imp A B => int_f A i j -> int_f B i j
  | Allb x A => let X := intTi x i in
                let hm := intm x i j in
                forall a:X, snd hm a (fst hm) ->
                int_f A (icons X i) (fun k => match k with 0 => (a,snd hm) | S k=>j k end)
  | Exb x A => let X := intTi x i in
               let hm := intm x i j in
               exists a:X, snd hm a (fst hm) /\
               int_f A (icons X i) (fun k => match k with 0 => (a,snd hm) | S k=>j k end)
  end
with intm (t:zterm) (i:nat->Ti) (j:forall n, setm(i n)) : setm (intTi t i) :=
  match t return setm (intTi t i) with
  | Var n => j n
  | Pair x y => (None,pairm (mks (intTi x i) (intm x i j))
                            (mks (intTi y i) (intm y i j)))
  | Union x => (None,unionm (mks (intTi x i) (intm x i j)))
  | Power x => (None,powerm (mks (intTi x i) (intm x i j)))
  | Subset x P => let X := intTi x i in
                  let hm := intm x i j in
                  (None, subsetm (mks (intTi x i) (intm x i j))
                           (fun a => int_f P (icons X i)
           (fun k => match k with 0 => (a,snd hm) | S k=>j k end)))
  | Nat => (None, infr)
end.

End CICInterp.

Module ShallowProp_Interp.

Inductive Ty :=
| opt : Ty -> Ty (* Or sum inf X *)
| sum : Ty -> Ty -> Ty
| cart : Ty -> Ty -> Ty
| arr : Ty -> Ty -> Ty
| pr : Ty
| inf : Ty.

Parameter Elpr : Ti. (* Should be Pr... To avoid inductive-rec *)

Fixpoint El (t:Ty) : Ti :=
  match t with
  | opt x => option (El x)
  | sum x y => (El x + El y)%type
  | cart x y => (El x * El y)%type
  | arr x y => El x -> El y
  | pr => Elpr
  | inf => nat
  end.

Inductive Pr :=
| all : forall X:Ty, (El X -> Pr) -> Pr
| ex : forall X:Ty, (El X -> Pr) -> Pr
| abs
| imp : Pr -> Pr -> Pr
| and : Pr -> Pr -> Pr
| or : Pr -> Pr -> Pr
| equ : forall X:Ty, El X -> El X -> Pr.

Fixpoint ElP (P:Pr) : Prop :=
  match P with
  | all X P => forall x:El X, ElP(P x)
  | ex X P => exists x:El X, ElP(P x)
  | abs => False
  | imp P Q => ElP P -> ElP Q
  | and P Q => ElP P /\ ElP Q
  | or P Q => ElP P \/ ElP Q
  | equ X a b => a=b
end.

Parameter prI : Pr -> El pr.
Parameter prE : El pr -> Pr.
Parameter pr_ok : forall P, ElP (prE (prI P)) <-> ElP P.

Definition impr_abs := all pr (fun P => prE P).

Lemma impr_fa : ~ ElP impr_abs.
simpl.
intro.
generalize (H (prI abs)).
apply pr_ok.
Qed.

Definition impr_and (A B:Pr) : Pr :=
  all pr (fun P => imp (imp A (imp B (prE P))) (prE P)).

Lemma impr_and_ok A B : ElP (impr_and A B) <-> ElP A /\ ElP B.
split; simpl; intros.
*apply (pr_ok (and A B)).
 apply H; intros.
 rewrite pr_ok; simpl; auto.
*destruct H; auto.
Qed.

Definition pow x := arr x pr.
Definition rel X Y := arr X (arr Y pr).

Fixpoint intTi (t:zterm) (i:nat->Ty) : Ty :=
  match t with
  | Var n => i n
  | Pair x y => opt (sum (intTi x i) (intTi y i))
  | Union x => opt (intTi x i)
  | Power x => opt(sum(pow (intTi x i))(intTi x i))
  | Subset x P => opt (intTi x i)
  | Nat => opt inf
end.

Definition setm (X:Ty) := cart X (rel X X).
Definition memP {X} (mx:El(setm X)) (i j:El X) : Pr :=
  prE (snd mx i j).

Definition setr {X} (m:El(setm X)) :=
  fun x y => ElP (memP m x y).

Definition simP (X Y : Ty) Rx Ry R :=
 and (all X (fun i => all X (fun i' => all Y (fun j =>
         imp(Rx i' i) (imp (R i j) (ex Y (fun j'=>and(Ry j' j)(R i' j'))))))))
     (all Y (fun j => all Y (fun j' => all X (fun i =>
         imp(Ry j' j) (imp (R i j) (ex X (fun i'=>and(Rx i' i)(R i' j')))))))).

Definition eqsP (X Y:Ty) (mx:El(setm X)) (my:El(setm Y)) : Pr :=
  ex (rel X Y) (fun R => let R i j := prE(R i j) in
                               and (R(fst mx)(fst my))
                                 (simP X Y (memP mx) (memP my) R)).
Definition insP (X Y:Ty) (mx:El(setm X)) (my:El(setm Y)) : Pr :=
  ex Y (fun j => and(memP my j (fst my)) (eqsP X Y mx (j,snd my))).

Definition eqs (X Y:Ty) (mx:El(setm X)) (my:El(setm Y)) : Prop :=
  exists R:El X->El Y->Prop, R (fst mx) (fst my) /\ sim (setr mx) (setr my) R.


Definition mks (X:Ty)(m:El(setm X)) : set := mkS (El X) (fst m) (setr m).
Lemma eqs_ok X Y mx my : eqs X Y mx my <-> eq_set (mks _ mx) (mks _ my).
unfold eqs, eq_set; simpl; reflexivity.
Qed.

Definition ins (X Y:Ty) (mx:El(setm X)) (my:El(setm Y)) : Prop :=
  exists j:El Y, setr my j (fst my) /\ eqs X Y mx (j,snd my).

Lemma ins_ok X Y mx my : ins X Y mx my <-> in_set (mks _ mx) (mks _ my).
unfold ins, in_set; simpl.
split; intros.
*destruct H as (j&?&?).
 exists (exist _ j H); simpl.
 exact H0.
*destruct H as ((j,?),?).
 exists j; split; trivial.
Qed.
Lemma insP_ok X Y mx my : ElP (insP X Y mx my) <-> in_set (mks _ mx) (mks _ my).
Admitted.
Opaque insP.

(*Declare ML Module "magic.plugin".*)

Definition pair_m {X Y} (mx:El(setm X))(my:El(setm Y)) (i j:pairX (El X) (El Y)) : El pr :=
prI
match i with
| Some (inl i0) =>
    match j with
    | Some (inl j0) => memP mx i0 j0
    | Some (inr _) => abs
    | None => equ X i0 (fst mx)
    end
| Some (inr j0) =>
    match j with
    | Some (inl _) => abs
    | Some (inr j1) => memP my j0 j1
    | None => equ Y j0 (fst my)
    end
| None => abs
end.

Lemma pair_m_i1 {X Y} (mx:El(setm X))(my:El(setm Y)) i j :
  ElP (memP mx i j) ->
  ElP (prE (pair_m mx my (Some(inl i)) (Some(inl j)))).
unfold pair_m.
rewrite pr_ok; trivial.
Qed.

Lemma pair_m_elim {X Y} (mx:El(setm X))(my:El(setm Y)) i j P :
  (forall i j, ElP (memP mx i j) -> P (Some(inl i)) (Some(inl j))) ->
  (forall i j, ElP (memP my i j) -> P (Some(inr i)) (Some(inr j))) ->
  P (Some(inl(fst mx))) None ->
  P (Some(inr(fst my))) None ->
  ElP (prE (pair_m mx my i j)) -> P i j.
intros.
unfold pair_m in H.
rewrite pr_ok in H.
destruct i as [[i|i]|]; simpl in H; [| |contradiction].
*destruct j as [[j|?]|]; [auto|contradiction|].
 simpl in H; subst i; trivial.
*destruct j as [[j|?]|]; [contradiction|auto|].
 simpl in H; subst i; trivial.
Qed.

Definition union_m {X} (mx:El(setm X)) (i j:unionX (El X)) : El pr :=
prI
match i with
| Some i0 =>
    match j with
    | Some j0 => memP mx i0 j0
    | None => ex X (fun i' => and (memP mx i' (fst mx)) (memP mx i0 i'))
    end
| None => abs
end.
Definition tru := imp abs abs.

Definition power_m {X} (mx:El(setm X)) (i j:option((El X->El pr)+El X)) : El pr :=
  prI
  match i, j with
  | Some (inr i), Some (inr j) => memP mx i j
  | Some (inr i), Some (inl P) => and (memP mx i (fst mx)) (prE (P i))
  | Some (inl _), None => tru
  | _, _ => abs
  end.

Definition subset_m {X} (mx:El(setm X)) (P:El X->Pr) (i j:subsetX (El X)) : El pr :=
  prI
  match i, j with
  | Some i, Some j => memP mx i j
  | Some i, None => and (memP mx i (fst mx)) (P i)
  | None, _ => abs
  end.

Definition inf_m (i j : infX) : El pr :=
prI
match i with
| Some n => match j with
            | Some m => if Nat.ltb n m then tru else abs
            | None => tru
            end
| None => abs
end.
  

Fixpoint int_fP (f:zform) (i:nat->Ty) (j:forall n, El(setm(i n))) : Pr :=
  match f with
  | In x y => insP (intTi x i) (intTi y i) (intm x i j) (intm y i j)
  | Fa => abs
  | And A B => and (int_fP A i j) (int_fP B i j)
  | Or A B => or (int_fP A i j) (int_fP B i j)
  | Imp A B => imp (int_fP A i j) (int_fP B i j)
  | Allb x A => let X := intTi x i in
                let hm := intm x i j in
                all X (fun a=> imp (prE(snd hm a (fst hm)))
                  (int_fP A (icons X i) (fun k => match k with 0 => (a,snd hm) | S k=>j k end)))
  | Exb x A => let X := intTi x i in
               let hm := intm x i j in
               ex X (fun a=> and (prE(snd hm a (fst hm)))
                 (int_fP A (icons X i) (fun k => match k with 0 => (a,snd hm) | S k=>j k end)))
  end
with intm (t:zterm) (i:nat->Ty) (j:forall n, El(setm(i n))) : El(setm(intTi t i)) :=
  match t return El(setm (intTi t i)) with
  | Var n => j n
  | Pair x y => (None,pair_m (intm x i j) (intm y i j))
  | Union x => (None,union_m (intm x i j))
  | Power x => (None,power_m (intm x i j))
  | Subset x P => let X := intTi x i in
                  let hm := intm x i j in
                  let i' := icons X i in
                  let j' a k : El(setm(i' k)) :=
                    match k with 0 => (a,snd hm) | S k=>j k end in
                  (None, subset_m (intm x i j) (fun a => int_fP P i' (j' a)))
  | Nat => (None, inf_m)
end.


Fixpoint int_f (f:zform) (i:nat->Ty) (j:forall n, El(setm(i n))) : Prop :=
  match f with
  | In x y => ins (intTi x i) (intTi y i) (intm x i j) (intm y i j)
  | Fa => False
  | And A B => int_f A i j /\ int_f B i j
  | Or A B => int_f A i j \/ int_f B i j
  | Imp A B => int_f A i j -> int_f B i j
  | Allb x A => let X := intTi x i in
                let hm := intm x i j in
                forall a:El X, setr hm a (fst hm) ->
                int_f A (icons X i) (fun k => match k with 0 => (a,snd hm) | S k=>j k end)
  | Exb x A => let X := intTi x i in
               let hm := intm x i j in
               exists a:El X, setr hm a (fst hm) /\
               int_f A (icons X i) (fun k => match k with 0 => (a,snd hm) | S k=>j k end)
  end.


#[local] Definition mks2 := existT (fun X=>El(setm X)).

Definition f_equal2 :=
fun {A1 A2 B : Type} (f : A1 -> A2 -> B) {x1 y1 : A1} {x2 y2 : A2} (H : x1 = y1) =>
match H in (_ = a) return (x2 = y2 -> f x1 x2 = f a y2) with
| eq_refl =>
    fun H0 : x2 = y2 =>
    match H0 in (_ = a) return (f x1 x2 = f x1 a) with
    | eq_refl => eq_refl
    end
end.
Fixpoint intTi_ren y {l i i'}:
  (forall k, i k = i' (l k)) ->
  intTi y i = intTi (ren l y) i'.
revert l i i'; induction y; simpl; intros; auto.
*apply f_equal2 with (f:=fun X Y => opt (sum X Y)); auto.
*apply f_equal with (f:=opt); auto.
*apply f_equal with (f:=fun X=>opt(sum(pow X) X)); auto.
*apply f_equal with (f:=opt); auto.
Defined.


Inductive eqm {X} (mx:El(setm X)): forall {Y}, El(setm Y) -> X=Y -> Prop :=
  refl_eqm : eqm mx mx eq_refl.


Lemma f_eqm {X Y} {mx:El(setm X)}{my:El(setm Y)}{e:X=Y}(f:Ty->Ty)(F:forall X, El(setm X) -> El(setm (f X))) :
  eqm mx my e -> eqm (F X mx) (F Y my) (f_equal f e).
intros.
destruct H.
unfold f_equal.
constructor.
Defined.
 
Lemma f_eqm2 {X Y X' Y'} {mx:El(setm X)}{mx':El(setm X')}{my:El(setm Y)}{my':El(setm Y')}(e1:X=X')(e2:Y=Y')(f:Ty->Ty->Ty)(F:forall X Y, El(setm X) -> El(setm Y) -> El(setm (f X Y))) :
  eqm mx mx' e1 -> eqm my my' e2 -> eqm (F X Y mx my) (F X' Y' mx' my') (f_equal2 f e1 e2).
intros.
destruct H.
destruct H0.
unfold f_equal2.
constructor.
Defined.
(*Lemma f_eqmP2 {X Y X' Y'} {mx:El(setm X)}{mx':El(setm X')}{my:El(setm Y)}{my':El(setm Y')}(e1:X=X')(e2:Y=Y')(f:Ty->Ty->Pr)(F:forall X Y, El(setm X) -> El(setm Y) -> El(setm (f X Y))) :
  eqm mx mx' e1 -> eqm my my' e2 -> F X Y mx my = F X' Y' mx' my'.

) (f_equal2 f e1 e2).
intros.
destruct H.
destruct H0.
unfold f_equal2.
constructor.
Defined.
*)
Fixpoint int_ren y l i j i' j':
  forall E:(forall k, i k = i' (l k)) ,
  (forall k, eqm (j k) (j' (l k)) (E k)) ->
  eqm (intm y i j) (intm (ren l y) i' j') (intTi_ren y E)

with int_fP_ren y l i j i' j':
  forall E:(forall k, i k = i' (l k)) ,
  (forall k, eqm (j k) (j' (l k)) (E k)) ->
  int_fP y i j = int_fP (ren_f l y) i' j'.
*destruct y; simpl; intros; auto.
 +assert (e1 : eqm (intm y1 i j) (intm (ren l y1) i' j') (intTi_ren y1 E)).
  {apply int_ren; auto. }
  assert (e2 : eqm (intm y2 i j) (intm (ren l y2) i' j') (intTi_ren y2 E)).
  {apply int_ren; auto. }
  apply f_eqm2 with (f:=fun X Y => opt(sum X Y))(F:=fun X Y mx my => (None,pair_m mx my)); trivial.
 +assert (e : eqm (intm y i j) (intm (ren l y) i' j') (intTi_ren y E)).
  {apply int_ren; auto. }
  apply f_eqm with (f:=fun X => opt X)(F:=fun X mx => (None,union_m mx)); trivial.
 +assert (e : eqm (intm y i j) (intm (ren l y) i' j') (intTi_ren y E)).
  {apply int_ren; auto. }
  apply f_eqm with (f:=fun X => opt(sum(pow X) X))(F:=fun X mx => (None,power_m mx)); trivial.
 +assert (e : eqm (intm y i j) (intm (ren l y) i' j') (intTi_ren y E)).
  {apply int_ren; auto. }
  unfold subset_m, subsetX. 
  clear; admit.
 +constructor.
*destruct y; simpl; intros; auto.
 +admit.
 +rewrite <- int_fP_ren with (E:=E)(i:=i)(j:=j); [|trivial].
  rewrite <- int_fP_ren with (E:=E)(i:=i)(j:=j); [|trivial].
  trivial.
 +rewrite <- int_fP_ren with (E:=E)(i:=i)(j:=j); [|trivial].
  rewrite <- int_fP_ren with (E:=E)(i:=i)(j:=j); [|trivial].
  trivial.
 +rewrite <- int_fP_ren with (E:=E)(i:=i)(j:=j); [|trivial].
  rewrite <- int_fP_ren with (E:=E)(i:=i)(j:=j); [|trivial].
  trivial.
Admitted.



Lemma int_fP_incl x y i j :
  ElP (int_fP (Incl x y) i j) <->
  forall z, in_set z (mks _ (intm x i j)) -> in_set z (mks _ (intm y i j)).
set (il := icons (intTi x i) i) in *.
set (jl i' := fun k : nat =>
        match
          k as k0
          return
            (El (il k0) *
             (El (il k0) -> El (il k0) -> Elpr))
        with
        | 0 => (i', snd (intm x i j))
        | S k0 => j k0
        end).
 assert (tmp := fun i' => int_ren y S i j il (jl i') (fun _=>eq_refl) (fun _ => refl_eqm _)).
split; simpl; intros.
*destruct H0 as ((i',?),e).
 unfold elts in e; simpl in e.
 simpl in m.
 unfold setr, memP in m.
 apply H in m; clear H.
 fold il in m.
 rewrite insP_ok in m.
 apply eq_set_sym in e; apply in_reg with (1:=e).
 apply eq_elim with (1:=m).
 apply eq_set_sym.
 change (mks _ (intm y i j) == mks _ (intm (ren S y) il (jl i'))).
 case (tmp i'); apply eq_set_refl.
*rewrite insP_ok.
 apply eq_elim with (mks _ (intm y i j)).
 +apply H.
  apply in_set_intro with (i:=exist _ x0 H0).
 +change (mks _ (intm y i j) == mks _ (intm (ren S y) il (jl x0))).
  case (tmp x0); apply eq_set_refl.
Qed.

Lemma int_fP_eq x y i j :
  ElP (int_fP (Eq x y) i j) <-> mks _ (intm x i j) == mks _ (intm y i j).
simpl.
rewrite eq_set_incl; unfold incl_set.
apply and_iff_morphism.
*apply int_fP_incl.
*apply int_fP_incl.
Qed.
Opaque Eq.

Lemma pair_i1 X Y mx my :
  mks X mx == mks (opt(sum X Y)) (Some (inl (fst mx)), pair_m mx my).
unfold mks; simpl.
unfold setr, memP, pair_m; simpl.
apply eq_set_map with (f:=fun i => Some(inl i)); intros.
*rewrite pr_ok; trivial.
*rewrite pr_ok in H; trivial.
 destruct i as [[i|?]|]; try contradiction.
 exists i; split; auto.
Qed.
 

Lemma pair_i2 X Y mx my :
  mks Y my == mks (opt(sum X Y)) (Some (inr (fst my)), pair_m mx my).
unfold mks; simpl.
unfold setr, memP, pair_m; simpl.
apply eq_set_map with (f:=fun i => Some(inr i)); intros.
*rewrite pr_ok; trivial.
*rewrite pr_ok in H; trivial.
 destruct i as [[?|i]|]; try contradiction.
 exists i; split; auto.
Qed.


Lemma Pair_ax_ok i j : ElP (int_fP Pair_ax i j).
unfold Pair_ax.
unfold ElP.
unfold int_fP.
fold int_fP.
fold ElP.
split; [split|].
*rewrite insP_ok.
 simpl.
 eexists (exist (fun _=>_) (Some (inl (fst (j 0)))) _).
 unfold elts;simpl.
 Unshelve. 2:simpl; unfold setr, memP, pair_m; simpl; rewrite pr_ok; simpl; auto.
 apply pair_i1.
*rewrite insP_ok.
 simpl.
 eexists (exist (fun _=>_) (Some (inr (fst (j 1)))) _).
 unfold elts;simpl.
 Unshelve. 2:simpl; unfold setr, memP, pair_m; simpl; rewrite pr_ok; simpl; auto.
 apply pair_i2.
*intros.
 simpl in x, H |-.
 do 2 rewrite int_fP_eq; simpl.
 unfold pair_m in H; rewrite pr_ok in H.
 destruct x as [[a|a]|]; [left|right|contradiction].
 +apply eq_set_sym.
  simpl in H; subst a.
  apply pair_i1 with (my:=j 1).
 +apply eq_set_sym.
  simpl in H; subst a.
  apply pair_i2.
Qed.

End ShallowProp_Interp.




(******************************************************)

Module Interp.

Inductive Ty :=
| opt : Ty -> Ty (* Or sum inf X *)
| sum : Ty -> Ty -> Ty
| cart : Ty -> Ty -> Ty
| arr : Ty -> Ty -> Ty
| pr : Ty
| inf : Ty.

Definition pow x := arr x pr.
Definition rel X Y := arr X (arr Y pr).

Parameter El : Ty -> Ti.

Parameter None : forall {X}, El (opt X).
Parameter Some : forall {X}, El X -> El (opt X).
Parameter match_opt :
  forall {X} (P:Ty),
  El P ->
  (El X -> El P) ->
  El(opt X) -> El P.
(*Parameter opt_rect :
  forall {X} (P:El(opt X)->Ty),
  El (P None) ->
  (forall x:El X, El (P (Some x))) ->
  forall o:El(opt X), El (P o).*)
Parameter inl : forall {X Y}, El X -> El(sum X Y).
Parameter inr : forall {X Y}, El Y -> El(sum X Y).
Parameter match_sum :
  forall {X Y} (P:Ty),
  (El X -> El P) -> (El Y -> El P) -> El (sum X Y) -> El P.

Parameter pair : forall {X Y}, El X -> El Y -> El(cart X Y).
Parameter match_cart :
  forall {X Y} (P:Ty),
  (El X -> El Y -> El P) -> El (cart X Y) -> El P.
Parameter cart_eq : forall {X Y P} (f:El X->El Y->El P) x y,
  match_cart P f (pair x y) = f x y.

Definition fst {X Y} (p:El(cart X Y)) :=
  match_cart X (fun x y => x) p.
Definition snd {X Y} (p:El(cart X Y)) :=
  match_cart Y (fun x y => y) p.

Parameter lam : forall {X Y}, (El X -> El Y) -> El(arr X Y).
Parameter app : forall {X Y}, (El (arr X Y)) -> El X -> El Y.
Parameter infI : nat -> El inf.
Parameter infE : El inf -> nat.

Inductive Pr :=
| all : forall X:Ty, (El X -> Pr) -> Pr
| ex : forall X:Ty, (El X -> Pr) -> Pr
| abs
| imp : Pr -> Pr -> Pr
| and : Pr -> Pr -> Pr
| or : Pr -> Pr -> Pr
| equ : forall X:Ty, El X -> El X -> Pr.

Definition tru := imp abs abs.

Parameter prI : Pr -> El pr.
Parameter prE : El pr -> Pr.

Fixpoint ElP (P:Pr) : Prop :=
  match P with
  | all X P => forall x:El X, ElP(P x)
  | ex X P => exists x:El X, ElP(P x)
  | abs => False
  | imp P Q => ElP P -> ElP Q
  | and P Q => ElP P /\ ElP Q
  | or P Q => ElP P \/ ElP Q
  | equ X a b => a=b
end.

Parameter pr_ok : forall P, ElP (prE (prI P)) <-> ElP P.


Definition impr_abs := all pr (fun P => prE P).

Lemma impr_fa : ~ ElP impr_abs.
simpl.
intro.
generalize (H (prI abs)).
apply pr_ok.
Qed.

Definition impr_and (A B:Pr) : Pr :=
  all pr (fun P => imp (imp A (imp B (prE P))) (prE P)).

Lemma impr_and_ok A B : ElP (impr_and A B) <-> ElP A /\ ElP B.
split; simpl; intros.
*apply (pr_ok (and A B)).
 apply H; intros.
 rewrite pr_ok; simpl; auto.
*destruct H; auto.
Qed.


Fixpoint intTi (t:zterm) (i:nat->Ty) : Ty :=
  match t with
  | Var n => i n
  | Pair x y => opt (sum (intTi x i) (intTi y i))
  | Union x => opt (intTi x i)
  | Power x => opt(sum(pow (intTi x i))(intTi x i))
  | Subset x P => opt (intTi x i)
  | Nat => opt inf
end.

Definition setm (X:Ty) := cart X (rel X X).
Definition memP {X} (mx:El(setm X)) (i j:El X) : Pr :=
  prE (app (app (snd mx) i) j).

Definition setr {X} (m:El(setm X)) :=
  fun x y => ElP (memP m x y).

Definition simP (X Y : Ty) Rx Ry R :=
 and (all X (fun i => all X (fun i' => all Y (fun j =>
         imp(Rx i' i) (imp (R i j) (ex Y (fun j'=>and(Ry j' j)(R i' j'))))))))
     (all Y (fun j => all Y (fun j' => all X (fun i =>
         imp(Ry j' j) (imp (R i j) (ex X (fun i'=>and(Rx i' i)(R i' j')))))))).

Definition eqsP (X Y:Ty) (mx:El(setm X)) (my:El(setm Y)) : Pr :=
  ex (rel X Y) (fun R => let R i j := prE(app (app R i) j) in
                               and (R(fst mx)(fst my))
                                 (simP X Y (memP mx) (memP my) R)).
Definition insP (X Y:Ty) (mx:El(setm X)) (my:El(setm Y)) : Pr :=
  ex Y (fun j => and(memP my j (fst my)) (eqsP X Y mx (pair j (snd my)))).

Definition eqs (X Y:Ty) (mx:El(setm X)) (my:El(setm Y)) : Prop :=
  exists R:El X->El Y->Prop, R (fst mx) (fst my) /\ sim (setr mx) (setr my) R.


Definition mks (X:Ty)(m:El(setm X)) : set := mkS (El X) (fst m) (setr m).
Lemma eqs_ok X Y mx my : eqs X Y mx my <-> eq_set (mks _ mx) (mks _ my).
unfold eqs, eq_set; simpl; reflexivity.
Qed.

Definition ins (X Y:Ty) (mx:El(setm X)) (my:El(setm Y)) : Prop :=
  exists j:El Y, setr my j (fst my) /\ eqs X Y mx (pair j (snd my)).

Parameter sim_ext: forall X Y,
  Proper (pointwise_relation X (pointwise_relation X iff)  ==>
          pointwise_relation Y (pointwise_relation Y iff)  ==>
          pointwise_relation X (pointwise_relation Y iff)  ==> iff) sim.

Lemma ins_ok X Y mx my : ins X Y mx my <-> in_set (mks _ mx) (mks _ my).
unfold ins, in_set; simpl.
split; intros.
*destruct H as (j&?&?).
 exists (exist _ j H); simpl.
 unfold mks, elts, move; simpl.
 destruct H0 as (R,(?,?)); exists R; simpl.
 split.
 +unfold fst at 2 in H0.
  rewrite cart_eq in H0; trivial.
 +unfold setr at 2 in H1.
  revert H1; apply iff_impl; apply sim_ext; auto with *.
  do 2 red; intros.
  unfold setr, memP.
  unfold snd at 1; rewrite cart_eq; reflexivity.
*destruct H as ((j,?),?).
 exists j; split; trivial.
 red in H; simpl in H.
 red; simpl.
 replace (fst (pair j _)) with j; [|symmetry;apply cart_eq].
 destruct H as (R,(?,?)); exists R; simpl.
 split; trivial.
 revert H0; apply iff_impl; apply sim_ext; auto with *.
 do 2 red; intros.
 unfold setr, memP.
 unfold snd at 2; rewrite cart_eq; reflexivity.
Qed.

Definition mksetm {X} (h:El X) (R:El X->El X->El pr) : El(setm X) :=
  pair h (lam (fun i => lam (fun j => R i j))).

Definition pair_m {X Y} (mx:El(setm X))(my:El(setm Y)) (i j:El(opt(sum X Y))) : El pr :=
  match_opt pr
    (prI abs)
    (fun i =>
     match_sum pr
       (fun i:El X =>
          match_opt pr
            (prI(equ X i (fst mx)))
            (fun j =>
               match_sum pr
                 (fun j:El X => prI (memP mx i j))
                 (fun _:El Y => prI abs)
                 j)
            j)
       (fun i:El Y =>
          match_opt pr
            (prI(equ Y i (fst my)))
            (fun j =>
               match_sum pr
                 (fun _:El X => prI abs)
                 (fun j:El Y => prI (memP my i j))
                 j)
            j)
       i)
    i.


Definition union_m {X} (mx:El(setm X)) (i j:El(opt X)) : El pr :=
  match_opt pr
    (prI abs)
    (fun i:El X =>
       match_opt pr
         (prI (ex X (fun i' => and (memP mx i' (fst mx)) (memP mx i i'))))
         (fun j:El X => prI(memP mx i j))
         j)
    i.


Definition power_m {X} (mx:El(setm X)) (i j:El(opt(sum(arr X pr) X))) : El pr :=
  match_opt pr
    (prI abs)
    (fun i:El(sum _ _) =>
     match_sum pr
       (fun P:El(arr _ _) =>
        match_opt pr
          (prI tru)
          (fun _ => prI abs) j) 
       (fun i:El X =>
        match_opt pr
          (prI abs)
          (fun j:El(sum _ _) =>
           match_sum pr
             (fun P:El(arr _ _) =>
                prI(and (memP mx i (fst mx)) (prE (app P i))))
             (fun j:El X => prI (memP mx i j))
             j)
          j)
       i)
    i.

Definition subset_m {X} (mx:El(setm X)) (P:El X->Pr) (i j:El(opt X)) : El pr :=
  match_opt pr
    (prI abs)
    (fun i:El X =>
     match_opt pr
       (prI (and (memP mx i (fst mx)) (P i)))
       (fun j:El X => prI (memP mx i j))
       j)
    i.

Definition inf_m (i j : El(opt inf)) : El pr :=
  match_opt pr
    (prI abs)
    (fun i:El inf =>
     match_opt pr
       (prI tru)
       (fun j:El inf => if Nat.ltb (infE i) (infE j) then prI tru else prI abs)
       j)
    i.

Fixpoint int_fP (f:zform) (i:nat->Ty) (j:forall n, El(setm(i n))) : Pr :=
  match f with
  | In x y => insP (intTi x i) (intTi y i) (intm x i j) (intm y i j)
  | Fa => abs
  | And A B => and (int_fP A i j) (int_fP B i j)
  | Or A B => or (int_fP A i j) (int_fP B i j)
  | Imp A B => imp (int_fP A i j) (int_fP B i j)
  | Allb x A => let X := intTi x i in
                let hm := intm x i j in
                all X (fun a=> imp (memP hm a (fst hm))
                  (int_fP A (icons X i) (fun k => match k with 0 => (pair a (snd hm)) | S k=>j k end)))
  | Exb x A => let X := intTi x i in
               let hm := intm x i j in
               ex X (fun a=> and (memP hm a (fst hm))
                 (int_fP A (icons X i) (fun k => match k with 0 => (pair a (snd hm)) | S k=>j k end)))
  end
with intm (t:zterm) (i:nat->Ty) (j:forall n, El(setm(i n))) : El(setm(intTi t i)) :=
  match t return El(setm (intTi t i)) with
  | Var n => j n
  | Pair x y => mksetm None (pair_m (intm x i j) (intm y i j))
  | Union x => mksetm None (union_m (intm x i j))
  | Power x => mksetm None (power_m (intm x i j))
  | Subset x P => let X := intTi x i in
                  let hm := intm x i j in
                  let i' := icons X i in
                  let j' a k : El(setm(i' k)) :=
                    match k with 0 => pair a (snd hm) | S k=>j k end in
                  mksetm None (subset_m (intm x i j) (fun a => int_fP P i' (j' a)))
  | Nat => mksetm None inf_m
end.

