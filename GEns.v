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

Definition sim_step {X Y:Ti} Rx Ry (R:X->Y->Prop) (i:X) (j:Y) :=
  (forall i', Rx i' i -> exists j', Ry j' j /\ R i' j') /\
  (forall j', Ry j' j -> exists i', Rx i' i /\ R i' j').

Definition sim {X Y:Ti} Rx Ry (R:X->Y->Prop) :=
  (forall i i' j, Rx i' i -> R i j -> exists j', Ry j' j /\ R i' j') /\
  (forall j j' i, Ry j' j -> R i j -> exists i', Rx i' i /\ R i' j').

Definition eq_set (x y:set) : Prop :=
  exists R:pts x -> pts y -> Prop,
    R (head x) (head y) /\ sim (mem x) (mem y) R.

Definition eq_set_isL x y : isL (eq_set x y) := fun h => h.

Lemma eq_set_refl : forall x, eq_set x x.
intros x.
exists (fun i j:pts x => i=j).
split;[|split];[trivial|intros |intros].
*subst j; exists i'; auto.
*subst i; exists j'; auto.
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
(*
Lemma Acc_in_set : forall x, Acc in_set x.
cut (forall x y, eq_set x y -> Acc in_set y).
 intros.
 apply H with x; apply eq_set_refl.
induction x; intros.
constructor; intros.
specialize eq_elim with (1:=H1)(2:=eq_set_sym _ _ H0); intro.
clear y H0 H1.
destruct H2; simpl in *.
apply H with x.
apply eq_set_sym; trivial.
Qed.


Lemma wf_rec :
  forall P : set -> Type,
  (forall x, (forall y, in_set y x -> P y) -> P x) -> forall x, P x.
intros.
elim (Acc_in_set x); intros.
apply X; apply X0.
Defined.


Lemma wf_ax :
  forall (P:set->Prop),
  (forall x, (forall y, in_set y x -> P y) -> P x) -> forall x, P x.
intros P H x.
cut (forall x', eq_set x x' -> P x');[auto using eq_set_refl|].
induction x; intros.
apply H; intros.
assert (in_set y (sup X f)).
 apply eq_elim with x'; trivial.
 apply eq_set_sym; trivial.
clear H1 H2.
destruct H3; simpl in *.
apply eq_set_sym in H1; eauto.
Qed.
*)
(* *)

Definition supX (X:Ti) (f:X->Ti) : Ti :=
  option {i:X & f i}.

Definition sup (X:Ti) (f:X->set) : set :=
  mkS (supX X (fun i => pts (f i)))
    None
    (fun i j =>
       match i, j with
         Some(existT _ i' x), None => x = head (f i')
       | Some(existT _ i' x), Some(existT _ j' y) =>
           exists e: i' = j',
             mem (f j') (eq_rect _ (fun i=>_) x _ e) y
       | None, _ => False
       end).

Lemma eq_set_elts X f (i:X) :
  eq_set (move (sup X f) (Some(existT _ i (head (f i))))) (f i).
red.
simpl.
exists (fun i' j' => i' = Some(existT _ i j')); split; [trivial|].
split; intros.
*subst i0.
 destruct i' as [(i',x)|]; [|contradiction].
 destruct H as (e,H).
 destruct e; simpl in H.
 exists x; auto.
*subst i0.
 eexists; split;[|reflexivity]; simpl.
 exists (eq_refl i); simpl; trivial.
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
Definition subsetm (x:set) (P:set->Prop) (i j:subsetX (pts x)) : Prop :=
  match i, j with
  | Some i, Some j => mem x i j
  | Some i, None => mem x i (head x) /\ P (move x i)
  | None, _ => False
  end.
Definition subset0 (x:set) (P:set->Prop) :=
  mkS (subsetX (pts x)) None (subsetm x P).

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
(*
Parameter WFR
     : forall {A}, relation A -> (set -> set) -> ((set -> A -> set) -> set -> A -> set) -> set -> A -> set
Parameter WFR_eqn
     : forall {A : Type} (Aeq : relation A),
       Equivalence Aeq ->
       forall R : set -> set,
       Proper (eq_set ==> eq_set) R ->
       forall (F : (set -> A -> set) -> set -> A -> set) (xx : set),
       (forall (x x' : set) (a a' : A) (f f' : set -> A -> set),
        clos_refl_trans set (fun x y => in_set x (R y)) x xx ->
        Acc (fun x y => in_set x (R y)) x ->
        (forall (y y' : set) (a a' : A),
         in_set y (R x) -> eq_set y y' -> Aeq a a' -> eq_set (f y a) (f' y' a')) ->
        eq_set x x' -> Aeq a a' -> eq_set (F f x a) (F f' x' a')) ->
       forall a : A, Acc (fun x y : set => in_set x (R y)) xx -> eq_set (WFR R F xx a) (F (WFR R F) xx a)
WFR_eqn
     : forall Rsub : set -> set,
       morph1 Rsub ->
       forall (F : (set -> A -> set) -> set -> A -> set) (x : set),
       (forall (x0 x' : set) (a a' : A) (f f' : set -> A -> set),
        WFRle Rsub x0 x ->
        (forall (y y' : set) (a0 a'0 : A), y ∈ Rsub x0 -> y == y' -> Aeq a0 a'0 -> f y a0 == f' y' a'0) ->
        x0 == x' -> Aeq a a' -> F f x0 a == F f' x' a') ->
       forall a : A, Acc (fun x0 y : set => x0 ∈ Rsub y) x -> WFR Rsub F x a == F (WFR Rsub F) x a


*)

(*
Parameter replrec : set -> ((set->set)->set->set) -> set.
Lemma replrec_ax : forall a R F z,
  Proper ((eq_set==>eq_set)==>eq_set==>eq_set) F ->
  (forall x, in_set x a -> Acc (fun x y => in_set x A /\ R x y) x) ->
  (in_set z (replrec x F) <->
   exists2 y, in_set y x & eq_set z (F y)).



Section weakerWFR.

  Section Unpacked.

    Hypothesis A : Ti.

    Hypothesis R : A -> A -> Prop.

    Hypothesis F : (A -> Ti) -> A -> Ti.

Definition WFRX (x:A) : Ti :=
 F WFRX

    Inductive WFRX (x:A) : Ti :=
    | Wi : forall y:A, R y x -> WFR y
(*
    Fixpoint WFRX_aux (x:A) (h:Acc R' x) : Ti :=
      F (fun y =>
         union (sup {i:idx (R x)|eq_set y (elts (R x) i)}
                  (fun i => WFR_aux (elts (R x) (proj1_sig i)) a
                              (Acc_inv h (in_set_intro (R x) (proj1_sig i))))))
      x a.
*)
  End Unpacked.

  Hypothesis A : set.
  Hypothesis R : set -> set -> Prop.
  Hypothesis Rm : Proper (eq_set==>eq_set==>iff) R.
  Hypothesis F : (set -> set) -> set -> set.
 
  Let AX := pts A.
  Let RX (i j:AX) := R (move A i) (move A j).
  Let FX (f:AX->Ti) (x:AX) : Ti :=
        pts (F (fun y:set => ) (move A x)

  Definition WFRX (R:Ti->Ti)
*)

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

