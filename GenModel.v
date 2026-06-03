From Stdlib Require Import List.
Require Import basic.
Require Import VarMap.
Require Import Models TypModels.

(** A general model construction of a model of CC given an
    abstract model.
    It produces both the semantic judgements (as done by GenModel)
    and the fact that the this judgment is sound w.r.t the
    syntactic jugments *)

Module MakeModel(M : CC_Model) <: Judge.
Import M.

Lemma eqX_fun_sym : forall x f1 f2, eqX_fun x f1 f2 -> eqX_fun x f2 f1.
Proof.
unfold eqX_fun in |- *; intros.
symmetry  in |- *.
apply H.
 rewrite <- H1; trivial.
 symmetry  in |- *; trivial.
Qed.

Lemma eqX_fun_trans : forall x f1 f2 f3,
   eqX_fun x f1 f2 -> eqX_fun x f2 f3 -> eqX_fun x f1 f3.
Proof.
unfold eqX_fun in |- *; intros.
transitivity (f2 y1); auto.
apply H; trivial.
reflexivity.
Qed.

(** Valuations *)
Module Xeq.
  Definition t := X.
  Definition eq := eqX.
  Definition eq_equiv : Equivalence eq := eqX_equiv.
  Existing Instance eq_equiv.
End Xeq.
Module V := VarMap.Make(Xeq).

Notation val := V.map.
Notation eq_val := V.eq_map.

Definition vnil : val := V.nil props.

Import V.
Existing Instance cons_morph.
Existing Instance cons_morph'.
Hint Unfold eq_val : core.


(** * Pseudo-Terms *)

Module T.

Definition term :=
  option {f:val -> X|Proper (eq_val ==> eqX) f}.

Definition eq_term (x y:term) :=
  match x, y with
  | Some f, Some g => (eq_val ==> eqX)%signature (proj1_sig f) (proj1_sig g)
  | None, None => True
  | _, _ => False
  end.

#[global] Instance eq_term_refl : Reflexive eq_term.
red; intros.
destruct x; simpl; trivial.
destruct s; trivial.
Qed.

#[global] Instance eq_term_sym : Symmetric eq_term.
red; intros.
destruct x; destruct y; simpl in *; auto.
symmetry; trivial.
Qed.

#[global] Instance eq_term_trans : Transitive eq_term.
red; intros.
destruct x; destruct y; try contradiction; destruct z; simpl in *; auto.
transitivity (proj1_sig s0); trivial.
Qed.

Definition dummy_int := props.
Lemma dummy_type : istype dummy_int.
exact istype_props.
Qed.
#[global]Opaque dummy_int.
Hint Resolve dummy_type : core.

(** Denotation as value *)
Definition int (t:term) (i:val) : X :=
  match t with
  | Some f => proj1_sig f (fun k => i k)
  | None => dummy_int
  end.

#[global] Instance int_morph : Proper (eq_term ==> eq_val ==> eqX) int.
unfold int; do 3 red; intros.
destruct x; destruct y; simpl in *; (contradiction||reflexivity||auto).
Qed.

Definition int1 (A:term) (i:val) (x:X) : X :=
  int A (V.cons x i).

#[global]Instance int1_morph : Proper (eq_term ==> eq_val ==> eqX ==> eqX) int1.
do 4 red; intros.
unfold int1.
apply int_morph; auto with *.
apply V.cons_morph; trivial.
Qed.


Definition Op1 (f:X->X) {fm:Proper(eqX==>eqX) f} (t:term) : term.
(* begin show *)
left; exists (fun i => f (int t i)).
(*end show*)
do 2 red; intros.
apply fm; apply int_morph; auto with *.
Defined.

Definition Op2 (f:X->X->X) {fm:Proper(eqX==>eqX==>eqX) f} (t1 t2:term) : term.
(* begin show *)
left; exists (fun i => f (int t1 i) (int t2 i)).
(*end show*)
do 2 red; intros.
apply fm; apply int_morph; auto with *.
Defined.

(** Denotation as type *)
Definition el (t:term) (i:val) (x:X) :=
  match t with
  | Some _ => x ∈ int t i
  | None => istype x
  end.

#[global] Instance el_morph : Proper (eq_term ==> eq_val ==> eqX ==> iff) el.
apply morph_impl_iff3; auto with *.
unfold el; do 5 red; intros.
destruct y; trivial; destruct x; (contradiction||simpl in * ).
rewrite <- H1.
rewrite <- (H (fun k => x0 k) (fun k => y0 k)); auto.
rewrite <-H1; trivial.
Qed.

Lemma in_int_not_kind T i x :
  T <> None ->
  (el T i x <-> x ∈ int T i).
destruct T as [(T,Tm)|]; [simpl;reflexivity|destruct 1;reflexivity].
Qed.

(*
Lemma in_int_el : forall i x T,
  istype x \/ x ∈ int T i -> el T i x.
destruct T as [(T,Tm)|]; simpl; trivial.
Qed.*)

(** Injecting sets into the model *)
Definition cst (x:X) : term.
(*begin show*)
left; exists (fun _ => x).
(*end show*)
do 2 red; reflexivity.
Defined.


(** General substitutions *)
Record sub_ := mkSub {
  sub_f :> val -> val;
  sub_m : Proper (eq_val ==> eq_val) sub_f
}.
Definition sub := sub_.
Existing Instance sub_m.

Definition eq_sub (s1 s2:sub) :=
  (eq_val==>eq_val)%signature s1 s2.
  
#[global] Instance eq_sub_equiv : Equivalence eq_sub.
split; red; intros.
 apply x.

 do 2 red; intros.
 symmetry; apply H.
 symmetry; trivial.

 do 2 red; intros.
 transitivity (y y0); auto. 
 transitivity (y x0); auto.
 apply y; symmetry; trivial.
Qed.

Definition Sub (t:term) (s:sub) : term.
(* begin show *)
destruct t as [(t,tm)|];
 [left; exists (fun i => t (s i))|right].
(* end show *)
do 2 red; intros; auto.
apply tm; apply sub_m; trivial.
Defined.

#[global] Instance Sub_morph : Proper (eq_term ==> eq_sub ==> eq_term) Sub.
do 3 red; intros.
destruct x as [(x,xm)|]; destruct y as [(y,ym)|];simpl in *; try contradiction; trivial.
red; intros.
apply H.
apply H0; trivial.
Qed.

Definition sub_id : sub.
exists (fun x => x).
do 2 red; auto.
Defined.

Lemma eq_sub_id t : eq_term (Sub t sub_id) t.
destruct t as [(t,tm)|]; simpl; trivial.
Qed.

Definition sub_comp (s1 s2:sub) : sub.
exists (fun i => s1 (s2 i)).
do 2 red; intros.
apply sub_m.
apply sub_m.
trivial.
Defined.

Definition sub_lift (m:nat) (s:sub) : sub.
exists (V.lams m s).
do 2 red; intros.
apply V.lams_morph; trivial.
apply sub_m.
Defined.

Instance sub_lift_morph : Proper (eq ==> eq_sub ==> eq_sub) sub_lift.
do 4 red; simpl; intros.
red; intros.
apply V.lams_morph; auto with *.
Qed.

Definition sub_shift (n:nat) : sub.
exists (V.shift n); auto with *.
Defined.

Definition sub_cons (t:term) (s:sub) : sub.
exists (fun i => V.cons (int t i) (s i)).
do 2 red; intros.
apply V.cons_morph.
 apply int_morph; auto with *.
 apply sub_m; trivial.
Defined.

Lemma eq_sub_comp t s1 s2 :
  Sub (Sub t s1) s2 = Sub t (sub_comp s1 s2).
destruct t as [(t,tm)|]; simpl; reflexivity.
Qed.

Lemma sub_lift_split m n s :
  eq_sub (sub_lift (m+n) s) (sub_lift m (sub_lift n s)).
red; simpl.
red; intros.
rewrite <- V.lams_split.
 apply V.lams_morph; trivial.
 apply sub_m.
apply sub_m.
Qed.

Lemma sub_lift0 s : eq_sub (sub_lift 0 s) s.
red; red; intros.
simpl.
rewrite V.lams0.
apply sub_m; trivial.
Qed.

Lemma int_Sub_eq T s i :
  int (Sub T s) i = int T (s i).
intros; destruct T as [(T,Tm)|]; simpl; reflexivity.
Qed.

Lemma sub_nk t s :
  t <> None <->
  Sub t s <> None.
destruct t as [(t,tm)|]; simpl; auto with *.
split; intros; discriminate.
Qed.

(** Relocations *)
Section Lift.

Definition lift_rec (n m:nat) (t:term) : term.
(*begin show*)
destruct t as [(t,tm)|]; [left|exact None].
exists (fun i => t (V.lams m (V.shift n) i)).
(*end show*)
 do 2 red; intros.
 rewrite H; reflexivity.
Defined.

Global Instance lift_rec_morph n k : Proper (eq_term ==> eq_term) (lift_rec n k).
do 3 red; intros.
destruct x as [(x,xm)|]; destruct y as [(y,ym)|]; simpl in H|-*; try contradiction; trivial.
red; intros.
apply H.
rewrite H0; reflexivity.
Qed.

Lemma lift_rec_equiv n k t :
  eq_term (lift_rec n k t) (Sub t (sub_lift k (sub_shift n))).
destruct t as [(t,tm)|]; simpl; trivial.
red; intros.
rewrite H.
reflexivity.
Qed.

Lemma lift_rec_nk n t k :
  t <> None <->
  lift_rec n k t <> None.
destruct t as [(t,tm)|]; simpl; auto with *.
split; intros; discriminate.
Qed.

Definition lift1 n := lift_rec n 1.

Lemma lift10: forall T, eq_term (lift1 0 T) T.
unfold lift1.
destruct T as [(T,Tm)|]; simpl; trivial.
red; intros.
apply Tm; do 2 red; intros.
unfold V.lams, V.shift; destruct a; simpl.
 apply H.

 replace (a-0) with a; auto with arith.
Qed.

Lemma el_lift_rec_eq : forall n k T i x,
  el (lift_rec n k T) i x <-> el T (V.lams k (V.shift n) i) x.
intros; destruct T as [(T,Tm)|]; simpl; reflexivity.
Qed.

Lemma int_lift_rec_eq : forall n k T i,
  int (lift_rec n k T) i == int T (V.lams k (V.shift n) i).
intros; destruct T as [(T,Tm)|]; simpl; reflexivity.
Qed.

Definition lift n := lift_rec n 0.

Lemma int_lift_Sk_eq k T i :
  int (lift (S k) T) i == int (lift k T) (V.shift 1 i).
destruct T as [(T,Tm)|]; simpl in *; reflexivity.
Qed.

Lemma el_lift_Sk_eq k T i a :
  el (lift (S k) T) i a <-> el (lift k T) (V.shift 1 i) a.
destruct T as [(T,Tm)|]; simpl in *; reflexivity.
Qed.

Global Instance lift_morph : forall k, Proper (eq_term ==> eq_term) (lift k).
do 3 red; simpl; intros.
destruct x as [(x,xm)|]; destruct y as [(y,ym)|];
  simpl in *; (contradiction||trivial).
red; intros.
apply H.
rewrite H0; reflexivity.
Qed.

Lemma lift0_term T : eq_term (lift 0 T) T.
destruct T as [(T,Tm)|]; simpl; trivial.
red; intros.
apply Tm.
rewrite V.lams0.
rewrite V.shift0.
do 2 red; apply H.
Qed.

Lemma eq_term_liftS n t : eq_term (lift (S n) t) (lift 1 (lift n t)).
destruct t as [(t,tm)|]; simpl; trivial.
red; intros.
apply tm.
rewrite V.lams0.
rewrite V.lams0.
rewrite V.lams0.
rewrite V.shiftS_split.
apply V.shift_morph; trivial.
apply V.shift_morph; trivial.
Qed.

Lemma simpl_int_lift : forall i n x T,
  int (lift (S n) T) (V.cons x i) == int (lift n T) i.
intros.
destruct T as [(T,Tm)|]; simpl; auto with *.
apply Tm.
red; red; intros; reflexivity.
Qed.
Lemma simpl_el_lift : forall i n x T a,
  el (lift (S n) T) (V.cons x i) a <-> el (lift n T) i a.
intros.
destruct T as [(T,Tm)|]; simpl; auto with *.
Qed.

Lemma simpl_int_lift1 : forall i x T,
  int (lift 1 T) (V.cons x i) == int T i.
intros.
rewrite simpl_int_lift; rewrite lift0_term; reflexivity.
Qed.

Lemma simpl_lift1 : forall i n x y T,
  int (lift1 (S n) T) (V.cons x (V.cons y i)) == int (lift1 n T) (V.cons x i).
unfold lift1; simpl; intros.
do 2 rewrite int_lift_rec_eq.
repeat rewrite <- V.cons_lams.
 reflexivity.

 do 2 red; intros; rewrite H; reflexivity.

 do 2 red; intros; rewrite H; reflexivity.
Qed.

Lemma eqterm_lift_cst : forall n k c,
  eq_term (lift_rec n k (cst c)) (cst c).
red; simpl; intros.
red; reflexivity.
Qed.

End Lift.

(** Substitution *)
Section Substitution.

Definition subst_rec (arg:term) (m:nat) (t:term) : term.
(*begin show*)
destruct t as [(body,bm)|]; [left|right].
exists (fun i => body (V.lams m (V.cons (int arg (V.shift m i))) i)).
(*end show*)
 do 2 red; intros.
 rewrite H; reflexivity.
Defined.

Global Instance subst_rec_morph : Proper (eq_term ==> eq ==> eq_term ==> eq_term) subst_rec.
do 4 red; intros.
destruct x1 as [(x1,x1m)|]; destruct y1 as [(y1,y1m)|]; simpl in H1|-*; try contradiction; trivial.
red; intros.
apply H1.
rewrite H; rewrite H0; rewrite H2; reflexivity.
Qed.

Lemma subst_rec_equiv a k t :
  eq_term (subst_rec a k t) (Sub t (sub_lift k (sub_cons a sub_id))).
destruct t as [(t,tm)|]; simpl; trivial.
red; intros.
apply tm.
unfold V.lams; do 2 red; intros.
destruct (le_gt_dec k a0); auto with *.
rewrite H; reflexivity.
Qed.

Lemma subst_rec_nk a t k :
  t <> None <->
  subst_rec a k t <> None.
destruct t as [(t,tm)|]; simpl; auto with *.
split; intros; discriminate.
Qed.

Lemma int_subst_rec_eq : forall arg k T i,
  int (subst_rec arg k T) i == int T (V.lams k (V.cons (int arg (V.shift k i))) i).
intros; destruct T as [(T,Tm)|]; simpl; reflexivity.
Qed.

Definition subst arg := subst_rec arg 0.

Global Instance subst_morph : Proper (eq_term ==> eq_term ==> eq_term) subst.
do 3 red; simpl; intros.
destruct x0 as [(x0,xm0)|]; destruct y0 as [(y0,ym0)|];
  simpl in *; (contradiction||trivial).
red; intros.
apply H0.
rewrite H; rewrite H1; reflexivity.
Qed.

Lemma int_subst_eq : forall N M i,
  int (subst N M) i == int M (V.cons (int N i) i).
destruct M as [(M,Mm)|]; simpl; intros.
2:reflexivity.
rewrite V.lams0.
rewrite V.shift0.
reflexivity.
Qed.

Lemma el_subst_eq : forall N M i x,
  el (subst N M) i x <-> el M (V.cons (int N i) i) x.
destruct M as [(M,Mm)|]; simpl; intros.
2:reflexivity.
rewrite V.lams0.
rewrite V.shift0.
reflexivity.
Qed.

End Substitution.



(** Syntax of the Calculus of Constructions *)
Definition prop := cst props.

Definition kind : term := None.

Definition Ref (n:nat) : term.
(*begin show*)
left; exists (fun i => i n).
(*end show*)
do 2 red; simpl; auto.
Defined.

Definition App (u v:term) : term.
(*begin show*)
left; exists (fun i => app (int u i) (int v i)).
(*end show*)
do 2 red; simpl; intros.
rewrite H; reflexivity.
Defined.

Global Instance App_morph : Proper (eq_term ==> eq_term ==> eq_term) App.
unfold App; do 3 red; simpl; intros.
red; intros.
rewrite H; rewrite H0; rewrite H1; reflexivity.
Qed.

Lemma eq_Sub_app a b s :
  eq_term (Sub (App a b) s) (App (Sub a s) (Sub b s)).
red; simpl.
red; intros.
apply app_ext.
 rewrite H.
 rewrite int_Sub_eq; reflexivity.

 rewrite H.
 rewrite int_Sub_eq; reflexivity.
Qed.

Lemma eqterm_subst_App : forall N u v,
  eq_term (subst N (App u v)) (App (subst N u) (subst N v)).
red; simpl; intros.
red; intros.
unfold subst.
do 2 rewrite int_subst_rec_eq.
rewrite H.
reflexivity.
Qed.

Definition Abs (A M:term) : term.
(*begin show*)
left; exists (fun i => lam (int A i) (int1 M i)).
(*end show*)
do 2 red; simpl; intros.
apply lam_ext.
 rewrite H; reflexivity.
(**)
 red; intros.
 rewrite H; rewrite H1; reflexivity.
Defined.

Global Instance Abs_morph : Proper (eq_term ==> eq_term ==> eq_term) Abs.
unfold Abs; do 5 red; simpl; intros.
apply lam_ext.
 apply int_morph; auto.

 red; intros.
 rewrite H0; rewrite H1; rewrite H3; reflexivity.
Qed.

Lemma eq_sub_Abs a b s :
  eq_term (Sub (Abs a b) s) (Abs (Sub a s) (Sub b (sub_lift 1 s))).
red; simpl.
red; intros.
apply lam_ext.
 rewrite H.
 rewrite int_Sub_eq; reflexivity.

 red; intros.
 unfold int1; rewrite int_Sub_eq; simpl.
 rewrite <- V.cons_lams.
 2:apply sub_m.
 rewrite V.lams0.
 apply int_morph; auto with *.
 apply V.cons_morph; auto.
 apply sub_m; trivial.
Qed.

Lemma eq_lift_abs : forall n A B k,
  eq_term (lift_rec n k (Abs A B))
    (Abs (lift_rec n k A) (lift_rec n (S k) B)).
do 5 red; simpl; intros.
apply lam_ext; intros.
 rewrite int_lift_rec_eq.
 rewrite H; reflexivity.

 red; intros.
 unfold int1; rewrite int_lift_rec_eq.
 rewrite <- V.cons_lams; auto with *.
  rewrite H1; rewrite H; reflexivity.
Qed.

Definition Prod (A B:term) : term.
(*begin show*)
left; exists (fun i => prod (int A i) (int1 B i)).
(*end show*)
do 2 red; simpl; intros.
apply prod_ext.
 rewrite H; reflexivity.
(**)
 red; intros.
 rewrite H; rewrite H1; reflexivity.
Defined.

Global Instance Prod_morph : Proper (eq_term ==> eq_term ==> eq_term) Prod.
unfold Prod; do 5 red; simpl; intros.
apply prod_ext.
 apply int_morph; auto.

 red; intros.
 rewrite H0; rewrite H1; rewrite H3; reflexivity.
Qed.

Lemma eq_Sub_prod s A B :
  eq_term (Sub (Prod A B) s) (Prod (Sub A s) (Sub B (sub_lift 1 s))).
simpl.
red; intros.
apply prod_ext.
 rewrite int_Sub_eq.
 rewrite H; reflexivity.

 red; intros.
 unfold int1; rewrite int_Sub_eq.
 simpl; rewrite <- V.cons_lams.
  apply int_morph; auto with *.
  apply V.cons_morph; trivial.
  rewrite V.lams0; apply sub_m; trivial.

  apply sub_m.
Qed.

Lemma eq_lift_prod : forall n A B k,
  eq_term (lift_rec n k (Prod A B))
    (Prod (lift_rec n k A) (lift_rec n (S k) B)).
do 5 red; simpl; intros.
apply prod_ext; intros.
 rewrite int_lift_rec_eq.
 rewrite H; reflexivity.

 red; intros.
 unfold int1; rewrite int_lift_rec_eq.
 rewrite <- V.cons_lams; auto with *.
  rewrite H1; rewrite H; reflexivity.
Qed.

Lemma eq_subst_prod : forall u A B k,
  eq_term (subst_rec u k (Prod A B))
    (Prod (subst_rec u k A) (subst_rec u (S k) B)).
do 5 red; simpl; intros.
apply prod_ext; intros.
 rewrite int_subst_rec_eq.
 rewrite H; reflexivity.

 red; intros.
 unfold int1; rewrite int_subst_rec_eq.
 rewrite <- V.cons_lams; auto with *.
  rewrite H1; rewrite H; reflexivity.
Qed.

Lemma int_Prod_arr T U i :
  int (Prod T (lift 1 U)) i == prod (int T i) (fun _ => int U i).
simpl.
apply prod_ext.
*reflexivity.
*red; intros.
 unfold int1; rewrite simpl_int_lift.
 rewrite lift0_term; reflexivity.
Qed.

End T.
Import T.

(** * Environments *)
Definition env := list term.
Definition mt_env : env := List.nil.

Definition val_ok (e:env) (i:val) :=
  forall n T, nth_error e n = value T -> el (lift (S n) T) i (i n).

Lemma val_ok_nil i : val_ok mt_env i.
Proof.
intros [|n]; simpl; intros; discriminate.
Qed.
Hint Resolve val_ok_nil : core.

Lemma val_ok_shift1 e ty i :
  val_ok (ty::e) i ->
  val_ok e (V.shift 1 i).
intros iok n T itm.
generalize (iok (S n) T itm).
destruct T as [(T,Tm)|]; simpl; auto.
Qed.

Instance val_ok_morph : Proper (list_eq eq_term ==> eq_val ==> iff) val_ok.
apply morph_impl_iff2; auto with *.
do 4 red.
induction 1; simpl; intros.
 red; intros.
 destruct n; discriminate.

 red; intros.
 destruct n; simpl in *.
  generalize (H2 0 _ eq_refl).
  injection H3; intros; subst T.
  revert H5; apply el_morph; symmetry; auto.
  apply lift_morph; trivial.

  red in IHForall2.
  apply (V.shift_morph 1 _ eq_refl) in H1.
  apply val_ok_shift1 in H2.
  specialize IHForall2 with (1:=H1)(2:=H2)(3:=H3).
  destruct T as [(T,Tm)|]; simpl in *; auto.
Qed.

Lemma vcons_add_var0 : forall e T i x,
  val_ok e i -> el T i x -> val_ok (T::e) (V.cons x i).
unfold val_ok; simpl; intros.
destruct n; simpl in *.
 injection H1; clear H1; intro; subst; simpl in *.

 destruct T0 as [(T0,Tm)|]; simpl in *; trivial.
 rewrite V.lams0; assumption.

 apply H in H1; simpl in H1; trivial.
 destruct T0 as [(T0,Tm)|]; simpl in *; trivial.
Qed.

Lemma vcons_add_var e T i x : T<>kind ->
  val_ok e i -> x ∈ int T i -> val_ok (T::e) (V.cons x i).
intros.
apply vcons_add_var0; trivial.
apply in_int_not_kind; trivial.
(*destruct T as[(T,Tm)|]; simpl in *; trivial.*)
Qed.


Lemma add_var_eq_fun : forall T U U' i,
  T <> kind ->
  (forall x, el T i x -> int U (V.cons x i) == int U' (V.cons x i)) -> 
  eqX_fun (int T i)
    (fun x => int U (V.cons x i))
    (fun x => int U' (V.cons x i)).
red; intros.
rewrite <- H2.
apply in_int_not_kind in H1; auto.
Qed.


(** * Judgements *)

Module J.

(** Typing *)
Definition typ (e:env) (M T:term) :=
  forall i, val_ok e i -> el T i (int M i).
(** Equality *)
Definition eq_typ (e:env) (M M':term) :=
  forall i, val_ok e i -> int M i == int M' i.
(** Subtyping *)
Definition sub_typ (e:env) (M M':term) :=
  forall i x, val_ok e i -> x ∈ int M i -> x ∈ int M' i.
(** Alternative equality (with kind=kind) *)
Definition eq_typ' e M M' :=
  eq_typ e M M' /\ match M,M' with None,None => True|Some _,Some _=>True|_,_=>False end.
(** Subtyping as inclusion of values *)
Definition sub_typ' (e:env) (M M':term) :=
  forall i x, val_ok e i -> el M i x -> el M' i x.


Definition typ_sub (e:env) (s:sub) (f:env) :=
  forall i, val_ok e i -> val_ok f (s i).

Global Instance typ_morph : forall e, Proper (eq_term ==> eq_term ==> iff) (typ e).
intros.
apply morph_impl_iff2; auto with *.
unfold typ; do 4 red; intros.
rewrite <- H; rewrite <- H0; auto.
Qed.

Global Instance eq_typ_morph : forall e, Proper (eq_term ==> eq_term ==> iff) (eq_typ e).
intros.
apply morph_impl_iff2; auto with *.
unfold eq_typ; do 4 red; intros.
rewrite <- H; rewrite <- H0; auto.
Qed.

(*
Instance eq_typ'_morph : forall e, Proper (eq_term ==> eq_term ==> iff) (eq_typ' e).
unfold eq_typ'; split; simpl; intros.
 destruct x; destruct y; try contradiction.

 rewrite <- H; rewrite <- H0; auto.
 rewrite H; rewrite H0; auto.
Qed.
*)
Global Instance sub_typ_morph : forall e, Proper (eq_term ==> eq_term ==> iff) (sub_typ e).
intros.
apply morph_impl_iff2; auto with *.
unfold sub_typ; do 4 red; intros.
rewrite <- H in H3; rewrite <- H0; auto.
Qed.

Global Instance sub_typ'_morph : forall e, Proper (eq_term ==> eq_term ==> iff) (sub_typ' e).
intros.
apply morph_impl_iff2; auto with *.
unfold sub_typ'; do 4 red; intros.
rewrite <- H in H3; rewrite <- H0; auto.
Qed.

Instance typ_sub_morph :
  Proper (list_eq eq_term ==> eq_sub ==> list_eq eq_term ==> iff) typ_sub.
do 4 red; intros.
unfold typ_sub.
apply fa_morph; intros i.
apply impl_morph.
 apply val_ok_morph; trivial.
 reflexivity.
intros.
apply val_ok_morph; trivial.
apply H0; reflexivity.
Qed.

End J.
Import J.

Lemma typ_elim e M T i :
  typ e M T ->
  T <> kind ->
  val_ok e i ->
  int M i ∈ int T i.
intros.
apply H in H1.
apply in_int_not_kind in H1; trivial.
Qed.

(** * Inference rules *)

Module R.

(** Equality rules *)

Lemma refl : forall e M, eq_typ e M M.
red; simpl; reflexivity.
Qed.

Lemma sym : forall e M M', eq_typ e M M' -> eq_typ e M' M.
unfold eq_typ; symmetry; auto.
Qed.

Lemma trans : forall e M M' M'', eq_typ e M M' -> eq_typ e M' M'' -> eq_typ e M M''.
unfold eq_typ; intros.
transitivity (int M' i); auto.
Qed.

Global Instance eq_typ_equiv : forall e, Equivalence (eq_typ e).
split.
 exact (refl e).
 exact (sym e).
 exact (trans e).
Qed.


Lemma eq_typ_app : forall e M M' N N',
  eq_typ e M M' ->
  eq_typ e N N' ->
  eq_typ e (App M N) (App M' N').
unfold eq_typ; simpl; intros.
apply app_ext; auto.
Qed.

Lemma eq_typ_abs : forall e T T' M M',
  T <> kind ->
  eq_typ e T T' ->
  eq_typ (T::e) M M' ->
  eq_typ e (Abs T M) (Abs T' M').
Proof.
unfold eq_typ; simpl; intros.
apply lam_ext; auto.
apply add_var_eq_fun; trivial.
intros.
apply H1.
apply vcons_add_var0; trivial.
Qed.

Lemma eq_typ_prod : forall e T T' U U',
  T <> kind ->
  eq_typ e T T' ->
  eq_typ (T::e) U U' ->
  eq_typ e (Prod T U) (Prod T' U').
unfold eq_typ; simpl; intros.
apply prod_ext; auto.
apply add_var_eq_fun; trivial.
intros.
apply H1.
apply vcons_add_var0; trivial.
Qed.

Lemma eq_typ_beta : forall e T M M' N N',
  eq_typ (T::e) M M' ->
  eq_typ e N N' ->
  typ e N T -> (* Typed reduction! *)
  T <> kind ->
  eq_typ e (App (Abs T M) N) (subst N' M').
Proof.
unfold eq_typ, typ, App, Abs; simpl; intros.
rewrite int_subst_eq.
assert (eqX_fun (int T i) (fun x => int M (V.cons x i)) (fun x => int M (V.cons x i))).
 apply add_var_eq_fun with (T:=T); intros; trivial; reflexivity.
assert (int N i ∈ int T i).
 destruct T as [(T,Tm)|]; [clear H2;simpl in *;auto|elim H2;reflexivity]. 
rewrite beta_eq; auto.
rewrite <- H0; auto.
apply H.
apply vcons_add_var0; simpl; auto.
Qed.

(** Typing rules *)

Lemma typ_prop : forall e, typ e prop kind.
red; simpl; trivial.
Qed.

Lemma typ_prop_kind e T :
  typ e T prop ->
  typ e T kind.
red; intros.
apply H in H0.
simpl in *.
apply istype_prop; trivial.
Qed.

Lemma typ_var : forall e n T,
  nth_error e n = value T -> typ e (Ref n) (lift (S n) T).
unfold lift; red; simpl; intros.
apply H0 in H.
destruct T; simpl in *; trivial.
Qed.

Lemma typ_app e u v T U :
  typ e v T ->
  typ e u (Prod T U) ->
  T <> kind ->
  U <> kind ->
  typ e (App u v) (subst v U).
unfold typ, App, Prod; simpl;
intros ty_v ty_u T_nk U_nk i is_val.
specialize (ty_v _ is_val).
specialize (ty_u _ is_val).
apply in_int_not_kind in ty_v; trivial.
rewrite el_subst_eq.
apply in_int_not_kind; trivial.
apply prod_elim with (dom := int T i) (F:=fun x => int U (V.cons x i)); trivial.
red; intros.
rewrite H0; reflexivity.
Qed.

Lemma typ_abs : forall e T M U,
  typ (T :: e) M U ->
  T <> kind ->
  U <> kind ->
  typ e (Abs T M) (Prod T U).
Proof.
unfold typ, Abs, Prod; simpl; intros e T M U ty_M T_nk U_nk i is_val.
apply prod_intro.
*apply add_var_eq_fun; trivial; intros; reflexivity.
*apply add_var_eq_fun; trivial; intros; reflexivity.
*intros.
 apply in_int_not_kind; trivial.
 apply ty_M.
 apply vcons_add_var; trivial.
Qed.

Lemma typ_beta : forall e T M N U,
  typ e N T ->
  typ (T::e) M U ->
  T <> kind ->
  U <> kind ->
  typ e (App (Abs T M) N) (subst N U).
Proof.
intros.
apply typ_app with T; trivial.
apply typ_abs; trivial.
Qed.

Lemma typ_prod e T U s2 :
  T <> kind ->
  s2 = kind \/ s2 = prop ->
  typ e T kind ->
  typ (T :: e) U s2 ->
  typ e (Prod T U) s2.
Proof.
unfold typ, Prod; simpl; red; intros T_nk is_srt2 ty_T ty_U i is_val.
destruct s2 as [(s2,sm)|]; trivial; simpl in *.
*destruct is_srt2 as [is_srt2|is_srt2];
   [discriminate|injection is_srt2;clear is_srt2; intro; subst s2].
 apply impredicative_prod.
 +red; intros.
  rewrite H0; reflexivity.
 +intros.
  apply ty_U.
  apply vcons_add_var; trivial.
*apply istype_prod.
 +intros ??? h; rewrite h; reflexivity.
 +apply ty_T; trivial.
 +intros; apply ty_U.
  apply vcons_add_var; trivial.
Qed.

Lemma typ_conv : forall e M T T',
  typ e M T ->
  eq_typ e T T' ->
  T <> kind ->
  T' <> kind ->
  typ e M T'.
Proof.
unfold typ, eq_typ; simpl; intros.
apply in_int_not_kind; trivial.
rewrite <-H0; trivial.
apply in_int_not_kind; auto.
Qed.

(** Extendability *)

Lemma typ_cst_ty e x :
  istype x ->
  typ e (cst x) kind.
red; simpl; intros; trivial.
Qed.

Lemma typ_cst e x y :
  x ∈ y ->
  typ e (cst x) (cst y).
red; simpl; intros; trivial.
Qed.

Lemma eq_typ_cst e x y :
  x == y ->
  eq_typ e (cst x) (cst y).
red; simpl; intros; trivial.
Qed.

(** Weakening *)

Lemma weakening : forall e M T A,
  typ e M T ->
  typ (A::e) (lift 1 M) (lift 1 T).
unfold typ; intros.
rewrite el_lift_Sk_eq, int_lift_Sk_eq, !lift0_term.
apply H.
apply val_ok_shift1 in H0; trivial.
Qed.

Lemma weakening0 : forall e M T,
  typ e M T ->
  typ e (lift 0 M) (lift 0 T).
intros.
rewrite !lift0_term; trivial.
Qed.

(* TODO: use split lift! *)
Lemma weakeningS : forall e k M T A,
  typ e (lift k M) (lift k T) ->
  typ (A::e) (lift (S k) M) (lift (S k) T).
red; intros.
apply val_ok_shift1 in H0.
rewrite el_lift_Sk_eq, int_lift_Sk_eq; auto.
Qed.

(** Subtyping *)
Lemma sub_refl : forall e M M',
  eq_typ e M M' -> sub_typ e M M'.
red; intros.
apply H in H0.
clear H.
rewrite <- H0; trivial.
Qed.

Lemma sub_trans : forall e M1 M2 M3,
  sub_typ e M1 M2 -> sub_typ e M2 M3 -> sub_typ e M1 M3.
unfold sub_typ; auto.
Qed.

(* subsumption: generalizes typ_conv *)
Lemma typ_subsumption : forall e M T T',
  typ e M T ->
  sub_typ e T T' ->
  T <> kind ->
  T' <> kind ->
  typ e M T'.
Proof.
unfold typ, sub_typ; simpl; intros; auto.
rewrite in_int_not_kind; trivial.
apply H0; trivial.
apply in_int_not_kind; auto.
Qed.

Lemma sub_refl' : forall e M M',
  eq_typ' e M M' -> sub_typ' e M M'.
red; intros.
destruct H.
apply H in H0.
destruct M; destruct M'; try contradiction; trivial.
unfold el in *.
rewrite <- H0; trivial.
Qed.

Lemma sub_trans' : forall e M1 M2 M3,
  sub_typ' e M1 M2 -> sub_typ' e M2 M3 -> sub_typ' e M1 M3.
unfold sub_typ'; auto.
Qed.

Lemma typ_subsumption' : forall e M T T',
  typ e M T ->
  sub_typ' e T T' ->
  typ e M T'.
Proof.
unfold typ, sub_typ'; simpl; intros; auto.
Qed.

(** Subtitution *)

Lemma typ_sub_comp e f g s1 s2 :
  typ_sub e s1 f ->
  typ_sub f s2 g ->
  typ_sub e (sub_comp s2 s1) g.
unfold typ_sub; simpl; intros.
auto.
Qed.

Lemma typ_Sub e f s m u :
  typ f m u ->
  typ_sub e s f ->
  typ e (Sub m s) (Sub u s).
unfold typ, typ_sub; intros.
destruct u as [(u,um)|]; simpl in *; trivial.
*destruct m as [(m,mm)|]; simpl in *; auto.
*destruct m as [(m,mm)|]; simpl in *; auto.
Qed.

Lemma typ_sub_shift1 e ty :
  typ_sub (ty::e) (sub_shift 1) e.
red; intros.
eapply val_ok_shift1.
exact H.
Qed.

Lemma typ_sub_lams1 e s f t :
  typ_sub e s f ->
  typ_sub (Sub t s :: e) (sub_lift 1 s) (t::f).
unfold typ_sub; simpl; intros.
setoid_replace (lams 1 s i) with (V.cons (i 0) (s (V.shift 1 i))).
*apply vcons_add_var0.
 +apply H.
  apply val_ok_shift1 in H0; trivial.
 +red in H0.
  generalize (H0 0 _ eq_refl).
  destruct t as [(t,tm)|]; simpl; trivial.
  rewrite V.lams0; trivial.
*intros [|k]; [reflexivity|simpl].
 unfold lams; simpl.
 replace (k-0) with k; auto with *.
Qed.


(** Derived rules of the basic judgements *)

Lemma eq_typ_betar : forall e N T M,
  typ e N T ->
  T <> kind ->
  eq_typ e (App (Abs T M) N) (subst N M).
intros.
apply eq_typ_beta; trivial.
 reflexivity.
 reflexivity.
Qed.

Lemma typ_var0 : forall e n T,
  match T, nth_error e n with
    Some _, Some T' => T' <> kind /\ sub_typ e (lift (S n) T') T
  | _,_ => False end ->
  typ e (Ref n) T.
red; intros.
destruct T as [(T,Tm)|]; [simpl|contradiction].
generalize (H0 n).
destruct (nth_error e n) as [T'|]; [|contradiction].
intros.
destruct H.
apply H2; trivial.
apply in_int_not_kind; [apply lift_rec_nk; trivial|].
auto.
Qed.

End R.

(*Hint Resolve in_int_el : core.*)

(** Consistency *)

Lemma abstract_non_provability (TH:env) T :
  (exists2 i, val_ok TH i & (forall x, ~ el T i x)) ->
  forall M, ~ typ TH M T.
red in |- *; intros (i,iok,Tmt) M prf.
apply Tmt with (int M i).
red in prf.
apply prf; trivial.
Qed.

Lemma abstract_theory_consistency (TH:env) M FF :
  FF ∈ props ->
  (exists i, val_ok TH i) ->
  (forall x, ~ x ∈ FF) ->
  ~ typ TH M (Prod prop (Ref 0)).
intros FFty (i,THcons) FFmt.
apply abstract_non_provability.
exists i; [trivial|].
simpl.
intros abs tyabs.
apply FFmt with (x:=app abs FF).
apply prod_elim with (2:=tyabs) (3:=FFty).
red; auto.
Qed.

Lemma abstract_consistency M FF :
  FF ∈ props ->
  (forall x, ~ x ∈ FF) ->
  ~ typ mt_env M (Prod prop (Ref 0)).
intros; apply abstract_theory_consistency with (FF:=FF); trivial.
exists (V.nil props).
red; simpl; intros.
destruct n; discriminate H1.
Qed.

End MakeModel.

