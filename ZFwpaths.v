Require Import ZF ZFpairs ZFsum ZFnats ZFrelations ZFtarski ZFstable.
Require Import ZFgrothendieck.
Require Import ZFlist.
Require Import ZFcoc.
Require Import ZFord ZFcofix.
Require Import ZFfix.
Require Import ZFfixfun.
Require Import ZFw.

Import ZFrepl.

(** In this file we develop the theory of W-types as a type of trees encoded
    as a relation from paths to labels.
 *)
  
Module Type Wsized.

Parameter Wf : set -> (set -> set) -> set -> set.
Parameter Wf_morph_gen :
  Proper (eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) Wf.
Existing Instance Wf_morph_gen.
Parameter Wf_mono : forall A B,
  morph1 B -> Proper (incl_set ==> incl_set) (Wf A B).
Parameter Wf_ext : forall A A' B B' X X',
  A == A' ->
  eq_fun A B B' ->
  X == X' ->
  Wf A B X == Wf A' B' X'.
Parameter Wsup : set -> set -> set.
Parameter Wsup_morph : morph2 Wsup.
Parameter Wf_intro : forall A B,
       morph1 B ->
       forall X x f, x ∈ A -> f ∈ (Π __ ∈ B x, X) -> Wsup x f ∈ Wf A B X.

Parameter wsubterms : set -> (set->set) -> set -> set.
Parameter wsubterms_morph :
  Proper (eq_set==>(eq_set==>eq_set)==>eq_set==>eq_set) wsubterms.
Existing Instance wsubterms_morph.
Parameter wsubterms_ext : forall A A' B B' X X',
  A == A' ->
  eq_fun A B B' ->
  X == X' ->
  wsubterms A B X == wsubterms A' B' X'.

Parameter W : set -> (set->set) -> set.
Parameter W_morph : Proper (eq_set==>(eq_set==>eq_set)==>eq_set) W.
Existing Instance W_morph.
Parameter W_ext : forall A A' B B',
  A == A' ->
  eq_fun A B B' ->
  W A B == W A' B'.
Parameter Wf_stable : forall A B, morph1 B ->
  stable_class (fun X => X ⊆ W A B) (Wf A B).
Parameter W_eqn : forall A B, morph1 B -> W A B == Wf A B (W A B).
Parameter wsubterms_incl_W : forall A B,
  morph1 B -> forall X, wsubterms A B X ⊆ W A B.
Parameter wsubterms_trans : forall A B,
  morph1 B ->
  forall X,
  wsubterms A B X ⊆ Wf A B (wsubterms A B X).
Parameter wsubterms_compl : forall A B,
   morph1 B -> forall X, X ∩ W A B ⊆ wsubterms A B X.
Parameter wsubterms_proj : forall A B,
       morph1 B ->
       forall X, X ⊆ W A B -> X ⊆ Wf A B X -> wsubterms A B X == X.
Parameter G_W
     : forall A B,
       morph1 B ->
       forall U,
       grot_univ U ->
       ZFord.omega ∈ U ->
       A ∈ U -> (forall a : set, a ∈ A -> B a ∈ U) -> W A B ∈ U.

(*Require Import ZFwpaths.*)
(*Parameter Wf_elim : forall A B,
       morph1 B ->
       forall a X,
       a ∈ Wf A B X ->
       exists2 x, x ∈ A &
       exists2 f, f ∈ (Π _ ∈ B x, X) & a == Wsup x f.
*)
(*Parameter Wfst : set -> set.
Parameter Wfst_morph : morph1 Wfst.
Parameter Wsnd_fun : set -> set.
Parameter Wsnd_fun_morph : morph1 Wsnd_fun.
Parameter Wfst_typ_gen : forall A B,
  morph1 B ->
  forall X w,
  w ∈ Wf A B X ->
  Wfst w ∈ A.
Parameter Wsnd_typ_gen : forall A B,
  morph1 B ->
  forall X w i,
  X ⊆ W(*dom*) A B ->
  w ∈ Wf A B X ->
  i ∈ B (Wfst w) ->
  Wsnd w i ∈ X.
Parameter Wfst_def : forall x f, Wfst (Wsup x f) == x.
Parameter Wsnd_fun_def : forall A B Y x f,
  f ∈ (Π _ ∈ Y, W A B) -> Wsnd_fun (Wsup x f) == f.
*)

Parameter Wcase : (set -> set -> set) -> set -> set.
Parameter Wcase_morph_gen : Proper ((eq_set==>eq_set==>eq_set)==>eq_set==>eq_set) Wcase.
Existing Instance Wcase_morph_gen.
Parameter Wcase_ext : forall A A' B B' X X' h h' c c',
  morph1 B ->
  morph1 B' ->
  X ⊆ W A B ->
  X' ⊆ W A' B' ->
  (forall x x' f f', x ∈ A -> x' ∈ A' -> x == x' ->
   f ∈ (Π __ ∈ B x, X) -> f' ∈ (Π __ ∈ B' x', X') ->
   f == f' -> h x f == h' x' f') ->
  c ∈ Wf A B X ->
  c' ∈ Wf A' B' X' ->
  c == c' ->
  Wcase h c == Wcase h' c'.

Parameter Wcase_typ : forall (A : set) (B : set -> set),
       morph1 B ->
       forall (X : set) (Q : set -> set) (h : set -> set -> set) (w : set),
       morph1 Q ->
       X ⊆ W A B ->
       (forall x f : set, x ∈ A -> f ∈ (Π __ ∈ B x, X) -> h x f ∈ Q (Wsup x f)) ->
       w ∈ Wf A B X -> Wcase h w ∈ Q w.

Parameter Wcase_eqn : forall A B,
       morph1 B -> forall h x f,
       morph2 h -> f ∈ (Π __ ∈ B x, W A B) -> Wcase h (Wsup x f) == h x f.

Class subtermClass A B (K:set->Prop) :=
  { Kinter : forall X,
      (exists z0, z0 ∈ X) ->
      (forall z, z ∈ X -> K z) ->
      K (inter X);
    Ksup : forall I X,
      ext_fun I X ->
      (forall i, i ∈ I -> K (X i)) ->
      K (sup I X);
    KW : forall X, K X -> X ⊆ W A B;
    KWtop : K (W A B);
    Kintro : forall X, K X -> K (Wf A B X);
    Ktrans : forall X, K X -> X ⊆ Wf A B X }.
(*Module Type SubtermClass.
  Parameter K : set -> (set->set) -> set -> Prop.
  Parameter Km : forall A B, Proper (eq_set==>iff) (K A B).

  Parameter Kinter : forall A B X,
    (exists z0, z0 ∈ X) ->
    (forall z, z ∈ X -> K A B z) ->
    K A B(inter X).
  Parameter Ksup : forall A B I X,
    ext_fun I X ->
    (forall i, i ∈ I -> K A B (X i)) ->
    K A B (sup I X).

  Parameter KW : forall A B X, K A B X -> X ⊆ (W A B).
  Parameter KWtop : forall A B, K A B (W A B).

  Parameter Kintro : forall A B X,
    K A B X -> K A B (Wf A B X).
  Parameter Ktrans : forall A B X,
    K A B X -> X ⊆ Wf A B X.
  Hint Resolve KW KWtop Kintro Ktrans.
End SubtermClass.*)

(*Module Type WRecursor (Sub:SubtermClass).
Import Sub.*)
Parameter WSREC' : set -> (set -> set) -> (set->Prop) -> (set -> set -> set -> set) -> set -> set.
Parameter WSREC'_morph_gen
     : Proper
         (eq_set ==> (eq_set ==> eq_set) ==> (eq_set==>iff) ==>
          (eq_set ==> eq_set ==> eq_set ==> eq_set) ==> eq_set ==> eq_set)
         WSREC'.
Existing Instance WSREC'_morph_gen.
(*Parameter WSREC'_ext : forall A A' B B' O O' U U' F F',
       A == A' ->
       eq_fun A B B' ->
       O ⊆ W A B ->
       O == O' ->
       (forall X,
        K A B X -> forall w w', w ∈ W A B -> w == w' -> U X w == U' X w') ->
       (forall X recf x,
        K A B X ->
        recf ∈ (Π w ∈ X, U X w) -> x ∈ Wf A B X -> F X recf x == F' X recf x) ->
       eq_fun (W A B) (WSREC' A B F) (WSREC' A' B' F').*)
Parameter WSREC_typ' : forall A B,
       morph1 B ->
       forall K, Proper (eq_set==>iff) K -> subtermClass A B K ->
       forall O,
       K O ->
       forall P,
       morph2 P ->
       (forall X Y x,
        K Y ->
        (forall w, w ∈ X ->
         exists2 w', w' ∈ Y & forall X, K X -> w' ∈ Wf A B X -> w ∈ X) ->
        P (Wf A B X) x ⊆ P Y x) ->
       forall F,
       Proper (eq_set ==> eq_set ==> eq_set ==> eq_set) F ->
       (forall X x recf,
        X ⊆ O ->
        K X ->
        x ∈ Wf A B X ->
        recf ∈ (Π w ∈ X, P X w) -> F X recf x ∈ P (Wf A B X) x) ->
(*       (forall X X' recf recf',
        X ⊆ O ->
        K X ->
        X' ⊆ O ->
        K X' ->
        recf ∈ (Π w ∈ X, P X w) ->
        recf' ∈ (Π w ∈ X', P X' w) ->
        (forall x, x ∈ X -> x ∈ X' -> cc_app recf x == cc_app recf' x) ->
        forall x,
        x ∈ Wf A B X -> x ∈ Wf A B X' -> F X recf x == F X' recf' x) ->*)
       forall w, w ∈ O -> WSREC' A B K F w ∈ P O w.
Parameter WSREC_eqn' : forall A B,
       morph1 B ->
       forall K, Proper (eq_set==>iff) K -> subtermClass A B K ->
       forall O,
       K O ->
       forall P,
       morph2 P ->
       (forall X Y x,
        K Y ->
        (forall w, w ∈ X ->
         exists2 w', w' ∈ Y & forall X, K X -> w' ∈ Wf A B X -> w ∈ X) ->
        P (Wf A B X) x ⊆ P Y x) ->
       forall F,
       Proper (eq_set ==> eq_set ==> eq_set ==> eq_set) F ->
       (forall X x recf,
        X ⊆ O ->
        K X ->
        x ∈ Wf A B X ->
        recf ∈ (Π w ∈ X, P X w) -> F X recf x ∈ P (Wf A B X) x) ->
       (forall X X' recf recf',
        X ⊆ O ->
        K X ->
        X' ⊆ O ->
        K X' ->
        recf ∈ (Π w ∈ X, P X w) ->
        recf' ∈ (Π w ∈ X', P X' w) ->
        (forall x, x ∈ X -> x ∈ X' -> cc_app recf x == cc_app recf' x) ->
        forall x,
        x ∈ Wf A B X -> x ∈ Wf A B X' -> F X recf x == F X' recf' x) ->
       (* concl: *)
       forall w,
       w ∈ O ->
       WSREC' A B K F w == F O (λ w0 ∈ O, WSREC' A B K F w0) w.
(*End WRecursor.
Declare Module MakeRec (Sub:SubtermClass) : WRecursor.*)

End Wsized.

Module Wpaths <: Wsized.

  
  Include ZFw.


  Section WCase.
    
Variable A : set.
Variable B : set -> set.
Hypothesis Bm : morph1 B.

Notation Wdom := (ZFwdom.Wdom A B).

Definition Wf := ZFwdom.Wf A B.
Definition Wf_morph_gen := ZFwdom.Wf_morph_gen.
Definition Wf_mono := ZFwdom.Wf_mono.
(*Existing Instance Wf_morph_gen.*)
Definition Wf_ext := ZFwdom.Wf_ext.
Definition Wsup := ZFwdom.Wsup.
Definition Wsup_morph := ZFwdom.Wsup_morph.
Definition Wf_intro := ZFwdom.Wf_intro.


Notation Wfst := ZFwdom.Wfst.
Notation Wsnd_fun := ZFwdom.Wsnd_fun.
Existing Instance ZFwdom.Wf_mono.
  
Definition Wcase (h:set->set->set) w := h (ZFwdom.Wfst w) (ZFwdom.Wsnd_fun w).

Lemma Wcase_eqn_dom h x f :
  morph2 h ->
  f ∈ (Π i ∈ B x, Wdom) ->
  Wcase h (Wsup x f) == h x f.
intros hm tyf.
unfold Wcase.
apply hm.
 apply ZFwdom.Wfst_def.

 apply ZFwdom.Wsnd_fun_def_dom with (1:=tyf).
Qed.

Lemma Wcase_typ_dom X Q h w :
  morph1 Q ->
  X ⊆ Wdom ->
  (forall x f, x ∈ A -> f ∈ (Π i ∈ B x, X) -> h x f ∈ Q (Wsup x f)) ->
  w ∈ Wf X ->
  Wcase h w ∈ Q w.
intros Qm tyX tyh tyw.
apply ZFwdom.Wf_elim in tyw; trivial.
destruct tyw as (x,tyx,(f,tyf,eqw)).
assert (eq1 : Wfst w == x).
 rewrite eqw, ZFwdom.Wfst_def; reflexivity.
assert (eq2 : Wsnd_fun w == f).
 rewrite eqw.
 eapply cc_prod_covariant in tyf.
  apply ZFwdom.Wsnd_fun_def_dom with (A:=A)(B:=B)(1:=tyf).
   auto with *.
   reflexivity.
   trivial.
unfold Wcase.
eapply eq_elim.
2:apply tyh.
 apply Qm.
 symmetry; apply transitivity with (1:=eqw).
 apply ZFwdom.Wsup_morph; auto with *.

 rewrite eq1; trivial.

 rewrite eq2.
 revert tyf; apply eq_elim.
 apply cc_prod_ext; auto with *.
 red; reflexivity.
Qed.

Lemma Wcase_typ X Q h w :
  morph1 Q ->
  X ⊆ W A B ->
  (forall x f, x ∈ A -> f ∈ (Π i ∈ B x, X) -> h x f ∈ Q (Wsup x f)) ->
  w ∈ Wf X ->
  Wcase h w ∈ Q w.
intros.
apply Wcase_typ_dom with X; trivial.
transitivity (W A B); trivial.
apply W_typ; trivial.
Qed.

Lemma Wcase_eqn h x f :
  morph2 h ->
  f ∈ (Π i ∈ B x, W A B) ->
  Wcase h (Wsup x f) == h x f.
intros.
apply Wcase_eqn_dom; trivial.
revert H0; apply cc_prod_covariant; auto with *.
intros.
apply W_typ; trivial.
Qed.

  End WCase.


Local Notation E := eq_set (only parsing).

Lemma Wcase_ext A A' B B' X X' h h' c c' :
  morph1 B ->
  morph1 B' ->
  X ⊆ W A B ->
  X' ⊆ W A' B' ->
  (forall x x' f f', x ∈ A -> x' ∈ A' -> x == x' ->
   f ∈ (Π __ ∈ B x, X) -> f' ∈ (Π __ ∈ B' x', X') ->
   f == f' -> h x f == h' x' f') ->
  c ∈ Wf A B X ->
  c' ∈ Wf A' B' X' ->
  c == c' ->
  Wcase h c == Wcase h' c'.
unfold Wcase; intros.
apply H3.
 apply ZFwdom.Wfst_typ_gen with (B:=B) (X:=X); trivial.
 apply ZFwdom.Wfst_typ_gen with (B:=B') (X:=X'); trivial.
 apply ZFwdom.Wfst_morph; trivial.
 apply ZFwdom.Wsnd_fun_typ_gen with (A:=A); trivial.
  transitivity (W A B);[trivial|apply W_typ; trivial].
 apply ZFwdom.Wsnd_fun_typ_gen with (A:=A'); trivial.
  transitivity (W A' B');[trivial|apply W_typ; trivial].
 apply ZFwdom.Wsnd_fun_morph; trivial.
Qed.

Instance Wcase_morph_gen :
  Proper ((E==>E==>E)==>E==>E) Wcase.
do 3 red; intros.
unfold Wcase.
apply H.
 apply ZFwdom.Wfst_morph; trivial.

 apply ZFwdom.Wsnd_fun_morph; trivial.
Qed.
  
End Wpaths.


