Require Import ZF Zpairs Zsum ZFnats Zrelations ZFord ZFfix ZFfixfun.
Require Import Zstable ZFiso ZFind_w ZFspos.
Require Import ZFsposd.

(** Examples *)

Module Vectors.


Definition vect A :=
  dpos_sum
    (* vect 0 *)
    (dpos_inst zero)
    (* forall n:N, A -> vect n -> vect (S n) *)
    (dpos_norec N (fun k => dpos_consrec (dpos_cst A) (dpos_consrec (dpos_rec k) (dpos_inst (succ k))))).

Lemma vect_pos A : isDPositive N (vect A).
unfold vect; intros.
apply isDPos_sum.
 apply isDPos_inst.

 apply isDPos_norec.
  do 2 red; intros.
  apply dpos_consrec_morph.
  apply dpos_cst_morph; reflexivity.
  apply dpos_consrec_morph.
  apply dpos_rec_morph; trivial.
  apply dpos_inst_morph; rewrite H; reflexivity.

  intros.
  apply isDPos_consrec.
   apply isDPos_cst.
  apply isDPos_consrec.
   apply isDPos_rec; trivial.

   apply isDPos_inst.
Qed.

Definition nil := inl empty.

Lemma nil_typ A X :
  morph1 X ->
  nil ∈ dpos_oper (vect A) X zero.
simpl; intros.
apply inl_typ.
rewrite cond_set_ax; split.
 apply singl_intro.
 reflexivity.
Qed.

Definition cons k x l :=
  inr (couple k (couple x (couple l empty))).

Lemma cons_typ A X k x l :
  morph1 X ->
  k ∈ N ->
  x ∈ A ->
  l ∈ X k ->
  cons k x l ∈ dpos_oper (vect A) X (succ k).
simpl; intros.
apply inr_typ.
apply couple_intro_sigma; trivial.
 do 2 red; intros.
 rewrite H4; reflexivity.

 apply couple_intro; trivial.
 apply couple_intro; trivial.
 rewrite cond_set_ax; split.
  apply singl_intro.
  reflexivity.
Qed.

End Vectors.

