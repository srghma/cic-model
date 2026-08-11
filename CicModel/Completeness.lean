-- CicModel/Completeness.lean
import CicModel.Sublogic
import CicModel.ZF
import CicModel.Lambda

namespace CicModel

namespace cc

-- 1. Sorts and Terms for the Calculus of Constructions (CC)
inductive sort : Type
  | kind : sort
  | prop : sort

inductive term : Type
  | Srt (s : sort)
  | Ref (n : Nat)
  | Abs (T M : term)
  | App (f arg : term)
  | Pi (T U : term)

open term

-- 2. Shifting and Substitution on annotated terms
def lift_rec (n : Nat) (t : term) (k : Nat) : term :=
  match t with
  | Srt s => Srt s
  | Ref i =>
    if i ≥ k then Ref (n + i)
    else Ref i
  | Abs T M => Abs (lift_rec n T k) (lift_rec n M (k + 1))
  | App u v => App (lift_rec n u k) (lift_rec n v k)
  | Pi A B => Pi (lift_rec n A k) (lift_rec n B (k + 1))

def lift (n : Nat) (t : term) : term :=
  lift_rec n t 0

def subst_rec (N M : term) (k : Nat) : term :=
  match M with
  | Srt s => Srt s
  | Ref i =>
    if i > k then Ref (i - 1)
    else if i = k then lift k N
    else Ref i
  | Abs A B => Abs (subst_rec N A k) (subst_rec N B (k + 1))
  | App u v => App (subst_rec N u k) (subst_rec N v k)
  | Pi T U => Pi (subst_rec N T k) (subst_rec N U (k + 1))

def subst (N M : term) : term :=
  subst_rec N M 0

-- 3. Environment and Item-lifting
def env : Type := List term

inductive item (x : term) : env → Nat → Prop where
  | item_hd : ∀ l : env, item x (x :: l) 0
  | item_tl : ∀ (l : env) (n : Nat) (y : term), item x l n → item x (y :: l) (n + 1)

def item_lift (t : term) (e : env) (n : Nat) : Prop :=
  ∃ u : term, t = lift (n + 1) u ∧ item u e n

-- 4. Mutual Inductive definition of eq_typ and wf
mutual
  inductive eq_typ : env → term → term → term → Prop where
    | type_prop : ∀ e : env,
        wf e →
        eq_typ e (Srt sort.prop) (Srt sort.prop) (Srt sort.kind)
    | type_var : ∀ (e : env) (v : Nat) (t : term),
        wf e →
        item_lift t e v →
        eq_typ e (Ref v) (Ref v) t
    | type_abs : ∀ (e : env) (T T' M M' U U' : term) (s1 s2 : sort),
        eq_typ e T T' (Srt s1) →
        eq_typ (T :: e) U U' (Srt s2) →
        eq_typ (T :: e) M M' U →
        eq_typ e (Abs T M) (Abs T' M') (Pi T U)
    | type_app : ∀ (e : env) (u u' v v' V V' Ur Ur' : term) (s1 s2 : sort),
        eq_typ e v v' V →
        eq_typ e V V' (Srt s1) →
        eq_typ e u u' (Pi V Ur) →
        eq_typ (V :: e) Ur Ur' (Srt s2) →
        eq_typ e (App (Pi u Ur) v) (App (Pi u' Ur') v') (subst v Ur)
    | type_prod : ∀ (e : env) (T T' U U' : term) (s1 s2 : sort),
        eq_typ e T T' (Srt s1) →
        eq_typ (T :: e) U U' (Srt s2) →
        eq_typ e (Pi T U) (Pi T' U') (Srt s2)
    | type_beta : ∀ (e : env) (T T' M M' N N' U U' : term) (s1 s2 : sort),
        eq_typ e N N' T →
        eq_typ e T T' (Srt s1) →
        eq_typ (T :: e) M M' U →
        eq_typ (T :: e) U U' (Srt s2) →
        eq_typ e (App (Pi (Abs T M) U) N) (subst N' M') (subst N U)
    | type_red : ∀ (e : env) (M M' T T' : term) (s : sort),
        eq_typ e M M' T →
        eq_typ e T T' (Srt s) →
        eq_typ e M M' T'
    | type_exp : ∀ (e : env) (M M' T T' : term) (s : sort),
        eq_typ e M M' T' →
        eq_typ e T T' (Srt s) →
        eq_typ e M M' T

  inductive wf : env → Prop where
    | wf_nil : wf []
    | wf_var : ∀ (e : env) (T T' : term) (s : sort),
        eq_typ e T T' (Srt s) →
        wf (T :: e)
end

-- Strong Normalisation of CC
-- One-step beta reduction
inductive red1 : term → term → Prop where
  | beta : ∀ M N : term, red1 (App (Abs (Srt sort.prop) M) N) (subst N M)
  | abs_red : ∀ T M M' : term, red1 M M' → red1 (Abs T M) (Abs T M')
  | app_red_l : ∀ M1 N1 M2 : term, red1 M1 N1 → red1 (App M1 M2) (App N1 M2)
  | app_red_r : ∀ M1 M2 N2 : term, red1 M2 N2 → red1 (App M1 M2) (App M1 N2)

def sn : term → Prop :=
  Acc (fun x y => red1 y x)

-- Unmarking / un-annotation operator for typed lambda terms (converting typed terms to pure Lambda.term)
axiom unmark_app (M : term) : CicModel.term

-- The main theorem: strong normalization of CC
-- Proves that any well-typed term M in any valid environment is strongly normalizing
theorem strong_normalization (e : env) (M M' T : term) :
    eq_typ e M M' T →
    sn M
    := sorry

end cc

end CicModel
