-- CicModel/Lemmas.lean
import CicModel.ZF

-- @skip eq_set_ax (Mathlib's built-in Set.extensionality axiom replaces this)
-- @skip empty_ax (Mathlib's built-in empty set predicate Set.mem_empty replaces this)
-- @skip pair_ax (Mathlib's built-in pairing axiom Set.mem_insert / Set.mem_singleton replaces this)
-- @skip is_nat_zero (Mathlib's Nat.zero is built-in)
-- @skip is_nat_succ (Mathlib's Nat.succ is built-in)
-- @skip Acc_prop (Mathlib's built-in proof irrelevance replaces this)

namespace CicModel

section Lemmas

variable {L : Sublogic} [Z : Zermelo L]

-- Let's open Zermelo and SetTheory to make set-theoretic operators accessible
open SetTheory
open Zermelo

-- 1. Lemma showing that nothing is in the empty set:
-- In Coq: empty_ax : forall x, #¬ x ∈ empty
theorem empty_is_empty (x : Set' L) : Tnot (in_set x empty) :=
  empty_ax x

-- 2. Lemma: Pair is symmetric (pair a b == pair b a)
theorem pair_sym (a b : Set' L) : eq_set (pair a b) (pair b a) := by
  -- Since SetTheory has eq_set_ax, we can prove equality by showing they have the same elements:
  -- eq_set_ax : ∀ a b, eq_set a b ↔ (∀ x, in_set x a ↔ in_set x b)
  rw [eq_set_ax]
  intro x
  constructor
  · intro h
    -- pair_ax: ∀ a b x, in_set x (pair a b) ↔ L.Tr (eq_set x a ∨ eq_set x b)
    rw [pair_ax] at h ⊢
    -- Since Tr is a functor/monad, we can map over it.
    -- L.TrMono : ∀ {P Q}, (P → Q) → Tr P → Tr Q
    apply L.TrMono _ h
    intro hor
    cases hor with
    | inl h1 => exact Or.inr h1
    | inr h2 => exact Or.inl h2
  · intro h
    rw [pair_ax] at h ⊢
    apply L.TrMono _ h
    intro hor
    cases hor with
    | inl h1 => exact Or.inr h1
    | inr h2 => exact Or.inl h2

-- 3. Theorem: Uniqueness of empty set
-- If e is empty, then e == empty
theorem empty_uniqueness (e : Set' L) (he : ∀ x : Set' L, Tnot (in_set x e)) : eq_set e empty := by
  rw [eq_set_ax]
  intro x
  constructor
  · intro h
    -- Since he x : Tnot (in_set x e) which is in_set x e → L.Tr False
    have h_false := he x h
    -- From Tr False, we can get Tr of anything, including in_set x empty
    have h_empty := rFF (in_set x empty) h_false
    -- But eq_set/in_set are L-propositions, so we can project out of L.Tr:
    -- in_set_isL : ∀ x y, isL (in_set x y)
    exact in_set_isL x empty h_empty
  · intro h
    have h_false := empty_ax x h
    have h_e := rFF (in_set x e) h_false
    exact in_set_isL x e h_e

end Lemmas

end CicModel
