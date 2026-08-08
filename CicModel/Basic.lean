-- CicModel/Basic.lean
import Mathlib.Order.Max
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

namespace CicModel

-- Indexed relations as defined in Coq:
-- Definition indexed_relation A A' B (R:B->B->Prop) (f:A->B) (g:A'->B) :=
--   (forall x, exists y, R (f x) (g y)) /\
--   (forall y, exists x, R (f x) (g y)).
def indexed_relation {A A' B : Type} (R : B → B → Prop) (f : A → B) (g : A' → B) : Prop :=
  (∀ x, ∃ y, R (f x) (g y)) ∧ (∀ y, ∃ x, R (f x) (g y))

theorem indexed_relation_id {A B : Type} (R : B → B → Prop) (F F' : A → B)
    (h : ∀ x, R (F x) (F' x)) : indexed_relation R F F' := by
  constructor
  · intro x; exact ⟨x, h x⟩
  · intro x; exact ⟨x, h x⟩

-- Asymmetric and-split
theorem and_split {A B : Prop} (hA : A) (hB : A → B) : A ∧ B :=
  ⟨hA, hB hA⟩

-- List relation
def list_eq {A : Type} (R : A → A → Prop) : List A → List A → Prop
  | [], [] => True
  | x :: xs, y :: ys => R x y ∧ list_eq R xs ys
  | _, _ => False

theorem list_eq_refl {A : Type} (R : A → A → Prop) (h : ∀ x, R x x) (xs : List A) : list_eq R xs xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨h x, ih⟩

-- Cantor pairing function
-- nat_sum (fun x => x) n = n * (n - 1) / 2
def nat_sum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => nat_sum f n + f n

def nn2n1 (x y : Nat) : Nat × Nat := (x + y, y)

def nn2n2 (p : Nat × Nat) : Nat :=
  nat_sum (fun x => x) (p.1 + 1) + p.2

def nn2n (x y : Nat) : Nat :=
  nn2n2 (nn2n1 x y)

-- We can prove the basic monotonicity/inequality property:
-- Lemma nn2n_order n m : (n <= nn2n n m /\ m <= nn2n n m)%nat.
theorem nat_sum_mono (f : Nat → Nat) {m n : Nat} (h : m ≤ n) : nat_sum f m ≤ nat_sum f n := by
  induction h with
  | refl => rfl
  | step _ ih =>
    rw [nat_sum]
    exact Nat.le_add_right_of_le ih

theorem nn2n_order (n m : Nat) : n ≤ nn2n n m ∧ m ≤ nn2n n m := by
  unfold nn2n nn2n2 nn2n1
  dsimp
  have h1 : nat_sum (fun x => x) (n + m + 1) = nat_sum (fun x => x) (n + m) + (n + m) := rfl
  rw [h1]
  constructor
  · have h2 : n ≤ n + m := Nat.le_add_right n m
    have h3 := nat_sum_mono (fun x => x) h2
    linarith
  · linarith

end CicModel
