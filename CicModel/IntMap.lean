-- CicModel/IntMap.lean
import Mathlib.Data.Nat.Basic

namespace CicModel

section IntMap

variable {A : Type}

def eq_map_int (m1 m2 : Nat → A) : Prop :=
  ∀ i : Nat, m1 i = m2 i

theorem refl_eq_map_int (m : Nat → A) : eq_map_int m m :=
  fun _ => rfl

theorem sym_eq_map_int (m1 m2 : Nat → A) (h : eq_map_int m1 m2) : eq_map_int m2 m1 :=
  fun i => (h i).symm

theorem trans_eq_map_int (m1 m2 m3 : Nat → A) (h1 : eq_map_int m1 m2) (h2 : eq_map_int m2 m3) : eq_map_int m1 m3 :=
  fun i => (h1 i).trans (h2 i)

def cons_map_int (x : A) (m : Nat → A) : Nat → A
  | 0 => x
  | k + 1 => m k

theorem cons_map_int_ext (x y : A) (m1 m2 : Nat → A) (hx : x = y) (hm : eq_map_int m1 m2) :
    eq_map_int (cons_map_int x m1) (cons_map_int y m2) := by
  intro i
  cases i with
  | zero => exact hx
  | succ k => exact hm k

def ins_map_int (n : Nat) (x : A) (m : Nat → A) (i : Nat) : A :=
  if i > n then m (i - 1)
  else if i = n then x
  else m i

def del_map_int (n k : Nat) (m : Nat → A) (i : Nat) : A :=
  if i ≥ k then m (i + n)
  else m i

theorem del_cons_map_int (x : A) (n k : Nat) (m : Nat → A) :
    eq_map_int (del_map_int n (k + 1) (cons_map_int x m)) (cons_map_int x (del_map_int n k m)) := by
  intro i
  cases i with
  | zero =>
    dsimp [del_map_int, cons_map_int]
  | succ i' =>
    dsimp [del_map_int, cons_map_int]
    by_cases h : i' ≥ k
    · have h_succ : i' + 1 ≥ k + 1 := by omega
      rw [if_pos h_succ, if_pos h]
      have h_eq : i' + 1 + n = i' + n + 1 := by omega
      change cons_map_int x m (i' + 1 + n) = m (i' + n)
      rw [h_eq]
      rfl
    · have h_succ : ¬ (i' + 1 ≥ k + 1) := by omega
      rw [if_neg h_succ, if_neg h]

theorem del_cons_map2_int (n : Nat) (x : A) (m : Nat → A) :
    eq_map_int (del_map_int (n + 1) 0 (cons_map_int x m)) (del_map_int n 0 m) := by
  intro i
  dsimp [del_map_int, cons_map_int]

theorem ins_cons_map_int (x y : A) (k : Nat) (m : Nat → A) :
    eq_map_int (ins_map_int (k + 1) y (cons_map_int x m)) (cons_map_int x (ins_map_int k y m)) := by
  intro i
  cases i with
  | zero =>
    dsimp [ins_map_int, cons_map_int]
  | succ i' =>
    dsimp [ins_map_int, cons_map_int]
    by_cases h1 : i' > k
    · have h1_succ : i' + 1 > k + 1 := by omega
      rw [if_pos h1_succ, if_pos h1]
      have h_eq : i' + 1 - 1 = i' := by omega
      change cons_map_int x m (i' + 1 - 1) = m (i' - 1)
      rw [h_eq]
      have h_succ : i' = (i' - 1) + 1 := by omega
      conv =>
        lhs
        rw [h_succ]
      rfl
    · have h1_succ : ¬ (i' + 1 > k + 1) := by omega
      rw [if_neg h1_succ, if_neg h1]
      by_cases h2 : i' = k
      · have h2_succ : i' + 1 = k + 1 := by omega
        rw [if_pos h2_succ, if_pos h2]
      · have h2_succ : ¬ (i' + 1 = k + 1) := by omega
        rw [if_neg h2_succ, if_neg h2]

end IntMap

end CicModel
