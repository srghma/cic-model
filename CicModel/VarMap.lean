-- CicModel/VarMap.lean
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Basic

namespace CicModel

def Map (T : Type) : Type := Nat → T

def eq_map {T : Type} (eq_T : T → T → Prop) (i1 i2 : Map T) : Prop :=
  ∀ k : Nat, eq_T (i1 k) (i2 k)

def nil_map {T : Type} (x : T) : Map T :=
  fun _ => x

def cons_map {T : Type} (x : T) (i : Map T) : Map T
  | 0 => x
  | k + 1 => i k

def shift {T : Type} (n : Nat) (i : Map T) : Map T :=
  fun k => i (k + n)

def lams {T : Type} (n : Nat) (f : Map T → Map T) (i : Map T) : Map T :=
  fun k =>
    if k ≥ n then f (shift n i) (k - n)
    else i k

-- Morphisms as theorems:
theorem cons_morph {T : Type} (eq_T : T → T → Prop) {x y : T} (hxy : eq_T x y) {i1 i2 : Map T} (hi : eq_map eq_T i1 i2) :
    eq_map eq_T (cons_map x i1) (cons_map y i2) := by
  intro k
  cases k with
  | zero => exact hxy
  | succ k' => exact hi k'

theorem shift_morph {T : Type} (eq_T : T → T → Prop) (n : Nat) {i1 i2 : Map T} (hi : eq_map eq_T i1 i2) :
    eq_map eq_T (shift n i1) (shift n i2) := by
  intro k
  exact hi (k + n)

theorem lams_morph {T : Type} (eq_T : T → T → Prop) {n : Nat} {f1 f2 : Map T → Map T}
    (hf : ∀ {i1 i2 : Map T}, eq_map eq_T i1 i2 → eq_map eq_T (f1 i1) (f2 i2))
    {i1 i2 : Map T} (hi : eq_map eq_T i1 i2) :
    eq_map eq_T (lams n f1 i1) (lams n f2 i2) := by
  intro k
  unfold lams
  split_ifs with h
  · apply hf
    apply shift_morph eq_T
    exact hi
  · exact hi k

theorem cons_ext {T : Type} (eq_T : T → T → Prop) (x : T) (i i' : Map T)
    (hx : eq_T x (i' 0)) (hs : eq_map eq_T i (shift 1 i')) :
    eq_map eq_T (cons_map x i) i' := by
  intro k
  cases k with
  | zero => exact hx
  | succ k' => exact hs k'

theorem surj_pair {T : Type} (eq_T : T → T → Prop) (equiv : Equivalence eq_T) (i : Map T) :
    eq_map eq_T i (cons_map (i 0) (shift 1 i)) := by
  intro k
  cases k with
  | zero => exact equiv.refl _
  | succ k' => exact equiv.refl _

theorem shift0 {T : Type} (eq_T : T → T → Prop) (equiv : Equivalence eq_T) (i : Map T) :
    eq_map eq_T (shift 0 i) i := by
  intro k
  exact equiv.refl _

theorem shift_split {T : Type} (eq_T : T → T → Prop) (equiv : Equivalence eq_T) (m n : Nat) (i : Map T) :
    eq_map eq_T (shift (m + n) i) (shift n (shift m i)) := by
  intro k
  unfold shift
  have h : k + (m + n) = k + n + m := by omega
  rw [h]
  exact equiv.refl _

theorem shiftS_split {T : Type} (eq_T : T → T → Prop) (equiv : Equivalence eq_T) (n : Nat) (i : Map T) :
    eq_map eq_T (shift (n + 1) i) (shift n (shift 1 i)) := by
  intro k
  unfold shift
  have h : k + (n + 1) = k + 1 + n := by omega
  rw [h]
  have h2 : k + 1 + n = k + n + 1 := by omega
  rw [h2]
  exact equiv.refl _

theorem shift_cons {T : Type} (eq_T : T → T → Prop) (equiv : Equivalence eq_T) (x : T) (i : Map T) :
    eq_map eq_T (shift 1 (cons_map x i)) i := by
  intro k
  unfold shift cons_map
  have h : k + 1 = Nat.succ k := by omega
  rw [h]
  exact equiv.refl _

theorem shiftS_cons {T : Type} (eq_T : T → T → Prop) (equiv : Equivalence eq_T) (n : Nat) (x : T) (i : Map T) :
    eq_map eq_T (shift (n + 1) (cons_map x i)) (shift n i) := by
  intro k
  unfold shift cons_map
  have h : k + (n + 1) = k + n + 1 := by omega
  rw [h]
  have h2 : k + n + 1 = Nat.succ (k + n) := by omega
  rw [h2]
  exact equiv.refl _

theorem lams_split {T : Type} (eq_T : T → T → Prop) (equiv : Equivalence eq_T) (k k' : Nat) (f : Map T → Map T)
    (hf : ∀ {i1 i2 : Map T}, eq_map eq_T i1 i2 → eq_map eq_T (f i1) (f i2))
    (i : Map T) :
    eq_map eq_T (lams (k + k') f i) (lams k (lams k' f) i) := by
  intro n
  unfold lams
  split_ifs with h1 h2 h3 h4
  · have h_eq : n - k - k' = n - (k + k') := by omega
    rw [h_eq]
    apply hf
    apply shift_split eq_T equiv
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · unfold shift
    have h_n : n = n - k + k := by omega
    conv =>
      lhs
      rw [h_n]
    exact equiv.refl _
  · exact equiv.refl _

theorem lams_bv {T : Type} (eq_T : T → T → Prop) (equiv : Equivalence eq_T) (m : Nat) (f : Map T → Map T) (i : Map T) (k : Nat) (h : k < m) :
    eq_T (lams m f i k) (i k) := by
  unfold lams
  split_ifs with h_cond
  · omega
  · exact equiv.refl _

theorem lams_shift {T : Type} (eq_T : T → T → Prop) (equiv : Equivalence eq_T) (m : Nat) (f : Map T → Map T) (i : Map T) :
    eq_map eq_T (shift m (lams m f i)) (f (shift m i)) := by
  intro k
  unfold shift lams
  split_ifs with h
  · have h_eq : k + m - m = k := by omega
    rw [h_eq]
    exact equiv.refl _
  · omega

theorem lams0 {T : Type} (eq_T : T → T → Prop) (equiv : Equivalence eq_T) (f : Map T → Map T)
    (hf : ∀ {i1 i2 : Map T}, eq_map eq_T i1 i2 → eq_map eq_T (f i1) (f i2))
    (i : Map T) :
    eq_map eq_T (lams 0 f i) (f i) := by
  intro k
  unfold lams
  dsimp
  apply hf
  apply shift0 eq_T equiv

theorem shift_lams {T : Type} (eq_T : T → T → Prop) (equiv : Equivalence eq_T) (k : Nat) (f : Map T → Map T) (i : Map T) :
    eq_map eq_T (shift 1 (lams (k + 1) f i)) (lams k f (shift 1 i)) := by
  intro n
  unfold shift lams
  split_ifs with h1 h2
  · have h_eq : n + 1 - (k + 1) = n - k := by omega
    rw [h_eq]
    exact equiv.refl _
  · exfalso; omega
  · exfalso; omega
  · exact equiv.refl _

theorem cons_lams {T : Type} (eq_T : T → T → Prop) (equiv : Equivalence eq_T) (k : Nat) (f : Map T → Map T)
    (hf : ∀ {i1 i2 : Map T}, eq_map eq_T i1 i2 → eq_map eq_T (f i1) (f i2))
    (i : Map T) (x : T) :
    eq_map eq_T (cons_map x (lams k f i)) (lams (k + 1) f (cons_map x i)) := by
  intro n
  cases n with
  | zero =>
    dsimp [cons_map, lams]
    exact equiv.refl _
  | succ n' =>
    dsimp [cons_map, shift, lams]
    split_ifs with h1 h2
    · have h_eq : n' + 1 - (k + 1) = n' - k := by omega
      rw [h_eq]
      apply hf
      intro m'
      exact equiv.refl _
    · exfalso; omega
    · exfalso; omega
    · exact equiv.refl _

end CicModel
