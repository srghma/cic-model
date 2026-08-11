import CicModel.Sublogic
import CicModel.ZFdef

universe u

inductive Set_ : Type (u + 1) where
  | sup (X : Type u) (f : X → Set_)

def Set_.idx : Set_ → Type u
  | sup X _ => X

def Set_.elts : ∀ (x : Set_), idx x → Set_
  | sup _ f => f

def eqSet (Tr : Prop → Prop) [SublogicTheory Tr] : Set_ → Set_ → Prop
  | Set_.sup X f, Set_.sup Y g =>
    (∀ i : X, Tr (∃ j : Y, eqSet Tr (f i) (g j))) ∧
    (∀ j : Y, Tr (∃ i : X, eqSet Tr (f i) (g j)))

def inSet (Tr : Prop → Prop) [SublogicTheory Tr] (x y : Set_) : Prop :=
  Tr (∃ j : Set_.idx y, eqSet Tr x (Set_.elts y j))

theorem eqSet_refl (Tr : Prop → Prop) [SublogicTheory Tr] (x : Set_) : eqSet Tr x x := by
  induction x with
  | sup X f ih =>
    constructor
    · intro i
      apply Sublogic.TrI
      exists i
      exact ih i
    · intro j
      apply Sublogic.TrI
      exists j
      exact ih j

theorem eqSet_sym (Tr : Prop → Prop) [SublogicTheory Tr] : ∀ (x y : Set_), eqSet Tr x y → eqSet Tr y x
  | Set_.sup X f, Set_.sup Y g => by
    rintro ⟨h1, h2⟩
    constructor
    · intro j
      apply Sublogic.TrMono (fun (⟨i, h_eq⟩ : ∃ i, eqSet Tr (f i) (g j)) ↦ (⟨i, eqSet_sym Tr (f i) (g j) h_eq⟩ : ∃ i, eqSet Tr (g j) (f i))) (h2 j)
    · intro i
      apply Sublogic.TrMono (fun (⟨j, h_eq⟩ : ∃ j, eqSet Tr (f i) (g j)) ↦ (⟨j, eqSet_sym Tr (f i) (g j) h_eq⟩ : ∃ j, eqSet Tr (g j) (f i))) (h1 i)

theorem eqSet_trans (Tr : Prop → Prop) [SublogicTheory Tr] :
  ∀ (x y z : Set_), eqSet Tr x y → eqSet Tr y z → eqSet Tr x z
  | Set_.sup X f, Set_.sup Y g, Set_.sup Z h => by
    rintro ⟨h1, h2⟩ ⟨h3, h4⟩
    constructor
    · intro i
      apply SublogicTheory.TrB (h1 i)
      rintro ⟨j, hij⟩
      apply Sublogic.TrMono (fun (⟨k, hjk⟩ : ∃ k, eqSet Tr (g j) (h k)) ↦ (⟨k, eqSet_trans Tr (f i) (g j) (h k) hij hjk⟩ : ∃ k, eqSet Tr (f i) (h k))) (h3 j)
    · intro k
      apply SublogicTheory.TrB (h4 k)
      rintro ⟨j, hjk⟩
      apply Sublogic.TrMono (fun (⟨i, hij⟩ : ∃ i, eqSet Tr (f i) (g j)) ↦ (⟨i, eqSet_trans Tr (f i) (g j) (h k) hij hjk⟩ : ∃ i, eqSet Tr (f i) (h k))) (h2 j)

theorem in_reg (Tr : Prop → Prop) [SublogicTheory Tr] (a a' b : Set_) (heq : eqSet Tr a a') (hin : inSet Tr a b) : inSet Tr a' b := by
  dsimp [inSet] at *
  apply SublogicTheory.TrB hin
  rintro ⟨j, haj⟩
  apply Sublogic.TrI
  exists j
  exact eqSet_trans Tr a' a (Set_.elts b j) (eqSet_sym Tr a a' heq) haj

theorem eq_set_ax (Tr : Prop → Prop) [SublogicTheory Tr] (a b : Set_.{u}) : eqSet Tr a b ↔ (∀ x : Set_.{u}, inSet Tr x a ↔ inSet Tr x b) := by
  constructor
  · intro hab x
    constructor
    · intro hxa
      dsimp [inSet] at *
      apply SublogicTheory.TrB hxa
      rintro ⟨i, h_eq_a⟩
      rcases a with ⟨X, f⟩
      rcases b with ⟨Y, g⟩
      rcases hab with ⟨hab1, _⟩
      apply SublogicTheory.TrB (hab1 i)
      rintro ⟨j, h_eq_ab⟩
      apply Sublogic.TrI
      exists j
      exact eqSet_trans Tr x (f i) (g j) h_eq_a h_eq_ab
    · intro hxb
      dsimp [inSet] at *
      apply SublogicTheory.TrB hxb
      rintro ⟨j, h_eq_b⟩
      rcases a with ⟨X, f⟩
      rcases b with ⟨Y, g⟩
      rcases hab with ⟨_, hab2⟩
      apply SublogicTheory.TrB (hab2 j)
      rintro ⟨i, h_eq_ab⟩
      apply Sublogic.TrI
      exists i
      exact eqSet_trans Tr x (g j) (f i) h_eq_b (eqSet_sym Tr (f i) (g j) h_eq_ab)
  · intro h
    rcases a with ⟨X, f⟩
    rcases b with ⟨Y, g⟩
    constructor
    · intro i
      have h_in_self : inSet Tr (f i) (Set_.sup X f) := by
        apply Sublogic.TrI
        exists i
        exact eqSet_refl Tr (f i)
      exact (h (f i)).mp h_in_self
    · intro j
      have h_in_self : inSet Tr (g j) (Set_.sup Y g) := by
        apply Sublogic.TrI
        exists j
        exact eqSet_refl Tr (g j)
      have h_in_other := (h (g j)).mpr h_in_self
      apply Sublogic.TrMono (fun ⟨i, heq⟩ ↦ ⟨i, eqSet_sym Tr (g j) (f i) heq⟩) h_in_other
