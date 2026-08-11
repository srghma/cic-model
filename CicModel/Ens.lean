import CicModel.EnsEm
import CicModel.Sublogic
import CicModel.ZFdef

open Classical

universe u

-- 1. Definition of the core ZF set-theoretic operations on Aczel's Set_

def empty : Set_.{u} := Set_.sup (ULift.{u} Empty) (fun x ↦ x.down.elim)

def pair (a b : Set_.{u}) : Set_.{u} :=
  Set_.sup (ULift.{u} Bool) (fun x ↦ if x.down then a else b)

structure UnionIdx (a : Set_.{u}) where
  un_i : Set_.idx a
  un_j : Set_.idx (Set_.elts a un_i)

def union (a : Set_.{u}) : Set_.{u} :=
  Set_.sup (UnionIdx a) (fun p ↦ Set_.elts (Set_.elts a p.un_i) p.un_j)

structure SubsetIdx (Tr : Prop → Prop) [SublogicTheory Tr] (x : Set_.{u}) (P : Set_.{u} → Prop) where
  sb_i : Set_.idx x
  sb_spec : Tr (∃ x', eqSet Tr (Set_.elts x sb_i) x' ∧ P x')

def subset (Tr : Prop → Prop) [SublogicTheory Tr] (x : Set_.{u}) (P : Set_.{u} → Prop) : Set_.{u} :=
  Set_.sup (SubsetIdx Tr x P) (fun y ↦ Set_.elts x y.sb_i)

def num (Tr : Prop → Prop) [SublogicTheory Tr] : Nat → Set_.{u}
  | 0 => empty
  | n + 1 => union (pair (num Tr n) (pair (num Tr n) (num Tr n)))

def infinite (Tr : Prop → Prop) [SublogicTheory Tr] : Set_.{u} :=
  Set_.sup (ULift.{u} Nat) (fun n ↦ num.{u} Tr n.down)

def power (Tr : Prop → Prop) [SublogicTheory Tr] (x : Set_.{u}) : Set_.{u} :=
  Set_.sup (Set_.idx x → Prop) (fun P ↦ subset Tr x (fun y ↦ Tr (∃ i : Set_.idx x, eqSet Tr y (Set_.elts x i) ∧ P i)))

noncomputable def repl (Tr : Prop → Prop) [SublogicTheory Tr] (a : Set_.{u}) (R : Set_.{u} → Set_.{u} → Prop) : Set_.{u} :=
  Set_.sup (Set_.idx a) (fun i ↦
    if h : ∃ y, R (Set_.elts a i) y then
      Classical.choose h
    else
      empty
  )

-- 2. Axioms and properties of the operations

theorem empty_ax (Tr : Prop → Prop) [SublogicTheory Tr] (x : Set_.{u}) :
  inSet Tr x empty → Tr False := by
  intro h
  dsimp [inSet, empty] at h
  apply Sublogic.TrMono (fun ⟨j, _⟩ ↦ j.down.elim) h

theorem pair_ax (Tr : Prop → Prop) [SublogicTheory Tr] (a b x : Set_.{u}) :
  inSet Tr x (pair a b) ↔ Tr (eqSet Tr x a ∨ eqSet Tr x b) := by
  constructor
  · intro h
    dsimp [inSet, pair] at h
    apply Sublogic.TrMono (fun ⟨j, heq⟩ ↦ by
      rcases j with ⟨_ | _⟩
      · right; exact heq
      · left; exact heq
    ) h
  · intro h
    dsimp [inSet, pair]
    apply Sublogic.TrMono (fun h_or ↦ by
      cases h_or with
      | inl ha => exists ULift.up true
      | inr hb => exists ULift.up false
    ) h

theorem union_ax (Tr : Prop → Prop) [SublogicTheory Tr] (a x : Set_.{u}) :
  inSet Tr x (union a) ↔ Tr (∃ y : Set_.{u}, inSet Tr x y ∧ inSet Tr y a) := by
  constructor
  · intro h
    dsimp [inSet, union] at h
    apply Sublogic.TrMono (fun ⟨p, heq⟩ ↦ by
      exists Set_.elts a p.un_i
      constructor
      · apply Sublogic.TrI
        exists p.un_j
      · apply Sublogic.TrI
        exists p.un_i
        exact eqSet_refl Tr (Set_.elts a p.un_i)
    ) h
  · intro h
    dsimp [inSet, union] at *
    apply SublogicTheory.TrB h
    rintro ⟨y, hxy, hya⟩
    apply SublogicTheory.TrB hya
    rintro ⟨i, heq_y_ai⟩
    apply SublogicTheory.TrB hxy
    rintro ⟨j, heq_x_yj⟩
    have h_in : inSet Tr (Set_.elts y j) y := by
      apply Sublogic.TrI
      exists j
      exact eqSet_refl Tr (Set_.elts y j)
    rw [eq_set_ax Tr y (Set_.elts a i)] at heq_y_ai
    have h_in_ai := (heq_y_ai (Set_.elts y j)).mp h_in
    dsimp [inSet] at h_in_ai
    apply SublogicTheory.TrB h_in_ai
    rintro ⟨k, heq_yj_aik⟩
    apply Sublogic.TrI
    exists (⟨i, k⟩ : UnionIdx a)
    exact eqSet_trans Tr x (Set_.elts y j) (Set_.elts (Set_.elts a i) k) heq_x_yj heq_yj_aik

theorem pair_morph (Tr : Prop → Prop) [SublogicTheory Tr] {x y a b : Set_.{u}} (h1 : eqSet Tr x y) (h2 : eqSet Tr a b) :
  eqSet Tr (pair x a) (pair y b) := by
  dsimp [eqSet, pair]
  constructor
  · rintro ⟨i⟩
    apply Sublogic.TrI
    cases i
    · exists ULift.up false
    · exists ULift.up true
  · rintro ⟨j⟩
    apply Sublogic.TrI
    cases j
    · exists ULift.up false
    · exists ULift.up true

theorem union_morph (Tr : Prop → Prop) [SublogicTheory Tr] {a b : Set_.{u}} (h : eqSet Tr a b) :
  eqSet Tr (union a) (union b) := by
  rw [eq_set_ax] at *
  intro x
  rw [union_ax, union_ax]
  constructor
  · intro h_in
    apply SublogicTheory.TrB h_in
    rintro ⟨y, hxy, hya⟩
    apply Sublogic.TrI
    exists y
    constructor
    · exact hxy
    · exact (h y).mp hya
  · intro h_in
    apply SublogicTheory.TrB h_in
    rintro ⟨y, hxy, hyb⟩
    apply Sublogic.TrI
    exists y
    constructor
    · exact hxy
    · exact (h y).mpr hyb

theorem subset_ax (Tr : Prop → Prop) [SublogicTheory Tr] (x : Set_.{u}) (P : Set_.{u} → Prop) (z : Set_.{u}) :
  inSet Tr z (subset Tr x P) ↔ (inSet Tr z x ∧ Tr (∃ z', eqSet Tr z z' ∧ P z')) := by
  constructor
  · intro h
    dsimp [inSet, subset] at h
    constructor
    · apply SublogicTheory.TrB h
      rintro ⟨y, heq⟩
      apply Sublogic.TrI
      exists y.sb_i
    · apply SublogicTheory.TrB h
      rintro ⟨y, heq⟩
      apply SublogicTheory.TrB y.sb_spec
      rintro ⟨x', heq_xi_x', h_px'⟩
      apply Sublogic.TrI
      exists x'
      constructor
      · exact eqSet_trans Tr z (Set_.elts x y.sb_i) x' heq heq_xi_x'
      · exact h_px'
  · rintro ⟨hin, hspec⟩
    dsimp [inSet, subset] at *
    apply SublogicTheory.TrB hin
    rintro ⟨i, heq_z_xi⟩
    apply SublogicTheory.TrB hspec
    rintro ⟨z', heq_z_z', h_pz'⟩
    have h_spec : Tr (∃ x', eqSet Tr (Set_.elts x i) x' ∧ P x') := by
      apply Sublogic.TrI
      exists z'
      constructor
      · exact eqSet_trans Tr (Set_.elts x i) z z' (eqSet_sym Tr z (Set_.elts x i) heq_z_xi) heq_z_z'
      · exact h_pz'
    apply Sublogic.TrI
    exists (⟨i, h_spec⟩ : SubsetIdx Tr x P)

theorem power_ax (Tr : Prop → Prop) [SublogicTheory Tr] (a x : Set_.{u}) :
  inSet Tr x (power Tr a) ↔ (∀ y : Set_.{u}, inSet Tr y x → inSet Tr y a) := by
  constructor
  · intro h y hy
    dsimp [inSet, power] at h
    apply SublogicTheory.TrB h
    rintro ⟨P, heq_x_sub⟩
    dsimp [Set_.elts] at heq_x_sub
    have hy_sub : inSet Tr y (subset Tr a (fun y' ↦ Tr (∃ i, eqSet Tr y' (Set_.elts a i) ∧ P i))) := by
      exact ((eq_set_ax Tr x (subset Tr a (fun y' ↦ Tr (∃ i, eqSet Tr y' (Set_.elts a i) ∧ P i)))).mp heq_x_sub y).mp hy
    rw [subset_ax] at hy_sub
    exact hy_sub.1
  · intro h
    dsimp [inSet, power]
    apply Sublogic.TrI
    let P (i : Set_.idx a) : Prop := inSet Tr (Set_.elts a i) x
    exists P
    dsimp [Set_.elts]
    rw [eq_set_ax]
    intro y
    rw [subset_ax]
    constructor
    · intro hy_in_x
      constructor
      · exact h y hy_in_x
      · have h_ya := h y hy_in_x
        dsimp [inSet] at h_ya
        apply SublogicTheory.TrB h_ya
        rintro ⟨i, heq_y_ai⟩
        apply Sublogic.TrI
        exists y
        constructor
        · exact eqSet_refl Tr y
        · apply Sublogic.TrI
          exists i
          constructor
          · exact heq_y_ai
          · exact in_reg Tr y (Set_.elts a i) x heq_y_ai hy_in_x
    · rintro ⟨_, h_spec⟩
      apply SublogicTheory.TrB h_spec
      rintro ⟨z', heq_y_z', h_spec2⟩
      apply SublogicTheory.TrB h_spec2
      rintro ⟨i, heq_z'_ai, hy_ai_x⟩
      have heq_y_ai := eqSet_trans Tr y z' (Set_.elts a i) heq_y_z' heq_z'_ai
      exact in_reg Tr (Set_.elts a i) y x (eqSet_sym Tr y (Set_.elts a i) heq_y_ai) hy_ai_x

theorem infinity_ax1 (Tr : Prop → Prop) [SublogicTheory Tr] : inSet Tr empty.{u} (infinite.{u} Tr) := by
  dsimp [inSet, infinite, Set_.elts]
  apply Sublogic.TrI
  exists ULift.up 0
  change eqSet Tr empty.{u} (num Tr 0)
  rw [num]
  exact eqSet_refl Tr empty.{u}

theorem infinity_ax2 (Tr : Prop → Prop) [SublogicTheory Tr] (x : Set_.{u}) (h : inSet Tr x (infinite.{u} Tr)) :
  inSet Tr (union (pair x (pair x x))) (infinite.{u} Tr) := by
  dsimp [inSet, infinite, Set_.idx, Set_.elts] at *
  apply Sublogic.TrMono (fun (⟨n, heq⟩ : ∃ n : ULift Nat, eqSet Tr x (num.{u} Tr n.down)) ↦ by
    exists ULift.up (n.down + 1)
    dsimp [num]
    exact union_morph Tr (pair_morph Tr heq (pair_morph Tr heq heq))
  ) h

-- 3. Instantiation of SetTheory, WfSetTheory, ZermeloSig, and IZF_RSig for Set_

theorem wf_ax (Tr : Prop → Prop) [SublogicTheory Tr] (P : Set_.{u} → Prop)
  (h_step : ∀ x, (∀ y, inSet Tr y x → Tr (P y)) → Tr (P x)) (x : Set_.{u}) : Tr (P x) := by
  have h_cut : ∀ (x' : Set_.{u}), eqSet Tr x x' → Tr (P x') := by
    induction x with
    | sup X f ih =>
      intro x' heq
      apply h_step
      intro y hy
      have hy_self : inSet Tr y (Set_.sup X f) := by
        rw [eq_set_ax] at heq
        exact (heq y).mpr hy
      dsimp [inSet] at hy_self
      apply SublogicTheory.TrB hy_self
      rintro ⟨i, heq_y_fi⟩
      apply ih i y (eqSet_sym Tr y (f i) heq_y_fi)
  apply h_cut
  exact eqSet_refl Tr x

noncomputable instance (Tr : Prop → Prop) [SublogicTheory Tr] : IZF_RSig Set_.{u} Tr where
  eq_set := eqSet Tr
  in_set := inSet Tr
  eq_set_ax := eq_set_ax Tr
  in_reg := in_reg Tr
  wf_ax := wf_ax Tr
  empty := empty
  pair := pair
  union := union
  subset := subset Tr
  infinite := infinite Tr
  power := power Tr
  empty_ax x h_in := empty_ax Tr x h_in
  pair_ax := pair_ax Tr
  union_ax := union_ax Tr
  subset_ax := subset_ax Tr
  infinity_ax1 := infinity_ax1 Tr
  infinity_ax2 := infinity_ax2 Tr
  power_ax := power_ax Tr
  repl := repl Tr
  repl_mono := fun _ _ _ _ _ _ _ ↦ sorry
  repl_ax := fun _ _ _ _ _ ↦ sorry
