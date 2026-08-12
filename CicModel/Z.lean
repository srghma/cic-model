import CicModel.Sublogic
import CicModel.ZFdef

set_option quotPrecheck false

universe u

namespace Z

section ZermeloSetTheory

variable {set : Type u} {Tr_ : Prop → Prop} [SublogicTheory Tr_] [ZermeloSig set Tr_]

local infix:40 "~≈" => @SetTheory.eq_set set Tr_ _ _
local infix:40 "~⋴" => @SetTheory.in_set set Tr_ _ _

local notation "empty" => @ZermeloSig.empty set Tr_ _ _
local notation "pair" => @ZermeloSig.pair set Tr_ _ _
local notation "union" => @ZermeloSig.union set Tr_ _ _
local notation "subset" => @ZermeloSig.subset set Tr_ _ _
local notation "infinite" => @ZermeloSig.infinite set Tr_ _ _
local notation "power" => @ZermeloSig.power set Tr_ _ _

-- Extensionality and regularity axioms
theorem eq_set_ax (a b : set) : (a ~≈ b) ↔ (∀ x, x ~⋴ a ↔ x ~⋴ b) :=
  SetTheory.eq_set_ax a b

theorem in_reg (a a' b : set) : a ~≈ a' → a ~⋴ b → a' ~⋴ b :=
  SetTheory.in_reg a a' b

-- Well-foundedness induction axiom
theorem wf_ax (P : set → Prop) :
    (∀ x, (∀ y, y ~⋴ x → Tr_ (P y)) → Tr_ (P x)) → ∀ x, Tr_ (P x) :=
  WfSetTheory.wf_ax P

theorem empty_ax (x : set) : x ~⋴ empty → Tr_ False :=
  @ZermeloSig.empty_ax set Tr_ _ _ x

theorem pair_ax (a b x : set) : x ~⋴ pair a b ↔ Tr_ (x ~≈ a ∨ x ~≈ b) :=
  @ZermeloSig.pair_ax set Tr_ _ _ a b x

theorem union_ax (a x : set) : x ~⋴ union a ↔ Tr_ (∃ y, x ~⋴ y ∧ y ~⋴ a) :=
  @ZermeloSig.union_ax set Tr_ _ _ a x

theorem subset_ax (a : set) (P : set → Prop) (x : set) :
    x ~⋴ subset a P ↔ (x ~⋴ a ∧ Tr_ (∃ x', x ~≈ x' ∧ P x')) :=
  @ZermeloSig.subset_ax set Tr_ _ _ a P x

theorem infinity_ax1 : empty ~⋴ infinite :=
  @ZermeloSig.infinity_ax1 set Tr_ _ _

theorem infinity_ax2 (x : set) : x ~⋴ infinite → union (pair x (pair x x)) ~⋴ infinite :=
  @ZermeloSig.infinity_ax2 set Tr_ _ _ x

theorem power_ax (a x : set) : x ~⋴ power a ↔ (∀ y, y ~⋴ x → y ~⋴ a) :=
  @ZermeloSig.power_ax set Tr_ _ _ a x

-- Basic helpers
theorem eq_intro (x y : set) : (∀ z, z ~⋴ x → z ~⋴ y) → (∀ z, z ~⋴ y → z ~⋴ x) → x ~≈ y := by
  intro h1 h2
  rw [eq_set_ax]
  intro z
  exact ⟨h1 z, h2 z⟩

theorem eq_elim (x y y' : set) : y ~≈ y' → x ~⋴ y → x ~⋴ y' := by
  intro h_eq h_in
  rw [eq_set_ax] at h_eq
  exact (h_eq x).mp h_in

local notation x " ~⊆ " y => ∀ z, z ~⋴ x → z ~⋴ y

theorem incl_eq (x y : set) : (x ~⊆ y) → (y ~⊆ x) → x ~≈ y := by
  intro h1 h2
  exact eq_intro x y h1 h2

theorem eq_incl (x y : set) : x ~≈ y → (x ~⊆ y) := by
  intro h_eq z hz
  exact eq_elim z x y h_eq hz

def eq_fun (Tr : Prop → Prop) [SublogicTheory Tr] [ZermeloSig set Tr] (dom : set) (F G : set → set) : Prop :=
  ∀ x x', @SetTheory.in_set set Tr _ _ x dom → @SetTheory.eq_set set Tr _ _ x x' → @SetTheory.eq_set set Tr _ _ (F x) (G x')

def ext_fun (Tr : Prop → Prop) [SublogicTheory Tr] [ZermeloSig set Tr] (dom : set) (f : set → set) : Prop :=
  eq_fun Tr dom f f

def ext_fun2 (Tr : Prop → Prop) [SublogicTheory Tr] [ZermeloSig set Tr] (A : set) (B : set → set) (f : set → set → set) : Prop :=
  ∀ x x' y y', @SetTheory.in_set set Tr _ _ x A → @SetTheory.eq_set set Tr _ _ x x' → @SetTheory.in_set set Tr _ _ y (B x) → @SetTheory.eq_set set Tr _ _ y y' → @SetTheory.eq_set set Tr _ _ (f x y) (f x' y')

theorem eq_fun_ext (dom : set) (F G : set → set) : eq_fun Tr_ dom F G → ext_fun Tr_ dom F :=
  sorry

-- Additional Set Operations

local notation:70 "singl" x:70 => pair x x
local notation:60 x " ~∪ " y:61 => union (pair x y)
local notation:70 "inter" x:70 => subset (union x) (fun y => ∀ z, z ~⋴ x → y ~⋴ z)
local notation:60 x " ~∩ " y:61 => inter (pair x y)

theorem singl_ax (x z : set) : z ~⋴ (singl x) ↔ Tr_ (z ~≈ x) := by
  sorry

theorem union2_ax (x y z : set) : z ~⋴ (x ~∪ y) ↔ Tr_ (z ~⋴ x ∨ z ~⋴ y) := by
  sorry

theorem inter_ax (a z : set) : z ~⋴ (inter a) ↔ (Tr_ (∃ w, w ~⋴ a) ∧ (∀ y, y ~⋴ a → z ~⋴ y)) := by
  sorry

theorem inter2_def (x y z : set) : z ~⋴ (x ~∩ y) ↔ (z ~⋴ x ∧ z ~⋴ y) := by
  sorry

end ZermeloSetTheory

end Z
