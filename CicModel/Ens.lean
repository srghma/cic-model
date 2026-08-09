-- CicModel/Ens.lean
import CicModel.Sublogic

namespace CicModel

-- Statement of unique choice principles in the given logic
def Tchoice (Tr : Prop → Prop) (A B : Type) : Prop :=
  ∀ (R : A → B → Prop),
  (∀ x : A, Tr (∃ y : B, R x y)) →
  Tr (∃ f : A → B, ∀ x : A, Tr (R x (f x)))

-- The level of ensembles (Aczel's model of ZF set theory)
inductive Set' (L : Sublogic) : Type 1
  | sup (X : Type) (f : X → Set' L) : Set' L

namespace Set'

variable {L : Sublogic}

def idx : Set' L → Type
  | sup X _ => X

def elts : ∀ (x : Set' L), idx x → Set' L
  | sup _ f => f

-- Equality on ensembles (recursively defined)
def eq_set (x y : Set' L) : Prop :=
  match x, y with
  | sup X f, sup Y g =>
    (∀ i : X, L.Tr (∃ j : Y, eq_set (f i) (g j))) ∧
    (∀ j : Y, L.Tr (∃ i : X, eq_set (f i) (g j)))

-- Membership relation: x ∈ y
def in_set (x y : Set' L) : Prop :=
  match y with
  | sup Y g => L.Tr (∃ j : Y, eq_set x (g j))

-- eq_set is an L-proposition
theorem eq_set_isL (x y : Set' L) : isL (eq_set x y) := by
  cases x
  cases y
  unfold eq_set isL
  intro h
  exact ⟨fun i => and_isL (fa_isL (fun _ => Tr_isL _)) (fa_isL (fun _ => Tr_isL _)) h |>.1 i,
         fun j => and_isL (fa_isL (fun _ => Tr_isL _)) (fa_isL (fun _ => Tr_isL _)) h |>.2 j⟩

-- in_set is an L-proposition
theorem in_set_isL (x y : Set' L) : isL (in_set x y) := by
  cases y
  unfold in_set isL
  intro h
  exact L.TrP h

end Set'

end CicModel
