-- CicModel/Choice.lean

namespace CicModel

def choice (A B : Type) : Prop :=
  ∀ (R : A → B → Prop),
  (∀ x : A, ∃ y : B, R x y) →
  ∃ f : A → B, ∀ x : A, R x (f x)

def unique_choice (A B : Type) (E : B → B → Prop) : Prop :=
  ∀ (R : A → B → Prop),
  (∀ x : A, ∃ y : B, R x y) →
  (∀ x : A, ∀ y y' : B, R x y → (R x y' ↔ E y y')) →
  ∃ f : A → B, ∀ x : A, R x (f x)

end CicModel
