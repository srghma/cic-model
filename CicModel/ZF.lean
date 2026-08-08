-- CicModel/ZF.lean
import CicModel.Sublogic

namespace CicModel

-- A generic set theory signature
class SetTheory (L : Sublogic) where
  Set' : Type
  eq_set : Set' → Set' → Prop
  in_set : Set' → Set' → Prop
  eq_set_isL : ∀ x y : Set', isL (eq_set x y)
  in_set_isL : ∀ x y : Set', isL (in_set x y)
  eq_set_ax : ∀ a b : Set', eq_set a b ↔ (∀ x : Set', in_set x a ↔ in_set x b)
  in_reg : ∀ a a' b : Set', eq_set a a' → in_set a b → in_set a' b

-- WfSetTheory (regularity / well-foundation)
class WfSetTheory (L : Sublogic) extends SetTheory L where
  wf_ax : ∀ P : Set' → Prop,
    (∀ x : Set', (∀ y : Set', in_set y x → P y) → P x) →
    ∀ x : Set', P x

-- Zermelo set theory signature
class Zermelo (L : Sublogic) extends WfSetTheory L where
  empty : Set'
  pair : Set' → Set' → Set'
  union : Set' → Set'
  subset : Set' → (Set' → Prop) → Set'
  infinite : Set'
  power : Set' → Set'
  empty_ax : ∀ x : Set', Tnot (in_set x empty)
  pair_ax : ∀ a b x : Set', in_set x (pair a b) ↔ L.Tr (eq_set x a ∨ eq_set x b)
  union_ax : ∀ a x : Set', in_set x (union a) ↔ L.Tr (∃ y : Set', in_set x y ∧ in_set y a)
  subset_ax : ∀ (a : Set') (P : Set' → Prop) (x : Set'), in_set x (subset a P) ↔ (in_set x a ∧ L.Tr (∃ x' : Set', eq_set x x' ∧ P x'))
  infinity_ax1 : L.Tr (in_set empty infinite)
  infinity_ax2 : ∀ x : Set', L.Tr (in_set x infinite) → L.Tr (in_set (union (pair x (pair x x))) infinite)
  power_ax : ∀ a x : Set', in_set x (power a) ↔ (∀ y : Set', in_set y x → in_set y a)

-- Fully skolemized structural form of IZF_R (without sublogic wrappers inside, as in Coq)
structure IZFR (L : Sublogic) where
  Set' : Type
  eq_set : Set' → Set' → Prop
  in_set : Set' → Set' → Prop
  eq_set_ax : ∀ a b : Set', eq_set a b ↔ (∀ x : Set', in_set x a ↔ in_set x b)
  in_reg : ∀ a a' b : Set', eq_set a a' → in_set a b → in_set a' b
  wf_ax : ∀ P : Set' → Prop, (∀ x : Set', (∀ y : Set', in_set y x → P y) → P x) → ∀ x : Set', P x
  empty : Set'
  pair : Set' → Set' → Set'
  union : Set' → Set'
  subset : Set' → (Set' → Prop) → Set'
  infinite : Set'
  power : Set' → Set'
  empty_ax : ∀ x : Set', ¬ in_set x empty
  pair_ax : ∀ a b x : Set', in_set x (pair a b) ↔ (eq_set x a ∨ eq_set x b)
  union_ax : ∀ a x : Set', in_set x (union a) ↔ (∃ y : Set', in_set x y ∧ in_set y a)
  subset_ax : ∀ (a : Set') (P : Set' → Prop) (x : Set'), in_set x (subset a P) ↔ (in_set x a ∧ ∃ x' : Set', eq_set x x' ∧ P x')
  infinity_ax1 : in_set empty infinite
  infinity_ax2 : ∀ x : Set', in_set x infinite → in_set (union (pair x (pair x x))) infinite
  power_ax : ∀ a x : Set', in_set x (power a) ↔ (∀ y : Set', in_set y x → in_set y a)

end CicModel
