import CicModel.Sublogic

universe u v

class SetTheory (set : Type u) (Tr : Prop → Prop) [SublogicTheory Tr] where
  eq_set : set → set → Prop
  in_set : set → set → Prop
  eq_set_ax : ∀ a b, eq_set a b ↔ (∀ x, in_set x a ↔ in_set x b)
  in_reg : ∀ a a' b, eq_set a a' → in_set a b → in_set a' b

class WfSetTheory (set : Type u) (Tr : Prop → Prop) [SublogicTheory Tr] extends SetTheory set Tr where
  wf_ax : ∀ (P : set → Prop),
    (∀ x, (∀ y, in_set y x → Tr (P y)) → Tr (P x)) →
    ∀ x, Tr (P x)

class ZermeloSig (set : Type u) (Tr : Prop → Prop) [SublogicTheory Tr] extends WfSetTheory set Tr where
  empty : set
  pair : set → set → set
  union : set → set
  subset : set → (set → Prop) → set
  infinite : set
  power : set → set
  empty_ax : ∀ x, in_set x empty → Tr False
  pair_ax : ∀ a b x, in_set x (pair a b) ↔ Tr (eq_set x a ∨ eq_set x b)
  union_ax : ∀ a x, in_set x (union a) ↔ Tr (∃ y, in_set x y ∧ in_set y a)
  subset_ax : ∀ a P x, in_set x (subset a P) ↔ (in_set x a ∧ Tr (∃ x', eq_set x x' ∧ P x'))
  infinity_ax1 : in_set empty infinite
  infinity_ax2 : ∀ x, in_set x infinite → in_set (union (pair x (pair x x))) infinite
  power_ax : ∀ a x, in_set x (power a) ↔ (∀ y, in_set y x → in_set y a)

class IZF_RSig (set : Type u) (Tr : Prop → Prop) [SublogicTheory Tr] extends ZermeloSig set Tr where
  repl : set → (set → set → Prop) → set
  repl_mono : ∀ a a',
    (∀ z, in_set z a → in_set z a') →
    ∀ (R R' : set → set → Prop),
    (∀ x x', eq_set x x' → ∀ y y', eq_set y y' → (R x y ↔ R' x' y')) →
    ∀ z, in_set z (repl a R) → in_set z (repl a' R')
  repl_ax : ∀ a (R : set → set → Prop),
    (∀ x x' y y', in_set x a → eq_set x x' → eq_set y y' → R x y → R x' y') →
    (∀ x y y', in_set x a → R x y → R x y' → eq_set y y') →
    ∀ x, in_set x (repl a R) ↔ Tr (∃ y, in_set y a ∧ R y x)
