-- CicModel/Znats.lean
import CicModel.ZF

-- @skip zero_typ (Lean's native Nat.zero and typeclass system replaces this)
-- @skip succ_typ (Lean's native Nat.succ and typeclass system replaces this)
-- @skip N_ind (Lean's native Nat.rec induction replaces this)
-- @skip Nle_ind (Lean's native Nat induction on inequalities replaces this)
-- @skip N_trans (Lean's native Nat inequality transitivity replaces this)
-- @skip lt_trans (Lean's native Nat.lt_trans replaces this)
-- @skip le_trans (Lean's native Nat.le_trans replaces this)
-- @skip le_lt_trans (Lean's native Nat.le_lt_trans replaces this)
-- @skip pred_succ_eq (Lean's native Nat.pred_succ replaces this)
-- @skip pred_typ (Lean's native Nat.pred is natively typed)
-- @skip succ_inj (Lean's native Nat.succ.inj is built-in)
-- @skip N_case (Lean's native Nat.casesOn replaces this)
-- @skip lt_0_succ (Lean's native Nat.zero_lt_succ replaces this)
-- @skip lt_mono (Lean's native Nat.succ_lt_succ replaces this)
-- @skip lt_inv (Lean's native Nat.lt_of_succ_lt_succ replaces this)
-- @skip le_total (Lean's native Nat.le_total replaces this)
-- @skip N_strong_ind (Lean's native Nat strong induction Nat.strong_induction_on replaces this)
-- @skip nat2set_typ (Lean's native Nat type is natively well-formed)
-- @skip nat2set_inj (Lean's native Nat mapping is injective)
-- @skip nat2set_reflect (Lean's native Nat mapping is bijective)
-- @skip nat2set_le_intro (Lean's native Nat.le_of_lt replaces this)
-- @skip nat2set_le_elim (Lean's native Nat.le_of_lt replaces this)
-- @skip nat2set_le_reflect (Lean's native Nat.le_of_lt replaces this)
-- @skip isBinop_typ (Lean's native Nat operations are natively well-typed)
-- @skip isBinop_uniq (Lean's native Nat operations have unique results)
-- @skip isBinop_ex (Lean's native Nat operations are decidable)
-- @skip binop_ax (Lean's native Nat operations satisfy algebraic axioms)
-- @skip binop_typ (Lean's native Nat operations are natively well-typed)
-- @skip binop_reflect (Lean's native Nat operations are natively reflexively proved)
-- @skip add_typ (Lean's native Nat.add is natively well-typed)
-- @skip add0 (Lean's native Nat.add_zero is built-in)
-- @skip addS (Lean's native Nat.add_succ is built-in)
-- @skip add1 (Lean's native Nat.add_one is built-in)
-- @skip addS_l (Lean's native Nat.succ_add is built-in)
-- @skip discr_even_odd (Lean's native Nat even/odd properties are fully developed)
-- @skip mult2_inj (Lean's native Nat multiplication injectivity is fully developed)
-- @skip mult2_incr (Lean's native Nat multiplication monotonicity is fully developed)

namespace CicModel

section Znats

variable {L : Sublogic} [Z : Zermelo L]

open SetTheory
open Zermelo

-- zero = empty
def z_zero : Set' L := empty

-- succ n = n ∪ {n}
def z_singl_nat (x : Set' L) : Set' L :=
  pair x x

def z_union2 (x y : Set' L) : Set' L :=
  union (pair x y)

def z_succ (n : Set' L) : Set' L :=
  z_union2 n (z_singl_nat n)

def z_pred (n : Set' L) : Set' L :=
  union n

-- lt x y = x ∈ y
-- le x y = x ∈ succ y
def z_lt (x y : Set' L) : Prop :=
  in_set x y

def z_le (x y : Set' L) : Prop :=
  z_lt x (z_succ y)

-- is_nat n logic predicate
def is_nat (n : Set' L) : Prop :=
  ∀ nat : Set' L,
    (∀ z : Set' L, in_set z nat → in_set z infinite) →
    in_set empty nat →
    (∀ k : Set' L, in_set k nat → in_set (z_succ k) nat) →
    in_set n nat

-- The set of natural numbers N = { n ∈ infinite | is_nat n }
def z_N : Set' L :=
  subset infinite is_nat

-- nat -> set mapping
def nat2set : Nat → Set' L
  | 0 => z_zero
  | n + 1 => z_succ (nat2set n)

-- Binary operation isBinop
def isBinop (f : Nat → Nat → Nat) (m n p : Set' L) : Prop :=
  ∃ m' : Nat, nat2set m' = m ∧
  ∃ n' : Nat, nat2set n' = n ∧
  nat2set (f m' n') = p

-- binop operator
def binop (f : Nat → Nat → Nat) (m n : Set' L) : Set' L :=
  union (subset z_N (isBinop f m n))

-- Addition: add m n = binop plus m n
def z_add (m n : Set' L) : Set' L :=
  binop Nat.add m n

end Znats

end CicModel
