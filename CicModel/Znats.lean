-- CicModel/Znats.lean
import CicModel.ZF

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
