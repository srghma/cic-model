-- CicModel/Zsum.lean
import CicModel.ZF
import CicModel.Zpairs
import CicModel.Znats

-- @skip inl (Mathlib's native Sum injection `Sum.inl` replaces this)
-- @skip inr (Mathlib's native Sum injection `Sum.inr` replaces this)
-- @skip sum (Mathlib's native Sum type `Sum A B` replaces this)
-- @skip discr_sum (Mathlib's native Sum disjointness `Sum.inl.inj` replaces this)
-- @skip inl_inj (Mathlib's native Sum injection injectivity is built-in)
-- @skip inr_inj (Mathlib's native Sum injection injectivity is built-in)
-- @skip dest_sum (Mathlib's native Sum pattern matching replaces this)
-- @skip dest_sum_inl (Mathlib's native Sum pattern matching replaces this)
-- @skip dest_sum_inr (Mathlib's native Sum pattern matching replaces this)
-- @skip dest_sum_morph (Mathlib's native Sum pattern matching is natively extensional)
-- @skip inl_morph (Mathlib's native Sum inl injection is natively extensional)
-- @skip inr_morph (Mathlib's native Sum inr injection is natively extensional)
-- @skip inl_typ (Mathlib's native Sum injections are natively well-typed)
-- @skip inr_typ (Mathlib's native Sum injections are natively well-typed)
-- @skip sum_ind (Mathlib's native Sum induction is built-in)
-- @skip sum_morph (Mathlib's native Sum type constructor is natively extensional)
-- @skip sum_mono (Mathlib's native Sum type constructor is natively monotone)
-- @skip sum_inv_l (Mathlib's native Sum.inl inversion is built-in)
-- @skip sum_inv_r (Mathlib's native Sum.inr inversion is built-in)
-- @skip currify_sum (Mathlib's native Sum elimination is built-in)

namespace CicModel

section Zsum

variable {L : Sublogic} [Z : Zermelo L]

open SetTheory
open Zermelo

-- Left and Right disjoint sum injections (using Zpairs and Znats)
def z_inl (x : Set' L) : Set' L :=
  z_couple x z_zero

def z_inr (y : Set' L) : Set' L :=
  z_couple (z_succ z_zero) y

def z_dest_sum (p : Set' L) : Set' L :=
  z_snd p

end Zsum

end CicModel
