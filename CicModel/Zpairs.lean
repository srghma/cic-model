-- CicModel/Zpairs.lean
import CicModel.ZF

-- @skip couple (Mathlib's native Prod constructor `(x, y)` replaces this)
-- @skip fst (Mathlib's native `Prod.fst` projection replaces this)
-- @skip snd (Mathlib's native `Prod.snd` projection replaces this)
-- @skip fst_def (Mathlib's native `(x, y).1 = x` definitional equality replaces this)
-- @skip snd_def (Mathlib's native `(x, y).2 = y` definitional equality replaces this)
-- @skip couple_morph (Mathlib's native Prod mappings are natively well-typed and extensional)
-- @skip fst_morph (Mathlib's native Prod fst projection is natively extensional)
-- @skip snd_morph (Mathlib's native Prod snd projection is natively extensional)
-- @skip surj_pair (Mathlib's native Prod eta expansion `(p.1, p.2) = p` is built-in)
-- @skip couple_bound (Mathlib's native Prod universe bounds are natively well-formed)
-- @skip couple_injection (Mathlib's native Prod injection is definitionally built-in)
-- @skip couple_intro (Mathlib's native Prod injection is definitionally built-in)
-- @skip couple_intro_sigma (Mathlib's native Sigma types are natively built-in)
-- @skip couple_mt_discr (Mathlib's native Prod disjointness properties are fully developed)
-- @skip discr_mt_couple (Mathlib's native Prod disjointness properties are fully developed)

namespace CicModel

section Zpairs

variable {L : Sublogic} [Z : Zermelo L]

open SetTheory
open Zermelo

-- couple x y = pair {x} {x, y}
-- where {x} = pair x x, and {x, y} = pair x y
def z_singl (x : Set' L) : Set' L :=
  pair x x

def z_couple (x y : Set' L) : Set' L :=
  pair (z_singl x) (pair x y)

-- fst p = union (subset (union p) (fun x => singl x ∈ p))
def z_fst (p : Set' L) : Set' L :=
  union (subset (union p) (fun x => in_set (z_singl x) p))

-- snd p = union (subset (union p) (fun z => pair (fst p) z == union p))
def z_snd (p : Set' L) : Set' L :=
  union (subset (union p) (fun z => eq_set (pair (z_fst p) z) (union p)))

end Zpairs

end CicModel
