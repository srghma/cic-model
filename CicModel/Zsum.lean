-- CicModel/Zsum.lean
import CicModel.ZF
import CicModel.Zpairs

namespace CicModel

section Zsum

variable {L : Sublogic} [Z : Zermelo L]

open SetTheory
open Zermelo

-- Zero and successor can be defined in any Zermelo set theory model:
-- zero = empty
-- succ x = union (pair x (pair x x))
def z_zero : Set' L := empty

def z_succ (x : Set' L) : Set' L :=
  union (pair x (pair x x))

-- Left and Right disjoint sum injections (using Zpairs)
def z_inl (x : Set' L) : Set' L :=
  z_couple x z_zero

def z_inr (y : Set' L) : Set' L :=
  z_couple (z_succ z_zero) y

end Zsum

end CicModel
