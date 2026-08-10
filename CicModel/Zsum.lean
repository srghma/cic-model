-- CicModel/Zsum.lean
import CicModel.ZF

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

-- Ordered couples/pairs can be defined in any Zermelo set theory model:
-- couple x y = pair {x} {x, y}
-- where {x} = pair x x, and {x, y} = pair x y
def z_singl (x : Set' L) : Set' L :=
  pair x x

def z_couple (x y : Set' L) : Set' L :=
  pair (z_singl x) (pair x y)

-- Left and Right disjoint sum injections
def z_inl (x : Set' L) : Set' L :=
  z_couple z_zero x

def z_inr (y : Set' L) : Set' L :=
  z_couple (z_succ z_zero) y

end Zsum

end CicModel
