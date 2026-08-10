-- CicModel/Zpairs.lean
import CicModel.ZF

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
