-- CicModel/Zsum.lean
import CicModel.ZF
import CicModel.Zpairs
import CicModel.Znats

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

end Zsum

end CicModel
