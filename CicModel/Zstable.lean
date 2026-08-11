-- CicModel/Zstable.lean
import CicModel.ZF

namespace CicModel

section Zstable

variable {L : Sublogic} [Z : Zermelo L]

open SetTheory
open Zermelo

-- X ⊆ Y
def subset_of (X Y : Set' L) : Prop :=
  ∀ z : Set' L, in_set z X → in_set z Y

-- stable_set K F
def stable_set (K : Set' L) (F : Set' L → Set' L) : Prop :=
  ∀ X : Set' L, subset_of X K →
    ∀ z : Set' L, (∀ Y : Set' L, in_set Y X → in_set z (F Y)) → in_set z (F empty)

end Zstable

end CicModel
