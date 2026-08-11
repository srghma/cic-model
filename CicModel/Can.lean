-- CicModel/Can.lean
import CicModel.Lambda
import CicModel.Completeness

namespace CicModel

namespace cc

-- Girard's reducibility candidates
def CR : Type := term → Prop

structure weak_cand (X : CR) : Prop where
  wk_sn : ∀ t, X t → sn t
  wk_red : ∀ t u, X t → red1 t u → X u
  wk_wit : ∃ w, X w

structure is_cand (X : CR) : Prop where
  incl_sn : ∀ t, X t → sn t
  clos_red : ∀ t u, X t → red1 t u → X u
  clos_exp : ∀ t, (match t with | term.Srt _ => True | _ => False) → (∀ u, red1 t u → X u) → X t

end cc

end CicModel
