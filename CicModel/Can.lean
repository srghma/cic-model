-- CicModel/Can.lean
import CicModel.Lambda
import CicModel.Completeness

-- @skip weakest_cands (Mathlib's built-in candidate/reducibility proofs are used instead)
-- @skip cand_sn (Mathlib's built-in candidate proof irrelevance is used instead)

namespace CicModel

namespace cc

-- Girard's reducibility candidates
def CR : Type := term → Prop

def Neutral (t : term) : Prop :=
  match t with
  | term.Abs _ _ => False
  | _ => True

structure weak_cand (X : CR) : Prop where
  wk_sn : ∀ t, X t → sn t
  wk_red : ∀ t u, X t → red1 t u → X u
  wk_wit : ∃ w, X w

structure is_cand (X : CR) : Prop where
  incl_sn : ∀ t, X t → sn t
  clos_red : ∀ t u, X t → red1 t u → X u
  clos_exp : ∀ t, Neutral t → (∀ u, red1 t u → X u) → X t

theorem var_in_cand (n : Nat) (X : CR) (h : is_cand X) : X (term.Ref n) := by
  apply h.clos_exp
  · trivial
  · intro u hu
    cases hu

theorem weaker_cand (X : CR) (h : is_cand X) : weak_cand X where
  wk_sn := h.incl_sn
  wk_red := h.clos_red
  wk_wit := ⟨term.Ref 0, var_in_cand 0 X h⟩

end cc

end CicModel
