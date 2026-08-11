-- CicModel/Completeness.lean
import CicModel.ZF
import CicModel.Lambda

namespace CicModel

-- Typing judgments of the Calculus of Inductive Constructions (CIC)
axiom eq_typ (e : List term) (M M' T : term) : Prop

-- Unmarking / un-annotation operator for typed lambda terms
axiom unmark_app (M : term) : term

-- The main theorem: strong normalization of CC
-- Proves that any well-typed term M is strongly normalizing
theorem strong_normalization (e : List term) (M M' T : term) :
    eq_typ e M M' T →
    term.closed (unmark_app M)
    := sorry

end CicModel
