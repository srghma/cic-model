universe u v

class HOLogic (prop : Type u) where
  TT : prop
  FF : prop
  Not : prop → prop
  Imp : prop → prop → prop
  And : prop → prop → prop
  Or : prop → prop → prop
  Forall : {A : Type v} → (A → prop) → prop
  Exist : {A : Type v} → (A → prop) → prop
  holds : prop → Prop
  rTT : holds TT
  rFF : ∀ P, holds FF → holds P
  rAnd : ∀ P Q, holds (And P Q) ↔ holds P ∧ holds Q
  rImp : ∀ P Q, holds (Imp P Q) ↔ (holds P → holds Q)
  rForall : ∀ {A : Type v} (P : A → prop), holds (Forall P) ↔ ∀ x : A, holds (P x)
  rNot : ∀ P, holds (Not P) ↔ (holds P → holds FF)
  rOrI : ∀ P Q, holds P ∨ holds Q → holds (Or P Q)
  rOrE : ∀ P Q C, (holds P ∨ holds Q → holds C) → holds (Or P Q) → holds C
  rExI : ∀ {A : Type v} (P : A → prop), (∃ x : A, holds (P x)) → holds (Exist P)
  rExE : ∀ {A : Type v} (P : A → prop) C, (∀ x : A, holds (P x) → holds C) → holds (Exist P) → holds C

class ConsistentLogic (prop : Type u) [HOLogic prop] : Prop where
  rCons : ¬ HOLogic.holds (HOLogic.FF : prop)

class IntuitionisticLogic (prop : Type u) [HOLogic prop] [ConsistentLogic prop] where
  Atom : Prop → prop
  rAtom : ∀ P : Prop, HOLogic.holds (Atom P) ↔ P

structure NegProp (prop : Type u) [H : HOLogic prop] where
  nnf : prop
  nnh : ((H.holds nnf → H.holds H.FF) → H.holds H.FF) → H.holds nnf

namespace NegProp

variable {prop : Type u} [H : HOLogic prop]

def holds (P : NegProp prop) : Prop :=
  H.holds P.nnf

def TT : NegProp prop where
  nnf := H.TT
  nnh _ := H.rTT

def FF : NegProp prop where
  nnf := H.FF
  nnh h := h id

def Imp (P Q : NegProp prop) : NegProp prop where
  nnf := H.Imp P.nnf Q.nnf
  nnh h := by
    rw [H.rImp] at *
    intro hp
    apply Q.nnh
    intro hq
    apply h
    intro h_imp
    apply hq
    apply h_imp
    exact hp

def Not (P : NegProp prop) : NegProp prop :=
  Imp P FF

def And (P Q : NegProp prop) : NegProp prop where
  nnf := H.And P.nnf Q.nnf
  nnh h := by
    rw [H.rAnd] at *
    constructor
    · apply P.nnh
      intro h_not_p
      apply h
      intro h_and
      exact h_not_p h_and.1
    · apply Q.nnh
      intro h_not_q
      apply h
      intro h_and
      exact h_not_q h_and.2

end NegProp
