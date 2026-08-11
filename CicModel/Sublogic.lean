universe u

class Sublogic (Tr : Prop → Prop) where
  TrI : ∀ {P : Prop}, P → Tr P
  TrP : ∀ {P : Prop}, Tr (Tr P) → Tr P
  TrMono : ∀ {P Q : Prop}, (P → Q) → Tr P → Tr Q

def isL (Tr : Prop → Prop) (P : Prop) : Prop := Tr P → P

class SublogicTheory (Tr : Prop → Prop) extends Sublogic Tr where
  TrB : ∀ {P Q : Prop}, Tr P → (P → Tr Q) → Tr Q := fun hp f ↦ TrP (TrMono f hp)
  Tr_morph : ∀ {P Q : Prop}, (P ↔ Q) → (Tr P ↔ Tr Q)
  and_isL : ∀ {P Q : Prop}, isL Tr P → isL Tr Q → isL Tr (P ∧ Q)
  fa_isL : ∀ {A : Type u} {P : A → Prop}, (∀ x, isL Tr (P x)) → isL Tr (∀ x, P x)
  imp_isL : ∀ {P Q : Prop}, isL Tr Q → isL Tr (P → Q)

-- Universal theorems for any sublogic
section General

variable {Tr : Prop → Prop} [S : Sublogic Tr]

theorem Tr_isL (P : Prop) : isL Tr (Tr P) :=
  fun h_tr_tr_p ↦ S.TrP h_tr_tr_p

end General

theorem T_isL (Tr : Prop → Prop) (P : Prop) (hp : P) : isL Tr P :=
  fun _ ↦ hp

-- 1. Identity Sublogic (represents standard Prop)
def IdTr (P : Prop) : Prop := P

instance : Sublogic IdTr where
  TrI p := p
  TrP p := p
  TrMono f p := f p

instance : SublogicTheory IdTr where
  Tr_morph h := h
  and_isL _ _ hpq := hpq
  fa_isL _ h_fa := h_fa
  imp_isL _ h_imp := h_imp

-- 2. Double Negation Sublogic
def DNTr (P : Prop) : Prop := ¬¬P

instance : Sublogic DNTr where
  TrI p := fun hn ↦ hn p
  TrP p := fun h_not_p ↦ p (fun h_not_not_p ↦ h_not_not_p h_not_p)
  TrMono f p := fun h_not_q ↦ p (fun h_not_p ↦ h_not_q (f h_not_p))

instance : SublogicTheory DNTr where
  Tr_morph h := by
    dsimp [DNTr]
    rw [h]
  and_isL hP hQ := by
    dsimp [isL, DNTr] at *
    intro h_not_not_pq
    constructor
    · apply hP
      intro h_not_p
      apply h_not_not_pq
      intro hpq
      exact h_not_p hpq.1
    · apply hQ
      intro h_not_q
      apply h_not_not_pq
      intro hpq
      exact h_not_q hpq.2
  fa_isL {A} {P} hP := by
    dsimp [isL, DNTr] at *
    intro h_not_not_fa x
    apply hP
    intro h_not_px
    apply h_not_not_fa
    intro h_fa
    exact h_not_px (h_fa x)
  imp_isL {P} {Q} hQ := by
    dsimp [isL, DNTr] at *
    intro h_not_not_imp hp
    apply hQ
    intro h_not_q
    apply h_not_not_imp
    intro h_imp
    exact h_not_q (h_imp hp)
