-- CicModel/Sublogic.lean

namespace CicModel

class Sublogic where
  Tr : Prop → Prop
  TrI : ∀ {P : Prop}, P → Tr P
  TrP : ∀ {P : Prop}, Tr (Tr P) → Tr P
  TrMono : ∀ {P Q : Prop}, (P → Q) → Tr P → Tr Q

open Sublogic

def isL [L : Sublogic] (P : Prop) : Prop :=
  L.Tr P → P

theorem Tr_isL [L : Sublogic] (P : Prop) : isL (L.Tr P) :=
  fun h => L.TrP h

theorem T_isL [L : Sublogic] {P : Prop} (hp : P) : isL P :=
  fun _ => hp

theorem and_isL [L : Sublogic] {P Q : Prop} (hP : isL P) (hQ : isL Q) : isL (P ∧ Q) :=
  fun h =>
    ⟨hP (L.TrMono (fun ⟨hp, _⟩ => hp) h),
     hQ (L.TrMono (fun ⟨_, hq⟩ => hq) h)⟩

theorem fa_isL [L : Sublogic] {A : Type} {P : A → Prop} (hP : ∀ x, isL (P x)) : isL (∀ x, P x) :=
  fun h x => hP x (L.TrMono (fun hfa => hfa x) h)

theorem imp_isL [L : Sublogic] {P Q : Prop} (hQ : isL Q) : isL (P → Q) :=
  fun h hp => hQ (L.TrMono (fun hf => hf hp) h)

theorem iff_isL [L : Sublogic] {P Q : Prop} (hP : isL P) (hQ : isL Q) : isL (P ↔ Q) := by
  intro h
  constructor
  · intro hp
    exact hQ (L.TrMono (fun h_iff => h_iff.mp hp) h)
  · intro hq
    exact hP (L.TrMono (fun h_iff => h_iff.mpr hq) h)

theorem rFF [L : Sublogic] (Q : Prop) : L.Tr False → L.Tr Q :=
  L.TrMono (fun h => False.elim h)

theorem rFF' [L : Sublogic] (Q : Prop) (hQ : isL Q) : L.Tr False → Q :=
  fun h => hQ (rFF Q h)

def Tnot [L : Sublogic] (P : Prop) : Prop :=
  P → L.Tr False

-- Concrete instances
-- 1. CoqSublogic (Standard Lean Intuitionistic/Classical Logic)
instance CoqSublogic : Sublogic where
  Tr P := P
  TrI hp := hp
  TrP h := h
  TrMono f h := f h

-- 2. ClassicSublogic (Double negation translation)
instance ClassicSublogic : Sublogic where
  Tr P := ¬¬P
  TrI hp := fun h => h hp
  TrP h := fun hnP => h (fun hnP' => hnP' hnP)
  TrMono f hnnp := fun hnq => hnnp (fun p => hnq (f p))

-- 3. ASublogic (Friedman's A-translation)
@[reducible]
def ASublogic (A : Prop) : Sublogic where
  Tr P := P ∨ A
  TrI hp := Or.inl hp
  TrP h :=
    match h with
    | Or.inl (Or.inl hp) => Or.inl hp
    | Or.inl (Or.inr ha) => Or.inr ha
    | Or.inr ha => Or.inr ha
  TrMono f h :=
    match h with
    | Or.inl hp => Or.inl (f hp)
    | Or.inr ha => Or.inr ha

end CicModel
