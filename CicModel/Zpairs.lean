import CicModel.Sublogic
import CicModel.ZFdef
import CicModel.Z

set_option quotPrecheck false

universe u

namespace Z

section ZpairsTheory

variable {set : Type u} {Tr_ : Prop → Prop} [SublogicTheory Tr_] [ZermeloSig set Tr_]

local infix:40 "~≈" => @SetTheory.eq_set set Tr_ _ _
local infix:40 "~⋴" => @SetTheory.in_set set Tr_ _ _

local notation "empty" => @ZermeloSig.empty set Tr_ _ _
local notation "pair" => @ZermeloSig.pair set Tr_ _ _
local notation "union" => @ZermeloSig.union set Tr_ _ _
local notation "subset" => @ZermeloSig.subset set Tr_ _ _
local notation "infinite" => @ZermeloSig.infinite set Tr_ _ _
local notation "power" => @ZermeloSig.power set Tr_ _ _

local notation x " ~⊆ " y => incl_set x y
local notation x " ~∪ " y => Z.union2 x y

-- Ordered pairs untyped operations

def couple (x y : set) : set := pair (Z.singl x) (pair x y)

theorem couple_bound (a b : set) : (couple a b) ~⊆ (power (power (a ~∪ b))) := by
  sorry

theorem union_couple_eq (a b : set) : union (couple a b) ~≈ pair a b := by
  sorry

theorem discr_mt_couple (a b : set) : ¬ empty ~≈ couple a b := by
  sorry

def fst (p : set) : set := union (subset (union p) (fun x => (Z.singl x) ~⋴ p))

theorem fst_def (x y : set) : fst (couple x y) ~≈ x := by
  sorry

theorem fst_mt : fst empty ~≈ empty := by
  sorry

def snd (p : set) : set :=
  union (subset (union p) (fun z => pair (fst p) z ~≈ union p))

theorem snd_def (x y : set) : snd (couple x y) ~≈ y := by
  sorry

theorem couple_mt_discr (a b : set) : ¬ couple a b ~≈ empty := by
  sorry

theorem couple_injection (x y x' y' : set) :
    couple x y ~≈ couple x' y' → (x ~≈ x' ∧ y ~≈ y') := by
  sorry

def isCouple (c : set) : Prop := c ~≈ couple (fst c) (snd c)

theorem isCouple_couple (a b : set) : isCouple (couple a b) := by
  sorry

-- Cartesian products

def prodcart (A B : set) : set :=
  subset (power (power (A ~∪ B)))
    (fun x => ∃ a, a ~⋴ A ∧ ∃ b, b ~⋴ B ∧ x ~≈ couple a b)

theorem prodcart_bound (A B : set) : prodcart A B ~⊆ power (power (A ~∪ B)) := by
  sorry

theorem prodcart_ax (A B z : set) :
    z ~⋴ prodcart A B ↔ (isCouple z ∧ fst z ~⋴ A ∧ snd z ~⋴ B) := by
  sorry

theorem couple_intro (x y A B : set) :
    x ~⋴ A → y ~⋴ B → couple x y ~⋴ prodcart A B := by
  sorry

theorem surj_pair (p A B : set) :
    p ~⋴ prodcart A B → p ~≈ couple (fst p) (snd p) := by
  sorry

theorem fst_typ (p A B : set) : p ~⋴ prodcart A B → fst p ~⋴ A := by
  sorry

theorem snd_typ (p A B : set) : p ~⋴ prodcart A B → snd p ~⋴ B := by
  sorry

end ZpairsTheory

end Z
