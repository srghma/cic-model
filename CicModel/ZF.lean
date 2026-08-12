import CicModel.Sublogic
import CicModel.ZFdef
import CicModel.Z

set_option quotPrecheck false

universe u

namespace ZF

section ZFTheory

variable {set : Type u} {Tr_ : Prop → Prop} [SublogicTheory Tr_] [IZF_RSig set Tr_]

local infix:40 "~≈" => @SetTheory.eq_set set Tr_ _ _
local infix:40 "~⋴" => @SetTheory.in_set set Tr_ _ _

-- Structural structure of Intuitionistic Zermelo-Fraenkel Set Theory with Replacement
structure Izfr where
  set' : Type u
  eq_set' : set' → set' → Prop
  in_set' : set' → set' → Prop

def replf (Tr : Prop → Prop) [SublogicTheory Tr] [IZF_RSig set Tr] (a : set) (F : set → set) : set :=
  @IZF_RSig.repl set Tr _ _ a (fun x y => (∀ u v, @SetTheory.eq_set set Tr _ _ u v → @SetTheory.eq_set set Tr _ _ (F u) (F v)) ∧ @SetTheory.eq_set set Tr _ _ y (F x))

def sup (Tr : Prop → Prop) [SublogicTheory Tr] [IZF_RSig set Tr] (x : set) (F : set → set) : set :=
  @ZermeloSig.union set Tr _ _ (replf Tr x F)

local notation "replf" => replf Tr_
local notation "sup" => sup Tr_

theorem replf_ax (a : set) (F : set → set) (z : set) :
    z ~⋴ (replf a F) ↔ Tr_ (∃ x, x ~⋴ a ∧ (∀ u v, u ~≈ v → F u ~≈ F v) ∧ z ~≈ F x) := by
  sorry

theorem sup_ax (x : set) (F : set → set) (z : set) :
    z ~⋴ (sup x F) ↔ Tr_ (∃ y, z ~⋴ y ∧ y ~⋴ (replf x F)) := by
  sorry

end ZFTheory

end ZF
