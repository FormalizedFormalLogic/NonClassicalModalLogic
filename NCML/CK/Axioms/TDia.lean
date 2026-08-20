module

public import NCML.CK.Axioms.D

@[expose] public section

namespace CK

variable {κ : Type*} {M : Model κ}
variable {x : M.World} {A : BDFormula}

namespace Model

/-- Condition (C): every world has an `⊏`-successor that is either an
`≼`-successor of the source or fallible. -/
class AscendingMRel (M : Model κ) : Prop where
  ascending_mRel : ∀ x : M.World, ∃ z, x ⊏ z ∧ (x ≼ z ∨ M.Fallible z)

export AscendingMRel (ascending_mRel)

/-- Condition (C′): every world has an `≼`-successor with an `⊏`-edge back to it. -/
class StrictlyAscendingMRel (M : Model κ) : Prop where
  strictly_ascending_mRel : ∀ x : M.World, ∃ z, x ⊏ z ∧ x ≼ z

export StrictlyAscendingMRel (strictly_ascending_mRel)

instance [M.StrictlyAscendingMRel] : M.AscendingMRel where
  ascending_mRel x := by
    sorry

instance [M.AscendingMRel] : M.SerialMRel where
  serial_mRel x := by
    sorry

theorem forces_TDia_of_ascendingMRel [M.AscendingMRel] : x ⊩[_] (A 🡒 ◇A) := by
  sorry

theorem valid_TDia_of_ascendingMRel [M.AscendingMRel] : M ⊧ (A 🡒 ◇A) := fun
  _ => forces_TDia_of_ascendingMRel

end Model

end CK

end
