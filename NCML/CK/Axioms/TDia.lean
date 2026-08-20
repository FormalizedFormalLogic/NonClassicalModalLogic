module

public import NCML.CK.Axioms.D

@[expose] public section

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

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
    obtain ⟨z, Mxz, Ixz⟩ := strictly_ascending_mRel x;
    exact ⟨z, Mxz, Or.inl Ixz⟩;

instance [M.AscendingMRel] : M.SerialMRel where
  serial_mRel x := by
    sorry

theorem valid_TDia_of_ascendingMRel [M.AscendingMRel] : M ⊧ (A 🡒 ◇A) := by
  sorry

end Model

end CK

end
