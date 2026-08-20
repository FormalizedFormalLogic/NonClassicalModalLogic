module

public import NCML.CK.Axioms.D

@[expose] public section

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

open Model.Forces

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
    refine ⟨z, Mxz, ?_⟩;
    left;
    exact Ixz;

instance [M.AscendingMRel] : M.SerialMRel where
  serial_mRel x := by
    obtain ⟨z, Mxz, _⟩ := ascending_mRel x;
    exact ⟨z, Mxz⟩;

theorem valid_TDia_of_ascendingMRel [M.AscendingMRel] : M ⊧ (A 🡒 ◇A) := by
  intro x y Ixy hyA u Iyu;
  obtain ⟨z, Muz, hz⟩ := ascending_mRel u;
  have huA : u ⊩[_] A := persistent hyA Iyu;
  rcases hz with Iuz | hzFallible;
  · exact ⟨z, Muz, persistent huA Iuz⟩;
  · exact ⟨z, Muz, of_fallible hzFallible⟩;

theorem valid_of_mem_LogicCKTDia [M.AscendingMRel] (hA : A ∈ LogicCKTDia) : M ⊧ A :=
  valid_of_mem_logic (by rintro B ⟨C, rfl⟩; exact valid_TDia_of_ascendingMRel) hA

end Model

/-- Every `⋁K` over the forbidden formulas of a `CK + T◇`-pair `w` stays outside the MP-closure
of `w.th ∪ □⁻¹w.th`. -/
private lemma avoid_disjSet_mdpClosure {w : CanonicalPair { A 🡒 ◇A | (A) }} :
  ∀ C ∈ disjSet w.forb, C ∉ BDTheory.mdpClosure (w.th ∪ □⁻¹w.th) := sorry

/-- The canonical model of `CK + T◇` satisfies the strong ascending condition. -/
instance : (canonicalModel { A 🡒 ◇A | (A) }).StrictlyAscendingMRel := sorry

end CK

/-- The model characterization of `CK + T◇`: a formula is a theorem of `CK + T◇` exactly when it is
valid on every ascending CK-model.

- [Pac24, Problem in §4]
-/
theorem LogicCKTDia.mem_iff_valid {A : BDFormula} :
  A ∈ LogicCKTDia ↔ ∀ {κ : Type 0}, ∀ M : CK.Model κ, [M.AscendingMRel] → M ⊧ A := sorry

/-- The model characterization of `CK + T◇` by the strong ascending condition.

- [Pac24, Problem in §4]
-/
theorem LogicCKTDia.mem_iff_valid_strictlyAscendingMRel {A : BDFormula} :
  A ∈ LogicCKTDia ↔ ∀ {κ : Type 0}, ∀ M : CK.Model κ, [M.StrictlyAscendingMRel] → M ⊧ A := sorry

end
