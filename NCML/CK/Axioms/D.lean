module

public import NCML.CK.Canonical

@[expose] public section

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

/-- `⊏` is serial: every world has an `⊏`-successor. -/
class SerialMRel (M : Model κ) : Prop where
  serial_mRel : ∀ x : M.World, ∃ y, x ⊏ y

export SerialMRel (serial_mRel)

theorem valid_D_of_serialMRel [M.SerialMRel] : M ⊧ (□A 🡒 ◇A) := by
  intro x y Ixy hyBoxA u Iyu;
  obtain ⟨z, Muz⟩ := serial_mRel u;
  exact ⟨z, Muz, hyBoxA u z Iyu Muz⟩;

theorem valid_PDia_of_serialMRel [M.SerialMRel] : M ⊧ ◇⊤ := by
  intro x y Ixy;
  obtain ⟨z, Mxz⟩ := serial_mRel y;
  exact ⟨z, Mxz, by grind⟩;

theorem valid_of_mem_LogicCKD [M.SerialMRel] (hA : A ∈ LogicCKD) : M ⊧ A :=
  valid_of_mem_logic (by rintro B ⟨C, rfl⟩; exact valid_D_of_serialMRel) hA

theorem valid_of_mem_LogicCKPDia [M.SerialMRel] (hA : A ∈ LogicCKPDia) : M ⊧ A :=
  valid_of_mem_logic (by rintro B rfl; exact valid_PDia_of_serialMRel) hA

end Model

/-- The canonical model of `CK + D` has a serial `⊏`. -/
instance : (canonicalModel { □A 🡒 ◇A | (A) }).SerialMRel := sorry

end CK

/-- The model characterization of `CK + D`: a formula is a theorem of `CK + D` exactly when it is
valid on every CK-model with a serial `⊏`.

- [Pac24, Problem in §4]
-/
theorem LogicCKD.mem_iff_valid {A : BDFormula} :
  A ∈ LogicCKD ↔ ∀ {κ : Type 0}, ∀ M : CK.Model κ, [M.SerialMRel] → M ⊧ A := sorry

/-- The model characterization of `CK + PDia`: a formula is a theorem of `CK + PDia` exactly when
it is valid on every CK-model with a serial `⊏`.

- [Pac24, Problem in §4]
-/
theorem LogicCKPDia.mem_iff_valid {A : BDFormula} :
  A ∈ LogicCKPDia ↔ ∀ {κ : Type 0}, ∀ M : CK.Model κ, [M.SerialMRel] → M ⊧ A := sorry

end
