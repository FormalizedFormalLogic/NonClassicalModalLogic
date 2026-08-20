module

public import NCML.CK.Semantics

@[expose] public section

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

theorem valid_PDia_of_serialMRel [M.SerialMRel] : M ⊧ (◇⊤ : BDFormula) := by
  intro x y Ixy;
  obtain ⟨z, Mxz⟩ := serial_mRel y;
  exact ⟨z, Mxz, fun w _ h => h⟩;

end Model

end CK

end
