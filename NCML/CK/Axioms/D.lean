module

public import NCML.CK.Semantics

@[expose] public section

namespace CK

variable {κ : Type*} {M : Model κ}
variable {x : M.World} {A : BDFormula}

namespace Model

/-- `⊏` is serial: every world has an `⊏`-successor. -/
class SerialMRel (M : Model κ) : Prop where
  serial_mRel : ∀ x : M.World, ∃ y, x ⊏ y

export SerialMRel (serial_mRel)

theorem forces_D_of_serialMRel [M.SerialMRel] : x ⊩[_] (□A 🡒 ◇A) := by
  intro y Ixy hyBoxA u Iyu;
  obtain ⟨z, Muz⟩ := serial_mRel u;
  exact ⟨z, Muz, hyBoxA u z Iyu Muz⟩;

theorem valid_D_of_serialMRel [M.SerialMRel] : M ⊧ (□A 🡒 ◇A) := fun
  _ => forces_D_of_serialMRel

theorem forces_PDia_of_serialMRel [M.SerialMRel] : x ⊩[_] (◇⊤ : BDFormula) := by
  intro y Ixy;
  obtain ⟨z, Mxz⟩ := serial_mRel y;
  exact ⟨z, Mxz, fun w _ h => h⟩;

theorem valid_PDia_of_serialMRel [M.SerialMRel] : M ⊧ (◇⊤ : BDFormula) := fun
  _ => forces_PDia_of_serialMRel

end Model

end CK

end
