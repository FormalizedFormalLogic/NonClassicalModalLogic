module

public import NCML.CK.Axioms.D

@[expose] public section

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

open CK.Frame

lemma valid_PDia_of_serialMRel [M.SerialMRel] : M ⊧ ◇⊤ := by
  intro x y Ixy;
  obtain ⟨z, Mxz⟩ := serial_mRel y;
  exact ⟨z, Mxz, by grind⟩;

lemma valid_of_mem_LogicCKPDia [M.SerialMRel] (hA : A ∈ LogicCKPDia) : M ⊧ A :=
  valid_of_mem_logic (by rintro B rfl; exact valid_PDia_of_serialMRel) hA

end Model

namespace Frame

variable {F : Frame κ}

lemma valid_PDia_of_serialMRel [F.SerialMRel] : F ⊧ ◇⊤ :=
  fun _ _ _ => Model.valid_PDia_of_serialMRel

lemma serialMRel_of_valid_PDia (h : F ⊧ ◇⊤) : F.SerialMRel where
  serial_mRel x := by
    let M : Model κ := {
      toFrame := F,
      val := fun _ _ => True,
      val_persistent := by intros; trivial,
      fallible_val := by intros; trivial,
    }
    obtain ⟨z, Mxz, -⟩ := h M.val M.val_persistent M.fallible_val x x (refl x);
    exact ⟨z, Mxz⟩;

/-- `P◇` defines the frames whose `⊏` is serial. -/
theorem serialMRel_iff_valid_PDia : F.SerialMRel ↔ F ⊧ (◇⊤ : BDFormula) := by
  constructor;
  . intro _; exact valid_PDia_of_serialMRel;
  . exact serialMRel_of_valid_PDia;

lemma valid_D_iff_valid_PDia : (∀ A : BDFormula, F ⊧ (□A 🡒 ◇A)) ↔ F ⊧ (◇⊤ : BDFormula) := by
  constructor;
  . intro h; have := serialMRel_of_valid_D (h (#0)); exact valid_PDia_of_serialMRel;
  . intro h; have := serialMRel_of_valid_PDia h; exact fun A => valid_D_of_serialMRel;

end Frame

end CK

end
