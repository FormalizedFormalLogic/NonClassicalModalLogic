module

public import NCML.CK.Logic.CKD

/-! A CK-model with a serial `⊏` on which `∼◇⊥` fails. -/

@[expose] public section

namespace CK

open Model BDFormula

namespace SerialMRel

def counterModel : Model (Fin 2) where
  iRel' x y := x = y
  iRel_preorder := {
    refl := by grind,
    trans := by grind
  }
  mRel' x y := x ≤ y
  Fallible' x := x = 1
  fallible_iRel' := by grind
  fallible_mRel' := by omega
  fallible_exists_mRel' := fun _ => ⟨1, by omega⟩
  val _ _ := True
  val_persistent := by grind
  fallible_val := by grind

instance : counterModel.SerialMRel where
  serial_mRel x := ⟨x, le_refl x⟩

lemma counterModel_not_forces : 0 ⊮[counterModel] ∼◇⊥ := by
  intro h;
  have h₁ : 0 ⊩[counterModel] ◇⊥ := fun y _ => ⟨1, Fin.le_last y, rfl⟩;
  have h₂ : (0 : Fin 2) = 1 := h 0 rfl h₁;
  contradiction;

end SerialMRel

lemma exists_serialMRel_not_forces_N :
  ∃ (κ : Type) (M : Model κ), M.SerialMRel ∧ ∃ x : M.World, x ⊮[_] ∼◇⊥ :=
  ⟨Fin 2, SerialMRel.counterModel, inferInstance, 0, SerialMRel.counterModel_not_forces⟩

end CK

theorem LogicCKD.not_provable_N : (∼◇⊥) ∉ LogicCKD :=
  fun h => CK.SerialMRel.counterModel_not_forces (CK.Model.valid_of_mem_LogicCKD h 0)

end
