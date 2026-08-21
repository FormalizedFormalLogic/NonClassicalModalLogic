module

public import NCML.CK.Logic.CKTBox
public import NCML.CK.Countermodel.SerialMRel

/-! CK-models refuting `◇⊤`, `D` and `∼◇⊥` over `CK + T□`. -/

@[expose] public section

namespace CK

open Model BDFormula

namespace ReturningMRel

def counterModel : Model (Fin 2) where
  iRel' x y := x ≤ y
  iRel_preorder := { refl := by grind, trans := by omega }
  mRel' x _ := x = 1
  Fallible' _ := False
  fallible_iRel' := by grind
  fallible_mRel' := by grind
  fallible_exists_mRel' := by grind
  val _ _ := True
  val_persistent := by grind
  fallible_val := by grind

instance : counterModel.ReturningMRel where
  returning_mRel x := ⟨1, Fin.le_last x, rfl⟩

lemma counterModel_not_serialMRel : ¬counterModel.SerialMRel := by
  rintro ⟨h⟩;
  obtain ⟨y, My⟩ := h 0;
  simp_all [counterModel, Frame.mRel];

lemma counterModel_not_forces_PDia : 0 ⊮[counterModel] ◇⊤ := by
  intro h;
  obtain ⟨z, Mz, -⟩ := h 0 (le_refl 0);
  simp_all [counterModel, Frame.mRel];

lemma counterModel_not_forces_D : 0 ⊮[counterModel] (□⊤ 🡒 ◇⊤) :=
  fun h => counterModel_not_forces_PDia (h 0 (le_refl 0) fun _ _ _ _ => forces_top)

end ReturningMRel

instance : SerialMRel.counterModel.ReturningMRel where
  returning_mRel x := ⟨x, rfl, le_refl x⟩

theorem exists_returningMRel_not_serialMRel :
  ∃ (κ : Type) (M : Model κ), M.ReturningMRel ∧ ¬ M.SerialMRel :=
  ⟨Fin 2, ReturningMRel.counterModel, inferInstance, ReturningMRel.counterModel_not_serialMRel⟩

lemma exists_tBox_not_forces_N :
  ∃ (κ : Type) (M : Model κ), M.TBox ∧ ∃ x : M.World, x ⊮[_] ∼◇⊥ :=
  ⟨Fin 2, SerialMRel.counterModel, inferInstance, 0, SerialMRel.counterModel_not_forces⟩

end CK

theorem LogicCKTBox.not_provable_PDia : ◇⊤ ∉ LogicCKTBox :=
  fun h => CK.ReturningMRel.counterModel_not_forces_PDia (CK.Model.valid_of_mem_LogicCKTBox h 0)

lemma LogicCKTBox.not_provable_D : □⊤ 🡒 ◇⊤ ∉ LogicCKTBox :=
  fun h => CK.ReturningMRel.counterModel_not_forces_D (CK.Model.valid_of_mem_LogicCKTBox h 0)

theorem LogicCKTBox.not_provable_N : ∼◇⊥ ∉ LogicCKTBox :=
  fun h => CK.SerialMRel.counterModel_not_forces (CK.Model.valid_of_mem_LogicCKTBox h 0)

end
