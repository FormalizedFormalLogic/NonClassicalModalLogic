module

public import NCML.CK.Axioms.TDia
public import NCML.CK.Countermodel.D

/-! CK-models refuting `T◇` over `CK + D`, and `∼◇⊥` over `CK + T◇`. -/

@[expose] public section

namespace CK

open Model BDFormula

namespace TDia

def counterModel : Model (Fin 2) where
  iRel' x y := x = y
  iRel_preorder := { refl := by grind, trans := by grind }
  mRel' _ y := y = 1
  Fallible' _ := False
  fallible_iRel' := by grind
  fallible_mRel' := by grind
  fallible_exists_mRel' := by grind
  val x _ := x = 0
  val_persistent := by grind
  fallible_val := by grind

instance : counterModel.SerialMRel where
  serial_mRel _ := ⟨1, rfl⟩

lemma counterModel_not_ascendingMRel : ¬ counterModel.AscendingMRel := by
  rintro ⟨h⟩;
  obtain ⟨z, Mz, hz⟩ := h 0;
  simp_all [counterModel, Model.iRel, Model.mRel, Model.Fallible];

lemma counterModel_not_forces : (0 : counterModel.World) ⊮[_] (#0 🡒 ◇(#0)) := by
  intro h;
  obtain ⟨z, Mz, hz⟩ := h 0 rfl rfl 0 rfl;
  simp_all [counterModel, Model.mRel, Model.Forces];

end TDia

instance : D.counterModel.StrictlyAscendingMRel where
  strictly_ascending_mRel x := ⟨x, le_refl x, rfl⟩

theorem exists_serialMRel_not_ascendingMRel :
  ∃ (κ : Type) (M : Model κ), M.SerialMRel ∧ ¬ M.AscendingMRel :=
  ⟨Fin 2, TDia.counterModel, inferInstance, TDia.counterModel_not_ascendingMRel⟩

lemma exists_ascendingMRel_not_forces_N :
  ∃ (κ : Type) (M : Model κ), M.AscendingMRel ∧ ∃ x : M.World, x ⊮[_] ∼◇⊥ :=
  ⟨Fin 2, D.counterModel, inferInstance, 0, D.counterModel_not_forces⟩

end CK

theorem LogicCKD.not_provable_TDia : (#0 🡒 ◇(#0)) ∉ LogicCKD :=
  fun h => CK.TDia.counterModel_not_forces (CK.Model.valid_of_mem_LogicCKD h 0)

theorem LogicCKD.ssubset_CKTDia : LogicCKD ⊂ LogicCKTDia :=
  LogicCKD.subset_CKTDia.ssubset_of_not_subset
    fun h => LogicCKD.not_provable_TDia (h LogicCKTDia.provable_TDia)

theorem LogicCKTDia.not_provable_N : (∼◇⊥) ∉ LogicCKTDia :=
  fun h => CK.D.counterModel_not_forces (CK.Model.valid_of_mem_LogicCKTDia h 0)

end
