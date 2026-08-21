module

public import NCML.CK.Logic.CKTDia
public import NCML.CK.Countermodel.SerialMRel

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

lemma counterModel_not_tDia : ¬ counterModel.TDia := by
  rintro ⟨h⟩;
  obtain ⟨z, Mz, hz⟩ := h 0;
  simp_all [counterModel, Frame.iRel, Frame.mRel, Frame.Fallible];

lemma counterModel_not_forces : 0 ⊮[counterModel] (#0 🡒 ◇(#0)) := by
  intro h;
  obtain ⟨z, Mz, hz⟩ := h 0 rfl rfl 0 rfl;
  simp_all [counterModel, Frame.mRel, Forces];

end TDia

instance : SerialMRel.counterModel.StrictlyAscendingMRel where
  strictly_ascending_mRel x := ⟨x, le_refl x, rfl⟩

theorem exists_serialMRel_not_tDia :
  ∃ (κ : Type) (M : Model κ), M.SerialMRel ∧ ¬M.TDia :=
  ⟨Fin 2, TDia.counterModel, inferInstance, TDia.counterModel_not_tDia⟩

lemma exists_tDia_not_forces_N :
  ∃ (κ : Type) (M : Model κ), M.TDia ∧ ∃ x : M.World, x ⊮[_] ∼◇⊥ :=
  ⟨Fin 2, SerialMRel.counterModel, inferInstance, 0, SerialMRel.counterModel_not_forces⟩

end CK

lemma LogicCKD.not_provable_TDia : (#0 🡒 ◇(#0)) ∉ LogicCKD := by
  intro h;
  apply CK.TDia.counterModel_not_forces (CK.Model.valid_of_mem_LogicCKD h 0)

theorem LogicCKD.ssubset_CKTDia : LogicCKD ⊂ LogicCKTDia := by
  apply Set.ssubset_iff_exists.mpr;
  constructor;
  . apply LogicCKD.subset_CKTDia;
  . use #0 🡒 ◇(#0);
    constructor;
    . grind;
    . apply LogicCKD.not_provable_TDia;

theorem LogicCKTDia.not_provable_N : (∼◇⊥) ∉ LogicCKTDia := by
  intro h;
  apply CK.SerialMRel.counterModel_not_forces (CK.Model.valid_of_mem_LogicCKTDia h 0)

end
