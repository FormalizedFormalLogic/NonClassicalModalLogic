module

public import NCML.CK.Axioms.TDia
public import NCML.CK.Countermodel.D

/-!
# Countermodels for `CK + T◇`

A two-world CK-model with a serial but not ascending `⊏`, on which `T◇` fails, together with the
failure of `∼◇⊥` on the ascending model of `NCML.CK.Countermodel.D`.
-/

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

theorem counterModel_not_ascendingMRel : ¬ counterModel.AscendingMRel := by
  sorry

theorem counterModel_not_forces : (0 : counterModel.World) ⊮[_] (#0 🡒 ◇(#0)) := by
  sorry

end TDia

instance : D.counterModel.StrictlyAscendingMRel where
  strictly_ascending_mRel x := ⟨x, le_refl x, rfl⟩

theorem exists_serialMRel_not_ascendingMRel :
  ∃ (κ : Type) (M : Model κ), M.SerialMRel ∧ ¬ M.AscendingMRel :=
  ⟨Fin 2, TDia.counterModel, inferInstance, TDia.counterModel_not_ascendingMRel⟩

theorem exists_ascendingMRel_not_forces_N :
  ∃ (κ : Type) (M : Model κ), M.AscendingMRel ∧ ∃ x : M.World, x ⊮[_] ∼◇⊥ :=
  ⟨Fin 2, D.counterModel, inferInstance, 0, D.counterModel_not_forces⟩

end CK

theorem LogicCKD.not_provable_TDia : (#0 🡒 ◇(#0)) ∉ LogicCKD := by
  sorry

theorem LogicCKD.ssubset_CKTDia : LogicCKD ⊂ LogicCKTDia := by
  sorry

theorem LogicCKTDia.not_provable_N : (∼◇⊥) ∉ LogicCKTDia := by
  sorry

end
