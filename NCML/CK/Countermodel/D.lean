module

public import NCML.CK.Axioms.D

@[expose] public section

namespace CK

open Model BDFormula

namespace D

/-- Two worlds, the second fallible, with `≼` the equality and `⊏` the order of `Fin 2`. -/
def counterModel : Model (Fin 2) where
  iRel' x y := x = y
  iRel_preorder := { refl := by grind, trans := by grind }
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

theorem counterModel_not_forces : (0 : counterModel.World) ⊮[_] ∼◇⊥ := by
  sorry

end D

theorem exists_serialMRel_not_forces_N :
    ∃ (κ : Type) (M : Model κ), M.SerialMRel ∧ ∃ x : M.World, x ⊮[_] ∼◇⊥ :=
  ⟨Fin 2, D.counterModel, inferInstance, 0, D.counterModel_not_forces⟩

end CK

theorem LogicCKD.not_provable_N : (∼◇⊥) ∉ LogicCKD := by
  sorry

end
