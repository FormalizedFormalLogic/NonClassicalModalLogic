module

public import NCML.CK.Confluence

@[expose] public section

namespace CK

open Model BDFormula

namespace BBox

def counterModel : Model (Fin 3) where
  iRel' x y := x = y ∨ (x = 1 ∧ y = 2)
  iRel_preorder := { refl := by grind, trans := by grind }
  mRel' x y := (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)
  Fallible' _ := False
  fallible_iRel' := by grind
  fallible_mRel' := by grind
  val x a := match a with
    | 0 => x = 0
    | _ => True
  val_persistent := by grind
  fallible_val := by grind

instance : counterModel.SymmetricMRel where
  symm_mRel := by grind [counterModel]

theorem counterModel_not_forwardConfluent : ¬ counterModel.ForwardConfluent := by
  rintro ⟨h⟩;
  obtain ⟨y₁, -, M2y₁⟩ := h (x := 1) (y := 0) (x₁ := 2) (by tauto) (by tauto);
  simp only [counterModel, Model.mRel] at M2y₁;
  omega;

theorem counterModel_not_forces :
    ¬ (0 : counterModel.World) ⊩[_] (#0 🡒 □◇(#0)) := by
  intro h;
  have h0 : (0 : counterModel.World) ⊩[_] (#0 : BDFormula) := by
    show counterModel.val 0 0;
    grind [counterModel];
  have hbox : (0 : counterModel.World) ⊩[_] □◇(#0) := h 0 (by tauto) h0;
  have h1 : (1 : counterModel.World) ⊩[_] ◇(#0) := hbox 0 1 (by tauto) (by tauto);
  obtain ⟨z, M2z, hzA⟩ := h1 2 (by tauto);
  simp only [counterModel, Model.mRel] at M2z;
  omega;

end BBox

/-- - [Pac24, Proposition 9] -/
theorem exists_symmetricMRel_not_forces_bBox :
    ∃ (κ : Type) (M : Model κ), M.SymmetricMRel ∧ ∃ x : M.World, ¬ x ⊩[_] (#0 🡒 □◇(#0)) :=
  ⟨Fin 3, BBox.counterModel, inferInstance, 0, BBox.counterModel_not_forces⟩

end CK

end
