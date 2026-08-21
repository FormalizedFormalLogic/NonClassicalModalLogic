module

public import NCML.CK.Axioms.BBox

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
  fallible_exists_mRel' := by grind
  val x a := match a with
    | 0 => x = 0
    | _ => True
  val_persistent := by grind
  fallible_val := by grind

instance : counterModel.SymmetricMRel where
  symm_mRel := by grind [counterModel]

lemma counterModel_not_forwardConfluent : ¬counterModel.ForwardConfluent := by
  rintro ⟨h⟩;
  obtain ⟨w, -, M2w⟩ := h (x := 1) (y := 0) (z := 2) (by tauto) (by tauto);
  simp only [counterModel, Frame.mRel] at M2w;
  omega;

lemma counterModel_not_circularMComp : ¬counterModel.CircularMComp := by
  rintro ⟨h⟩;
  obtain ⟨w, M2w, -⟩ := h (x := 0) (y := 1) (z := 2) (by tauto) (by tauto);
  simp [counterModel, Frame.mRel] at M2w;

lemma counterModel_not_forces : 0 ⊮[counterModel] (#0 🡒 □◇(#0)) := by
  by_contra! h;
  have h0 : 0 ⊩[counterModel] (#0) := by tauto;
  have hbox : 0 ⊩[counterModel] □◇(#0) := h 0 (by tauto) h0;
  have h1 : 1 ⊩[counterModel] ◇(#0) := hbox 0 1 (by tauto) (by tauto);
  obtain ⟨z, M2z, hzA⟩ := h1 2 (by tauto);
  simp [counterModel, Frame.mRel] at M2z;

end BBox

/-- - [Pac24, Proposition 9] -/
theorem exists_symmetricMRel_not_forces_bBox :
  ∃ (κ : Type) (M : Model κ), M.SymmetricMRel ∧ ∃ x : M.World, x ⊮[_] (#0 🡒 □◇(#0)) :=
  ⟨Fin 3, BBox.counterModel, inferInstance, 0, BBox.counterModel_not_forces⟩

theorem exists_symmetricMRel_not_circularMComp :
  ∃ (κ : Type) (F : Frame κ), F.SymmetricMRel ∧ ¬F.CircularMComp :=
  ⟨Fin 3, BBox.counterModel.toFrame, inferInstance, BBox.counterModel_not_circularMComp⟩

end CK

end
