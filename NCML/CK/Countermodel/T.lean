module

public import NCML.CK.Frame.T
public import NCML.CK.Frame.ReflexiveMRel

/-! Frames refuting `Frame.ReflexiveMRel` while validating `T` (i.e. `T□` and `T◇`), or
satisfying `ReturningMRel` and `StrictlyAscendingMRel`. -/

@[expose] public section

namespace CK

open BDFormula

namespace T

def counterFrame : Frame (Fin 2) where
  iRel' _ _ := True
  iRel_preorder := { refl := fun _ => trivial, trans := fun _ _ _ _ _ => trivial }
  mRel' _ y := y = 1
  Fallible' _ := False
  fallible_iRel' := by grind
  fallible_mRel' := by grind
  fallible_exists_mRel' := by grind

instance : counterFrame.TBox where
  tBox x _hx := ⟨x, 1, trivial, rfl, trivial⟩

instance : counterFrame.TDia where
  tDia _x := ⟨1, rfl, fun _ => trivial⟩

instance : counterFrame.T where
  toTBox := inferInstance
  toTDia := inferInstance

lemma counterFrame_not_reflexiveMRel : ¬counterFrame.ReflexiveMRel := by
  rintro ⟨h⟩;
  have h₀ : (0 : Fin 2) ⊏ (0 : Fin 2) := h 0;
  simp_all [counterFrame, Frame.mRel];

end T

namespace ReturningStrictlyAscendingMRel

def counterFrame : Frame (Fin 3) where
  iRel' _ _ := True
  iRel_preorder := { refl := fun _ => trivial, trans := fun _ _ _ _ _ => trivial }
  mRel' x y := y = x + 1
  Fallible' _ := False
  fallible_iRel' := by grind
  fallible_mRel' := by grind
  fallible_exists_mRel' := by grind

instance : counterFrame.ReturningMRel where
  returning_mRel x := ⟨x - 1, trivial, by ext; omega⟩

instance : counterFrame.StrictlyAscendingMRel where
  strictly_ascending_mRel x := ⟨x + 1, rfl, trivial⟩

lemma counterFrame_not_reflexiveMRel : ¬counterFrame.ReflexiveMRel := by
  rintro ⟨h⟩;
  have h₀ : (0 : Fin 3) ⊏ (0 : Fin 3) := h 0;
  simp_all [counterFrame, Frame.mRel];

end ReturningStrictlyAscendingMRel

theorem exists_frame_T_not_reflexiveMRel :
  ∃ (κ : Type) (F : Frame κ), F.T ∧ ¬F.ReflexiveMRel :=
  ⟨Fin 2, T.counterFrame, inferInstance, T.counterFrame_not_reflexiveMRel⟩

theorem exists_frame_returningMRel_strictlyAscendingMRel_not_reflexiveMRel :
  ∃ (κ : Type) (F : Frame κ), F.ReturningMRel ∧ F.StrictlyAscendingMRel ∧ ¬F.ReflexiveMRel :=
  ⟨Fin 3, ReturningStrictlyAscendingMRel.counterFrame, inferInstance, inferInstance,
    ReturningStrictlyAscendingMRel.counterFrame_not_reflexiveMRel⟩

/-- `Frame.ReflexiveMRel` is not definable by `T□` and `T◇`: there is a frame validating both
axioms whose `⊏` is not reflexive. -/
theorem not_frame_ReflexiveMRel_of_frameValidate_T :
  ¬∀ {κ : Type} (F : Frame κ), F ⊧ ((□(#0) 🡒 #0) ⋏ (#0 🡒 ◇(#0))) → F.ReflexiveMRel := by
  intro h;
  have : T.counterFrame.ReflexiveMRel := h T.counterFrame (fun V V_per V_fal x =>
    ⟨Frame.frameValidate_TBox_of_frame_TBox V V_per V_fal x,
      Frame.frameValidate_TDia_of_frame_TDia V V_per V_fal x⟩);
  exact T.counterFrame_not_reflexiveMRel this;

end CK

end
