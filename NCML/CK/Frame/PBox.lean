module

public import NCML.CK.Frame.TBox

@[expose] public section

namespace CK

variable {κ : Type*}

namespace Frame

variable {F : Frame κ}

/-- The frame condition defined by `P□`: an infallible world has an infallible
`≼ ∘ ⊏`-successor. -/
class PBox (F : Frame κ) : Prop where
  pBox : ∀ {x : F.World}, F.Infallible x → ∃ y z, x ≼ y ∧ y ⊏ z ∧ F.Infallible z

export PBox (pBox)

instance [F.TBox] : F.PBox where
  pBox {x} hx := by
    obtain ⟨y, z, Ixy, Myz, Izx⟩ := tBox x hx;
    exact ⟨y, z, Ixy, Myz, infallible_iRel hx Izx⟩;

lemma frameValidate_PBox_of_frame_PBox [F.PBox] : F ⊧ (∼□⊥ : BDFormula) := by
  intro V V_per V_fal x y Ixy hy;
  by_contra hInfallible;
  obtain ⟨z, w, Iyz, Mzw, hw⟩ := pBox hInfallible;
  exact hw (hy z w Iyz Mzw);

lemma frame_PBox_of_frameValidate_PBox (h : F ⊧ (∼□⊥ : BDFormula)) : F.PBox where
  pBox {x} hx := by
    by_contra! hc;
    let M : Model κ := {
      toFrame := F,
      val := fun _ _ => True,
      val_persistent := by intros; trivial,
      fallible_val := by intros; trivial,
    }
    exact hx (h M.val M.val_persistent M.fallible_val x x (refl x) hc);

/-- `P□` defines the frames whose infallible worlds have an infallible `≼ ∘ ⊏`-successor. -/
theorem frame_PBox_iff_frameValidate_PBox : F.PBox ↔ F ⊧ (∼□⊥ : BDFormula) := by
  constructor;
  . intro _;
    exact frameValidate_PBox_of_frame_PBox;
  . exact frame_PBox_of_frameValidate_PBox;

end Frame

end CK

end
