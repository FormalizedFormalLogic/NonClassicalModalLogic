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
  pBox : ∀ {x : F.World}, ¬F.Fallible x → ∃ y z, x ≼ y ∧ y ⊏ z ∧ ¬F.Fallible z

export PBox (pBox)

instance [F.TBox] : F.PBox where
  pBox {x} hx := by
    rcases tBox x with hFallible | ⟨y, z, Ixy, Myz, Izx⟩;
    . exact absurd hFallible hx;
    . refine ⟨y, z, Ixy, Myz, ?_⟩;
      intro hFallible;
      exact hx (F.fallible_iRel hFallible Izx);

lemma frameValidate_PBox_of_frame_PBox [F.PBox] : F ⊧ (∼□⊥ : BDFormula) := by
  intro V V_per V_fal x y Ixy hy;
  by_contra hFallible;
  obtain ⟨z, w, Iyz, Mzw, hw⟩ := pBox hFallible;
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
