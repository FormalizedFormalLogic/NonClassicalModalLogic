module

public import NCML.CK.Frame.ReflexiveMComp

@[expose] public section

namespace CK

variable {κ : Type*}

namespace Frame

variable {F : Frame κ}

/-- The frame condition defined by `P□`: a world all of whose `≼ ∘ ⊏`-successors are
fallible is itself fallible. -/
class PBox (F : Frame κ) : Prop where
  pBox : ∀ {x : F.World}, (∀ y z, x ≼ y → y ⊏ z → F.Fallible z) → F.Fallible x

export PBox (pBox)

instance [F.ReflexiveMComp] : F.PBox where
  pBox {x} h := by
    rcases reflexive_mComp x with hFallible | ⟨y, z, Ixy, Myz, Izx⟩;
    . exact hFallible;
    . exact F.fallible_iRel (h y z Ixy Myz) Izx;

lemma valid_PBox [F.PBox] : F ⊧ (∼□⊥ : BDFormula) := by
  intro V V_per V_fal x y Ixy hy;
  exact pBox hy;

lemma pBox_of_valid_PBox (h : F ⊧ (∼□⊥ : BDFormula)) : F.PBox where
  pBox {x} h₁ := by
    let M : Model κ := {
      toFrame := F,
      val := fun _ _ => True,
      val_persistent := by intros; trivial,
      fallible_val := by intros; trivial,
    }
    exact h M.val M.val_persistent M.fallible_val x x (refl x) h₁;

/-- `P□` defines the frames whose infallible worlds have an infallible `≼ ∘ ⊏`-successor. -/
theorem pBox_iff_valid_PBox : F.PBox ↔ F ⊧ (∼□⊥ : BDFormula) := by
  constructor;
  . intro _;
    exact valid_PBox;
  . exact pBox_of_valid_PBox;

end Frame

end CK

end
