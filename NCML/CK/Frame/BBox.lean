module

public import NCML.CK.Frame.SymmetricMRel
public import NCML.CK.Frame.ForwardConfluent

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class BBox (F : Frame κ) : Prop where
  bBox : ∀ {x y z : F.World}, x ⊏ y → y ≼ z → ∃ w, z ⊏ w ∧ (F.Infallible w → x ≼ w)

lemma BBox.bBox' [F.BBox] : ∀ {x y z : F.World}, x ⊏ y → y ≼ z →
  ∃ w, z ⊏ w ∧ (x ≼ w ∨ F.Fallible w) := by
  intro x y z Mxy Iyz;
  obtain ⟨w, Mzw, hw⟩ := bBox Mxy Iyz;
  refine ⟨w, Mzw, ?_⟩;
  by_cases hFallible : F.Fallible w;
  . right;
    exact hFallible;
  . left;
    exact hw hFallible;

export BBox (bBox bBox')

instance [F.SymmetricMRel] [F.ForwardConfluent] : F.BBox where
  bBox Mxy Iyz := by
    obtain ⟨w, Ixw, Mzw⟩ := forward_confluent (symm_mRel Mxy) Iyz;
    exact ⟨w, Mzw, fun _ => Ixw⟩;

lemma frameValidate_BBox_of_frame_BBox [F.BBox] : F ⊧ (A 🡒 □◇A) := by
  intro V V_per V_fal x y Ixy hyA z w Iyz Mzw v Iwv;
  obtain ⟨u, Mvu, Izu | hu⟩ := bBox' Mzw Iwv;
  . exact ⟨u, Mvu, forces_persistent hyA (Trans.trans Iyz Izu)⟩;
  . exact ⟨u, Mvu, forces_of_fallible hu⟩;

lemma frame_BBox_of_frameValidate_BBox (h : F ⊧ (#0 🡒 □◇(#0))) : F.BBox where
  bBox {x y z} Mxy Iyz := by
    let M : Model κ := {
      toFrame := F,
      val := fun w _ => F.Infallible w → x ≼ w,
      val_persistent := by
        rintro w v a h Iwv Iv;
        trans w;
        . exact h $ infallible_iRel Iv Iwv;
        . assumption;
      fallible_val := by grind;
    }
    have hxA : x ⊩[M] (#0) := fun _ => refl x;
    exact h M.val M.val_persistent M.fallible_val x x (refl x) hxA x y (refl x) Mxy z Iyz;

theorem frame_BBox_TFAE : List.TFAE [
  F.BBox,
  ∀ A : BDFormula, F ⊧ (A 🡒 □◇A),
  F ⊧ (#0 🡒 □◇(#0)),
] := by
  tfae_have 1 → 2 := by intro h A; exact frameValidate_BBox_of_frame_BBox;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := frame_BBox_of_frameValidate_BBox
  tfae_finish

end Frame

end CK

end
