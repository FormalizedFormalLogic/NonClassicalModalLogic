module

public import NCML.CK.Confluence

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

/-- The frame condition defined by `B□`: a `⊏`-step followed by a `≼`-step can always be
reversed by a `⊏`-step, up to `≼` and fallibility. -/
class BBox (F : Frame κ) : Prop where
  bBox : ∀ {x y z : F.World}, x ⊏ y → y ≼ z → ∃ w, z ⊏ w ∧ (x ≼ w ∨ F.Fallible w)
export BBox (bBox)

/-- `BBox` with the fallibility escape dropped: the reversing `⊏`-step lands `≼`-back at `x`. -/
class StrictBBox (F : Frame κ) : Prop where
  strict_bBox : ∀ {x y z : F.World}, x ⊏ y → y ≼ z → ∃ w, z ⊏ w ∧ x ≼ w
export StrictBBox (strict_bBox)

instance [F.StrictBBox] : F.BBox where
  bBox Mxy Iyz := by
    obtain ⟨w, Mzw, Ixw⟩ := strict_bBox Mxy Iyz;
    exact ⟨w, Mzw, Or.inl Ixw⟩;

instance [F.SymmetricMRel] [F.ForwardConfluent] : F.StrictBBox where
  strict_bBox Mxy Iyz := by
    obtain ⟨w, Ixw, Mzw⟩ := forward_confluent (symm_mRel Mxy) Iyz;
    exact ⟨w, Mzw, Ixw⟩;

lemma valid_BBox [F.BBox] : F ⊧ (A 🡒 □◇A) := by
  intro V V_per V_fal x y Ixy hyA z w Iyz Mzw v Iwv;
  obtain ⟨u, Mvu, Izu | hu⟩ := bBox Mzw Iwv;
  . exact ⟨u, Mvu, forces_persistent hyA (Trans.trans Iyz Izu)⟩;
  . exact ⟨u, Mvu, forces_of_fallible hu⟩;

lemma bBox_of_valid_BBox (h : F ⊧ (#0 🡒 □◇(#0))) : F.BBox where
  bBox {x y z} Mxy Iyz := by
    let M : Model κ := {
      toFrame := F,
      val := fun w _ => x ≼ w ∨ F.Fallible w,
      val_persistent := by
        rintro w v a (Ixw | hw) Iwv;
        . left;
          exact Trans.trans Ixw Iwv;
        . right;
          exact F.fallible_iRel hw Iwv;
      fallible_val := by
        rintro w a hw;
        right;
        exact hw;
    }
    have hxA : x ⊩[M] (#0) := Or.inl (refl x);
    exact h M.val M.val_persistent M.fallible_val x x (refl x) hxA x y (refl x) Mxy z Iyz;

theorem bBox_TFAE : List.TFAE [
  F.BBox,
  ∀ A : BDFormula, F ⊧ (A 🡒 □◇A),
  F ⊧ (#0 🡒 □◇(#0)),
] := by
  tfae_have 1 → 2 := by intro h A; exact valid_BBox;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := bBox_of_valid_BBox
  tfae_finish

end Frame

end CK

end
