module

public import NCML.CK.Confluence

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class CircularMComp (F : Frame κ) : Prop where
  circular_mComp : ∀ {x y z : F.World}, x ⊏ y → y ≼ z → ∃ w, z ⊏ w ∧ (x ≼ w ∨ F.Fallible w)
export CircularMComp (circular_mComp)

class StrictlyCircularMComp (F : Frame κ) : Prop where
  strictly_circular_mComp : ∀ {x y z : F.World}, x ⊏ y → y ≼ z → ∃ w, z ⊏ w ∧ x ≼ w
export StrictlyCircularMComp (strictly_circular_mComp)

instance [F.StrictlyCircularMComp] : F.CircularMComp where
  circular_mComp Mxy Iyz := by
    obtain ⟨w, Mzw, Ixw⟩ := strictly_circular_mComp Mxy Iyz;
    exact ⟨w, Mzw, Or.inl Ixw⟩;

instance [F.SymmetricMRel] [F.ForwardConfluent] : F.StrictlyCircularMComp where
  strictly_circular_mComp Mxy Iyz := by
    obtain ⟨w, Ixw, Mzw⟩ := forward_confluent (symm_mRel Mxy) Iyz;
    exact ⟨w, Mzw, Ixw⟩;

lemma valid_BBox_of_circularMComp [F.CircularMComp] : F ⊧ (A 🡒 □◇A) := by
  intro val val_persistent fallible_val x y Ixy hyA z w Iyz Mzw v Iwv;
  obtain ⟨u, Mvu, Izu | hu⟩ := circular_mComp Mzw Iwv;
  . exact ⟨u, Mvu, forces_persistent hyA (Trans.trans Iyz Izu)⟩;
  . exact ⟨u, Mvu, forces_of_fallible hu⟩;

lemma circularMComp_of_valid_BBox (h : F ⊧ (#0 🡒 □◇(#0))) : F.CircularMComp where
  circular_mComp {x y z} Mxy Iyz := by
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

/-- `B□` defines the frames on which a `⊏`-step followed by a `≼`-step can always be
reversed by a `⊏`-step, up to `≼` and fallibility. -/
theorem circularMComp_TFAE : List.TFAE [
  F.CircularMComp,
  ∀ A : BDFormula, F ⊧ (A 🡒 □◇A),
  F ⊧ (#0 🡒 □◇(#0)),
] := by
  tfae_have 1 → 2 := by intro h A; exact valid_BBox_of_circularMComp;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := circularMComp_of_valid_BBox
  tfae_finish

end Frame

end CK

end
