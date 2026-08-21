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
  strictly_circular_mComp : ∀ {x y z : F.World}, x ⊏ y → y ≼ z → ∃ v, z ⊏ v ∧ x ≼ v
export StrictlyCircularMComp (strictly_circular_mComp)

instance [F.StrictlyCircularMComp] : F.CircularMComp where
  circular_mComp Mxz Izu := by
    obtain ⟨v, Muv, Ixv⟩ := strictly_circular_mComp Mxz Izu;
    exact ⟨v, Muv, Or.inl Ixv⟩;

instance [F.SymmetricMRel] [F.ForwardConfluent] : F.StrictlyCircularMComp where
  strictly_circular_mComp Mxz Izu := by
    obtain ⟨v, Ixv, Muv⟩ := forward_confluent (symm_mRel Mxz) Izu;
    exact ⟨v, Muv, Ixv⟩;

lemma valid_BBox_of_circularMComp [F.CircularMComp] : F ⊧ (A 🡒 □◇A) := by
  intro val val_persistent fallible_val x y Ixy hyA y₁ z Iyy₁ My₁z u Izu;
  obtain ⟨v, Muv, Iy₁v | hv⟩ := circular_mComp My₁z Izu;
  . exact ⟨v, Muv, forces_persistent hyA (Trans.trans Iyy₁ Iy₁v)⟩;
  . exact ⟨v, Muv, forces_of_fallible hv⟩;

lemma circularMComp_of_valid_BBox (h : F ⊧ (#0 🡒 □◇(#0))) : F.CircularMComp where
  circular_mComp {x z u} Mxz Izu := by
    let M : Model κ := {
      toFrame := F,
      val := fun p _ => x ≼ p ∨ F.Fallible p,
      val_persistent := by
        rintro p q a (Ixp | hp) Ipq;
        . left;
          exact Trans.trans Ixp Ipq;
        . right;
          exact F.fallible_iRel hp Ipq;
      fallible_val := by
        rintro p a hp;
        right;
        exact hp;
    }
    have hxA : x ⊩[M] (#0) := Or.inl (refl x);
    exact h M.val M.val_persistent M.fallible_val x x (refl x) hxA x z (refl x) Mxz u Izu;

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
