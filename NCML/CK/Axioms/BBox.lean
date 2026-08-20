module

public import NCML.CK.Confluence

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class SymmetricMComp (F : Frame κ) : Prop where
  symm_mComp : ∀ {x z u : F.World}, x ⊏ z → z ≼ u → ∃ v, u ⊏ v ∧ (x ≼ v ∨ F.Fallible v)

export SymmetricMComp (symm_mComp)

class StrictlySymmetricMComp (F : Frame κ) : Prop where
  strictly_symm_mComp : ∀ {x z u : F.World}, x ⊏ z → z ≼ u → ∃ v, u ⊏ v ∧ x ≼ v

export StrictlySymmetricMComp (strictly_symm_mComp)

instance [F.StrictlySymmetricMComp] : F.SymmetricMComp where
  symm_mComp Mxz Izu := by
    obtain ⟨v, Muv, Ixv⟩ := strictly_symm_mComp Mxz Izu;
    exact ⟨v, Muv, Or.inl Ixv⟩;

instance [F.SymmetricMRel] [F.ForwardConfluent] : F.StrictlySymmetricMComp where
  strictly_symm_mComp Mxz Izu := by
    obtain ⟨v, Ixv, Muv⟩ := forward_confluent (symm_mRel Mxz) Izu;
    exact ⟨v, Muv, Ixv⟩;

lemma valid_BBox_of_symmetricMComp [F.SymmetricMComp] : F ⊧ (A 🡒 □◇A) := by
  intro val val_persistent fallible_val x y Ixy hyA y₁ z Iyy₁ My₁z u Izu;
  obtain ⟨v, Muv, Iy₁v | hv⟩ := symm_mComp My₁z Izu;
  . exact ⟨v, Muv, forces_persistent hyA (Trans.trans Iyy₁ Iy₁v)⟩;
  . exact ⟨v, Muv, forces_of_fallible hv⟩;

lemma symmetricMComp_of_valid_BBox (h : F ⊧ (#0 🡒 □◇(#0))) : F.SymmetricMComp where
  symm_mComp {x z u} Mxz Izu := by
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

/-- `B□` defines the frames whose `⊏ ∘ ≼` is symmetric up to `≼` and fallibility. -/
theorem symmetricMComp_TFAE : List.TFAE [
  F.SymmetricMComp,
  ∀ A : BDFormula, F ⊧ (A 🡒 □◇A),
  F ⊧ (#0 🡒 □◇(#0)),
] := by
  tfae_have 1 → 2 := by intro h A; exact valid_BBox_of_symmetricMComp;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := symmetricMComp_of_valid_BBox
  tfae_finish

end Frame

end CK

end
