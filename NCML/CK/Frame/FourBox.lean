module

public import NCML.CK.Frame.TransitiveMRel
public import NCML.CK.Frame.BackwardConfluent

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

/-- The frame condition defined by `4□`: two `⊏`-steps with a `≼`-step in between are
covered by a single `≼ ∘ ⊏`-step, up to `≼` and fallibility. -/
class FourBox (F : Frame κ) : Prop where
  fourBox : ∀ {x y z w : F.World}, x ⊏ y → y ≼ z → z ⊏ w →
    F.Fallible w ∨ ∃ v u, x ≼ v ∧ v ⊏ u ∧ u ≼ w
export FourBox (fourBox)

instance [F.TransitiveMRel] [F.BackwardConfluent] : F.FourBox where
  fourBox {x y z w} Mxy Iyz Mzw := by
    obtain ⟨v, Ixv, Mvz⟩ := backward_confluent Mxy Iyz;
    right;
    exact ⟨v, w, Ixv, trans_mRel Mvz Mzw, refl w⟩;

lemma valid_FourBox [F.FourBox] : F ⊧ (□A 🡒 □□A) := by
  intro V V_per V_fal x y Ixy hy z w Iyz Mzw v u Iwv Mvu;
  rcases fourBox Mzw Iwv Mvu with hu | ⟨v₁, u₁, Izv₁, Mv₁u₁, Iu₁u⟩;
  . exact forces_of_fallible hu;
  . exact forces_persistent (hy v₁ u₁ (Trans.trans Iyz Izv₁) Mv₁u₁) Iu₁u;

lemma fourBox_of_valid_FourBox (h : F ⊧ (□(#0) 🡒 □□(#0))) : F.FourBox where
  fourBox {x y z w} Mxy Iyz Mzw := by
    let M : Model κ := {
      toFrame := F,
      val := fun v _ => (∃ u₁ t₁, x ≼ u₁ ∧ u₁ ⊏ t₁ ∧ t₁ ≼ v) ∨ F.Fallible v,
      val_persistent := by
        rintro v u a (⟨u₁, t₁, Ixu₁, Mu₁t₁, Itv⟩ | hv) Ivu;
        . left;
          exact ⟨u₁, t₁, Ixu₁, Mu₁t₁, Trans.trans Itv Ivu⟩;
        . right;
          exact F.fallible_iRel hv Ivu;
      fallible_val := by
        rintro v a hv;
        right;
        exact hv;
    }
    have hxBoxA : x ⊩[M] □(#0) := fun v u₁ Ixv Mvu₁ => Or.inl ⟨v, u₁, Ixv, Mvu₁, refl u₁⟩;
    have hxBoxBoxA : x ⊩[M] □□(#0) :=
      h M.val M.val_persistent M.fallible_val x x (refl x) hxBoxA;
    rcases hxBoxBoxA x y (refl x) Mxy z w Iyz Mzw with ⟨v₁, u₁, Ixv₁, Mv₁u₁, Iu₁w⟩ | hw;
    . right;
      exact ⟨v₁, u₁, Ixv₁, Mv₁u₁, Iu₁w⟩;
    . left;
      exact hw;

/-- `4□` defines the frames on which `⊏ ∘ ≼ ∘ ⊏` collapses to `≼ ∘ ⊏ ∘ ≼`, away from the
fallible worlds. -/
theorem fourBox_TFAE : List.TFAE [
  F.FourBox,
  ∀ A : BDFormula, F ⊧ (□A 🡒 □□A),
  F ⊧ (□(#0) 🡒 □□(#0)),
] := by
  tfae_have 1 → 2 := by intro h A; exact valid_FourBox;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := fourBox_of_valid_FourBox
  tfae_finish

end Frame

end CK

end
