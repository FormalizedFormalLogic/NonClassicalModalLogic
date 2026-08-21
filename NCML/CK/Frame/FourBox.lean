module

public import NCML.CK.Frame.TransitiveMRel
public import NCML.CK.Frame.BackwardConfluent

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class FourBox (F : Frame κ) : Prop where
  fourBox : ∀ {x y z w : F.World}, x ⊏ y → y ≼ z → z ⊏ w →
    F.Infallible w → ∃ v u, x ≼ v ∧ v ⊏ u ∧ u ≼ w

lemma FourBox.fourBox' [F.FourBox] : ∀ {x y z w : F.World}, x ⊏ y → y ≼ z → z ⊏ w →
  F.Fallible w ∨ ∃ v u, x ≼ v ∧ v ⊏ u ∧ u ≼ w := by
  intro x y z w Mxy Iyz Mzw;
  by_cases hFallible : F.Fallible w;
  . left;
    exact hFallible;
  . right;
    exact fourBox Mxy Iyz Mzw hFallible;

export FourBox (fourBox fourBox')

instance [F.TransitiveMRel] [F.BackwardConfluent] : F.FourBox where
  fourBox {x y z w} Mxy Iyz Mzw _ := by
    obtain ⟨v, Ixv, Mvz⟩ := backward_confluent Mxy Iyz;
    exact ⟨v, w, Ixv, trans_mRel Mvz Mzw, refl w⟩;

lemma frameValidate_FourBox_of_frame_FourBox [F.FourBox] : F ⊧ (□A 🡒 □□A) := by
  intro V V_per V_fal x y Ixy hy z w Iyz Mzw v u Iwv Mvu;
  rcases fourBox' Mzw Iwv Mvu with hu | ⟨v₁, u₁, Izv₁, Mv₁u₁, Iu₁u⟩;
  . exact forces_of_fallible hu;
  . exact forces_persistent (hy v₁ u₁ (Trans.trans Iyz Izv₁) Mv₁u₁) Iu₁u;

lemma frame_FourBox_of_frameValidate_FourBox (h : F ⊧ (□(#0) 🡒 □□(#0))) : F.FourBox where
  fourBox {x y z w} Mxy Iyz Mzw := by
    let M : Model κ := {
      toFrame := F,
      val := fun v _ => F.Infallible v → ∃ u₁ t₁, x ≼ u₁ ∧ u₁ ⊏ t₁ ∧ t₁ ≼ v,
      val_persistent := by
        rintro v u a h Ivu Iu;
        obtain ⟨u₁, t₁, Ixu₁, Mu₁t₁, Itv⟩ := h (infallible_iRel Iu Ivu);
        exact ⟨u₁, t₁, Ixu₁, Mu₁t₁, Trans.trans Itv Ivu⟩;
      fallible_val := by grind;
    }
    have hxBoxA : x ⊩[M] □(#0) := fun v u₁ Ixv Mvu₁ _ => ⟨v, u₁, Ixv, Mvu₁, refl u₁⟩;
    have hxBoxBoxA : x ⊩[M] □□(#0) :=
      h M.val M.val_persistent M.fallible_val x x (refl x) hxBoxA;
    exact hxBoxBoxA x y (refl x) Mxy z w Iyz Mzw;

theorem frame_FourBox_TFAE : List.TFAE [
  F.FourBox,
  ∀ A : BDFormula, F ⊧ (□A 🡒 □□A),
  F ⊧ (□(#0) 🡒 □□(#0)),
] := by
  tfae_have 1 → 2 := by intro h A; exact frameValidate_FourBox_of_frame_FourBox;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := frame_FourBox_of_frameValidate_FourBox
  tfae_finish

end Frame

end CK

end
