module

public import NCML.CK.Frame.EuclideanMRel

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class FiveDia (F : Frame κ) : Prop where
  fiveDia : ∀ {x y : F.World}, x ⊏ y → F.Infallible y →
    ∃ z, x ≼ z ∧ ∀ w, z ⊏ w → ∃ v u, w ≼ v ∧ v ⊏ u ∧ u ≼ y
export FiveDia (fiveDia)

instance [F.EuclideanMRel] : F.FiveDia where
  fiveDia {x y} Mxy _ := by
    use x;
    constructor;
    . apply refl;
    . intro w Mxw;
      use w, y;
      and_intros;
      . apply refl;
      . exact eucl_mRel Mxw Mxy;
      . apply refl;

lemma frameValidate_FiveDia_of_frame_FiveDia [F.FiveDia] : F ⊧ (◇(□A) 🡒 □A) := by
  intro V V_per V_fal x y Ixy hy z w Iyz Mzw;
  by_cases hFallible : F.Fallible w;
  . exact forces_of_fallible hFallible;
  . obtain ⟨v, Izv, hv⟩ := fiveDia Mzw hFallible;
    obtain ⟨u, Mvu, hu⟩ := hy v (Trans.trans Iyz Izv);
    obtain ⟨v₁, u₁, Iuv₁, Mv₁u₁, Iu₁w⟩ := hv u Mvu;
    exact forces_persistent (hu v₁ u₁ Iuv₁ Mv₁u₁) Iu₁w;

lemma frame_FiveDia_of_frameValidate_FiveDia (h : F ⊧ (◇(□(#0)) 🡒 □(#0))) : F.FiveDia where
  fiveDia {x y} Mxy hy := by
    by_contra! hc;
    let M : Model κ := {
      toFrame := F,
      val := fun z _ => F.Infallible z → ¬(z ≼ y),
      val_persistent := by
        rintro z z₁ a hz Izz₁ Iz₁ hz₁y;
        exact hz (infallible_iRel Iz₁ Izz₁) (Trans.trans Izz₁ hz₁y);
      fallible_val := by grind;
    }
    have hxDiaBox : x ⊩[M] ◇(□(#0)) := by
      intro z Ixz;
      obtain ⟨w, Mzw, hw⟩ := hc z Ixz;
      use w, Mzw;
      intro v u Iwv Mvu _;
      exact hw v u Iwv Mvu;
    have hxBox : x ⊩[M] □(#0) :=
      h M.val M.val_persistent M.fallible_val x x (refl x) hxDiaBox;
    exact hxBox x y (refl x) Mxy hy (refl y);

theorem frame_FiveDia_TFAE : List.TFAE [
  F.FiveDia,
  ∀ A : BDFormula, F ⊧ (◇(□A) 🡒 □A),
  F ⊧ (◇(□(#0)) 🡒 □(#0)),
] := by
  tfae_have 1 → 2 := by intro h A; exact frameValidate_FiveDia_of_frame_FiveDia;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := frame_FiveDia_of_frameValidate_FiveDia
  tfae_finish

end Frame

end CK

end
