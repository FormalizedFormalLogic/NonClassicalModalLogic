module

public import NCML.CK.Frame.SymmetricMRel

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class BDia (F : Frame κ) : Prop where
  bDia : ∀ x : F.World, F.Infallible x → ∃ y, x ≼ y ∧ ∀ z, y ⊏ z → ∃ w v, z ≼ w ∧ w ⊏ v ∧ v ≼ x
export BDia (bDia)

instance [F.SymmetricMRel] : F.BDia where
  bDia x _ := by
    use x;
    and_intros;
    . apply refl;
    . intro z Mxz;
      use z, x;
      and_intros;
      . apply refl;
      . apply symm_mRel Mxz;
      . apply refl;

lemma frameValidate_BDia_of_frame_BDia [F.BDia] : F ⊧ (◇(□A) 🡒 A) := by
  intro V V_per V_fal x y _ hy;
  by_cases hFallible : F.Fallible y;
  . exact forces_of_fallible hFallible;
  . obtain ⟨z, Iyz, hz⟩ := bDia y hFallible;
    obtain ⟨w, Izw, hw⟩ := hy z Iyz;
    obtain ⟨v, u, Iwv, Mvu, Iuy⟩ := hz w Izw;
    exact forces_persistent (hw v u Iwv Mvu) Iuy;

lemma frame_BDia_of_frameValidate_BDia (h : F ⊧ (◇(□(#0)) 🡒 #0)) : F.BDia where
  bDia x hx := by
    by_contra! hc;
    let M : Model κ := {
      toFrame := F,
      val := fun y _ => F.Infallible y → ¬(y ≼ x),
      val_persistent := by
        rintro y z a h Iyz Iz hzx;
        exact h (infallible_iRel Iz Iyz) $ Trans.trans Iyz hzx;
      fallible_val := by grind;
    }
    have hDiaBox : x ⊩[M] ◇(□(#0)) := by
      intro y Ixy;
      obtain ⟨z, Myz, hz⟩ := hc y Ixy;
      refine ⟨z, Myz, ?_⟩;
      intro w v Izw Mwv _;
      exact hz w v Izw Mwv;
    have hc₁ := h M.val M.val_persistent M.fallible_val x x (refl x) hDiaBox hx;
    exact hc₁ (refl x);

theorem frame_BDia_TFAE : List.TFAE [
  F.BDia,
  ∀ A : BDFormula, F ⊧ (◇(□A) 🡒 A),
  F ⊧ (◇(□(#0)) 🡒 #0),
] := by
  tfae_have 1 → 2 := by intro h A; exact frameValidate_BDia_of_frame_BDia;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := frame_BDia_of_frameValidate_BDia
  tfae_finish

end Frame

end CK

end
