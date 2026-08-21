module

public import NCML.CK.Frame.TransitiveMRel

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class FourDia (F : Frame κ) : Prop where
  fourDia : ∀ x : F.World, ∃ y, x ≼ y ∧ ∀ z, y ⊏ z → ∃ w, z ≼ w ∧
    ∀ v, w ⊏ v → ∃ u, x ⊏ u ∧ (F.Infallible u → v ≼ u)

lemma FourDia.fourDia' [F.FourDia] : ∀ x : F.World, ∃ y, x ≼ y ∧ ∀ z, y ⊏ z → ∃ w, z ≼ w ∧
  ∀ v, w ⊏ v → ∃ u, x ⊏ u ∧ (v ≼ u ∨ F.Fallible u) := by
  intro x;
  obtain ⟨y, Ixy, hy⟩ := fourDia x;
  refine ⟨y, Ixy, ?_⟩;
  intro z Myz;
  obtain ⟨w, Izw, hw⟩ := hy z Myz;
  refine ⟨w, Izw, ?_⟩;
  intro v Mwv;
  obtain ⟨u, Mxu, hu⟩ := hw v Mwv;
  refine ⟨u, Mxu, ?_⟩;
  by_cases hFallible : F.Fallible u;
  . right;
    exact hFallible;
  . left;
    exact hu hFallible;

export FourDia (fourDia fourDia')

instance [F.TransitiveMRel] : F.FourDia where
  fourDia x := by
    use x;
    constructor;
    . apply refl;
    . intro z Mxz;
      use z;
      constructor;
      . apply refl;
      . intro v Mzv;
        use v;
        constructor;
        . exact trans_mRel Mxz Mzv;
        . exact fun _ => refl v;

lemma frameValidate_FourDia_of_frame_FourDia [F.FourDia] : F ⊧ (◇◇A 🡒 ◇A) := by
  intro V V_per V_fal x y Ixy hy z Iyz;
  have hz := forces_persistent hy Iyz;
  obtain ⟨w, Izw, hw⟩ := fourDia' z;
  obtain ⟨v, Mwv, hv⟩ := hz w Izw;
  obtain ⟨u, Ivu, hu⟩ := hw v Mwv;
  obtain ⟨v₁, Muv₁, hv₁⟩ := hv u Ivu;
  obtain ⟨u₁, Mzu₁, hu₁⟩ := hu v₁ Muv₁;
  rcases hu₁ with Ivu₁ | hFallible;
  . exact ⟨u₁, Mzu₁, forces_persistent hv₁ Ivu₁⟩;
  . exact ⟨u₁, Mzu₁, forces_of_fallible hFallible⟩;

lemma frame_FourDia_of_frameValidate_FourDia (h : F ⊧ (◇◇(#0) 🡒 ◇(#0))) : F.FourDia where
  fourDia x := by
    by_contra! hc;
    obtain ⟨z, Mxz, hz⟩ := hc x (refl x);
    obtain ⟨v, Mzv, hv⟩ := hz z (refl z);
    have hNotFallible : ∀ u, x ⊏ u → F.Infallible u := fun u Mxu => (hv u Mxu).1;
    let M : Model κ := {
      toFrame := F,
      val := fun v _ => F.Infallible v → ∀ u, v ≼ u → ¬(x ⊏ u),
      val_persistent := by
        rintro v v₁ a h Ivv₁ Iv₁ u Iv₁u;
        exact h (infallible_iRel Iv₁ Ivv₁) u (Trans.trans Ivv₁ Iv₁u);
      fallible_val := by grind;
    }
    have hxDiaDia : x ⊩[M] ◇◇(#0) := by
      intro y Ixy;
      obtain ⟨z, Myz, hz⟩ := hc y Ixy;
      refine ⟨z, Myz, ?_⟩;
      intro w Izw;
      obtain ⟨v, Mwv, hv⟩ := hz w Izw;
      refine ⟨v, Mwv, ?_⟩;
      intro _ u Ivu hxu;
      exact (hv u hxu).2 Ivu;
    have hxDia : x ⊩[M] ◇(#0) := h M.val M.val_persistent M.fallible_val x x (refl x) hxDiaDia;
    obtain ⟨z, Mxz, hz⟩ := hxDia x (refl x);
    exact hz (hNotFallible z Mxz) z (refl z) Mxz;

theorem frame_FourDia_TFAE : List.TFAE [
  F.FourDia,
  ∀ A : BDFormula, F ⊧ (◇◇A 🡒 ◇A),
  F ⊧ (◇◇(#0) 🡒 ◇(#0)),
] := by
  tfae_have 1 → 2 := by intro h A; exact frameValidate_FourDia_of_frame_FourDia;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := frame_FourDia_of_frameValidate_FourDia
  tfae_finish

end Frame

end CK

end
