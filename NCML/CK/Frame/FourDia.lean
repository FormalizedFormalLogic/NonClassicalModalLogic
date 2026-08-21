module

public import NCML.CK.Frame.TransitiveMRel

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

/-- The frame condition defined by `4◇`: every world has a `≼`-successor from which two
`⊏`-steps, with a `≼`-step in between, are covered by a single `⊏`-step from the world
itself, up to `≼` and fallibility. -/
class FourDia (F : Frame κ) : Prop where
  fourDia : ∀ x : F.World, ∃ y, x ≼ y ∧ ∀ z, y ⊏ z → ∃ w, z ≼ w ∧
    ∀ v, w ⊏ v → ∃ u, x ⊏ u ∧ (v ≼ u ∨ F.Fallible u)
export FourDia (fourDia)

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
        . left;
          apply refl;

lemma valid_FourDia [F.FourDia] : F ⊧ (◇◇A 🡒 ◇A) := by
  intro V V_per V_fal x y Ixy hy z Iyz;
  have hz := forces_persistent hy Iyz;
  obtain ⟨w, Izw, hw⟩ := fourDia z;
  obtain ⟨v, Mwv, hv⟩ := hz w Izw;
  obtain ⟨u, Ivu, hu⟩ := hw v Mwv;
  obtain ⟨v₁, Muv₁, hv₁⟩ := hv u Ivu;
  obtain ⟨u₁, Mzu₁, hu₁⟩ := hu v₁ Muv₁;
  rcases hu₁ with Ivu₁ | hFallible;
  . exact ⟨u₁, Mzu₁, forces_persistent hv₁ Ivu₁⟩;
  . exact ⟨u₁, Mzu₁, forces_of_fallible hFallible⟩;

lemma fourDia_of_valid_FourDia (h : F ⊧ (◇◇(#0) 🡒 ◇(#0))) : F.FourDia where
  fourDia x := by
    by_contra! hc;
    obtain ⟨z, Mxz, hz⟩ := hc x (refl x);
    obtain ⟨v, Mzv, hv⟩ := hz z (refl z);
    have hNotFallible : ∀ u, x ⊏ u → ¬F.Fallible u := fun u Mxu => (hv u Mxu).2;
    let M : Model κ := {
      toFrame := F,
      val := fun v _ => (∀ u, v ≼ u → ¬(x ⊏ u)) ∨ F.Fallible v,
      val_persistent := by
        rintro v v₁ a (hv | hv) Ivv₁;
        . left;
          intro u Iv₁u;
          exact hv u (Trans.trans Ivv₁ Iv₁u);
        . right;
          exact F.fallible_iRel hv Ivv₁;
      fallible_val := by
        rintro v a hv;
        right;
        exact hv;
    }
    have hxDiaDia : x ⊩[M] ◇◇(#0) := by
      intro y Ixy;
      obtain ⟨z, Myz, hz⟩ := hc y Ixy;
      refine ⟨z, Myz, ?_⟩;
      intro w Izw;
      obtain ⟨v, Mwv, hv⟩ := hz w Izw;
      refine ⟨v, Mwv, ?_⟩;
      left;
      intro u Ivu hxu;
      exact (hv u hxu).1 Ivu;
    have hxDia : x ⊩[M] ◇(#0) := h M.val M.val_persistent M.fallible_val x x (refl x) hxDiaDia;
    obtain ⟨z, Mxz, hz⟩ := hxDia x (refl x);
    rcases hz with hz | hz;
    . exact hz z (refl z) Mxz;
    . exact hNotFallible z Mxz hz;

theorem fourDia_TFAE : List.TFAE [
  F.FourDia,
  ∀ A : BDFormula, F ⊧ (◇◇A 🡒 ◇A),
  F ⊧ (◇◇(#0) 🡒 ◇(#0)),
] := by
  tfae_have 1 → 2 := by intro h A; exact valid_FourDia;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := fourDia_of_valid_FourDia
  tfae_finish

end Frame

end CK

end
