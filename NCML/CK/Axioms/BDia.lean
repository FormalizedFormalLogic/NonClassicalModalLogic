module

public import NCML.CK.Confluence

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class ReturningMComp (F : Frame κ) : Prop where
  returning_mComp : ∀ w : F.World,
    F.Fallible w ∨ ∃ y, w ≼ y ∧ ∀ z, y ⊏ z → ∃ u v, z ≼ u ∧ u ⊏ v ∧ v ≼ w

export ReturningMComp (returning_mComp)

class StrictlyReturningMComp (F : Frame κ) : Prop where
  strictly_returning_mComp : ∀ w : F.World,
    ∃ y, w ≼ y ∧ ∀ z, y ⊏ z → ∃ u v, z ≼ u ∧ u ⊏ v ∧ v ≼ w

export StrictlyReturningMComp (strictly_returning_mComp)

instance [F.StrictlyReturningMComp] : F.ReturningMComp where
  returning_mComp w := Or.inr $ strictly_returning_mComp w;

instance [F.SymmetricMRel] : F.StrictlyReturningMComp where
  strictly_returning_mComp w := by
    refine ⟨w, refl w, ?_⟩;
    intro z Iwz;
    exact ⟨z, w, refl z, symm_mRel Iwz, refl w⟩;

lemma valid_BDia_of_returningMComp [F.ReturningMComp] : F ⊧ (◇(□A) 🡒 A) := by
  intro val val_persistent fallible_val x w _ hw;
  rcases returning_mComp w with hFallible | ⟨y, Iwy, hy⟩;
  . exact forces_of_fallible hFallible;
  . obtain ⟨z, Iyz, hz⟩ := hw y Iwy;
    obtain ⟨u, v, Izu, Muv, Ivw⟩ := hy z Iyz;
    exact forces_persistent (hz u v Izu Muv) Ivw;

lemma returningMComp_of_valid_BDia (h : F ⊧ (◇(□(#0)) 🡒 #0)) : F.ReturningMComp where
  returning_mComp w := by
    by_cases hw : F.Fallible w;
    . left;
      exact hw;
    . right;
      by_contra! hc;
      let M : Model κ := {
        toFrame := F,
        val := fun p _ => ¬(p ≼ w) ∨ F.Fallible p,
        val_persistent := by
          rintro p q a (hp | hp) Ipq;
          . left;
            intro hqw;
            exact hp $ Trans.trans Ipq hqw;
          . right;
            exact F.fallible_iRel hp Ipq;
        fallible_val := by
          rintro p a hp;
          right;
          exact hp;
      }
      have hDiaBox : w ⊩[M] ◇(□(#0)) := by
        intro y Iwy;
        obtain ⟨z, Myz, hz⟩ := hc y Iwy;
        refine ⟨z, Myz, ?_⟩;
        intro u v Izu Muv;
        exact Or.inl $ hz u v Izu Muv;
      rcases h M.val M.val_persistent M.fallible_val w w (refl w) hDiaBox with hc₁ | hc₁;
      . exact hc₁ (refl w);
      . exact hw hc₁;

/-- `B◇` defines the frames on which every world has a `≼`-successor all of whose `⊏`-successors
return to it. -/
theorem returningMComp_TFAE : List.TFAE [
  F.ReturningMComp,
  ∀ A : BDFormula, F ⊧ (◇(□A) 🡒 A),
  F ⊧ (◇(□(#0)) 🡒 #0),
] := by
  tfae_have 1 → 2 := by intro h A; exact valid_BDia_of_returningMComp;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := returningMComp_of_valid_BDia
  tfae_finish

end Frame

end CK

end
