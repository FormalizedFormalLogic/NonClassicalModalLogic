module

public import NCML.CK.Confluence

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class ReturningMComp (F : Frame κ) : Prop where
  returning_mComp : ∀ x : F.World,
    F.Fallible x ∨
    ∃ y, x ≼ y ∧ ∀ z, y ⊏ z → ∃ w v, z ≼ w ∧ w ⊏ v ∧ v ≼ x
export ReturningMComp (returning_mComp)


class StrictlyReturningMComp (F : Frame κ) : Prop where
  strictly_returning_mComp : ∀ x : F.World,
    ∃ y, x ≼ y ∧ ∀ z, y ⊏ z → ∃ w v, z ≼ w ∧ w ⊏ v ∧ v ≼ x
export StrictlyReturningMComp (strictly_returning_mComp)


instance [F.StrictlyReturningMComp] : F.ReturningMComp where
  returning_mComp x := Or.inr $ strictly_returning_mComp x;

instance [F.SymmetricMRel] : F.StrictlyReturningMComp where
  strictly_returning_mComp x := by
    use x;
    and_intros;
    . apply refl;
    . intro z Mxz;
      use z, x;
      and_intros;
      . apply refl;
      . apply symm_mRel Mxz;
      . apply refl;

lemma valid_BDia_of_returningMComp [F.ReturningMComp] : F ⊧ (◇(□A) 🡒 A) := by
  intro val val_persistent fallible_val x y _ hy;
  rcases returning_mComp y with hFallible | ⟨z, Iyz, hz⟩;
  . exact forces_of_fallible hFallible;
  . obtain ⟨w, Izw, hw⟩ := hy z Iyz;
    obtain ⟨v, u, Iwv, Mvu, Iuy⟩ := hz w Izw;
    exact forces_persistent (hw v u Iwv Mvu) Iuy;

lemma returningMComp_of_valid_BDia (h : F ⊧ (◇(□(#0)) 🡒 #0)) : F.ReturningMComp where
  returning_mComp x := by
    by_cases hx : F.Fallible x;
    . left;
      exact hx;
    . right;
      by_contra! hc;
      let M : Model κ := {
        toFrame := F,
        val := fun y _ => ¬(y ≼ x) ∨ F.Fallible y,
        val_persistent := by
          rintro y z a (hy | hy) Iyz;
          . left;
            intro hzx;
            exact hy $ Trans.trans Iyz hzx;
          . right;
            exact F.fallible_iRel hy Iyz;
        fallible_val := by
          rintro y a hy;
          right;
          exact hy;
      }
      have hDiaBox : x ⊩[M] ◇(□(#0)) := by
        intro y Ixy;
        obtain ⟨z, Myz, hz⟩ := hc y Ixy;
        refine ⟨z, Myz, ?_⟩;
        intro w v Izw Mwv;
        exact Or.inl $ hz w v Izw Mwv;
      rcases h M.val M.val_persistent M.fallible_val x x (refl x) hDiaBox with hc₁ | hc₁;
      . exact hc₁ (refl x);
      . exact hx hc₁;

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
