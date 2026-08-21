module

public import NCML.CK.Confluence

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

/-- The frame condition defined by `B◇`: every world has a `≼`-successor all of whose
`⊏`-successors return to it, unless it is fallible. -/
class BDia (F : Frame κ) : Prop where
  bDia : ∀ x : F.World, ¬F.Fallible x →
    ∃ y, x ≼ y ∧ ∀ z, y ⊏ z → ∃ w v, z ≼ w ∧ w ⊏ v ∧ v ≼ x
export BDia (bDia)

/-- `BDia` with the fallibility escape dropped: every world has such a returning `≼`-successor. -/
class StrictBDia (F : Frame κ) : Prop where
  strict_bDia : ∀ x : F.World,
    ∃ y, x ≼ y ∧ ∀ z, y ⊏ z → ∃ w v, z ≼ w ∧ w ⊏ v ∧ v ≼ x
export StrictBDia (strict_bDia)


instance [F.StrictBDia] : F.BDia where
  bDia x _ := strict_bDia x;

instance [F.SymmetricMRel] : F.StrictBDia where
  strict_bDia x := by
    use x;
    and_intros;
    . apply refl;
    . intro z Mxz;
      use z, x;
      and_intros;
      . apply refl;
      . apply symm_mRel Mxz;
      . apply refl;

lemma valid_BDia [F.BDia] : F ⊧ (◇(□A) 🡒 A) := by
  intro V V_per V_fal x y _ hy;
  by_cases hFallible : F.Fallible y;
  . exact forces_of_fallible hFallible;
  . obtain ⟨z, Iyz, hz⟩ := bDia y hFallible;
    obtain ⟨w, Izw, hw⟩ := hy z Iyz;
    obtain ⟨v, u, Iwv, Mvu, Iuy⟩ := hz w Izw;
    exact forces_persistent (hw v u Iwv Mvu) Iuy;

lemma bDia_of_valid_BDia (h : F ⊧ (◇(□(#0)) 🡒 #0)) : F.BDia where
  bDia x hx := by
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

theorem bDia_TFAE : List.TFAE [
  F.BDia,
  ∀ A : BDFormula, F ⊧ (◇(□A) 🡒 A),
  F ⊧ (◇(□(#0)) 🡒 #0),
] := by
  tfae_have 1 → 2 := by intro h A; exact valid_BDia;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := bDia_of_valid_BDia
  tfae_finish

end Frame

end CK

end
