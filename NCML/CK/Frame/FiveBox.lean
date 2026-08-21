module

public import NCML.CK.Frame.EuclideanMRel
public import NCML.CK.Frame.ForwardConfluent

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

/-- The frame condition defined by `5□`: whenever `z` is reached by a `⊏`-step followed by a
`≼`-step, some `≼`-successor of the origin has all its `⊏`-successors covered by `⊏`-successors
of `z`, up to `≼` and fallibility. -/
class FiveBox (F : Frame κ) : Prop where
  fiveBox : ∀ {x y z : F.World}, x ⊏ y → y ≼ z →
    ∃ w, x ≼ w ∧ ∀ v, w ⊏ v → ∃ u, z ⊏ u ∧ (v ≼ u ∨ F.Fallible u)
export FiveBox (fiveBox)

instance [F.EuclideanMRel] [F.ForwardConfluent] : F.FiveBox where
  fiveBox {x y z} Mxy Iyz := by
    use x;
    constructor;
    . apply refl;
    . intro v Mxv;
      obtain ⟨u, Ivu, Mzu⟩ := forward_confluent (eucl_mRel Mxy Mxv) Iyz;
      refine ⟨u, Mzu, ?_⟩;
      left;
      exact Ivu;

lemma frameValidate_FiveBox_of_frame_FiveBox [F.FiveBox] : F ⊧ (◇A 🡒 □◇A) := by
  intro V V_per V_fal x y Ixy hy z w Iyz Mzw v Iwv;
  obtain ⟨u, Izu, hu⟩ := fiveBox Mzw Iwv;
  obtain ⟨v₁, Muv₁, hv₁⟩ := hy u (Trans.trans Iyz Izu);
  obtain ⟨u₁, Mvu₁, hu₁⟩ := hu v₁ Muv₁;
  rcases hu₁ with Iv₁u₁ | hFallible;
  . exact ⟨u₁, Mvu₁, forces_persistent hv₁ Iv₁u₁⟩;
  . exact ⟨u₁, Mvu₁, forces_of_fallible hFallible⟩;

lemma frame_FiveBox_of_frameValidate_FiveBox (h : F ⊧ (◇(#0) 🡒 □◇(#0))) : F.FiveBox where
  fiveBox {x y z} Mxy Iyz := by
    by_contra! hc;
    obtain ⟨v, Mxv, hv⟩ := hc x (refl x);
    have hNotFallible : ∀ u, z ⊏ u → ¬F.Fallible u := fun u Mzu => (hv u Mzu).2;
    let M : Model κ := {
      toFrame := F,
      val := fun v _ => (∀ u, v ≼ u → ¬(z ⊏ u)) ∨ F.Fallible v,
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
    have hxDia : x ⊩[M] ◇(#0) := by
      intro w Ixw;
      obtain ⟨v, Mxv, hv⟩ := hc w Ixw;
      refine ⟨v, Mxv, ?_⟩;
      left;
      intro u Ivu Mzu;
      exact (hv u Mzu).1 Ivu;
    have hxBoxDia : x ⊩[M] □◇(#0) :=
      h M.val M.val_persistent M.fallible_val x x (refl x) hxDia;
    obtain ⟨u, Mzu, hu⟩ := hxBoxDia x y (refl x) Mxy z Iyz;
    rcases hu with hu | hu;
    . exact hu u (refl u) Mzu;
    . exact hNotFallible u Mzu hu;

theorem frame_FiveBox_TFAE : List.TFAE [
  F.FiveBox,
  ∀ A : BDFormula, F ⊧ (◇A 🡒 □◇A),
  F ⊧ (◇(#0) 🡒 □◇(#0)),
] := by
  tfae_have 1 → 2 := by intro h A; exact frameValidate_FiveBox_of_frame_FiveBox;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := frame_FiveBox_of_frameValidate_FiveBox
  tfae_finish

end Frame

end CK

end
