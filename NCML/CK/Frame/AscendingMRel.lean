module

public import NCML.CK.Frame.SerialMRel

@[expose] public section

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class AscendingMRel (F : Frame κ) : Prop where
  ascending_mRel : ∀ x : F.World, ∃ z, x ⊏ z ∧ (x ≼ z ∨ F.Fallible z)

export AscendingMRel (ascending_mRel)

instance [F.AscendingMRel] : F.SerialMRel where
  serial_mRel x := by
    obtain ⟨z, Mxz, _⟩ := ascending_mRel x;
    exact ⟨z, Mxz⟩;

end Frame

namespace Model

open CK.Frame

lemma valid_TDia_of_ascendingMRel [M.AscendingMRel] : M ⊧ (A 🡒 ◇A) := by
  intro x y Ixy hyA u Iyu;
  obtain ⟨z, Muz, hz⟩ := ascending_mRel u;
  have huA : u ⊩[_] A := forces_persistent hyA Iyu;
  rcases hz with Iuz | hzFallible;
  · exact ⟨z, Muz, forces_persistent huA Iuz⟩;
  · exact ⟨z, Muz, forces_of_fallible hzFallible⟩;

end Model

namespace Frame

variable {F : Frame κ}

lemma frameValidate_TDia_of_frame_AscendingMRel [F.AscendingMRel] : F ⊧ (A 🡒 ◇A) :=
  fun _ _ _ => Model.valid_TDia_of_ascendingMRel

lemma frame_AscendingMRel_of_frameValidate_TDia (h : F ⊧ (#0 🡒 ◇(#0))) : F.AscendingMRel where
  ascending_mRel w := by
    let M : Model κ := {
      toFrame := F,
      val := fun x _ => w ≼ x ∨ F.Fallible x,
      val_persistent := by
        rintro x y a (Iwx | hx) Ixy;
        . left;
          exact Trans.trans Iwx Ixy;
        . right;
          exact F.fallible_iRel hx Ixy;
      fallible_val := by
        rintro x a hx;
        right;
        exact hx;
    }
    have hwA : w ⊩[M] (#0) := Or.inl (refl w);
    exact h M.val M.val_persistent M.fallible_val w w (refl w) hwA w (refl w);

/-- `T◇` defines the frames whose `⊏` is ascending. -/
theorem frame_AscendingMRel_TFAE : List.TFAE [
  F.AscendingMRel,
  ∀ A : BDFormula, F ⊧ (A 🡒 ◇A),
  F ⊧ (#0 🡒 ◇(#0)),
] := by
  tfae_have 1 → 2 := by intro h A; exact frameValidate_TDia_of_frame_AscendingMRel;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := frame_AscendingMRel_of_frameValidate_TDia
  tfae_finish

end Frame

end CK

end
