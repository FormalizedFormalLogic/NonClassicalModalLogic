module

public import NCML.CK.Frame.SerialMRel

@[expose] public section

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

/-- The frame condition defined by `T◇`: every world has a `⊏`-successor that it `≼`-precedes,
unless that successor is fallible. -/
class TDia (F : Frame κ) : Prop where
  tDia : ∀ x : F.World, ∃ z, x ⊏ z ∧ (x ≼ z ∨ F.Fallible z)

export TDia (tDia)

instance [F.TDia] : F.SerialMRel where
  serial_mRel x := by
    obtain ⟨z, Mxz, _⟩ := tDia x;
    exact ⟨z, Mxz⟩;

end Frame

namespace Model

open CK.Frame

lemma valid_TDia [M.TDia] : M ⊧ (A 🡒 ◇A) := by
  intro x y Ixy hyA u Iyu;
  obtain ⟨z, Muz, hz⟩ := tDia u;
  have huA : u ⊩[_] A := forces_persistent hyA Iyu;
  rcases hz with Iuz | hzFallible;
  · exact ⟨z, Muz, forces_persistent huA Iuz⟩;
  · exact ⟨z, Muz, forces_of_fallible hzFallible⟩;

end Model

namespace Frame

variable {F : Frame κ}

lemma frameValidate_TDia_of_frame_TDia [F.TDia] : F ⊧ (A 🡒 ◇A) :=
  fun _ _ _ => Model.valid_TDia

lemma frame_TDia_of_frameValidate_TDia (h : F ⊧ (#0 🡒 ◇(#0))) : F.TDia where
  tDia x := by
    let M : Model κ := {
      toFrame := F,
      val := fun y _ => x ≼ y ∨ F.Fallible y,
      val_persistent := by
        rintro y z a (Ixy | hy) Iyz;
        . left;
          exact Trans.trans Ixy Iyz;
        . right;
          exact F.fallible_iRel hy Iyz;
      fallible_val := by
        rintro y a hy;
        right;
        exact hy;
    }
    have hxA : x ⊩[M] (#0) := Or.inl (refl x);
    exact h M.val M.val_persistent M.fallible_val x x (refl x) hxA x (refl x);

/-- `T◇` defines the frames whose `⊏` is ascending. -/
theorem frame_TDia_TFAE : List.TFAE [
  F.TDia,
  ∀ A : BDFormula, F ⊧ (A 🡒 ◇A),
  F ⊧ (#0 🡒 ◇(#0)),
] := by
  tfae_have 1 → 2 := by intro h A; exact frameValidate_TDia_of_frame_TDia;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := frame_TDia_of_frameValidate_TDia
  tfae_finish

end Frame

end CK

end
