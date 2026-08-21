module

public import NCML.CK.Frame.SerialMRel

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

/-- The frame condition defined by `T◇`: every world has a `⊏`-successor that it `≼`-precedes,
unless that successor is fallible. -/
class TDia (F : Frame κ) : Prop where
  tDia : ∀ x : F.World, ∃ z, x ⊏ z ∧ (F.Infallible z → x ≼ z)

lemma TDia.tDia' [F.TDia] : ∀ x : F.World, ∃ z, x ⊏ z ∧ (x ≼ z ∨ F.Fallible z) := by
  intro x;
  grind [tDia x];

export TDia (tDia tDia')

instance [F.TDia] : F.SerialMRel where
  serial_mRel x := by
    obtain ⟨z, Mxz, -⟩ := tDia x;
    exact ⟨z, Mxz⟩;

lemma frameValidate_TDia_of_frame_TDia [F.TDia] : F ⊧ (A 🡒 ◇A) := by
  intro V V_per V_fal x y Ixy hyA u Iyu;
  obtain ⟨z, Muz, hz⟩ := tDia' u;
  have huA : u ⊩[_] A := forces_persistent hyA Iyu;
  rcases hz with Iuz | hzFallible;
  · exact ⟨z, Muz, forces_persistent huA Iuz⟩;
  · exact ⟨z, Muz, forces_of_fallible hzFallible⟩;

lemma frame_TDia_of_frameValidate_TDia (h : F ⊧ (#0 🡒 ◇(#0))) : F.TDia where
  tDia x := by
    let M : Model κ := {
      toFrame := F,
      val := fun y _ => F.Infallible y → x ≼ y,
      val_persistent := by
        rintro y z a h Iyz hz;
        trans y;
        . exact h $ infallible_iRel hz Iyz;
        . assumption;
      fallible_val := by grind;
    }
    have hxA : x ⊩[M] (#0) := fun _ => refl _
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
