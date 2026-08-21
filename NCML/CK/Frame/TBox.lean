module

public import NCML.CK.Semantics

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

/-- The frame condition defined by `T□`: `≼ ∘ ⊏ ∘ ≼` is reflexive away from the fallible
worlds. -/
class TBox (F : Frame κ) : Prop where
  tBox : ∀ x : F.World, F.Infallible x → ∃ y z, x ≼ y ∧ y ⊏ z ∧ z ≼ x

lemma TBox.tBox' [F.TBox] : ∀ x : F.World, F.Fallible x ∨ ∃ y z, x ≼ y ∧ y ⊏ z ∧ z ≼ x := by
  intro x;
  by_cases hx : F.Fallible x;
  · left;
    exact hx;
  · right;
    exact tBox x hx;

export TBox (tBox tBox')

lemma frameValidate_TBox_of_frame_TBox [F.TBox] : F ⊧ (□A 🡒 A) := by
  intro V V_per V_fal x y Ixy hyBoxA;
  rcases tBox' y with hFallible | ⟨z, w, Iyz, Mzw, Iwy⟩;
  · exact forces_of_fallible hFallible;
  · exact forces_persistent (hyBoxA z w Iyz Mzw) Iwy;

lemma frame_TBox_of_frameValidate_TBox (h : F ⊧ (□(#0) 🡒 #0)) : F.TBox where
  tBox x hx := by
    let M : Model κ := {
      toFrame := F,
      val := fun y _ => F.Infallible y → ∃ z w, x ≼ z ∧ z ⊏ w ∧ w ≼ y,
      val_persistent := by
        rintro y z a h Iyz hz;
        obtain ⟨w, v, Ixw, Mwv, Ivy⟩ := h (infallible_iRel hz Iyz);
        exact ⟨w, v, Ixw, Mwv, Trans.trans Ivy Iyz⟩;
      fallible_val := by grind;
    }
    have hxBoxA : x ⊩[M] □(#0) := fun y z Ixy Myz _ => ⟨y, z, Ixy, Myz, refl z⟩;
    exact h M.val M.val_persistent M.fallible_val x x (refl x) hxBoxA hx;

/-- `T□` defines the frames on which `≼ ∘ ⊏ ∘ ≼` is reflexive away from the fallible worlds. -/
theorem frame_TBox_TFAE : List.TFAE [
  F.TBox,
  ∀ A : BDFormula, F ⊧ (□A 🡒 A),
  F ⊧ (□(#0) 🡒 #0),
] := by
  tfae_have 1 → 2 := by intro h A; exact frameValidate_TBox_of_frame_TBox;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := frame_TBox_of_frameValidate_TBox
  tfae_finish

end Frame

end CK

end
