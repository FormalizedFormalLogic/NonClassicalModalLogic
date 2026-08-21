module

public import NCML.CK.Semantics

@[expose] public section

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

/-- The frame condition defined by `T□`: `≼ ∘ ⊏ ∘ ≼` is reflexive away from the fallible
worlds. -/
class TBox (F : Frame κ) : Prop where
  tBox : ∀ x : F.World, F.Fallible x ∨ ∃ y z, x ≼ y ∧ y ⊏ z ∧ z ≼ x

export TBox (tBox)

end Frame

namespace Model

open CK.Frame

lemma valid_TBox [M.TBox] : M ⊧ (□A 🡒 A) := by
  intro x y Ixy hyBoxA;
  rcases tBox y with hFallible | ⟨z, w, Iyz, Mzw, Iwy⟩;
  · exact forces_of_fallible hFallible;
  · exact forces_persistent (hyBoxA z w Iyz Mzw) Iwy;

end Model

namespace Frame

variable {F : Frame κ}

lemma frameValidate_TBox_of_frame_TBox [F.TBox] : F ⊧ (□A 🡒 A) :=
  fun _ _ _ => Model.valid_TBox

lemma frame_TBox_of_frameValidate_TBox (h : F ⊧ (□(#0) 🡒 #0)) : F.TBox where
  tBox x := by
    let M : Model κ := {
      toFrame := F,
      val := fun y _ => (∃ z w, x ≼ z ∧ z ⊏ w ∧ w ≼ y) ∨ F.Fallible y,
      val_persistent := by
        rintro y z a (⟨w, v, Ixw, Mwv, Ivy⟩ | hy) Iyz;
        . left;
          exact ⟨w, v, Ixw, Mwv, Trans.trans Ivy Iyz⟩;
        . right;
          exact F.fallible_iRel hy Iyz;
      fallible_val := by
        rintro y a hy;
        right;
        exact hy;
    }
    have hxBoxA : x ⊩[M] □(#0) := fun y z Ixy Myz => Or.inl ⟨y, z, Ixy, Myz, refl z⟩;
    obtain ⟨y, z, Ixy, Myz, Izx⟩ | hx :=
      h M.val M.val_persistent M.fallible_val x x (refl x) hxBoxA;
    . right;
      exact ⟨y, z, Ixy, Myz, Izx⟩;
    . left;
      exact hx;

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
