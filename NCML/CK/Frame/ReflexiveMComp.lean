module

public import NCML.CK.Semantics

@[expose] public section

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class ReflexiveMComp (F : Frame κ) : Prop where
  reflexive_mComp : ∀ x : F.World, F.Fallible x ∨ ∃ y z, x ≼ y ∧ y ⊏ z ∧ z ≼ x

export ReflexiveMComp (reflexive_mComp)

end Frame

namespace Model

open CK.Frame

lemma valid_TBox_of_reflexiveMComp [M.ReflexiveMComp] : M ⊧ (□A 🡒 A) := by
  intro x y Ixy hyBoxA;
  rcases reflexive_mComp y with hFallible | ⟨y₁, z₁, Iyy₁, My₁z₁, Iz₁y⟩;
  · exact forces_of_fallible hFallible;
  · exact forces_persistent (hyBoxA y₁ z₁ Iyy₁ My₁z₁) Iz₁y;

end Model

namespace Frame

variable {F : Frame κ}

lemma frameValidate_TBox_of_frame_ReflexiveMComp [F.ReflexiveMComp] : F ⊧ (□A 🡒 A) :=
  fun _ _ _ => Model.valid_TBox_of_reflexiveMComp

lemma frame_ReflexiveMComp_of_frameValidate_TBox (h : F ⊧ (□(#0) 🡒 #0)) : F.ReflexiveMComp where
  reflexive_mComp w := by
    let M : Model κ := {
      toFrame := F,
      val := fun x _ => (∃ u v, w ≼ u ∧ u ⊏ v ∧ v ≼ x) ∨ F.Fallible x,
      val_persistent := by
        rintro x y a (⟨u, v, Iwu, Muv, Ivx⟩ | hx) Ixy;
        . left;
          exact ⟨u, v, Iwu, Muv, Trans.trans Ivx Ixy⟩;
        . right;
          exact F.fallible_iRel hx Ixy;
      fallible_val := by
        rintro x a hx;
        right;
        exact hx;
    }
    have hwBoxA : w ⊩[M] □(#0) := fun y z Iwy Myz => Or.inl ⟨y, z, Iwy, Myz, refl z⟩;
    obtain ⟨u, v, Iwu, Muv, Ivw⟩ | hw :=
      h M.val M.val_persistent M.fallible_val w w (refl w) hwBoxA;
    . right;
      exact ⟨u, v, Iwu, Muv, Ivw⟩;
    . left;
      exact hw;

/-- `T□` defines the frames on which `≼ ∘ ⊏ ∘ ≼` is reflexive away from the fallible worlds. -/
theorem frame_ReflexiveMComp_TFAE : List.TFAE [
  F.ReflexiveMComp,
  ∀ A : BDFormula, F ⊧ (□A 🡒 A),
  F ⊧ (□(#0) 🡒 #0),
] := by
  tfae_have 1 → 2 := by intro h A; exact frameValidate_TBox_of_frame_ReflexiveMComp;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := frame_ReflexiveMComp_of_frameValidate_TBox
  tfae_finish

end Frame

end CK

end
