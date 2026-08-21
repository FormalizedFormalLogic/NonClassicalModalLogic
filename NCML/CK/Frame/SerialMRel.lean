module

public import NCML.CK.Semantics

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class SerialMRel (F : Frame κ) : Prop where
  serial_mRel : ∀ x : F.World, ∃ y, x ⊏ y

export SerialMRel (serial_mRel)

lemma frameValidate_D_of_frame_SerialMRel [F.SerialMRel] : F ⊧ (□A 🡒 ◇A) := by
  intro V V_per V_fal x y Ixy hyBoxA z Iyz;
  obtain ⟨w, Mzw⟩ := serial_mRel z;
  exact ⟨w, Mzw, hyBoxA z w Iyz Mzw⟩;

lemma frameValidate_PDia_of_frame_SerialMRel [F.SerialMRel] : F ⊧ ◇⊤ := by
  intro V V_per V_fal x y Ixy;
  obtain ⟨z, Myz⟩ := serial_mRel y;
  exact ⟨z, Myz, by grind⟩;

lemma frame_SerialMRel_of_frameValidate_D (h : F ⊧ (□(#0) 🡒 ◇(#0))) : F.SerialMRel where
  serial_mRel x := by
    let M : Model κ := {
      toFrame := F,
      val := fun _ _ => True,
      val_persistent := by intros; trivial,
      fallible_val := by intros; trivial,
    }
    have hxBoxA : x ⊩[M] □(#0) := by intro y z _ _; trivial;
    obtain ⟨y, Mxy, -⟩ := h M.val M.val_persistent M.fallible_val x x (refl x) hxBoxA x (refl x);
    exact ⟨y, Mxy⟩;

lemma frame_SerialMRel_of_frameValidate_PDia (h : F ⊧ ◇⊤) : F.SerialMRel where
  serial_mRel x := by
    let M : Model κ := {
      toFrame := F,
      val := fun _ _ => True,
      val_persistent := by intros; trivial,
      fallible_val := by intros; trivial,
    }
    obtain ⟨y, Mxy, -⟩ := h M.val M.val_persistent M.fallible_val x x (refl x);
    exact ⟨y, Mxy⟩;

theorem frame_SerialMRel_TFAE : List.TFAE [
  F.SerialMRel,
  ∀ A : BDFormula, F ⊧ (□A 🡒 ◇A),
  F ⊧ (□(#0) 🡒 ◇(#0)),
  F ⊧ ◇⊤,
] := by
  tfae_have 1 → 2 := by intro h A; exact frameValidate_D_of_frame_SerialMRel;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := frame_SerialMRel_of_frameValidate_D
  tfae_have 1 → 4 := by intro h; exact frameValidate_PDia_of_frame_SerialMRel;
  tfae_have 4 → 1 := frame_SerialMRel_of_frameValidate_PDia
  tfae_finish

end Frame

end CK

end
