module

public import NCML.CK.Semantics

@[expose] public section

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class SerialMRel (F : Frame κ) : Prop where
  serial_mRel : ∀ x : F.World, ∃ y, x ⊏ y

export SerialMRel (serial_mRel)

end Frame

namespace Model

open CK.Frame

lemma valid_D_of_serialMRel [M.SerialMRel] : M ⊧ (□A 🡒 ◇A) := by
  intro x y Ixy hyBoxA z Iyz;
  obtain ⟨w, Mzw⟩ := serial_mRel z;
  exact ⟨w, Mzw, hyBoxA z w Iyz Mzw⟩;

lemma valid_PDia_of_serialMRel [M.SerialMRel] : M ⊧ ◇⊤ := by
  intro x y Ixy;
  obtain ⟨z, Myz⟩ := serial_mRel y;
  exact ⟨z, Myz, by grind⟩;

end Model

namespace Frame

variable {F : Frame κ}

lemma frameValidate_D_of_frame_SerialMRel [F.SerialMRel] : F ⊧ (□A 🡒 ◇A) :=
  fun _ _ _ => Model.valid_D_of_serialMRel

lemma frameValidate_PDia_of_frame_SerialMRel [F.SerialMRel] : F ⊧ ◇⊤ :=
  fun _ _ _ => Model.valid_PDia_of_serialMRel

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

/-- `D` defines the frames whose `⊏` is serial. -/
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
