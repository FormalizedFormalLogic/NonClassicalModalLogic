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
  intro x y Ixy hyBoxA u Iyu;
  obtain ⟨z, Muz⟩ := serial_mRel u;
  exact ⟨z, Muz, hyBoxA u z Iyu Muz⟩;

lemma valid_PDia_of_serialMRel [M.SerialMRel] : M ⊧ ◇⊤ := by
  intro x y Ixy;
  obtain ⟨z, Mxz⟩ := serial_mRel y;
  exact ⟨z, Mxz, by grind⟩;

end Model

namespace Frame

variable {F : Frame κ}

lemma valid_D_of_serialMRel [F.SerialMRel] : F ⊧ (□A 🡒 ◇A) :=
  fun _ _ _ => Model.valid_D_of_serialMRel

lemma valid_PDia_of_serialMRel [F.SerialMRel] : F ⊧ ◇⊤ :=
  fun _ _ _ => Model.valid_PDia_of_serialMRel

lemma serialMRel_of_valid_D (h : F ⊧ (□(#0) 🡒 ◇(#0))) : F.SerialMRel where
  serial_mRel x := by
    let M : Model κ := {
      toFrame := F,
      val := fun _ _ => True,
      val_persistent := by intros; trivial,
      fallible_val := by intros; trivial,
    }
    have hxBoxA : x ⊩[M] □(#0) := by intro y z _ _; trivial;
    obtain ⟨z, Mxz, -⟩ := h M.val M.val_persistent M.fallible_val x x (refl x) hxBoxA x (refl x);
    exact ⟨z, Mxz⟩;

lemma serialMRel_of_valid_PDia (h : F ⊧ ◇⊤) : F.SerialMRel where
  serial_mRel x := by
    let M : Model κ := {
      toFrame := F,
      val := fun _ _ => True,
      val_persistent := by intros; trivial,
      fallible_val := by intros; trivial,
    }
    obtain ⟨z, Mxz, -⟩ := h M.val M.val_persistent M.fallible_val x x (refl x);
    exact ⟨z, Mxz⟩;

/-- `D` defines the frames whose `⊏` is serial. -/
theorem serialMRel_TFAE : List.TFAE [
  F.SerialMRel,
  ∀ A : BDFormula, F ⊧ (□A 🡒 ◇A),
  F ⊧ (□(#0) 🡒 ◇(#0)),
  F ⊧ ◇⊤,
] := by
  tfae_have 1 → 2 := by intro h A; exact valid_D_of_serialMRel;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := serialMRel_of_valid_D
  tfae_have 1 → 4 := by intro h; exact valid_PDia_of_serialMRel;
  tfae_have 4 → 1 := serialMRel_of_valid_PDia
  tfae_finish

end Frame

end CK

end
