module

public import NCML.CK.Canonical

@[expose] public section

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

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
  obtain ⟨z, Mxz⟩ := serial_mRel y;
  exact ⟨z, Mxz, by grind⟩;

lemma valid_of_mem_LogicCKD [M.SerialMRel] (hA : A ∈ LogicCKD) : M ⊧ A :=
  valid_of_mem_logic (by rintro B ⟨C, rfl⟩; exact valid_D_of_serialMRel) hA

lemma valid_of_mem_LogicCKPDia [M.SerialMRel] (hA : A ∈ LogicCKPDia) : M ⊧ A :=
  valid_of_mem_logic (by rintro B rfl; exact valid_PDia_of_serialMRel) hA

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
    obtain ⟨y, Mxy, -⟩ := h M.val M.val_persistent M.fallible_val x x (refl x) hxBoxA x (refl x);
    exact ⟨y, Mxy⟩;

lemma serialMRel_of_valid_PDia (h : F ⊧ ◇⊤) : F.SerialMRel where
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

variable {L : BDLogic} [L.CK]

lemma serialMRel_canonicalModel (hD : ∀ {A}, (□A 🡒 ◇A) ∈ L) : (canonicalModel L).SerialMRel where
  serial_mRel P := by
    have h : ∀ C ∈ disjSet P.forbidden, C ∉ □⁻¹P.theory := by
      rintro C ⟨K, hne, hsub, rfl⟩ hmem;
      exact P.avoid (◇(⋁K)) ⟨⋁K, ⟨K, hne, hsub, rfl⟩, rfl⟩
        (P.theory.mdp (P.theory.subset (L := L) hD) hmem);
    obtain ⟨P₁, h₁, -, havoid⟩ :=
      CanonicalPair.exists_avoiding (L := L) (T := □⁻¹P.theory) orDirected_disjSet h;
    exact ⟨P₁, CanonicalPair.mRel_of_avoid_disjSet h₁ havoid⟩;

end CK

theorem LogicCKD_TFAE {A : BDFormula} : List.TFAE [
  A ∈ LogicCKD,
  A ∈ LogicCKPDia,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.SerialMRel] → F ⊧ A,
] := by
  tfae_have 1 → 2 := LogicCKD.eq_CKPDia ▸ id
  tfae_have 2 → 3 := fun h _ F _ V V_per V_fal => CK.Model.valid_of_mem_LogicCKPDia h
  tfae_have 3 → 1 := by
    contrapose!;
    intro h;
    obtain ⟨P, h₁⟩ := CK.exists_not_forces_of_not_mem h;
    refine ⟨_, (CK.canonicalModel LogicCKD).toFrame, ?_⟩;
    and_intros;
    . exact CK.serialMRel_canonicalModel (by grind);
    . by_contra! hF;
      exact h₁ $ CK.Model.valid_of_toFrame_valid hF P;
  tfae_finish

end
