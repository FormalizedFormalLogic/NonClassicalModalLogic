module

public import NCML.CK.Canonical

@[expose] public section

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

class SerialMRel (M : Model κ) : Prop where
  serial_mRel : ∀ x : M.World, ∃ y, x ⊏ y

export SerialMRel (serial_mRel)

lemma valid_D_of_serialMRel [M.SerialMRel] : M ⊧ (□A 🡒 ◇A) := by
  intro x y Ixy hyBoxA u Iyu;
  obtain ⟨z, Muz⟩ := serial_mRel u;
  exact ⟨z, Muz, hyBoxA u z Iyu Muz⟩;

lemma valid_PDia_of_serialMRel [M.SerialMRel] : M ⊧ ◇⊤ := by
  intro x y Ixy;
  obtain ⟨z, Mxz⟩ := serial_mRel y;
  exact ⟨z, Mxz, by grind⟩;

lemma valid_of_mem_LogicCKD [M.SerialMRel] (hA : A ∈ LogicCKD) : M ⊧ A :=
  valid_of_mem_logic (by rintro B ⟨C, rfl⟩; exact valid_D_of_serialMRel) hA

lemma valid_of_mem_LogicCKPDia [M.SerialMRel] (hA : A ∈ LogicCKPDia) : M ⊧ A :=
  valid_of_mem_logic (by rintro B rfl; exact valid_PDia_of_serialMRel) hA

end Model

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
  ∀ {κ : Type 0}, ∀ M : CK.Model κ, [M.SerialMRel] → M ⊧ A,
] := by
  tfae_have 1 → 2 := LogicCKD.eq_CKPDia ▸ id
  tfae_have 2 → 3 := fun h _ M _ => CK.Model.valid_of_mem_LogicCKPDia h
  tfae_have 3 → 1 := by
    contrapose!;
    intro h;
    obtain ⟨P, h₁⟩ := CK.exists_not_forces_of_not_mem h;
    exact ⟨_, CK.canonicalModel LogicCKD, CK.serialMRel_canonicalModel (by grind),
      fun hM => h₁ (hM P)⟩;
  tfae_finish

end
