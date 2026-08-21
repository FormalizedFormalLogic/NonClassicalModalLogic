module

public import NCML.CK.Frame.SerialMRel
public import NCML.CK.Canonical
public import NCML.CK.Soundness

@[expose] public section

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

open CK.Frame

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
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.SerialMRel] → F ⊧ A,
] := by
  tfae_have 1 → 2 := LogicCKD.eq_CKPDia ▸ id
  tfae_have 2 → 3 := fun h _ F _ val vp fv =>
    CK.Model.valid_of_mem_LogicCKD (LogicCKD.eq_CKPDia ▸ h)
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
