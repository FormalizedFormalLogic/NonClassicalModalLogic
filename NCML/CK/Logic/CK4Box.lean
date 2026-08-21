module

public import NCML.CK.Frame.FourBox
public import NCML.CK.Canonical
public import NCML.CK.Soundness

@[expose] public section

namespace BDLogic

class FourBox (L : BDLogic) where
  fourBox {A} : (□A 🡒 □□A) ∈ L
export FourBox (fourBox)

end BDLogic

instance : LogicCK4Box.FourBox := ⟨by grind⟩

open ProvableBDHilbert

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

open CK.Frame

lemma valid_of_mem_LogicCK4Box [M.FourBox] (hA : A ∈ LogicCK4Box) : M ⊧ A :=
  valid_of_mem_logic
    (by rintro B ⟨C, rfl⟩; exact valid_of_toFrame_valid frameValidate_FourBox_of_frame_FourBox) hA

end Model

variable {L : BDLogic} [L.CK]

instance fourBox_canonicalModel [L.FourBox] : (canonicalModel L).FourBox where
  fourBox {P P₁ P₂ P₃} MPP₁ IP₁P₂ MP₂P₃ _ := by
    refine ⟨P.erase, P₃.erase, CanonicalPair.iRel_erase, ⟨?_, by simp⟩, subset_rfl⟩;
    intro A hA;
    have h₁ : □□A ∈ P.theory := P.theory.mdp (P.theory.subset L.fourBox) hA;
    have h₂ : □A ∈ P₁.theory := MPP₁.1 h₁;
    have h₃ : □A ∈ P₂.theory := IP₁P₂ h₂;
    exact MP₂P₃.1 h₃;

end CK

theorem LogicCK4Box_TFAE {A : BDFormula} : List.TFAE [
  A ∈ LogicCK4Box,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.FourBox] → F ⊧ A,
] := by
  tfae_have 1 → 2 := fun h _ F _ V V_per V_fal => CK.Model.valid_of_mem_LogicCK4Box h
  tfae_have 2 → 1 := by
    contrapose!;
    intro h;
    obtain ⟨P, h₁⟩ := CK.exists_not_forces_of_not_mem h;
    refine ⟨_, (CK.canonicalModel LogicCK4Box).toFrame, ?_⟩;
    and_intros;
    . infer_instance;
    . by_contra! hF;
      exact h₁ $ CK.Model.valid_of_toFrame_valid hF P;
  tfae_finish

end
