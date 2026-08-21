module

public import NCML.CK.Frame.Four
public import NCML.CK.Logic.CK4Box
public import NCML.CK.Logic.CK4Dia

@[expose] public section

instance : LogicCK4.FourBox := ⟨LogicCK4.provable_FourBox⟩
instance : LogicCK4.FourDia := ⟨LogicCK4.provable_FourDia⟩

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

open CK.Frame

lemma valid_of_mem_LogicCK4 [M.Four] (hA : A ∈ LogicCK4) : M ⊧ A :=
  valid_of_mem_logic (by
    rintro B (⟨C, rfl⟩ | ⟨C, rfl⟩);
    · exact valid_of_toFrame_valid frameValidate_FourBox_of_frame_FourBox;
    · exact valid_of_toFrame_valid frameValidate_FourDia_of_frame_FourDia;
  ) hA

end Model

variable {L : BDLogic} [L.CK]

instance four_canonicalModel [L.FourBox] [L.FourDia] : (canonicalModel L).Four where

end CK

theorem LogicCK4_TFAE {A : BDFormula} : List.TFAE [
  A ∈ LogicCK4,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.Four] → F ⊧ A,
] := by
  tfae_have 1 → 2 := fun h _ F _ V V_per V_fal => CK.Model.valid_of_mem_LogicCK4 h
  tfae_have 2 → 1 := by
    contrapose!;
    intro h;
    obtain ⟨P, h₁⟩ := CK.exists_not_forces_of_not_mem h;
    refine ⟨_, (CK.canonicalModel LogicCK4).toFrame, ?_⟩;
    and_intros;
    . infer_instance;
    . by_contra! hF;
      exact h₁ $ CK.Model.valid_of_toFrame_valid hF P;
  tfae_finish

end
