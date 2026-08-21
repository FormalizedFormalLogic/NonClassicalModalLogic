module

public import NCML.CK.CanonicalHereditary
public import NCML.CK.Frame.CS4
public import NCML.CK.Soundness

@[expose] public section

instance : LogicCS4.TBox := ⟨LogicCS4.provable_TBox⟩
instance : LogicCS4.TDia := ⟨LogicCS4.provable_TDia⟩
instance : LogicCS4.FourBox := ⟨LogicCS4.provable_FourBox⟩
instance : LogicCS4.FourDia := ⟨LogicCS4.provable_FourDia⟩

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

open CK.Frame

lemma valid_of_mem_LogicCS4 [M.T] [M.Four] (hA : A ∈ LogicCS4) : M ⊧ A :=
  valid_of_mem_logic (by
    rintro B (((⟨C, rfl⟩ | ⟨C, rfl⟩) | ⟨C, rfl⟩) | ⟨C, rfl⟩);
    · exact valid_of_toFrame_valid frameValidate_TBox_of_frame_TBox;
    · exact valid_of_toFrame_valid frameValidate_TDia_of_frame_TDia;
    · exact valid_of_toFrame_valid frameValidate_FourBox_of_frame_FourBox;
    · exact valid_of_toFrame_valid frameValidate_FourDia_of_frame_FourDia;
  ) hA

end Model

end CK

theorem LogicCS4_TFAE {A : BDFormula} : List.TFAE [
  A ∈ LogicCS4,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.T] → [F.Four] → F ⊧ A,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.CS4] → F ⊧ A,
] := by
  tfae_have 1 → 2 := fun h _ F _ _ V V_per V_fal => CK.Model.valid_of_mem_LogicCS4 h
  tfae_have 2 → 3 := fun h _ F _ => h F
  tfae_have 3 → 1 := by
    contrapose!;
    intro h;
    obtain ⟨X, h₁⟩ := CK.hereditary_exists_not_forces_of_not_mem h;
    refine ⟨_, (CK.hereditaryCanonicalModel LogicCS4).toFrame, ?_⟩;
    and_intros;
    . infer_instance;
    . by_contra! hF;
      exact h₁ $ CK.Model.valid_of_toFrame_valid hF X;
  tfae_finish

end
