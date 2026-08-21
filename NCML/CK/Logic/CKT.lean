module

public import NCML.CK.Frame.T
public import NCML.CK.Logic.CKTBox
public import NCML.CK.Logic.CKTDia

@[expose] public section

instance : LogicCKT.TBox := ⟨LogicCKT.provable_TBox⟩
instance : LogicCKT.TDia := ⟨LogicCKT.provable_TDia⟩

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

open CK.Frame

lemma valid_of_mem_LogicCKT [M.TBox] [M.TDia] (hA : A ∈ LogicCKT) : M ⊧ A :=
  valid_of_mem_logic (by
    rintro B (⟨C, rfl⟩ | ⟨C, rfl⟩);
    · exact valid_of_toFrame_valid frameValidate_TBox_of_frame_TBox;
    · exact valid_of_toFrame_valid frameValidate_TDia_of_frame_TDia;
  ) hA

end Model

variable {L : BDLogic} [L.CK]

instance t_canonicalModel [L.TBox] [L.TDia] : (canonicalModel L).T where
  t P := by
    have hbox : □⁻¹P.theory ⊆ P.theory := fun _ hA => P.theory.mdp (P.theory.subset L.tBox) hA;
    refine ⟨P.erase, CanonicalPair.iRel_erase, ⟨hbox, ?_⟩, hbox, ?_⟩;
    . exact fun _ hB => CanonicalPair.forbidden_not_mem_theory (P := P) hB;
    . simp;

end CK

theorem LogicCKT_TFAE {A : BDFormula} : List.TFAE [
  A ∈ LogicCKT,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.TBox] → [F.TDia] → F ⊧ A,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.T] → F ⊧ A,
] := by
  tfae_have 1 → 2 := fun h _ F _ _ V V_per V_fal => CK.Model.valid_of_mem_LogicCKT h
  tfae_have 2 → 3 := fun h _ F _ => h F
  tfae_have 3 → 1 := by
    contrapose!;
    intro h;
    obtain ⟨P, h₁⟩ := CK.exists_not_forces_of_not_mem h;
    refine ⟨_, (CK.canonicalModel LogicCKT).toFrame, ?_⟩;
    and_intros;
    . infer_instance;
    . by_contra! hF;
      exact h₁ $ CK.Model.valid_of_toFrame_valid hF P;
  tfae_finish

end
