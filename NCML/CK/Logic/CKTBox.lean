module

public import NCML.CK.Frame.ReturningMRel
public import NCML.CK.Canonical
public import NCML.CK.Soundness

@[expose] public section

open ProvableBDHilbert

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

open CK.Frame

lemma valid_of_mem_LogicCKTBox [M.ReflexiveMComp] (hA : A ∈ LogicCKTBox) : M ⊧ A :=
  valid_of_mem_logic (by rintro B ⟨C, rfl⟩; exact valid_TBox_of_reflexiveMComp) hA

end Model

variable {L : BDLogic} [L.CK]

lemma returningMRel_canonicalModel (hTBox : ∀ {A}, (□A 🡒 A) ∈ L) : (canonicalModel L).ReturningMRel where
  returning_mRel P := ⟨
    P.erase,
    CanonicalPair.iRel_erase,
    fun _ hA => P.theory.mdp (P.theory.subset (L := L) hTBox) hA,
    by simp
  ⟩

end CK

theorem LogicCKTBox_TFAE {A : BDFormula} : List.TFAE [
  A ∈ LogicCKTBox,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.ReflexiveMComp] → F ⊧ A,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.ReturningMRel] → F ⊧ A,
] := by
  tfae_have 1 → 2 := fun h _ F _ V V_per V_fal => CK.Model.valid_of_mem_LogicCKTBox h
  tfae_have 2 → 3 := fun h _ F _ => h F
  tfae_have 3 → 1 := by
    contrapose!;
    intro h;
    obtain ⟨P, h₁⟩ := CK.exists_not_forces_of_not_mem h;
    refine ⟨_, (CK.canonicalModel LogicCKTBox).toFrame, ?_⟩;
    and_intros;
    . exact CK.returningMRel_canonicalModel (by grind);
    . by_contra! hF;
      exact h₁ $ CK.Model.valid_of_toFrame_valid hF P;
  tfae_finish

end
