module

public import NCML.CK.Frame.StrictlyAscendingMRel
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

lemma valid_of_mem_LogicCKTDia [M.AscendingMRel] (hA : A ∈ LogicCKTDia) : M ⊧ A :=
  valid_of_mem_logic (by rintro B ⟨C, rfl⟩; exact valid_TDia_of_ascendingMRel) hA

end Model

variable {L : BDLogic} [L.CK]

private lemma avoid_disjSet_mdpClosure (hTDia : ∀ {A}, (A 🡒 ◇A) ∈ L) (P : CanonicalPair L) :
  ∀ C ∈ disjSet P.forbidden, C ∉ BDTheory.mdpClosure (P.theory ∪ □⁻¹P.theory) := by
  rintro C ⟨K, hne, hsub, rfl⟩ hmem;
  obtain ⟨D, hD, E, hE, hDE⟩ := BDTheory.mdpClosure_union_finite_char hmem;
  have h₁ : □(D 🡒 ⋁K) ∈ P.theory :=
    P.theory.mdp (BDTheory.provable_mem (box_mono (mdp imp_swap hDE))) hE;
  have h₂ : (◇D 🡒 ◇(⋁K)) ∈ P.theory := P.theory.mdp (BDTheory.provable_mem kDia) h₁;
  have h₃ : ◇D ∈ P.theory := P.theory.mdp (P.theory.subset (L := L) hTDia) hD;
  exact P.avoid (◇(⋁K)) ⟨⋁K, ⟨K, hne, hsub, rfl⟩, rfl⟩ (P.theory.mdp h₂ h₃);

lemma strictlyAscendingMRel_canonicalModel (hTDia : ∀ {A}, (A 🡒 ◇A) ∈ L) :
  (canonicalModel L).StrictlyAscendingMRel where
  strictly_ascending_mRel P := by
    have : BDTheory.Of L (P.theory ∪ □⁻¹P.theory) :=
      ⟨(P.theory.subset (L := L)).trans Set.subset_union_left⟩;
    obtain ⟨P₁, h₁, -, havoid⟩ :=
      CanonicalPair.exists_avoiding (L := L) (T := BDTheory.mdpClosure (P.theory ∪ □⁻¹P.theory))
      orDirected_disjSet (avoid_disjSet_mdpClosure hTDia P);
    have h₂ : P.theory ∪ □⁻¹P.theory ⊆ P₁.theory := BDTheory.subset_mdpClosure.trans h₁;
    use P₁;
    constructor;
    . exact CanonicalPair.mRel_of_avoid_disjSet (Set.subset_union_right.trans h₂) havoid;
    . exact Set.subset_union_left.trans h₂;

end CK

theorem LogicCKTDia_TFAE {A : BDFormula} : List.TFAE [
  A ∈ LogicCKTDia,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.AscendingMRel] → F ⊧ A,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.StrictlyAscendingMRel] → F ⊧ A,
] := by
  tfae_have 1 → 2 := fun h _ F _ V V_per V_fal => CK.Model.valid_of_mem_LogicCKTDia h
  tfae_have 2 → 3 := fun h _ F _ => h F
  tfae_have 3 → 1 := by
    contrapose!;
    intro h;
    obtain ⟨P, h₁⟩ := CK.exists_not_forces_of_not_mem h;
    refine ⟨_, (CK.canonicalModel LogicCKTDia).toFrame, ?_⟩;
    and_intros;
    . exact CK.strictlyAscendingMRel_canonicalModel (by grind);
    . by_contra! hF;
      exact h₁ $ CK.Model.valid_of_toFrame_valid hF P;
  tfae_finish

end
