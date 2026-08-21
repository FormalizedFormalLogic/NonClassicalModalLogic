module

public import NCML.CK.Frame.StrictlyAscendingMRel
public import NCML.CK.Canonical
public import NCML.CK.Soundness

@[expose] public section

namespace BDLogic

class TDia (L : BDLogic) where
  tDia {A} : (A 🡒 ◇A) ∈ L
export TDia (tDia)

end BDLogic

instance : LogicCKTDia.TDia := ⟨by grind⟩

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

open CK.Frame

lemma valid_of_mem_LogicCKTDia [M.TDia] (hA : A ∈ LogicCKTDia) : M ⊧ A :=
  valid_of_mem_logic
    (by rintro B ⟨C, rfl⟩; exact valid_of_toFrame_valid frameValidate_TDia_of_frame_TDia) hA

end Model

variable {L : BDLogic} [L.CK]

/-- No forbidden formula of a pair belongs to its theory, when `L` proves `T◇`. -/
lemma CanonicalPair.forbidden_not_mem_theory [L.TDia] {P : CanonicalPair L} {B : BDFormula}
  (hB : B ∈ P.forbidden) : B ∉ P.theory := by
  intro h;
  have h₁ : ◇B ∈ P.theory := P.theory.mdp (P.theory.subset L.tDia) h;
  have h₂ : ◇(⋁[B]) ∈ P.theory :=
    P.theory.mdp (BDTheory.provable_mem (dia_mono (imp_ldisj (by simp)))) h₁;
  exact P.avoid (◇(⋁[B])) ⟨⋁[B], ⟨[B], by simp, by grind, rfl⟩, rfl⟩ h₂;

private lemma avoid_disjSet_mdpClosure [L.TDia] (P : CanonicalPair L) :
  ∀ C ∈ disjSet P.forbidden, C ∉ BDTheory.mdpClosure (P.theory ∪ □⁻¹P.theory) := by
  rintro C ⟨K, hne, hsub, rfl⟩ hmem;
  obtain ⟨D, hD, E, hE, hDE⟩ := BDTheory.mdpClosure_union_finite_char hmem;
  have h₁ : □(D 🡒 ⋁K) ∈ P.theory :=
    P.theory.mdp (BDTheory.provable_mem (box_mono (mdp imp_swap hDE))) hE;
  have h₂ : (◇D 🡒 ◇(⋁K)) ∈ P.theory := P.theory.mdp (BDTheory.provable_mem kDia) h₁;
  have h₃ : ◇D ∈ P.theory := P.theory.mdp (P.theory.subset L.tDia) hD;
  exact P.avoid (◇(⋁K)) ⟨⋁K, ⟨K, hne, hsub, rfl⟩, rfl⟩ (P.theory.mdp h₂ h₃);

instance strictlyAscendingMRel_canonicalModel [L.TDia] : (canonicalModel L).StrictlyAscendingMRel where
  strictly_ascending_mRel P := by
    have : BDTheory.Of L (P.theory ∪ □⁻¹P.theory) := ⟨P.theory.subset.trans Set.subset_union_left⟩;
    obtain ⟨P₁, h₁, -, havoid⟩ :=
      CanonicalPair.exists_avoiding (L := L) (T := BDTheory.mdpClosure (P.theory ∪ □⁻¹P.theory))
      orDirected_disjSet (avoid_disjSet_mdpClosure P);
    have h₂ : P.theory ∪ □⁻¹P.theory ⊆ P₁.theory := BDTheory.subset_mdpClosure.trans h₁;
    use P₁;
    constructor;
    . exact CanonicalPair.mRel_of_avoid_disjSet (Set.subset_union_right.trans h₂) havoid;
    . exact Set.subset_union_left.trans h₂;

end CK

theorem LogicCKTDia_TFAE {A : BDFormula} : List.TFAE [
  A ∈ LogicCKTDia,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.TDia] → F ⊧ A,
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
    . infer_instance;
    . by_contra! hF;
      exact h₁ $ CK.Model.valid_of_toFrame_valid hF P;
  tfae_finish

end
