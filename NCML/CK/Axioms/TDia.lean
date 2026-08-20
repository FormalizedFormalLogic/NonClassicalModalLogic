module

public import NCML.CK.Axioms.D

@[expose] public section

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

open Model.Forces

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

class AscendingMRel (M : Model κ) : Prop where
  ascending_mRel : ∀ x : M.World, ∃ z, x ⊏ z ∧ (x ≼ z ∨ M.Fallible z)

export AscendingMRel (ascending_mRel)

class StrictlyAscendingMRel (M : Model κ) : Prop where
  strictly_ascending_mRel : ∀ x : M.World, ∃ z, x ⊏ z ∧ x ≼ z

export StrictlyAscendingMRel (strictly_ascending_mRel)

instance [M.StrictlyAscendingMRel] : M.AscendingMRel where
  ascending_mRel x := by
    obtain ⟨z, Mxz, Ixz⟩ := strictly_ascending_mRel x;
    refine ⟨z, Mxz, ?_⟩;
    left;
    exact Ixz;

instance [M.AscendingMRel] : M.SerialMRel where
  serial_mRel x := by
    obtain ⟨z, Mxz, _⟩ := ascending_mRel x;
    exact ⟨z, Mxz⟩;

lemma valid_TDia_of_ascendingMRel [M.AscendingMRel] : M ⊧ (A 🡒 ◇A) := by
  intro x y Ixy hyA u Iyu;
  obtain ⟨z, Muz, hz⟩ := ascending_mRel u;
  have huA : u ⊩[_] A := persistent hyA Iyu;
  rcases hz with Iuz | hzFallible;
  · exact ⟨z, Muz, persistent huA Iuz⟩;
  · exact ⟨z, Muz, of_fallible hzFallible⟩;

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
    obtain ⟨P₁, hXv, -, havoid⟩ :=
      CanonicalPair.exists_avoiding (L := L) (T := BDTheory.mdpClosure (P.theory ∪ □⁻¹P.theory))
        orDirected_disjSet (avoid_disjSet_mdpClosure hTDia P);
    have h₁ : P.theory ∪ □⁻¹P.theory ⊆ P₁.theory := BDTheory.subset_mdpClosure.trans hXv;
    exact ⟨P₁, CanonicalPair.mRel_of_avoid_disjSet (Set.subset_union_right.trans h₁) havoid,
      Set.subset_union_left.trans h₁⟩;

end CK

theorem LogicCKTDia_TFAE {A : BDFormula} : List.TFAE [
  A ∈ LogicCKTDia,
  ∀ {κ : Type 0}, ∀ M : CK.Model κ, [M.AscendingMRel] → M ⊧ A,
  ∀ {κ : Type 0}, ∀ M : CK.Model κ, [M.StrictlyAscendingMRel] → M ⊧ A,
] := by
  tfae_have 1 → 2 := fun h _ M _ => CK.Model.valid_of_mem_LogicCKTDia h
  tfae_have 2 → 3 := fun h _ M _ => h M
  tfae_have 3 → 1 := by
    contrapose!;
    intro h;
    obtain ⟨P, hw⟩ := CK.exists_not_forces_of_not_mem h;
    exact ⟨_, CK.canonicalModel LogicCKTDia, CK.strictlyAscendingMRel_canonicalModel (by grind),
      fun hM => hw (hM P)⟩;
  tfae_finish

end
