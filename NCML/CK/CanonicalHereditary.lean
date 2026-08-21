module

public import NCML.CK.Logic.CKTBox
public import NCML.CK.Logic.CKTDia
public import NCML.CK.Logic.CK4Box
public import NCML.CK.Logic.CK4Dia

@[expose] public section

/-!
# The hereditary canonical model

For a logic `L`, the canonical model on `CanonicalPair L` whose `⊏` hands the forbidden set on to
every `⊏`-successor rather than blocking it, and its truth lemma.

- [BDF21, Definition IV.4]
-/

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK.Hereditary

/-- The canonical model of `L` whose `⊏` hands `forbidden` on to every successor.

- [BDF21, Definition IV.4]
-/
def canonicalModel (L : BDLogic) [L.CK] : Model (CanonicalPair L) where
  iRel' P P₁ := P.theory ⊆ P₁.theory
  iRel_preorder := {
    refl := fun _ => subset_rfl,
    trans := fun _ _ _ => subset_trans
  }
  mRel' P P₁ := □⁻¹P.theory ⊆ P₁.theory ∧ P.forbidden ⊆ P₁.forbidden
  Fallible' P := ⊥ ∈ P.theory
  fallible_iRel' h IPP₁ := IPP₁ h
  fallible_mRel' h MPP₁ := MPP₁.1 (by rw [CanonicalPair.theory_eq_univ_of_bot_mem h]; trivial)
  fallible_exists_mRel' h :=
    ⟨CanonicalPair.univ L, Set.subset_univ _, by
      rw [CanonicalPair.forbidden_eq_empty_of_bot_mem h];
      exact Set.empty_subset _⟩
  val P a := (#a) ∈ P.theory
  val_persistent h IPP₁ := IPP₁ h
  fallible_val h := by rw [CanonicalPair.theory_eq_univ_of_bot_mem h]; trivial

section

variable {L : BDLogic} [L.CK] {A : BDFormula} {P : CanonicalPair L}

lemma exists_mRel_of_box_not_mem (h : □A ∉ P.theory) :
  ∃ P₁ : CanonicalPair L, (canonicalModel L).mRel P.erase P₁ ∧ A ∉ P₁.theory := by
  obtain ⟨P₁, h₁, -, havoid⟩ :=
    CanonicalPair.exists_avoiding (L := L) (T := □⁻¹P.theory) (Z := {A}) orDirected_singleton
      (by rintro C rfl; exact h);
  exact ⟨P₁, ⟨h₁, by simp⟩, havoid A rfl⟩;

private lemma avoid_diaDisjSet_impSet [L.FourDia] (h : ◇A ∈ P.theory) :
  ∀ C ∈ diaDisjSet P.forbidden, C ∉ BDTheory.impSet (□⁻¹P.theory) A := by
  rintro C ⟨D, hD, rfl⟩ hmem;
  have h₁ : (◇A 🡒 ◇◇D) ∈ P.theory := P.theory.mdp (BDTheory.provable_mem kDia) hmem;
  have h₂ : ◇◇D ∈ P.theory := P.theory.mdp h₁ h;
  exact P.avoid (◇D) ⟨D, hD, rfl⟩ (P.theory.mdp (P.theory.subset L.fourDia) h₂);

lemma exists_mRel_of_dia_mem [L.FourDia] (h : ◇A ∈ P.theory) :
  ∃ P₁ : CanonicalPair L, (canonicalModel L).mRel P P₁ ∧ A ∈ P₁.theory := by
  obtain ⟨Y, hY, hmdp, hprime, hof, havoid⟩ :=
    exists_prime_mdpClosed_avoiding (L := L) (T := BDTheory.impSet (□⁻¹P.theory) A)
      (Z := diaDisjSet P.forbidden) orDirected_diaDisjSet (avoid_diaDisjSet_impSet h);
  exact ⟨⟨Y, P.forbidden, havoid⟩, ⟨BDTheory.subset_impSet.trans hY, subset_rfl⟩,
    hY BDTheory.self_mem_impSet⟩;

lemma exists_iRel_of_dia_not_mem [L.TDia] (h : ◇A ∉ P.theory) :
  ∃ P₁ : CanonicalPair L, (canonicalModel L).iRel P P₁ ∧
  ∀ P₂ : CanonicalPair L, (canonicalModel L).mRel P₁ P₂ → A ∉ P₂.theory := by
  refine ⟨⟨P.theory, {A}, CanonicalPair.avoid_diaDisjSet_of_dia_not_mem h⟩, subset_rfl, ?_⟩;
  intro P₂ MP₁P₂;
  exact CanonicalPair.forbidden_not_mem_theory (MP₁P₂.2 rfl);

end

section

variable {L : BDLogic} [L.CK] [L.TDia] [L.FourDia] {A : BDFormula} {P : CanonicalPair L}

/-- - [BDF21, Lemma IV.9] -/
lemma truthlemma : P ⊩[canonicalModel L] A ↔ A ∈ P.theory := by
  sorry

lemma exists_not_forces_of_not_mem (h : A ∉ L) :
  ∃ P : CanonicalPair L, P ⊮[canonicalModel L] A := by
  sorry

end

end CK.Hereditary

end
