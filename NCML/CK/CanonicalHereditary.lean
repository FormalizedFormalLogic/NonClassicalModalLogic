module

public import NCML.CK.Logic.CKTBox
public import NCML.CK.Logic.CKTDia
public import NCML.CK.Logic.CK4Box
public import NCML.CK.Logic.CK4Dia
public import NCML.CK.Frame.ReflexiveMRel
public import NCML.CK.Frame.TransitiveMRel
public import NCML.CK.Frame.BackwardConfluent

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
  induction A generalizing P with
  | atom a => exact Iff.rfl;
  | falsum => exact Iff.rfl;
  | and A B ihA ihB =>
    constructor;
    · rintro ⟨hA, hB⟩;
      exact BDTheory.and_mem (ihA.mp hA) (ihB.mp hB);
    · intro h;
      constructor;
      . exact ihA.mpr (P.theory.mdp (BDTheory.provable_mem andElim₁) h);
      . exact ihB.mpr (P.theory.mdp (BDTheory.provable_mem andElim₂) h);
  | or A B ihA ihB =>
    constructor;
    · rintro (hA | hB);
      · exact P.theory.mdp (BDTheory.provable_mem orIntro₁) (ihA.mp hA);
      · exact P.theory.mdp (BDTheory.provable_mem orIntro₂) (ihB.mp hB);
    · intro h;
      rcases P.theory.prime h <;> grind;
  | imply A B ihA ihB =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨P₁, IPP₁, h₁, h₂⟩ := CanonicalPair.exists_iRel_of_imply_not_mem hc;
      exact h₂ (ihB.mp (h P₁ IPP₁ (ihA.mpr h₁)));
    · intro h P₁ IPP₁ h₁;
      exact ihB.mpr (P₁.theory.mdp (IPP₁ h) (ihA.mp h₁));
  | box A ih =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨P₁, MPP₁, h₁⟩ := exists_mRel_of_box_not_mem hc;
      exact h₁ (ih.mp (h P.erase P₁ CanonicalPair.iRel_erase MPP₁));
    · intro h P₁ P₂ IPP₁ MP₁P₂;
      exact ih.mpr (MP₁P₂.1 (IPP₁ h));
  | dia A ih =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨P₁, IPP₁, hblock⟩ := exists_iRel_of_dia_not_mem hc;
      obtain ⟨P₂, MP₁P₂, h₁⟩ := h P₁ IPP₁;
      exact hblock P₂ MP₁P₂ (ih.mp h₁);
    · intro h P₁ IPP₁;
      obtain ⟨P₂, MP₁P₂, h₁⟩ := exists_mRel_of_dia_mem (IPP₁ h);
      exact ⟨P₂, MP₁P₂, ih.mpr h₁⟩;

lemma exists_not_forces_of_not_mem (h : A ∉ L) :
  ∃ P : CanonicalPair L, P ⊮[canonicalModel L] A := by
  obtain ⟨P, -, -, havoid⟩ :=
    CanonicalPair.exists_avoiding (L := L) (T := L) (Z := {A}) orDirected_singleton
      (by rintro C rfl; exact h);
  exact ⟨P, fun h₁ => havoid A rfl (truthlemma.mp h₁)⟩;

end

variable {L : BDLogic} [L.CK]

instance reflexiveMRel_canonicalModel [L.TBox] : (canonicalModel L).ReflexiveMRel where
  refl_mRel P := ⟨fun _ hA => P.theory.mdp (P.theory.subset L.tBox) hA, subset_rfl⟩

instance transitiveMRel_canonicalModel [L.FourBox] : (canonicalModel L).TransitiveMRel where
  trans_mRel {P _P₁ _P₂} MPP₁ MP₁P₂ := ⟨
    fun _ hA => MP₁P₂.1 (MPP₁.1 (P.theory.mdp (P.theory.subset L.fourBox) hA)),
    MPP₁.2.trans MP₁P₂.2⟩

/-- - [BDF21, Proposition IV.7] -/
instance backwardConfluent_canonicalModel : (canonicalModel L).BackwardConfluent where
  backward_confluent {P P₁ P₂} MPP₁ IP₁P₂ :=
    ⟨P.erase, CanonicalPair.iRel_erase, fun _ hA => IP₁P₂ (MPP₁.1 hA), by simp⟩

end CK.Hereditary

end
