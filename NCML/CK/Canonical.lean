module

public import NCML.CK.Semantics
public import NCML.Hilbert.Theory

@[expose] public section

/-!
# The pair canonical model

For a logic `L`, the canonical model whose worlds are the pairs `(T, Θ)` of a prime MP-closed
theory `T` of `L` and a set `Θ` of formulas omitted by every `⊏`-successor, and its truth lemma.

- [MdP05, Definition 3, Lemma 3, Theorem 2]
-/

open BDFormula ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

/-- A pair of a prime MP-closed theory `theory` of `L` and a set `forbidden` of formulas none of
whose nonempty finite disjunctions is possible in `theory`.

- [MdP05, Definition 2]
-/
structure CanonicalPair (L : BDLogic) where
  theory : BDTheory
  forbidden : BDFormulaSet
  [theory_mdp : theory.Mdp]
  [theory_prime : theory.Prime]
  [theory_of : theory.Of L]
  avoid : ∀ B ∈ diaDisjSet forbidden, B ∉ theory

namespace CanonicalPair

variable {L : BDLogic} {P : CanonicalPair L}

instance : P.theory.Mdp := P.theory_mdp

instance : P.theory.Prime := P.theory_prime

instance : P.theory.Of L := P.theory_of

instance [L.CK] : P.theory.Of LogicCK := BDTheory.of_logicCK (L := L)

/-- The pair `(T, ∅)` of a prime MP-closed theory `T` of `L`. -/
def ofTheory (L : BDLogic) (T : BDTheory) [T.Mdp] [T.Prime] [T.Of L] : CanonicalPair L where
  theory := T
  forbidden := ∅
  theory_mdp := ‹_›
  theory_prime := ‹_›
  theory_of := ‹_›
  avoid := by simp

section

variable (L : BDLogic) (T : BDTheory) [T.Mdp] [T.Prime] [T.Of L]

@[simp] lemma ofTheory_theory : (ofTheory L T).theory = T := rfl

@[simp] lemma ofTheory_forbidden : (ofTheory L T).forbidden = ∅ := rfl

end

/-- An MP-closed theory of `L` disjoint from an ⋎-directed `Z` extends to the theory of a pair
with no forbidden formulas, still disjoint from `Z`. -/
lemma exists_avoiding [L.CK] {T : BDTheory} {Z : BDFormulaSet} [T.Mdp] [T.Of L]
  (hdir : OrDirected L Z) (hdisj : ∀ C ∈ Z, C ∉ T) :
  ∃ P₁ : CanonicalPair L, T ⊆ P₁.theory ∧ P₁.forbidden = ∅ ∧ ∀ C ∈ Z, C ∉ P₁.theory := by
  obtain ⟨Y, hTY, hmdp, hprime, hof, havoid⟩ := exists_prime_mdpClosed_avoiding hdir hdisj;
  exact ⟨ofTheory L Y, hTY, rfl, havoid⟩;

/-- The pair of the set of all formulas and the empty set of forbidden formulas. -/
def univ (L : BDLogic) : CanonicalPair L where
  theory := Set.univ
  forbidden := ∅
  theory_mdp := ⟨by tauto⟩
  theory_prime := ⟨by tauto⟩
  theory_of := ⟨by tauto⟩
  avoid := by simp

@[simp] lemma univ_theory : (univ L).theory = Set.univ := rfl

@[simp] lemma univ_forbidden : (univ L).forbidden = ∅ := rfl

variable [L.CK]

lemma theory_eq_univ_of_bot_mem (h : ⊥ ∈ P.theory) : P.theory = Set.univ :=
  BDTheory.eq_univ_of_bot_mem h

lemma forbidden_eq_empty_of_bot_mem (h : ⊥ ∈ P.theory) : P.forbidden = ∅ := by
  ext B;
  simp only [Set.mem_empty_iff_false, iff_false];
  intro hB;
  exact P.avoid (◇(⋁[B])) ⟨⋁[B], ⟨[B], by simp, by grind, rfl⟩, rfl⟩
    (by rw [theory_eq_univ_of_bot_mem h]; trivial);

lemma eq_univ_of_bot_mem (h : ⊥ ∈ P.theory) : P = univ L := by
  have h₁ := theory_eq_univ_of_bot_mem h;
  have h₂ := forbidden_eq_empty_of_bot_mem h;
  cases P;
  subst h₁;
  subst h₂;
  rfl;

end CanonicalPair

/-- The canonical model of `L`, whose worlds are the pairs of `CanonicalPair L`.

- [MdP05, Definition 3, Lemma 3]
-/
def canonicalModel (L : BDLogic) [L.CK] : Model (CanonicalPair L) where
  iRel' P P₁ := P.theory ⊆ P₁.theory
  iRel_preorder := {
    refl := fun _ => subset_rfl,
    trans := fun _ _ _ => subset_trans
  }
  mRel' P P₁ := □⁻¹P.theory ⊆ P₁.theory ∧ ∀ B ∈ P.forbidden, B ∉ P₁.theory
  Fallible' P := ⊥ ∈ P.theory
  fallible_iRel' h IPP₁ := IPP₁ h
  fallible_mRel' h MPP₁ := MPP₁.1 (by rw [CanonicalPair.theory_eq_univ_of_bot_mem h]; trivial)
  fallible_exists_mRel' h :=
    ⟨CanonicalPair.univ L, Set.subset_univ _, by
      rw [CanonicalPair.forbidden_eq_empty_of_bot_mem h];
      simp⟩
  val P a := (#a) ∈ P.theory
  val_persistent h IPP₁ := IPP₁ h
  fallible_val h := by rw [CanonicalPair.theory_eq_univ_of_bot_mem h]; trivial

namespace CanonicalPair

variable {L : BDLogic} {A B : BDFormula} {P : CanonicalPair L}

/-- The pair `P` with its forbidden formulas erased. -/
def erase (P : CanonicalPair L) : CanonicalPair L := ofTheory L P.theory

@[simp] lemma erase_theory : P.erase.theory = P.theory := rfl

@[simp] lemma erase_forbidden : P.erase.forbidden = ∅ := rfl

variable [L.CK]

lemma iRel_erase : (canonicalModel L).iRel P P.erase := subset_rfl

lemma exists_iRel_of_imply_not_mem (h : (A 🡒 B) ∉ P.theory) :
  ∃ P₁ : CanonicalPair L, (canonicalModel L).iRel P P₁ ∧ A ∈ P₁.theory ∧ B ∉ P₁.theory := by
  obtain ⟨P₁, h₁, -, havoid⟩ :=
    exists_avoiding (L := L) (T := P.theory.impSet A) (Z := {B}) orDirected_singleton
      (by rintro C rfl; exact h);
  exact ⟨P₁, BDTheory.subset_impSet.trans h₁, h₁ BDTheory.self_mem_impSet, havoid B rfl⟩;

lemma exists_mRel_of_box_not_mem (h : □A ∉ P.theory) :
  ∃ P₁ : CanonicalPair L, (canonicalModel L).mRel P.erase P₁ ∧ A ∉ P₁.theory := by
  obtain ⟨P₁, h₁, -, havoid⟩ :=
    exists_avoiding (L := L) (T := □⁻¹P.theory) (Z := {A}) orDirected_singleton
      (by rintro C rfl; exact h);
  exact ⟨P₁, ⟨h₁, by simp⟩, havoid A rfl⟩;

lemma mRel_of_avoid_disjSet {P₁ : CanonicalPair L} (hsub : □⁻¹P.theory ⊆ P₁.theory)
  (havoid : ∀ C ∈ disjSet P.forbidden, C ∉ P₁.theory) : (canonicalModel L).mRel P P₁ := by
  refine ⟨hsub, ?_⟩;
  intro B hB h₁;
  exact havoid (⋁[B]) ⟨[B], by simp, by simpa using hB, rfl⟩
    (P₁.theory.mdp (BDTheory.provable_mem (imp_ldisj (by simp))) h₁);

private lemma avoid_disjSet_of_dia_mem (h : ◇A ∈ P.theory) :
  ∀ C ∈ disjSet P.forbidden, C ∉ BDTheory.impSet (□⁻¹P.theory) A := by
  rintro C ⟨K, hne, hsub, rfl⟩ hmem;
  have h₁ : (◇A 🡒 ◇(⋁K)) ∈ P.theory := P.theory.mdp (BDTheory.provable_mem kDia) hmem;
  exact P.avoid (◇(⋁K)) ⟨⋁K, ⟨K, hne, hsub, rfl⟩, rfl⟩ (P.theory.mdp h₁ h);

lemma exists_mRel_of_dia_mem (h : ◇A ∈ P.theory) :
  ∃ P₁ : CanonicalPair L, (canonicalModel L).mRel P P₁ ∧ A ∈ P₁.theory := by
  obtain ⟨P₁, h₁, -, havoid⟩ :=
    exists_avoiding (L := L) (T := BDTheory.impSet (□⁻¹P.theory) A) (Z := disjSet P.forbidden)
      orDirected_disjSet (avoid_disjSet_of_dia_mem h);
  exact ⟨P₁, mRel_of_avoid_disjSet (BDTheory.subset_impSet.trans h₁) havoid,
    h₁ BDTheory.self_mem_impSet⟩;

private lemma avoid_diaDisjSet_of_dia_not_mem (h : ◇A ∉ P.theory) :
  ∀ C ∈ diaDisjSet {A}, C ∉ P.theory := by
  rintro C ⟨D, ⟨K, hne, hsub, rfl⟩, rfl⟩ hmem;
  have h₁ : (◇(⋁K) 🡒 ◇A) ∈ LogicCK := dia_mono (ldisj_imp (by
    intro B hB;
    obtain rfl : B = A := hsub B hB;
    exact imp_id));
  exact h (P.theory.mdp (BDTheory.provable_mem h₁) hmem);

lemma exists_iRel_of_dia_not_mem (h : ◇A ∉ P.theory) :
  ∃ P₁ : CanonicalPair L, (canonicalModel L).iRel P P₁ ∧
  ∀ P₂ : CanonicalPair L, (canonicalModel L).mRel P₁ P₂ → A ∉ P₂.theory := by
  obtain ⟨Y, hXY, hmdp, hprime, hof, havoid⟩ :=
    exists_prime_mdpClosed_avoiding (L := L) (T := P.theory) (Z := diaDisjSet {A})
      orDirected_diaDisjSet (avoid_diaDisjSet_of_dia_not_mem h);
  exact ⟨⟨Y, {A}, havoid⟩, hXY, fun _ MP₁P₂ => MP₁P₂.2 A rfl⟩;

/-- - [MdP05, Lemma 3] -/
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
      obtain ⟨P₁, IPP₁, h₁, h₂⟩ := exists_iRel_of_imply_not_mem hc;
      exact h₂ (ihB.mp (h P₁ IPP₁ (ihA.mpr h₁)));
    · intro h P₁ IPP₁ h₁;
      exact ihB.mpr (P₁.theory.mdp (IPP₁ h) (ihA.mp h₁));
  | box A ih =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨P₁, MPP₁, h₁⟩ := exists_mRel_of_box_not_mem hc;
      exact h₁ (ih.mp (h P.erase P₁ iRel_erase MPP₁));
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

end CanonicalPair

section

variable {L : BDLogic} [L.CK] {A : BDFormula}

/-- - [MdP05, Theorem 2] -/
lemma exists_not_forces_of_not_mem (h : A ∉ L) :
  ∃ P : CanonicalPair L, P ⊮[canonicalModel L] A := by
  obtain ⟨P, -, -, havoid⟩ :=
    CanonicalPair.exists_avoiding (L := L) (T := L) (Z := {A}) orDirected_singleton
      (by rintro C rfl; exact h);
  exact ⟨P, fun h₁ => havoid A rfl (CanonicalPair.truthlemma.mp h₁)⟩;

end

end CK

end
