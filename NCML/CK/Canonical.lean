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

variable {L : BDLogic} {X : CanonicalPair L}

instance : X.theory.Mdp := X.theory_mdp

instance : X.theory.Prime := X.theory_prime

instance : X.theory.Of L := X.theory_of

instance [L.CK] : X.theory.Of LogicCK := BDTheory.of_logicCK (L := L)

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
  ∃ X : CanonicalPair L, T ⊆ X.theory ∧ X.forbidden = ∅ ∧ ∀ C ∈ Z, C ∉ X.theory := by
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

/-- The pair `X` with its forbidden formulas erased. -/
def erase (X : CanonicalPair L) : CanonicalPair L := ofTheory L X.theory

@[simp] lemma erase_theory : X.erase.theory = X.theory := rfl

@[simp] lemma erase_forbidden : X.erase.forbidden = ∅ := rfl

variable [L.CK]

lemma theory_eq_univ_of_bot_mem (h : ⊥ ∈ X.theory) : X.theory = Set.univ :=
  BDTheory.eq_univ_of_bot_mem h

lemma forbidden_eq_empty_of_bot_mem (h : ⊥ ∈ X.theory) : X.forbidden = ∅ := by
  ext B;
  simp only [Set.mem_empty_iff_false, iff_false];
  intro hB;
  exact X.avoid (◇(⋁[B])) ⟨⋁[B], ⟨[B], by simp, by grind, rfl⟩, rfl⟩
    (by rw [theory_eq_univ_of_bot_mem h]; trivial);

lemma eq_univ_of_bot_mem (h : ⊥ ∈ X.theory) : X = univ L := by
  have h₁ := theory_eq_univ_of_bot_mem h;
  have h₂ := forbidden_eq_empty_of_bot_mem h;
  cases X;
  subst h₁;
  subst h₂;
  rfl;

end CanonicalPair

namespace CanonicalPair

variable {L : BDLogic} [L.CK] {A B : BDFormula} {X : CanonicalPair L}

/-- Every forbidden formula of `X` blocks any `Y` avoiding `disjSet X.forbidden`. -/
lemma avoid_forbidden_of_avoid_disjSet {Y : CanonicalPair L}
  (havoid : ∀ C ∈ disjSet X.forbidden, C ∉ Y.theory) : ∀ B ∈ X.forbidden, B ∉ Y.theory := by
  intro B hB h₁;
  exact havoid (⋁[B]) ⟨[B], by simp, by simpa using hB, rfl⟩
    (Y.theory.mdp (BDTheory.provable_mem (imp_ldisj (by simp))) h₁);

private lemma avoid_disjSet_of_dia_mem (h : ◇A ∈ X.theory) :
  ∀ C ∈ disjSet X.forbidden, C ∉ BDTheory.impSet (□⁻¹X.theory) A := by
  rintro C ⟨K, hne, hsub, rfl⟩ hmem;
  have h₁ : (◇A 🡒 ◇(⋁K)) ∈ X.theory := X.theory.mdp (BDTheory.provable_mem kDia) hmem;
  exact X.avoid (◇(⋁K)) ⟨⋁K, ⟨K, hne, hsub, rfl⟩, rfl⟩ (X.theory.mdp h₁ h);

lemma avoid_diaDisjSet_of_dia_not_mem (h : ◇A ∉ X.theory) :
  ∀ C ∈ diaDisjSet {A}, C ∉ X.theory := by
  rintro C ⟨D, ⟨K, hne, hsub, rfl⟩, rfl⟩ hmem;
  have h₁ : (◇(⋁K) 🡒 ◇A) ∈ LogicCK := dia_mono (ldisj_imp (by
    intro B hB;
    obtain rfl : B = A := hsub B hB;
    exact imp_id));
  exact h (X.theory.mdp (BDTheory.provable_mem h₁) hmem);

end CanonicalPair

/-- The relation `⊏` of a canonical model together with the existence witnesses its truth lemma
needs, stated on the raw components (`theory`/`forbidden`) of `CanonicalPair L` rather than on
`Model.mRel`/`Model.iRel` to avoid referring to the model it will build. -/
structure CanonicalRel (L : BDLogic) where
  Rel : CanonicalPair L → CanonicalPair L → Prop
  rel_univ : ∀ {X : CanonicalPair L}, ⊥ ∈ X.theory → Rel X (CanonicalPair.univ L)
  exists_of_box_not_mem : ∀ {X : CanonicalPair L} {A : BDFormula}, □A ∉ X.theory →
    ∃ Y, (□⁻¹X.theory ⊆ Y.theory ∧ Rel X.erase Y) ∧ A ∉ Y.theory
  exists_of_dia_mem : ∀ {X : CanonicalPair L} {A : BDFormula}, ◇A ∈ X.theory →
    ∃ Y, (□⁻¹X.theory ⊆ Y.theory ∧ Rel X Y) ∧ A ∈ Y.theory
  exists_of_dia_not_mem : ∀ {X : CanonicalPair L} {A : BDFormula}, ◇A ∉ X.theory →
    ∃ Y, X.theory ⊆ Y.theory ∧
      ∀ Z, (□⁻¹Y.theory ⊆ Z.theory ∧ Rel Y Z) → A ∉ Z.theory

/-- The canonical model of `L` whose `⊏` is `□`-preimage inclusion together with `C.Rel`. -/
def canonicalModelWith (L : BDLogic) [L.CK] (C : CanonicalRel L) : Model (CanonicalPair L) where
  iRel' X Y := X.theory ⊆ Y.theory
  iRel_preorder := {
    refl := fun _ => subset_rfl,
    trans := fun _ _ _ => subset_trans
  }
  mRel' X Y := □⁻¹X.theory ⊆ Y.theory ∧ C.Rel X Y
  Fallible' X := ⊥ ∈ X.theory
  fallible_iRel' h IXY := IXY h
  fallible_mRel' h MXY := MXY.1 (by rw [CanonicalPair.theory_eq_univ_of_bot_mem h]; trivial)
  fallible_exists_mRel' h := ⟨CanonicalPair.univ L, Set.subset_univ _, C.rel_univ h⟩
  val X a := (#a) ∈ X.theory
  val_persistent h IXY := IXY h
  fallible_val h := by rw [CanonicalPair.theory_eq_univ_of_bot_mem h]; trivial

/-- No forbidden formula of `X` belongs to the theory of a `⊏`-successor. -/
def canonicalRel (L : BDLogic) [L.CK] : CanonicalRel L where
  Rel X Y := ∀ B ∈ X.forbidden, B ∉ Y.theory
  rel_univ h := by
    rw [CanonicalPair.forbidden_eq_empty_of_bot_mem h];
    simp
  exists_of_box_not_mem {X A} h := by
    obtain ⟨Y, h₁, -, havoid⟩ :=
      CanonicalPair.exists_avoiding (L := L) (T := □⁻¹X.theory) (Z := {A}) orDirected_singleton
        (by rintro C rfl; exact h);
    exact ⟨Y, ⟨h₁, by simp⟩, havoid A rfl⟩;
  exists_of_dia_mem {X A} h := by
    obtain ⟨Y, h₁, -, havoid⟩ :=
      CanonicalPair.exists_avoiding (L := L) (T := BDTheory.impSet (□⁻¹X.theory) A)
        (Z := disjSet X.forbidden) orDirected_disjSet (CanonicalPair.avoid_disjSet_of_dia_mem h);
    exact ⟨Y,
      ⟨BDTheory.subset_impSet.trans h₁, CanonicalPair.avoid_forbidden_of_avoid_disjSet havoid⟩,
      h₁ BDTheory.self_mem_impSet⟩;
  exists_of_dia_not_mem {X A} h := by
    obtain ⟨Y, hXY, hmdp, hprime, hof, havoid⟩ :=
      exists_prime_mdpClosed_avoiding (L := L) (T := X.theory) (Z := diaDisjSet {A})
        orDirected_diaDisjSet (CanonicalPair.avoid_diaDisjSet_of_dia_not_mem h);
    exact ⟨⟨Y, {A}, havoid⟩, hXY, fun _ MYZ => MYZ.2 A rfl⟩;

@[simp] lemma canonicalRel_rel {L : BDLogic} [L.CK] {X Y : CanonicalPair L} :
  (canonicalRel L).Rel X Y ↔ ∀ B ∈ X.forbidden, B ∉ Y.theory := Iff.rfl

/-- The canonical model of `L`, whose worlds are the pairs of `CanonicalPair L`.

- [MdP05, Definition 3, Lemma 3]
-/
def canonicalModel (L : BDLogic) [L.CK] : Model (CanonicalPair L) :=
  canonicalModelWith L (canonicalRel L)

namespace CanonicalPair

variable {L : BDLogic} [L.CK] {X : CanonicalPair L}

lemma mRel_of_avoid_disjSet {Y : CanonicalPair L} (hsub : □⁻¹X.theory ⊆ Y.theory)
  (havoid : ∀ C ∈ disjSet X.forbidden, C ∉ Y.theory) : (canonicalModel L).mRel X Y :=
  ⟨hsub, avoid_forbidden_of_avoid_disjSet havoid⟩

lemma iRel_erase {C : CanonicalRel L} : (canonicalModelWith L C).iRel X X.erase := subset_rfl

lemma exists_iRel_of_imply_not_mem {C : CanonicalRel L} {A B : BDFormula}
  (h : (A 🡒 B) ∉ X.theory) :
  ∃ Y : CanonicalPair L, (canonicalModelWith L C).iRel X Y ∧
    A ∈ Y.theory ∧ B ∉ Y.theory := by
  obtain ⟨Y, h₁, -, havoid⟩ :=
    exists_avoiding (L := L) (T := X.theory.impSet A) (Z := {B}) orDirected_singleton
      (by rintro D rfl; exact h);
  exact ⟨Y, BDTheory.subset_impSet.trans h₁, h₁ BDTheory.self_mem_impSet, havoid B rfl⟩;

end CanonicalPair

variable {L : BDLogic} [L.CK] {A : BDFormula}

/-- - [MdP05, Lemma 3] -/
lemma CanonicalRel.truthlemma (C : CanonicalRel L) {X : CanonicalPair L} :
  X ⊩[canonicalModelWith L C] A ↔ A ∈ X.theory := by
  induction A generalizing X with
  | atom a => exact Iff.rfl;
  | falsum => exact Iff.rfl;
  | and A B ihA ihB =>
    constructor;
    · rintro ⟨hA, hB⟩;
      exact BDTheory.and_mem (ihA.mp hA) (ihB.mp hB);
    · intro h;
      constructor;
      . exact ihA.mpr (X.theory.mdp (BDTheory.provable_mem andElim₁) h);
      . exact ihB.mpr (X.theory.mdp (BDTheory.provable_mem andElim₂) h);
  | or A B ihA ihB =>
    constructor;
    · rintro (hA | hB);
      · exact X.theory.mdp (BDTheory.provable_mem orIntro₁) (ihA.mp hA);
      · exact X.theory.mdp (BDTheory.provable_mem orIntro₂) (ihB.mp hB);
    · intro h;
      rcases X.theory.prime h <;> grind;
  | imply A B ihA ihB =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨Y, IXY, h₁, h₂⟩ := CanonicalPair.exists_iRel_of_imply_not_mem hc;
      exact h₂ (ihB.mp (h Y IXY (ihA.mpr h₁)));
    · intro h Y IXY h₁;
      exact ihB.mpr (Y.theory.mdp (IXY h) (ihA.mp h₁));
  | box A ih =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨Y, MXY, h₁⟩ := C.exists_of_box_not_mem hc;
      exact h₁ (ih.mp (h X.erase Y CanonicalPair.iRel_erase MXY));
    · intro h Y Z IXY MYZ;
      exact ih.mpr (MYZ.1 (IXY h));
  | dia A ih =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨Y, IXY, hblock⟩ := C.exists_of_dia_not_mem hc;
      obtain ⟨Z, MYZ, h₁⟩ := h Y IXY;
      exact hblock Z MYZ (ih.mp h₁);
    · intro h Y IXY;
      obtain ⟨Z, MYZ, h₁⟩ := C.exists_of_dia_mem (IXY h);
      exact ⟨Z, MYZ, ih.mpr h₁⟩;

lemma CanonicalPair.truthlemma {X : CanonicalPair L} :
  X ⊩[canonicalModel L] A ↔ A ∈ X.theory :=
  (canonicalRel L).truthlemma

/-- `h`-avoiding theories yield a world of `canonicalModelWith L C` not forcing `A`, for any `C`. -/
lemma CanonicalRel.exists_not_forces_of_not_mem (C : CanonicalRel L) (h : A ∉ L) :
  ∃ X : CanonicalPair L, X ⊮[canonicalModelWith L C] A := by
  obtain ⟨X, -, -, havoid⟩ :=
    CanonicalPair.exists_avoiding (L := L) (T := L) (Z := {A}) orDirected_singleton
      (by rintro B rfl; exact h);
  exact ⟨X, fun h₁ => havoid A rfl (C.truthlemma.mp h₁)⟩;

/-- - [MdP05, Theorem 2] -/
lemma exists_not_forces_of_not_mem (h : A ∉ L) :
  ∃ X : CanonicalPair L, X ⊮[canonicalModel L] A :=
  (canonicalRel L).exists_not_forces_of_not_mem h

end CK

end
