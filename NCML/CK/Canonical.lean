module

public import NCML.CK.Semantics
public import NCML.CK.Soundness
public import NCML.Hilbert.Theory

@[expose] public section

/-!
# The pair canonical model

For an axiom set `𝔸`, the canonical model whose worlds are the pairs `(T, Θ)` of a prime
MP-closed theory `T` of `logic 𝔸` and a set `Θ` of formulas omitted by every `⊏`-successor.

- [MdP05, Definition 3]
-/

open BDFormula ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace BDTheory

variable {𝔸 : Set BDFormula} {T : BDTheory}

/-- Every theory of `logic 𝔸` is a theory of `LogicCK`. -/
lemma of_logicCK [T.Of (logic 𝔸)] : T.Of LogicCK :=
  ⟨(logic_monotone (Set.empty_subset 𝔸)).trans (subset (L := logic 𝔸))⟩

end BDTheory


namespace CK

/-- A pair of a prime MP-closed theory `th` of `logic 𝔸` and a set `forb` of formulas none of
whose nonempty finite disjunctions is possible in `th`.

- [MdP05, Definition 2]
-/
structure CanonicalPair (𝔸 : Set BDFormula) where
  th : BDTheory
  forb : BDFormulaSet
  mdp : th.Mdp
  prime : th.Prime
  of : th.Of (logic 𝔸)
  avoid : ∀ B ∈ diaDisjSet forb, B ∉ th

namespace CanonicalPair

variable {𝔸 : Set BDFormula} {w : CanonicalPair 𝔸}

instance : w.th.Mdp := w.mdp

instance : w.th.Prime := w.prime

instance : w.th.Of (logic 𝔸) := w.of

instance : w.th.Of LogicCK := BDTheory.of_logicCK (𝔸 := 𝔸)

/-- The pair `(T, ∅)` of a prime MP-closed theory `T` of `logic 𝔸`. -/
def ofTheory (𝔸 : Set BDFormula) (T : BDTheory) [T.Mdp] [T.Prime] [T.Of (logic 𝔸)] :
  CanonicalPair 𝔸 where
  th := T
  forb := ∅
  mdp := ‹_›
  prime := ‹_›
  of := ‹_›
  avoid := by simp

section

variable (𝔸 : Set BDFormula) (T : BDTheory) [T.Mdp] [T.Prime] [T.Of (logic 𝔸)]

@[simp] lemma ofTheory_th : (ofTheory 𝔸 T).th = T := rfl

@[simp] lemma ofTheory_forb : (ofTheory 𝔸 T).forb = ∅ := rfl

end

/-- An MP-closed theory of `logic 𝔸` disjoint from an ⋎-directed `Z` extends to the theory of a
pair with no forbidden formulas, still disjoint from `Z`. -/
lemma exists_avoiding {T : BDTheory} {Z : BDFormulaSet} [T.Mdp] [T.Of (logic 𝔸)]
  (hdir : OrDirected 𝔸 Z) (hdisj : ∀ C ∈ Z, C ∉ T) :
  ∃ v : CanonicalPair 𝔸, T ⊆ v.th ∧ v.forb = ∅ ∧ ∀ C ∈ Z, C ∉ v.th := by
  obtain ⟨Y, hTY, hmdp, hprime, hof, havoid⟩ := exists_prime_mdpClosed_avoiding hdir hdisj;
  have := hmdp;
  have := hprime;
  have := hof;
  exact ⟨ofTheory 𝔸 Y, hTY, rfl, havoid⟩;

/-- The pair of the set of all formulas and the empty set of forbidden formulas. -/
def univ (𝔸 : Set BDFormula) : CanonicalPair 𝔸 where
  th := Set.univ
  forb := ∅
  mdp := ⟨fun _ _ => trivial⟩
  prime := ⟨fun _ => Or.inl trivial⟩
  of := ⟨fun _ _ => trivial⟩
  avoid := by simp

@[simp] lemma univ_th : (univ 𝔸).th = Set.univ := rfl

@[simp] lemma univ_forb : (univ 𝔸).forb = ∅ := rfl

/-- The theory of a pair containing `⊥` is the set of all formulas. -/
lemma th_eq_univ_of_bot_mem (h : ⊥ ∈ w.th) : w.th = Set.univ :=
  BDTheory.eq_univ_of_bot_mem (𝔸 := 𝔸) h

/-- A pair containing `⊥` forbids nothing. -/
lemma forb_eq_empty_of_bot_mem (h : ⊥ ∈ w.th) : w.forb = ∅ := by
  ext B;
  simp only [Set.mem_empty_iff_false, iff_false];
  intro hB;
  exact w.avoid (◇(⋁[B])) ⟨⋁[B], ⟨[B], by simp, by simpa using hB, rfl⟩, rfl⟩
    (by rw [th_eq_univ_of_bot_mem h]; trivial);

/-- `univ 𝔸` is the only pair containing `⊥`. -/
lemma eq_univ_of_bot_mem (h : ⊥ ∈ w.th) : w = univ 𝔸 := by
  have h₁ := th_eq_univ_of_bot_mem h;
  have h₂ := forb_eq_empty_of_bot_mem h;
  cases w;
  subst h₁;
  subst h₂;
  rfl;

end CanonicalPair

/-- The canonical model of `logic 𝔸`, whose worlds are the pairs of `CanonicalPair 𝔸`.

- [MdP05, Definition 3, Lemma 3]
-/
def canonicalModel (𝔸 : Set BDFormula) : Model (CanonicalPair 𝔸) where
  iRel' w v := w.th ⊆ v.th
  iRel_preorder := {
    refl := fun _ => subset_rfl,
    trans := fun _ _ _ => subset_trans
  }
  mRel' w v := □⁻¹w.th ⊆ v.th ∧ ∀ B ∈ w.forb, B ∉ v.th
  Fallible' w := ⊥ ∈ w.th
  fallible_iRel' h Iwv := Iwv h
  fallible_mRel' h Mwv := Mwv.1 (by rw [CanonicalPair.th_eq_univ_of_bot_mem h]; trivial)
  fallible_exists_mRel' h :=
    ⟨CanonicalPair.univ 𝔸, Set.subset_univ _, by
      rw [CanonicalPair.forb_eq_empty_of_bot_mem h];
      simp⟩
  val w a := (#a) ∈ w.th
  val_persistent h Iwv := Iwv h
  fallible_val h := by rw [CanonicalPair.th_eq_univ_of_bot_mem h]; trivial

namespace CanonicalPair

variable {𝔸 : Set BDFormula} {A B : BDFormula} {w : CanonicalPair 𝔸}

/-- The pair `w` with its forbidden formulas erased. -/
def erase (w : CanonicalPair 𝔸) : CanonicalPair 𝔸 := ofTheory 𝔸 w.th

@[simp] lemma erase_th : w.erase.th = w.th := rfl

@[simp] lemma erase_forb : w.erase.forb = ∅ := rfl

lemma iRel_erase : (canonicalModel 𝔸).iRel w w.erase := subset_rfl

/-- A pair missing `A 🡒 B` has an `≼`-extension containing `A` and missing `B`. -/
lemma exists_iRel_of_imply_not_mem (h : (A 🡒 B) ∉ w.th) :
  ∃ v : CanonicalPair 𝔸, (canonicalModel 𝔸).iRel w v ∧ A ∈ v.th ∧ B ∉ v.th := by
  obtain ⟨v, hXv, -, havoid⟩ :=
    exists_avoiding (𝔸 := 𝔸) (T := w.th.impSet A) (Z := {B}) orDirected_singleton
      (by rintro C rfl; exact h);
  exact ⟨v, (BDTheory.subset_impSet (𝔸 := 𝔸)).trans hXv,
    hXv (BDTheory.self_mem_impSet (𝔸 := 𝔸)), havoid B rfl⟩;

/-- A pair missing `□A` has, after erasing its forbidden formulas, a `⊏`-successor missing `A`. -/
lemma exists_mRel_of_box_not_mem (h : □A ∉ w.th) :
  ∃ v : CanonicalPair 𝔸, (canonicalModel 𝔸).mRel w.erase v ∧ A ∉ v.th := by
  have := BDTheory.prebox_of' (𝔸 := 𝔸) (T := w.th);
  obtain ⟨v, hXv, -, havoid⟩ :=
    exists_avoiding (𝔸 := 𝔸) (T := □⁻¹w.th) (Z := {A}) orDirected_singleton
      (by rintro C rfl; exact h);
  exact ⟨v, ⟨hXv, by simp⟩, havoid A rfl⟩;

/-- For a pair `w` containing `◇A`, the theory `□⁻¹w.th` under the assumption `A` is disjoint
from `disjSet w.forb`. -/
private lemma avoid_disjSet_of_dia_mem (h : ◇A ∈ w.th) :
  ∀ C ∈ disjSet w.forb, C ∉ BDTheory.impSet (□⁻¹w.th) A := by
  rintro C ⟨K, hne, hsub, rfl⟩ hmem;
  have h₁ : (◇A 🡒 ◇(⋁K)) ∈ w.th := w.th.mdp (BDTheory.provable_mem (𝔸 := 𝔸) kDia) hmem;
  exact w.avoid (◇(⋁K)) ⟨⋁K, ⟨K, hne, hsub, rfl⟩, rfl⟩ (w.th.mdp h₁ h);

/-- A pair containing `◇A` has a `⊏`-successor containing `A`. -/
lemma exists_mRel_of_dia_mem (h : ◇A ∈ w.th) :
  ∃ v : CanonicalPair 𝔸, (canonicalModel 𝔸).mRel w v ∧ A ∈ v.th := by
  have := BDTheory.prebox_of' (𝔸 := 𝔸) (T := w.th);
  have := BDTheory.of_logicCK (𝔸 := 𝔸) (T := □⁻¹w.th);
  obtain ⟨v, hXv, -, havoid⟩ :=
    exists_avoiding (𝔸 := 𝔸) (T := BDTheory.impSet (□⁻¹w.th) A) (Z := disjSet w.forb)
      orDirected_disjSet (avoid_disjSet_of_dia_mem h);
  refine ⟨v, ⟨(BDTheory.subset_impSet (𝔸 := 𝔸)).trans hXv, ?_⟩,
    hXv (BDTheory.self_mem_impSet (𝔸 := 𝔸))⟩;
  intro B hB hBv;
  exact havoid (⋁[B]) ⟨[B], by simp, by simpa using hB, rfl⟩
    (v.th.mdp (BDTheory.provable_mem (𝔸 := 𝔸) (imp_ldisj (by simp))) hBv);

/-- The theory of a pair missing `◇A` is disjoint from `diaDisjSet {A}`. -/
private lemma avoid_diaDisjSet_of_dia_not_mem (h : ◇A ∉ w.th) :
  ∀ C ∈ diaDisjSet {A}, C ∉ w.th := by
  rintro C ⟨D, ⟨K, hne, hsub, rfl⟩, rfl⟩ hmem;
  have h₁ : ⊢ᴴ[CK;𝔸] ◇(⋁K) 🡒 ◇A := dia_mono (ldisj_imp (by
    intro B hB;
    obtain rfl : B = A := hsub B hB;
    exact imp_id));
  exact h (w.th.mdp (BDTheory.provable_mem (𝔸 := 𝔸) h₁) hmem);

/-- A pair missing `◇A` has an `≼`-extension none of whose `⊏`-successors contains `A`. -/
lemma exists_iRel_of_dia_not_mem (h : ◇A ∉ w.th) :
  ∃ v : CanonicalPair 𝔸, (canonicalModel 𝔸).iRel w v ∧
  ∀ u : CanonicalPair 𝔸, (canonicalModel 𝔸).mRel v u → A ∉ u.th := by
  obtain ⟨Y, hXY, hmdp, hprime, hof, havoid⟩ :=
    exists_prime_mdpClosed_avoiding (𝔸 := 𝔸) (T := w.th) (Z := diaDisjSet {A})
      orDirected_diaDisjSet (avoid_diaDisjSet_of_dia_not_mem h);
  exact ⟨⟨Y, {A}, hmdp, hprime, hof, havoid⟩, hXY, fun _ Mvu => Mvu.2 A rfl⟩;

/-- Truth lemma for the pair canonical model: a pair forces exactly the formulas of its theory.

- [MdP05, Lemma 3]
-/
theorem truthlemma : w ⊩[canonicalModel 𝔸] A ↔ A ∈ w.th := by
  induction A generalizing w with
  | atom a => exact Iff.rfl;
  | falsum => exact Iff.rfl;
  | and A B ihA ihB =>
    constructor;
    · rintro ⟨hA, hB⟩;
      exact BDTheory.and_mem (𝔸 := 𝔸) (ihA.mp hA) (ihB.mp hB);
    · intro h;
      constructor;
      . exact ihA.mpr (w.th.mdp (BDTheory.provable_mem (𝔸 := 𝔸) andElim₁) h);
      . exact ihB.mpr (w.th.mdp (BDTheory.provable_mem (𝔸 := 𝔸) andElim₂) h);
  | or A B ihA ihB =>
    constructor;
    · rintro (hA | hB);
      · exact w.th.mdp (BDTheory.provable_mem (𝔸 := 𝔸) orIntro₁) (ihA.mp hA);
      · exact w.th.mdp (BDTheory.provable_mem (𝔸 := 𝔸) orIntro₂) (ihB.mp hB);
    · intro h;
      rcases w.th.prime h <;> grind;
  | imply A B ihA ihB =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨v, Iwv, hAv, hBv⟩ := exists_iRel_of_imply_not_mem hc;
      exact hBv (ihB.mp (h v Iwv (ihA.mpr hAv)));
    · intro h v Iwv hvA;
      exact ihB.mpr (v.th.mdp (Iwv h) (ihA.mp hvA));
  | box A ih =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨v, Mwv, hAv⟩ := exists_mRel_of_box_not_mem hc;
      exact hAv (ih.mp (h w.erase v iRel_erase Mwv));
    · intro h v u Iwv Mvu;
      exact ih.mpr (Mvu.1 (Iwv h));
  | dia A ih =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨v, Iwv, hblock⟩ := exists_iRel_of_dia_not_mem hc;
      obtain ⟨u, Mvu, hAu⟩ := h v Iwv;
      exact hblock u Mvu (ih.mp hAu);
    · intro h v Iwv;
      obtain ⟨u, Mvu, hAu⟩ := exists_mRel_of_dia_mem (Iwv h);
      exact ⟨u, Mvu, ih.mpr hAu⟩;

end CanonicalPair

section

variable {𝔸 : Set BDFormula} {A : BDFormula}

/-- Model existence: a formula outside `logic 𝔸` is refuted at some pair of the canonical model.

- [MdP05, Theorem 2]
-/
theorem exists_not_forces_of_not_mem (h : A ∉ logic 𝔸) :
  ∃ w : CanonicalPair 𝔸, ¬(w ⊩[canonicalModel 𝔸] A) := by
  obtain ⟨w, -, -, havoid⟩ :=
    CanonicalPair.exists_avoiding (𝔸 := 𝔸) (T := logic 𝔸) (Z := {A}) orDirected_singleton
      (by rintro C rfl; exact h);
  exact ⟨w, fun hw => havoid A rfl (CanonicalPair.truthlemma.mp hw)⟩;

end

end CK

/-- Completeness of `CK` for the class of all CK-models.

- [MdP05, Theorem 1]
-/
theorem LogicCK.iff_valid {A : BDFormula} :
  A ∈ LogicCK ↔ ∀ {κ : Type 0}, ∀ M : CK.Model κ, M ⊧ A := by
  sorry

end
