module

public import NCML.CK.Semantics
public import NCML.Hilbert.Theory

@[expose] public section

/-!
# The pair canonical model

For an axiom set `𝔸`, the canonical model whose worlds are the pairs `(T, Θ)` of a prime
MP-closed theory `T` of `logic 𝔸` and a set `Θ` of formulas omitted by every `⊏`-successor.

- [MdP05]
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
whose nonempty finite disjunctions is possible in `th`. -/
structure CanonicalPair (𝔸 : Set BDFormula) where
  th : BDTheory
  forb : BDFormulaSet
  mdp : th.Mdp
  prime : th.Prime
  of : th.Of (logic 𝔸)
  avoid : ∀ B ∈ diaDisjSet forb, B ∉ th

namespace CanonicalPair

variable {𝔸 : Set BDFormula} {A B : BDFormula} {w v : CanonicalPair 𝔸}

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

/-- A pair containing `⊥` forces every formula. -/
lemma th_eq_univ_of_bot_mem (h : ⊥ ∈ w.th) : w.th = Set.univ := sorry

/-- A pair containing `⊥` forbids nothing. -/
lemma forb_eq_empty_of_bot_mem (h : ⊥ ∈ w.th) : w.forb = ∅ := sorry

/-- `univ 𝔸` is the only pair containing `⊥`. -/
lemma eq_univ_of_bot_mem (h : ⊥ ∈ w.th) : w = univ 𝔸 := sorry

end CanonicalPair

/-- The canonical model of `logic 𝔸`, whose worlds are the pairs `(T, Θ)`. -/
def canonicalModel (𝔸 : Set BDFormula) : Model (CanonicalPair 𝔸) where
  iRel' w v := w.th ⊆ v.th
  iRel_preorder := {
    refl := fun _ => subset_rfl,
    trans := fun _ _ _ => subset_trans
  }
  mRel' w v := □⁻¹w.th ⊆ v.th ∧ ∀ B ∈ w.forb, B ∉ v.th
  Fallible' w := ⊥ ∈ w.th
  fallible_iRel' h Iwv := Iwv h
  fallible_mRel' := sorry
  fallible_exists_mRel' := sorry
  val w a := (#a) ∈ w.th
  val_persistent h Iwv := Iwv h
  fallible_val := sorry

namespace CanonicalPair

variable {𝔸 : Set BDFormula} {A B : BDFormula} {w v : CanonicalPair 𝔸}

/-- The pair `w = (T, Θ)` with its forbidden formulas erased. -/
def erase (w : CanonicalPair 𝔸) : CanonicalPair 𝔸 := ofTheory 𝔸 w.th

@[simp] lemma erase_th : w.erase.th = w.th := rfl

@[simp] lemma erase_forb : w.erase.forb = ∅ := rfl

lemma iRel_erase : (canonicalModel 𝔸).iRel w w.erase := sorry

/-- A pair missing `A 🡒 B` has an `≼`-extension containing `A` and missing `B`. -/
lemma exists_iRel_of_imply_not_mem (h : (A 🡒 B) ∉ w.th) :
  ∃ v : CanonicalPair 𝔸, (canonicalModel 𝔸).iRel w v ∧ A ∈ v.th ∧ B ∉ v.th := sorry

/-- A pair missing `□A` has, after erasing its forbidden formulas, a `⊏`-successor missing `A`. -/
lemma exists_mRel_of_box_not_mem (h : □A ∉ w.th) :
  ∃ v : CanonicalPair 𝔸, (canonicalModel 𝔸).mRel w.erase v ∧ A ∉ v.th := sorry

/-- The theory `□⁻¹T` under the assumption `A` avoids the disjunctions over `Θ`, for a pair
`(T, Θ)` containing `◇A`. -/
private lemma avoid_disjSet_of_dia_mem (h : ◇A ∈ w.th) :
  ∀ C ∈ disjSet w.forb, C ∉ BDTheory.impSet (□⁻¹w.th) A := sorry

/-- A pair containing `◇A` has a `⊏`-successor containing `A`. -/
lemma exists_mRel_of_dia_mem (h : ◇A ∈ w.th) :
  ∃ v : CanonicalPair 𝔸, (canonicalModel 𝔸).mRel w v ∧ A ∈ v.th := sorry

/-- A pair `(T, Θ)` missing `◇A` avoids the `◇`-disjunctions over `{A}`. -/
private lemma avoid_diaDisjSet_of_dia_not_mem (h : ◇A ∉ w.th) :
  ∀ C ∈ diaDisjSet {A}, C ∉ w.th := sorry

/-- A pair missing `◇A` has an `≼`-extension none of whose `⊏`-successors contains `A`. -/
lemma exists_iRel_of_dia_not_mem (h : ◇A ∉ w.th) :
  ∃ v : CanonicalPair 𝔸, (canonicalModel 𝔸).iRel w v ∧
  ∀ u : CanonicalPair 𝔸, (canonicalModel 𝔸).mRel v u → A ∉ u.th := sorry

end CanonicalPair

end CK

end
