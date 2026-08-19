module

public import NCML.CK.Confluence
public import NCML.Hilbert.Logics
public import NCML.Hilbert.Theory
public import Mathlib.Data.SetLike.Basic

@[expose] public section

/-!
# Canonical model for `CKB`

- [Pac24, Section 3.2]
-/

namespace CK

open NCML BDFormula

/-- A CKB-theory: a set of formulas that contains every theorem of `CKB`, is closed under `MP`,
is prime, and is consistent.

- [Pac24, Section 3.2]
-/
structure CKBTheory where
  carrier : BDFormulaSet
  logicCKB_subset : LogicCKB ⊆ carrier
  mdp : ∀ {A B}, A 🡒 B ∈ carrier → A ∈ carrier → B ∈ carrier
  prime : ∀ {A B}, A ⋎ B ∈ carrier → A ∈ carrier ∨ B ∈ carrier
  consistent : ⊥ ∉ carrier

namespace CKBTheory

instance : SetLike CKBTheory BDFormula where
  coe Γ := Γ.carrier
  coe_injective p q h := by cases p; cases q; congr;

@[simp] lemma mem_carrier {Γ : CKBTheory} {A} : A ∈ Γ.carrier ↔ A ∈ Γ := Iff.rfl

@[ext] theorem ext {Γ Δ : CKBTheory} (h : ∀ A, A ∈ Γ ↔ A ∈ Δ) : Γ = Δ := SetLike.ext h

/-- Lindenbaum lemma for CKB-theories: an MP-closed set of formulas that contains every theorem of
`CKB` and misses `A` extends to a CKB-theory still missing `A`.

Pac24 does not isolate this statement: it is the Zorn step run inline in the implication case of
Lemma 19, and again in Lemma 20.

- [Pac24, Lemma 19, Lemma 20]
-/
lemma exists_extending {X : BDFormulaSet} {A : BDFormula}
  (hlog : LogicCKB ⊆ X) (hmp : X.MpClosed) (hA : A ∉ X) :
  ∃ Γ : CKBTheory, X ⊆ Γ.carrier ∧ A ∉ Γ.carrier := by
  obtain ⟨Y, hXY, hmax⟩ :=
    exists_maximal_mpClosed_avoiding (Z := {A}) hmp (by rintro B rfl; exact hA);
  obtain ⟨-, hmpY, havoid⟩ := hmax.prop;
  have hAY : A ∉ Y := havoid A rfl;
  have hlogY : LogicCKB ⊆ Y := hlog.trans hXY;
  have h₁ : ∀ {B}, B ∉ Y → (B 🡒 A) ∈ Y := by
    intro B hB;
    obtain ⟨C, hC, h⟩ := exists_imp_mem_of_maximal hlog hmax hB;
    exact Set.mem_singleton_iff.mp hC ▸ h;
  have h₂ : ∀ {B C}, B ⋎ C ∈ Y → B ∈ Y ∨ C ∈ Y := by
    intro B C hBC;
    by_contra hc;
    exact hAY <| BDFormulaSet.or_elim_mem hlogY hmpY (h₁ fun h => hc (Or.inl h))
      (h₁ fun h => hc (Or.inr h)) hBC;
  have h₃ : ⊥ ∉ Y := fun h =>
    hAY <| hmpY (BDFormulaSet.provable_mem hlogY ProvableBDHilbert.efq) h;
  exact ⟨⟨Y, hlogY, hmpY, h₂, h₃⟩, hXY, hAY⟩;

end CKBTheory

/-- - [Pac24, Section 3.2] -/
def canonicalModel : Model CKBTheory where
  iRel' Γ Δ := Γ.carrier ⊆ Δ.carrier
  mRel' Γ Δ := Γ.carrier.prebox ⊆ Δ.carrier ∧ Δ.carrier ⊆ Γ.carrier.predia
  Fallible' _ := False
  fallible_iRel' h _ := h.elim
  fallible_mRel' h _ := h.elim
  fallible_exists_mRel' h := h.elim
  val Γ a := (#a) ∈ Γ.carrier
  val_persistent h IΓΔ := IΓΔ h
  fallible_val h := h.elim

/-- - [Pac24, Lemma 15] -/
instance : canonicalModel.SymmetricMRel where
  symm_mRel {Γ Δ} := by
    rintro ⟨h₁, h₂⟩;
    constructor;
    · intro A hA;
      have h₃ : (◇(□A) 🡒 A) ∈ LogicCKB := ProvableBDHilbert.axm (Or.inr ⟨A, rfl⟩);
      exact Γ.mdp (Γ.logicCKB_subset h₃) (h₂ hA);
    · intro A hA;
      have h₃ : (A 🡒 □◇A) ∈ LogicCKB := ProvableBDHilbert.axm (Or.inl ⟨A, rfl⟩);
      exact h₁ (Γ.mdp (Γ.logicCKB_subset h₃) hA);

/-- - [Pac24, Lemma 16] -/
instance : canonicalModel.BackwardConfluent := sorry

instance : canonicalModel.ForwardConfluent :=
  Model.forwardConfluent_iff_backwardConfluent_of_symmetricMRel.mpr inferInstance

/-- - [Pac24, Lemma 17] -/
instance : canonicalModel.IsIKB where
  not_fallible _ h := h.elim

end CK

end
