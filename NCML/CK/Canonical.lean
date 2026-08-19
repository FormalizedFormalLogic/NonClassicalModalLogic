module

public import NCML.CK.Confluence
public import NCML.Hilbert.Logics
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

/-- - [Pac24, Proposition 10] -/
instance : canonicalModel.ForwardConfluent :=
  Model.forwardConfluent_iff_backwardConfluent_of_symmetricMRel.mpr inferInstance

/-- - [Pac24, Lemma 17] -/
instance : canonicalModel.IsIKB where
  not_fallible _ h := h.elim

end CK

end
