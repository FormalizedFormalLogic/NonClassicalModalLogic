module

public import NCML.Hilbert.Logics
public import NCML.Hilbert.Propositional
public import Mathlib.Order.Preorder.Chain

@[expose] public section

/-!
# MP-closed sets of formulas

Sets of formulas closed under modus ponens (`BDFormulaSet.MpClosed`), the MP-closure of a set
(`MPClosure`), and the implication set of a theory (`BDFormulaSet.impSet`), the relative deduction
lemma used to build maximal MP-closed sets.
-/

namespace NCML

open BDFormula ProvableBDHilbert

namespace BDFormulaSet

/-- `X` is closed under modus ponens. -/
def MpClosed (X : BDFormulaSet) : Prop := ∀ {A B}, (A 🡒 B) ∈ X → A ∈ X → B ∈ X

section General

variable {𝔸 : Set BDFormula} {X : BDFormulaSet} {A B C : BDFormula}

theorem provable_mem (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) (h : ProvableBDHilbert 𝔸 A) : A ∈ X :=
  hlog h

theorem and_mem (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) (hmp : X.MpClosed) (hA : A ∈ X) (hB : B ∈ X) :
    A ⋏ B ∈ X :=
  hmp (hmp (provable_mem hlog andIntro) hA) hB

theorem lconj_mem (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) (hmp : X.MpClosed) {Γ : List BDFormula}
    (h : ∀ A ∈ Γ, A ∈ X) : lconj Γ ∈ X := by
  induction Γ with
  | nil => exact provable_mem hlog verum;
  | cons A Γ ih => exact and_mem hlog hmp (h A (by simp)) (ih fun B hB => h B (by simp [hB]));

theorem or_elim_mem (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) (hmp : X.MpClosed)
    (hAC : (A 🡒 C) ∈ X) (hBC : (B 🡒 C) ∈ X) (hAB : (A ⋎ B) ∈ X) : C ∈ X :=
  hmp (hmp (hmp (provable_mem hlog orElim) hAC) hBC) hAB

end General

section CKB

variable {X : BDFormulaSet} {A : BDFormula}

theorem box_dia_mem (hlog : LogicCKB ⊆ X) (hmp : X.MpClosed) (hA : A ∈ X) : □◇A ∈ X :=
  hmp (hlog (ProvableBDHilbert.axm (Or.inl ⟨A, rfl⟩))) hA

theorem mem_of_dia_box_mem (hlog : LogicCKB ⊆ X) (hmp : X.MpClosed) (h : ◇(□A) ∈ X) : A ∈ X :=
  hmp (hlog (ProvableBDHilbert.axm (Or.inr ⟨A, rfl⟩))) h

end CKB

end BDFormulaSet

/-! ## MP-closure -/

/-- The closure of `X` under modus ponens. -/
inductive MPClosure (X : BDFormulaSet) : BDFormula → Prop
  | base {A} : A ∈ X → MPClosure X A
  | mp {A B} : MPClosure X (A 🡒 B) → MPClosure X A → MPClosure X B

theorem subset_mpClosure (X : BDFormulaSet) : X ⊆ MPClosure X := fun _ => MPClosure.base

theorem MPClosure.mpClosed (X : BDFormulaSet) : BDFormulaSet.MpClosed (MPClosure X) :=
  fun hAB hA => MPClosure.mp hAB hA

theorem MPClosure.mono {X Y : BDFormulaSet} (h : X ⊆ Y) {A} (hA : MPClosure X A) : MPClosure Y A := by
  induction hA with
  | base hA => exact MPClosure.base (h hA);
  | mp _ _ ih₁ ih₂ => exact MPClosure.mp ih₁ ih₂;

theorem logic_subset_mpClosure {𝔸 : Set BDFormula} {X : BDFormulaSet}
    (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) : ProvableBDHilbert.logic 𝔸 ⊆ MPClosure X :=
  hlog.trans (subset_mpClosure X)

/-- The union of a chain of MP-closed sets is MP-closed: given `(A 🡒 B) ∈ X₁` and `A ∈ X₂` with
`X₁, X₂` in the chain, one of `X₁ ⊆ X₂` or `X₂ ⊆ X₁` holds, so both facts land in the larger set
and MP-closedness of that set finishes the argument. -/
theorem MpClosed_sUnion_of_chain {c : Set BDFormulaSet} (hc : IsChain (· ⊆ ·) c)
    (h : ∀ X ∈ c, BDFormulaSet.MpClosed X) : BDFormulaSet.MpClosed (⋃₀ c) := by
  rintro A B ⟨X₁, hX₁c, hAB⟩ ⟨X₂, hX₂c, hA⟩;
  rcases hc.total hX₁c hX₂c with hsub | hsub;
  · exact ⟨X₂, hX₂c, h X₂ hX₂c (hsub hAB) hA⟩;
  · exact ⟨X₁, hX₁c, h X₁ hX₁c hAB (hsub hA)⟩;

/-! ## The implication set -/

namespace BDFormulaSet

/-- The formulas `B` with `A 🡒 B ∈ X`, i.e. `X` "under the assumption `A`". -/
def impSet (X : BDFormulaSet) (A : BDFormula) : BDFormulaSet := { B | (A 🡒 B) ∈ X }

@[simp, grind] lemma mem_impSet {X : BDFormulaSet} {A B} : B ∈ X.impSet A ↔ (A 🡒 B) ∈ X := Iff.rfl

section

variable {𝔸 : Set BDFormula} {X : BDFormulaSet} {A : BDFormula}

theorem subset_impSet (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) (hmp : X.MpClosed) :
    X ⊆ X.impSet A :=
  fun _ hB => hmp (provable_mem hlog imply₁) hB

theorem self_mem_impSet (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) : A ∈ X.impSet A := by
  show (A 🡒 A) ∈ X;
  exact provable_mem hlog id_;

theorem impSet_mpClosed (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) (hmp : X.MpClosed) :
    (X.impSet A).MpClosed :=
  fun hBC hB => hmp (hmp (provable_mem hlog imply₂) hBC) hB

end

end BDFormulaSet

end NCML

end
