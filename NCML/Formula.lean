module

public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Set.Defs

@[expose] public section

namespace NCML

/-- Propositional formula -/
inductive PFormula : Type
  | atom   : Nat → PFormula
  | falsum : PFormula
  | and    : PFormula → PFormula → PFormula
  | or     : PFormula → PFormula → PFormula
  | imply  : PFormula → PFormula → PFormula
deriving DecidableEq

/-- Modal formula with `□` -/
inductive BFormula : Type
  | atom   : Nat → BFormula
  | falsum : BFormula
  | and    : BFormula → BFormula → BFormula
  | or     : BFormula → BFormula → BFormula
  | imply  : BFormula → BFormula → BFormula
  | box    : BFormula → BFormula
deriving DecidableEq

/-- Modal formula with `◇` -/
inductive DFormula : Type
  | atom   : Nat → DFormula
  | falsum : DFormula
  | and    : DFormula → DFormula → DFormula
  | or     : DFormula → DFormula → DFormula
  | imply  : DFormula → DFormula → DFormula
  | dia    : DFormula → DFormula
deriving DecidableEq

/-- Modal formula with both `□` and `◇` -/
inductive BDFormula : Type
  | atom   : Nat → BDFormula
  | falsum : BDFormula
  | and    : BDFormula → BDFormula → BDFormula
  | or     : BDFormula → BDFormula → BDFormula
  | imply  : BDFormula → BDFormula → BDFormula
  | box    : BDFormula → BDFormula
  | dia    : BDFormula → BDFormula
deriving DecidableEq

namespace BDFormula


prefix:75 "#" => atom
notation:max "⊥" => falsum
infixr:69 " ⋏ " => and
infixr:68 " ⋎ " => or
infixr:60 " 🡒 " => imply
prefix:90 "□" => box
prefix:91 "◇" => dia

abbrev iff (φ ψ : BDFormula) := φ 🡒 ψ ⋏ ψ 🡒 φ
infixr:61 " 🡘 " => iff

abbrev neg (φ : BDFormula) := φ 🡒 ⊥
prefix:85 "∼" => neg

abbrev top : BDFormula := ∼⊥
notation:max "⊤" => top

@[grind]
def boxFree : BDFormula → Prop
  | □_ => False
  | #_ | ⊥ => True
  | φ ⋏ ψ | φ ⋎ ψ | φ 🡒 ψ => φ.boxFree ∧ ψ.boxFree
  | ◇φ => φ.boxFree

@[grind]
def diaFree : BDFormula → Prop
  | ◇_ => False
  | #_ | ⊥ => True
  | φ ⋏ ψ | φ ⋎ ψ | φ 🡒 ψ => φ.diaFree ∧ ψ.diaFree
  | □φ => φ.diaFree

end BDFormula

abbrev BDLogic := Set BDFormula

abbrev BDFormulaSet := Set BDFormula

namespace BDFormulaSet

open BDFormula

/-- The set of formulas `A` with `□A` in `X`. -/
def prebox (X : BDFormulaSet) : BDFormulaSet := { A | □A ∈ X }

/-- The set of formulas `A` with `◇A` in `X`. -/
def predia (X : BDFormulaSet) : BDFormulaSet := { A | ◇A ∈ X }

@[inherit_doc] scoped prefix:90 "□⁻¹" => BDFormulaSet.prebox
@[inherit_doc] scoped prefix:91 "◇⁻¹" => BDFormulaSet.predia

@[simp, grind] lemma mem_prebox {X : BDFormulaSet} {A} : A ∈ X.prebox ↔ □A ∈ X := Iff.rfl
@[simp, grind] lemma mem_predia {X : BDFormulaSet} {A} : A ∈ X.predia ↔ ◇A ∈ X := Iff.rfl

/-- The image of `X` under `□`. -/
def box (X : BDFormulaSet) : BDFormulaSet := (□·) '' X

/-- The image of `X` under `◇`. -/
def dia (X : BDFormulaSet) : BDFormulaSet := (◇·) '' X

@[inherit_doc] scoped prefix:90 "□" => BDFormulaSet.box
@[inherit_doc] scoped prefix:91 "◇" => BDFormulaSet.dia

variable {X : BDFormulaSet} {A : BDFormula}

@[grind] lemma mem_box_iff : A ∈ □X ↔ ∃ B ∈ X, □B = A := Iff.rfl
@[grind] lemma mem_dia_iff : A ∈ ◇X ↔ ∃ B ∈ X, ◇B = A := Iff.rfl

@[simp, grind] lemma mem_box : □A ∈ □X ↔ A ∈ X := by grind;
@[simp, grind] lemma mem_dia : ◇A ∈ ◇X ↔ A ∈ X := by grind;

end BDFormulaSet

abbrev BDFormulaList := List BDFormula

abbrev BDFormulaFinset := Finset BDFormula

namespace BDFormulaList

/-- Conjunction of a list of formulas, right-folded with `⊤` as the base case. -/
def conj (Γ : BDFormulaList) : BDFormula := Γ.foldr (· ⋏ ·) ⊤

@[simp] lemma conj_nil : conj ([] : BDFormulaList) = ⊤ := rfl

@[simp] lemma conj_cons (A : BDFormula) (Γ : BDFormulaList) : conj (A :: Γ) = A ⋏ conj Γ := rfl

end BDFormulaList

namespace BDFormulaFinset

/-- Conjunction of a finset of formulas, via an arbitrary enumeration as a list. -/
noncomputable def conj (Γ : BDFormulaFinset) : BDFormula := BDFormulaList.conj Γ.toList

end BDFormulaFinset

end NCML

end
