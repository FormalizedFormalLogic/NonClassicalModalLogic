module

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

@[simp, grind] lemma mem_prebox {X : BDFormulaSet} {A} : A ∈ X.prebox ↔ □A ∈ X := Iff.rfl
@[simp, grind] lemma mem_predia {X : BDFormulaSet} {A} : A ∈ X.predia ↔ ◇A ∈ X := Iff.rfl

end BDFormulaSet

end NCML

end
