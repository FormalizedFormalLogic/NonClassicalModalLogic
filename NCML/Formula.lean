module

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

@[grind]
def boxFree : BDFormula → Prop
  | box _ => False
  | atom _
  | falsum => True
  | and   φ ψ
  | or    φ ψ
  | imply φ ψ => φ.boxFree ∧ ψ.boxFree
  | dia φ     => φ.boxFree

@[grind]
def diaFree : BDFormula → Prop
  | dia _ => False
  | atom _
  | falsum => True
  | and   φ ψ
  | or    φ ψ
  | imply φ ψ => φ.diaFree ∧ ψ.diaFree
  | box φ     => φ.diaFree

end BDFormula

end NCML

end
