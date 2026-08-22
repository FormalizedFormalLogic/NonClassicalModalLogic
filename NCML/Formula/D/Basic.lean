module

@[expose] public section

/-- Modal formula with `◇` -/
inductive DFormula : Type
  | atom   : Nat → DFormula
  | falsum : DFormula
  | and    : DFormula → DFormula → DFormula
  | or     : DFormula → DFormula → DFormula
  | imply  : DFormula → DFormula → DFormula
  | dia    : DFormula → DFormula
deriving DecidableEq

end
