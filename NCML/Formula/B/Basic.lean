module

@[expose] public section

/-- Modal formula with `□` -/
inductive BFormula : Type
  | atom   : Nat → BFormula
  | falsum : BFormula
  | and    : BFormula → BFormula → BFormula
  | or     : BFormula → BFormula → BFormula
  | imply  : BFormula → BFormula → BFormula
  | box    : BFormula → BFormula
deriving DecidableEq

end
