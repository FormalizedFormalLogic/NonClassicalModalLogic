module

public import NCML.Formula.B.Basic
public import NCML.Formula.BD.Basic
public import NCML.Formula.D.Basic

@[expose] public section

/-- Propositional formula -/
inductive PFormula : Type
  | atom   : Nat → PFormula
  | falsum : PFormula
  | and    : PFormula → PFormula → PFormula
  | or     : PFormula → PFormula → PFormula
  | imply  : PFormula → PFormula → PFormula
deriving DecidableEq

end
