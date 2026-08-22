module

public import NCML.Formula

/-! This file defines the two-sided sequent `Γ ⟹ Δ` with at most one succedent formula. -/

@[expose] public section

/-- Two-sided sequent with at most one succedent formula. -/
structure Sequent where
  ant : BDFormulaFinset
  suc : Option BDFormula

infix:50 " ⟹ " => Sequent.mk

end
