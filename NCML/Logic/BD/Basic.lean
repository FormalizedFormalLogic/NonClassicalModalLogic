module

public import NCML.Formula

@[expose] public section

abbrev BDLogic := Set BDFormula

namespace BDLogic

open BDFormula

class Mdp (L : BDLogic) : Prop where
  mdp {A B} : (A 🡒 B) ∈ L → A ∈ L → B ∈ L
export Mdp (mdp)

class Nec (L : BDLogic) : Prop where
  nec {A} : A ∈ L → □A ∈ L
export Nec (nec)

end BDLogic

end
