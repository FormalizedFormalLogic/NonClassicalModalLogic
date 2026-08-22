module

public import NCML.Formula.BD.Basic

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

def DiaFree (L : BDLogic) := ∀ A ∈ L, A.DiaFree

def BoxFree (L : BDLogic) := ∀ A ∈ L, A.BoxFree

end BDLogic

abbrev DiaFreeBDLogic := { L : BDLogic // L.DiaFree }

def BDLogic.diaElim (L : BDLogic) : DiaFreeBDLogic :=
  ⟨{ A ∈ L | A.DiaFree }, by simp [BDLogic.DiaFree]⟩

abbrev BoxFreeBDLogic := { L : BDLogic // L.BoxFree }

def BDLogic.boxElim (L : BDLogic) : BoxFreeBDLogic :=
  ⟨{ A ∈ L | A.BoxFree }, by simp [BDLogic.BoxFree]⟩

end
