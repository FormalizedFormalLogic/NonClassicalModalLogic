module

public import NCML.Formula
public import Mathlib.Tactic

@[expose] public section

namespace NCML.Hilbert

open BDFormula

/--
Hilbert-style derivability relative to an extra axiom set `Ax`, closed under
modus ponens (`MP`) and necessitation (`Nec`) (Definition 1).
The base logic `CK` is obtained by taking `Ax = ∅`: it already contains every
intuitionistic-propositional-logic Hilbert axiom together with `K□` and `K◇`.
-/
inductive Derivation (Ax : Set BDFormula) : BDFormula → Prop
  | axm       {A}     : A ∈ Ax → Derivation Ax A
  | imply₁    {A B}   : Derivation Ax (A 🡒 B 🡒 A)
  | imply₂    {A B C} : Derivation Ax ((A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 A 🡒 C)
  | andElim₁  {A B}   : Derivation Ax (A ⋏ B 🡒 A)
  | andElim₂  {A B}   : Derivation Ax (A ⋏ B 🡒 B)
  | andIntro  {A B}   : Derivation Ax (A 🡒 B 🡒 A ⋏ B)
  | orIntro₁  {A B}   : Derivation Ax (A 🡒 A ⋎ B)
  | orIntro₂  {A B}   : Derivation Ax (B 🡒 A ⋎ B)
  | orElim    {A B C} : Derivation Ax ((A 🡒 C) 🡒 (B 🡒 C) 🡒 (A ⋎ B 🡒 C))
  | efq       {A}     : Derivation Ax (⊥ 🡒 A)
  | kBox      {A B}   : Derivation Ax (□(A 🡒 B) 🡒 □A 🡒 □B)
  | kDia      {A B}   : Derivation Ax (□(A 🡒 B) 🡒 ◇A 🡒 ◇B)
  | mp        {A B}   : Derivation Ax (A 🡒 B) → Derivation Ax A → Derivation Ax B
  | nec       {A}     : Derivation Ax A → Derivation Ax (□A)

/-- `Λ + X` (Definition 2): the least logic containing `Λ ∪ X`, when `Λ = theLogic Ax`. -/
abbrev theLogic (Ax : Set BDFormula) : Set BDFormula := { A | Derivation Ax A }

@[simp] lemma mem_theLogic {Ax : Set BDFormula} {A} : A ∈ theLogic Ax ↔ Derivation Ax A := Iff.rfl

/-- A (modal) logic is closed under `MP` and `Nec` (Definition 1). -/
def IsLogic (L : Set BDFormula) : Prop :=
  (∀ {A B}, A 🡒 B ∈ L → A ∈ L → B ∈ L) ∧ (∀ {A}, A ∈ L → □A ∈ L)

theorem isLogic_theLogic (Ax : Set BDFormula) : IsLogic (theLogic Ax) :=
  ⟨fun h₁ h₂ => Derivation.mp h₁ h₂, fun h => Derivation.nec h⟩

theorem theLogic_monotone {Ax Ax' : Set BDFormula} (h : Ax ⊆ Ax') :
    theLogic Ax ⊆ theLogic Ax' := by
  intro A hA
  induction hA with
  | axm hmem   => exact Derivation.axm (h hmem)
  | imply₁     => exact Derivation.imply₁
  | imply₂     => exact Derivation.imply₂
  | andElim₁   => exact Derivation.andElim₁
  | andElim₂   => exact Derivation.andElim₂
  | andIntro   => exact Derivation.andIntro
  | orIntro₁   => exact Derivation.orIntro₁
  | orIntro₂   => exact Derivation.orIntro₂
  | orElim     => exact Derivation.orElim
  | efq        => exact Derivation.efq
  | kBox       => exact Derivation.kBox
  | kDia       => exact Derivation.kDia
  | mp _ _ ih₁ ih₂ => exact Derivation.mp ih₁ ih₂
  | nec _ ih   => exact Derivation.nec ih

/-- Transitivity of derivable implications, via `imply₁`/`imply₂`/`mp`. -/
theorem imp_trans {Ax : Set BDFormula} {A B C} (h₁ : Derivation Ax (A 🡒 B)) (h₂ : Derivation Ax (B 🡒 C)) :
    Derivation Ax (A 🡒 C) := by
  have s : Derivation Ax ((A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 A 🡒 C) := Derivation.imply₂
  have k : Derivation Ax (A 🡒 B 🡒 C) := Derivation.mp Derivation.imply₁ h₂
  exact Derivation.mp (Derivation.mp s k) h₁

end NCML.Hilbert

end
