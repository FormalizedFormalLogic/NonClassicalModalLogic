module

public import NCML.Gentzen.Sequent
public import NCML.Hilbert.Logics

/-! This file defines the cut-free sequent calculus `GCK` for `LogicCK`. -/

@[expose] public section

open scoped BDFormulaFinset

namespace LogicCK

/-- The cut-free sequent calculus `GCK` for `LogicCK`.

- [Wij90, Section 1.2]
- [Sat26, Definition B.1]
-/
inductive ProofGentzen : Sequent → Type
  | axm (A)         : ProofGentzen ({A} ⟹ some A)
  | botL {Δ}        : ProofGentzen ({⊥} ⟹ Δ)
  | wkL  {Γ Γ' Δ}   : ProofGentzen (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → ProofGentzen (Γ' ⟹ Δ)
  | wkR  {Γ A}      : ProofGentzen (Γ ⟹ none) → ProofGentzen (Γ ⟹ some A)
  | andL₁ {Γ Δ A B} : ProofGentzen (insert A Γ ⟹ Δ) → ProofGentzen (insert (A ⋏ B) Γ ⟹ Δ)
  | andL₂ {Γ Δ A B} : ProofGentzen (insert B Γ ⟹ Δ) → ProofGentzen (insert (A ⋏ B) Γ ⟹ Δ)
  | andR {Γ A B}    : ProofGentzen (Γ ⟹ some A) → ProofGentzen (Γ ⟹ some B) → ProofGentzen (Γ ⟹ some (A ⋏ B))
  | orL  {Γ Δ A B}  : ProofGentzen (insert A Γ ⟹ Δ) → ProofGentzen (insert B Γ ⟹ Δ) → ProofGentzen (insert (A ⋎ B) Γ ⟹ Δ)
  | orR₁ {Γ A B}    : ProofGentzen (Γ ⟹ some A) → ProofGentzen (Γ ⟹ some (A ⋎ B))
  | orR₂ {Γ A B}    : ProofGentzen (Γ ⟹ some B) → ProofGentzen (Γ ⟹ some (A ⋎ B))
  | impL {Γ Δ A B}  : ProofGentzen (Γ ⟹ some A) → ProofGentzen (insert B Γ ⟹ Δ) → ProofGentzen (insert (A 🡒 B) Γ ⟹ Δ)
  | impR {Γ A B}    : ProofGentzen (insert A Γ ⟹ some B) → ProofGentzen (Γ ⟹ some (A 🡒 B))
  | box  {Γ A}      : ProofGentzen (Γ ⟹ some A) → ProofGentzen (□Γ ⟹ some (□A))
  | dia  {Γ A B}    : ProofGentzen (insert A Γ ⟹ some B) → ProofGentzen (insert (◇A) (□Γ) ⟹ some (◇B))

notation:120 "⊢ᵍ[CK]! " S:121 => ProofGentzen S


namespace ProofGentzen

variable {Γ Γ' : BDFormulaFinset} {Δ : Option BDFormula} {A B : BDFormula}

def union (A) (hΓ : A ∈ Γ := by grind) : ⊢ᵍ[CK]! (Γ ⟹ some A) := wkL (axm A)

def botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ[CK]! (Γ ⟹ Δ) := wkL botL

def wk (π : ⊢ᵍ[CK]! (Γ ⟹ none)) (h : Γ ⊆ Γ' := by grind) : ⊢ᵍ[CK]! (Γ' ⟹ some A) := wkR (wkL π h)

def andL (π : ⊢ᵍ[CK]! (insert A (insert B Γ) ⟹ Δ)) : ⊢ᵍ[CK]! (insert (A ⋏ B) Γ ⟹ Δ) := by
  have h₁ : ⊢ᵍ[CK]! (insert (A ⋏ B) (insert B Γ) ⟹ Δ) := andL₁ π;
  have h₂ : ⊢ᵍ[CK]! (insert B (insert (A ⋏ B) Γ) ⟹ Δ) := wkL h₁;
  have h₃ : ⊢ᵍ[CK]! (insert (A ⋏ B) (insert (A ⋏ B) Γ) ⟹ Δ) := andL₂ h₂;
  exact wkL h₃;

def verum : ⊢ᵍ[CK]! (Γ ⟹ some ⊤) := impR (wkL botL)

end ProofGentzen

end LogicCK

end
