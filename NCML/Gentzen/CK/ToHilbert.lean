module

public import NCML.Gentzen.CK.WithCut

/-! This file translates `GCK + cut` proofs into Hilbert-style `CK` proofs. -/

@[expose] public section

open scoped BDFormulaFinset
open ProvableBDHilbert

/-- The Hilbert-style translation `⋀Γ 🡒 A` of a sequent `Γ ⟹ some A`, or `⋀Γ 🡒 ⊥` if the
succedent is `none`. -/
noncomputable def Sequent.toFormula (S : Sequent) : BDFormula := ⋀S.ant 🡒 S.suc.getD ⊥

namespace LogicCK

namespace ProvableGentzenWithCut

variable {Γ Γ₁ Γ₂ : BDFormulaFinset} {A : BDFormula}

lemma toHilbert_aux {S : Sequent} (h : ⊢ᵍᶜ[CK] S) : ⊢ᴴ[CK;∅] S.toFormula := by
  induction h with
  | axm A => sorry
  | botL => sorry
  | wkL h h' ih => sorry
  | wkR h ih => sorry
  | andL₁ h ih => sorry
  | andL₂ h ih => sorry
  | andR h₁ h₂ ih₁ ih₂ => sorry
  | orL h₁ h₂ ih₁ ih₂ => sorry
  | orR₁ h ih => sorry
  | orR₂ h ih => sorry
  | impL h₁ h₂ ih₁ ih₂ => sorry
  | impR h ih => sorry
  | box h ih => sorry
  | dia h ih => sorry
  | cut h₁ h₂ ih₁ ih₂ => sorry

/-- - [Sat26, Proposition 4.18]
- [Dal25, Theorem 6.3] -/
theorem toHilbert (h : ⊢ᵍᶜ[CK] (Γ ⟹ some A)) : ⊢ᴴ[CK;∅] (⋀Γ 🡒 A) := toHilbert_aux h

end ProvableGentzenWithCut

end LogicCK

end
