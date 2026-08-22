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
  | axm A => exact fconj_imp (Finset.mem_singleton_self A)
  | botL => exact imp_trans (fconj_imp (Finset.mem_singleton_self ⊥)) efq
  | wkL h h' ih => exact imp_trans (fconj_subset h') ih
  | wkR h ih => exact imp_trans ih efq
  | andL₁ h ih => exact imp_trans (fconj_insert_mono andElim₁) ih
  | andL₂ h ih => exact imp_trans (fconj_insert_mono andElim₂) ih
  | andR h₁ h₂ ih₁ ih₂ => exact and_intro_ctx ih₁ ih₂
  | orL h₁ h₂ ih₁ ih₂ =>
    exact imp_trans fconj_insert_imp
      (uncurry (or_imp (curry (imp_trans imp_fconj_insert ih₁)) (curry (imp_trans imp_fconj_insert ih₂))))
  | orR₁ h ih => exact imp_trans ih orIntro₁
  | orR₂ h ih => exact imp_trans ih orIntro₂
  | impL h₁ h₂ ih₁ ih₂ =>
    exact imp_trans
      (and_intro_ctx
        (mdp_ctx (fconj_imp (Finset.mem_insert_self _ _))
          (imp_trans (fconj_subset (Finset.subset_insert _ _)) ih₁))
        (fconj_subset (Finset.subset_insert _ _)))
      (imp_trans imp_fconj_insert ih₂)
  | impR h ih => exact mdp imp_swap (curry (imp_trans imp_fconj_insert ih))
  | box h ih => exact imp_trans fconj_box (box_mono ih)
  | dia h ih =>
    exact mdp_ctx
      (imp_trans (fconj_subset (Finset.subset_insert _ _))
        (imp_trans fconj_box (imp_trans (box_mono (mdp imp_swap (curry (imp_trans imp_fconj_insert ih)))) kDia)))
      (fconj_imp (Finset.mem_insert_self _ _))
  | cut h₁ h₂ ih₁ ih₂ =>
    exact imp_trans
      (and_intro_ctx (imp_trans (fconj_subset Finset.subset_union_left) ih₁) (fconj_subset Finset.subset_union_right))
      (imp_trans imp_fconj_insert ih₂)

/-- - [Sat26, Proposition 4.18]
- [Dal25, Theorem 6.3] -/
theorem toHilbert (h : ⊢ᵍᶜ[CK] (Γ ⟹ some A)) : ⊢ᴴ[CK;∅] (⋀Γ 🡒 A) := toHilbert_aux h

end ProvableGentzenWithCut

end LogicCK

end
