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

lemma toHilbert_aux {S : Sequent} (h : ⊢ᵍᶜ[CK] S) : ⊢ʰ[CK;∅] S.toFormula := by
  induction h with
  | axm A => exact fconj_imp (Finset.mem_singleton_self A)
  | botL => exact imp_trans (fconj_imp (Finset.mem_singleton_self ⊥)) efq
  | wkL h h' ih => exact imp_trans (fconj_subset h') ih
  | wkR h ih => exact imp_trans ih efq
  | andL₁ h ih => exact imp_trans (fconj_insert_mono andElim₁) ih
  | andL₂ h ih => exact imp_trans (fconj_insert_mono andElim₂) ih
  | andR h₁ h₂ ih₁ ih₂ => exact and_intro_ctx ih₁ ih₂
  | @orL Γ Δ A B h₁ h₂ ih₁ ih₂ =>
    have h₃ : ⊢ʰ[CK;∅] A 🡒 (Γ ⟹ Δ).toFormula := curry (imp_trans imp_fconj_insert ih₁);
    have h₄ : ⊢ʰ[CK;∅] B 🡒 (Γ ⟹ Δ).toFormula := curry (imp_trans imp_fconj_insert ih₂);
    exact imp_trans fconj_insert_imp (uncurry (or_imp h₃ h₄));
  | orR₁ h ih => exact imp_trans ih orIntro₁
  | orR₂ h ih => exact imp_trans ih orIntro₂
  | @impL Γ Δ A B h₁ h₂ ih₁ ih₂ =>
    have h₃ : ⊢ʰ[CK;∅] ⋀(insert (A 🡒 B) Γ) 🡒 A := imp_trans (fconj_subset (Finset.subset_insert _ _)) ih₁;
    have h₄ : ⊢ʰ[CK;∅] ⋀(insert (A 🡒 B) Γ) 🡒 B := mdp_ctx (fconj_imp (Finset.mem_insert_self _ _)) h₃;
    have h₅ : ⊢ʰ[CK;∅] ⋀(insert (A 🡒 B) Γ) 🡒 B ⋏ ⋀Γ := and_intro_ctx h₄ (fconj_subset (Finset.subset_insert _ _));
    exact imp_trans h₅ (imp_trans imp_fconj_insert ih₂);
  | @impR Γ A B h ih =>
    have h₁ : ⊢ʰ[CK;∅] A 🡒 (Γ ⟹ some B).toFormula := curry (imp_trans imp_fconj_insert ih);
    exact mdp imp_swap h₁;
  | box h ih => exact imp_trans fconj_box (box_mono ih)
  | @dia Γ A B h ih =>
    have h₁ : ⊢ʰ[CK;∅] ⋀Γ 🡒 A 🡒 B := mdp imp_swap (curry (imp_trans imp_fconj_insert ih));
    have h₂ : ⊢ʰ[CK;∅] ⋀(□Γ) 🡒 ◇A 🡒 ◇B := imp_trans fconj_box (imp_trans (box_mono h₁) kDia);
    have h₃ : ⊢ʰ[CK;∅] ⋀(insert (◇A) (□Γ)) 🡒 ◇A 🡒 ◇B := imp_trans (fconj_subset (Finset.subset_insert _ _)) h₂;
    exact mdp_ctx h₃ (fconj_imp (Finset.mem_insert_self _ _));
  | @cut Γ₁ Γ₂ Δ A h₁ h₂ ih₁ ih₂ =>
    have h₃ : ⊢ʰ[CK;∅] ⋀(Γ₁ ∪ Γ₂) 🡒 A := imp_trans (fconj_subset Finset.subset_union_left) ih₁;
    have h₄ : ⊢ʰ[CK;∅] ⋀(Γ₁ ∪ Γ₂) 🡒 A ⋏ ⋀Γ₂ := and_intro_ctx h₃ (fconj_subset Finset.subset_union_right);
    exact imp_trans h₄ (imp_trans imp_fconj_insert ih₂);

lemma toHilbert (h : ⊢ᵍᶜ[CK] (Γ ⟹ some A)) : ⊢ʰ[CK;∅] (⋀Γ 🡒 A) := toHilbert_aux h

end ProvableGentzenWithCut

end LogicCK

end
