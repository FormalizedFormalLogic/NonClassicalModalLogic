module

public import NCML.Gentzen.CK.WithCut
public import NCML.Hilbert.Basic

/-! This file derives `GCK + cut` sequents from Hilbert-style `CK` derivations. -/

@[expose] public section

open scoped BDFormulaFinset BDFormulaList

namespace LogicCK

namespace ProvableGentzenWithCut

variable {Γ Γ₁ Γ₂ : BDFormulaFinset} {Δ : Option BDFormula} {A B C : BDFormula}

lemma union (A) (hΓ : A ∈ Γ := by grind) : ⊢ᵍᶜ[CK] (Γ ⟹ some A) := wkL (axm A)

lemma mdp (h₁ : ⊢ᵍᶜ[CK] (Γ ⟹ some (A 🡒 B))) (h₂ : ⊢ᵍᶜ[CK] (Γ ⟹ some A)) :
    ⊢ᵍᶜ[CK] (Γ ⟹ some B) := by
  have e : ⊢ᵍᶜ[CK] (insert (A 🡒 B) Γ ⟹ some B) := impL h₂ (union B);
  have h := cut h₁ e;
  rwa [Finset.union_self] at h;

lemma imply₁ : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (A 🡒 B 🡒 A)) :=
  impR (impR (union A))

lemma imply₂ : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some ((A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 A 🡒 C)) := by
  sorry

lemma andElim₁ : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (A ⋏ B 🡒 A)) := by
  sorry

lemma andElim₂ : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (A ⋏ B 🡒 B)) := by
  sorry

lemma andIntro : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (A 🡒 B 🡒 A ⋏ B)) := by
  sorry

lemma orIntro₁ : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (A 🡒 A ⋎ B)) := by
  sorry

lemma orIntro₂ : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (B 🡒 A ⋎ B)) := by
  sorry

lemma orElim : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some ((A 🡒 C) 🡒 (B 🡒 C) 🡒 (A ⋎ B 🡒 C))) := by
  sorry

lemma efq : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some ((⊥ : BDFormula) 🡒 A)) := by
  sorry

lemma kBox : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (□(A 🡒 B) 🡒 □A 🡒 □B)) := by
  sorry

lemma kDia : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (□(A 🡒 B) 🡒 ◇A 🡒 ◇B)) := by
  sorry

lemma nec (h : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some A)) :
    ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (□A)) := by
  sorry

lemma of_provable : (⊢ᴴ[CK;∅] A) → ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some A) := by
  sorry

lemma lconj_of_forall_mem {L : BDFormulaList} (h : ∀ B ∈ L, B ∈ Γ) :
    ⊢ᵍᶜ[CK] (Γ ⟹ some (⋀L)) := by
  sorry

lemma fconj : ⊢ᵍᶜ[CK] (Γ ⟹ some (⋀Γ)) := by
  sorry

lemma ofHilbert (h : ⊢ᴴ[CK;∅] (⋀Γ 🡒 A)) : ⊢ᵍᶜ[CK] (Γ ⟹ some A) := by
  sorry

end ProvableGentzenWithCut

end LogicCK

end
