module

public import NCML.Gentzen.CK.Basic

@[expose] public section

open scoped BDFormulaFinset

namespace LogicCK

/-- The sequent calculus `GCK` extended with the cut rule.

- [Wij90, Section 1.2]
-/
inductive ProofGentzenWithCut : Sequent → Type
  | axm (A)         : ProofGentzenWithCut ({A} ⟹ some A)
  | botL {Δ}        : ProofGentzenWithCut ({⊥} ⟹ Δ)
  | wkL  {Γ Γ' Δ}   : ProofGentzenWithCut (Γ ⟹ Δ) → (_ : Γ ⊆ Γ' := by grind) → ProofGentzenWithCut (Γ' ⟹ Δ)
  | wkR  {Γ A}      : ProofGentzenWithCut (Γ ⟹ none) → ProofGentzenWithCut (Γ ⟹ some A)
  | andL₁ {Γ Δ A B} : ProofGentzenWithCut (insert A Γ ⟹ Δ) → ProofGentzenWithCut (insert (A ⋏ B) Γ ⟹ Δ)
  | andL₂ {Γ Δ A B} : ProofGentzenWithCut (insert B Γ ⟹ Δ) → ProofGentzenWithCut (insert (A ⋏ B) Γ ⟹ Δ)
  | andR {Γ A B}    : ProofGentzenWithCut (Γ ⟹ some A) → ProofGentzenWithCut (Γ ⟹ some B) → ProofGentzenWithCut (Γ ⟹ some (A ⋏ B))
  | orL  {Γ Δ A B}  : ProofGentzenWithCut (insert A Γ ⟹ Δ) → ProofGentzenWithCut (insert B Γ ⟹ Δ) → ProofGentzenWithCut (insert (A ⋎ B) Γ ⟹ Δ)
  | orR₁ {Γ A B}    : ProofGentzenWithCut (Γ ⟹ some A) → ProofGentzenWithCut (Γ ⟹ some (A ⋎ B))
  | orR₂ {Γ A B}    : ProofGentzenWithCut (Γ ⟹ some B) → ProofGentzenWithCut (Γ ⟹ some (A ⋎ B))
  | impL {Γ Δ A B}  : ProofGentzenWithCut (Γ ⟹ some A) → ProofGentzenWithCut (insert B Γ ⟹ Δ) → ProofGentzenWithCut (insert (A 🡒 B) Γ ⟹ Δ)
  | impR {Γ A B}    : ProofGentzenWithCut (insert A Γ ⟹ some B) → ProofGentzenWithCut (Γ ⟹ some (A 🡒 B))
  | box  {Γ A}      : ProofGentzenWithCut (Γ ⟹ some A) → ProofGentzenWithCut (□Γ ⟹ some (□A))
  | dia  {Γ A B}    : ProofGentzenWithCut (insert A Γ ⟹ some B) → ProofGentzenWithCut (insert (◇A) (□Γ) ⟹ some (◇B))
  | cut {Γ₁ Γ₂ Δ A} : ProofGentzenWithCut (Γ₁ ⟹ some A) → ProofGentzenWithCut (insert A Γ₂ ⟹ Δ) → ProofGentzenWithCut (Γ₁ ∪ Γ₂ ⟹ Δ)
prefix:120 "⊢ᵍᶜ[CK]! " => ProofGentzenWithCut

/-- Every cut-free proof is a proof in the cut-extended calculus. -/
def ProofGentzenWithCut.ofProofGentzen {S : Sequent} : ⊢ᵍ[CK]! S → ⊢ᵍᶜ[CK]! S
  | .axm A => .axm A
  | .botL => .botL
  | .wkL h h' => .wkL (ofProofGentzen h) h'
  | .wkR h => .wkR (ofProofGentzen h)
  | .andL₁ h => .andL₁ (ofProofGentzen h)
  | .andL₂ h => .andL₂ (ofProofGentzen h)
  | .andR h₁ h₂ => .andR (ofProofGentzen h₁) (ofProofGentzen h₂)
  | .orL h₁ h₂ => .orL (ofProofGentzen h₁) (ofProofGentzen h₂)
  | .orR₁ h => .orR₁ (ofProofGentzen h)
  | .orR₂ h => .orR₂ (ofProofGentzen h)
  | .impL h₁ h₂ => .impL (ofProofGentzen h₁) (ofProofGentzen h₂)
  | .impR h => .impR (ofProofGentzen h)
  | .box h => .box (ofProofGentzen h)
  | .dia h => .dia (ofProofGentzen h)
abbrev ProvableGentzenWithCut (S : Sequent) : Prop := Nonempty (⊢ᵍᶜ[CK]! S)
prefix:120 "⊢ᵍᶜ[CK] " => ProvableGentzenWithCut
prefix:120 "⊬ᵍᶜ[CK] " => λ S => ¬ProvableGentzenWithCut S

namespace ProvableGentzenWithCut

variable {Γ Γ' Γ₁ Γ₂ : BDFormulaFinset} {Δ : Option BDFormula} {A B : BDFormula}

theorem of_without_cut {S : Sequent} : ⊢ᵍ[CK] S → ⊢ᵍᶜ[CK] S := λ ⟨p⟩ => ⟨ProofGentzenWithCut.ofProofGentzen p⟩

lemma axm (A : BDFormula) : ⊢ᵍᶜ[CK] ({A} ⟹ some A) := ⟨ProofGentzenWithCut.axm A⟩
lemma botL : ⊢ᵍᶜ[CK] ({⊥} ⟹ Δ) := ⟨ProofGentzenWithCut.botL⟩
lemma wkL (h : ⊢ᵍᶜ[CK] (Γ ⟹ Δ)) (h' : Γ ⊆ Γ' := by grind) : ⊢ᵍᶜ[CK] (Γ' ⟹ Δ) := ⟨ProofGentzenWithCut.wkL h.some h'⟩
lemma wkR (h : ⊢ᵍᶜ[CK] (Γ ⟹ none)) : ⊢ᵍᶜ[CK] (Γ ⟹ some A) := ⟨ProofGentzenWithCut.wkR h.some⟩
lemma andL₁ (h : ⊢ᵍᶜ[CK] (insert A Γ ⟹ Δ)) : ⊢ᵍᶜ[CK] (insert (A ⋏ B) Γ ⟹ Δ) := ⟨ProofGentzenWithCut.andL₁ h.some⟩
lemma andL₂ (h : ⊢ᵍᶜ[CK] (insert B Γ ⟹ Δ)) : ⊢ᵍᶜ[CK] (insert (A ⋏ B) Γ ⟹ Δ) := ⟨ProofGentzenWithCut.andL₂ h.some⟩
lemma andR (h₁ : ⊢ᵍᶜ[CK] (Γ ⟹ some A)) (h₂ : ⊢ᵍᶜ[CK] (Γ ⟹ some B)) : ⊢ᵍᶜ[CK] (Γ ⟹ some (A ⋏ B)) := ⟨ProofGentzenWithCut.andR h₁.some h₂.some⟩
lemma orL (h₁ : ⊢ᵍᶜ[CK] (insert A Γ ⟹ Δ)) (h₂ : ⊢ᵍᶜ[CK] (insert B Γ ⟹ Δ)) : ⊢ᵍᶜ[CK] (insert (A ⋎ B) Γ ⟹ Δ) := ⟨ProofGentzenWithCut.orL h₁.some h₂.some⟩
lemma orR₁ (h : ⊢ᵍᶜ[CK] (Γ ⟹ some A)) : ⊢ᵍᶜ[CK] (Γ ⟹ some (A ⋎ B)) := ⟨ProofGentzenWithCut.orR₁ h.some⟩
lemma orR₂ (h : ⊢ᵍᶜ[CK] (Γ ⟹ some B)) : ⊢ᵍᶜ[CK] (Γ ⟹ some (A ⋎ B)) := ⟨ProofGentzenWithCut.orR₂ h.some⟩
lemma impL (h₁ : ⊢ᵍᶜ[CK] (Γ ⟹ some A)) (h₂ : ⊢ᵍᶜ[CK] (insert B Γ ⟹ Δ)) : ⊢ᵍᶜ[CK] (insert (A 🡒 B) Γ ⟹ Δ) := ⟨ProofGentzenWithCut.impL h₁.some h₂.some⟩
lemma impR (h : ⊢ᵍᶜ[CK] (insert A Γ ⟹ some B)) : ⊢ᵍᶜ[CK] (Γ ⟹ some (A 🡒 B)) := ⟨ProofGentzenWithCut.impR h.some⟩
lemma box (h : ⊢ᵍᶜ[CK] (Γ ⟹ some A)) : ⊢ᵍᶜ[CK] (□Γ ⟹ some (□A)) := ⟨ProofGentzenWithCut.box h.some⟩
lemma dia (h : ⊢ᵍᶜ[CK] (insert A Γ ⟹ some B)) : ⊢ᵍᶜ[CK] (insert (◇A) (□Γ) ⟹ some (◇B)) := ⟨ProofGentzenWithCut.dia h.some⟩
lemma cut (h₁ : ⊢ᵍᶜ[CK] (Γ₁ ⟹ some A)) (h₂ : ⊢ᵍᶜ[CK] (insert A Γ₂ ⟹ Δ)) : ⊢ᵍᶜ[CK] (Γ₁ ∪ Γ₂ ⟹ Δ) := ⟨ProofGentzenWithCut.cut h₁.some h₂.some⟩

@[induction_eliminator]
lemma rec
  {motive : (S : Sequent) → ⊢ᵍᶜ[CK] S → Prop}
  (axm : ∀ A, motive ({A} ⟹ some A) (ProvableGentzenWithCut.axm A))
  (botL : ∀ {Δ}, motive ({⊥} ⟹ Δ) ProvableGentzenWithCut.botL)
  (wkL : ∀ {Γ Γ' Δ} (h : ⊢ᵍᶜ[CK] (Γ ⟹ Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹ Δ) h → motive (Γ' ⟹ Δ) (wkL h h'))
  (wkR : ∀ {Γ A} (h : ⊢ᵍᶜ[CK] (Γ ⟹ none)), motive (Γ ⟹ none) h → motive (Γ ⟹ some A) (wkR h))
  (andL₁ : ∀ {Γ Δ A B} (h : ⊢ᵍᶜ[CK] (insert A Γ ⟹ Δ)),
    motive (insert A Γ ⟹ Δ) h → motive (insert (A ⋏ B) Γ ⟹ Δ) (andL₁ h)
  )
  (andL₂ : ∀ {Γ Δ A B} (h : ⊢ᵍᶜ[CK] (insert B Γ ⟹ Δ)),
    motive (insert B Γ ⟹ Δ) h → motive (insert (A ⋏ B) Γ ⟹ Δ) (andL₂ h)
  )
  (andR : ∀ {Γ A B} (h₁ : ⊢ᵍᶜ[CK] (Γ ⟹ some A)) (h₂ : ⊢ᵍᶜ[CK] (Γ ⟹ some B)),
    motive (Γ ⟹ some A) h₁ → motive (Γ ⟹ some B) h₂ → motive (Γ ⟹ some (A ⋏ B)) (andR h₁ h₂)
  )
  (orL : ∀ {Γ Δ A B} (h₁ : ⊢ᵍᶜ[CK] (insert A Γ ⟹ Δ)) (h₂ : ⊢ᵍᶜ[CK] (insert B Γ ⟹ Δ)),
    motive (insert A Γ ⟹ Δ) h₁ → motive (insert B Γ ⟹ Δ) h₂ → motive (insert (A ⋎ B) Γ ⟹ Δ) (orL h₁ h₂)
  )
  (orR₁ : ∀ {Γ A B} (h : ⊢ᵍᶜ[CK] (Γ ⟹ some A)), motive (Γ ⟹ some A) h → motive (Γ ⟹ some (A ⋎ B)) (orR₁ h))
  (orR₂ : ∀ {Γ A B} (h : ⊢ᵍᶜ[CK] (Γ ⟹ some B)), motive (Γ ⟹ some B) h → motive (Γ ⟹ some (A ⋎ B)) (orR₂ h))
  (impL : ∀ {Γ Δ A B} (h₁ : ⊢ᵍᶜ[CK] (Γ ⟹ some A)) (h₂ : ⊢ᵍᶜ[CK] (insert B Γ ⟹ Δ)),
    motive (Γ ⟹ some A) h₁ → motive (insert B Γ ⟹ Δ) h₂ → motive (insert (A 🡒 B) Γ ⟹ Δ) (impL h₁ h₂)
  )
  (impR : ∀ {Γ A B} (h : ⊢ᵍᶜ[CK] (insert A Γ ⟹ some B)),
    motive (insert A Γ ⟹ some B) h → motive (Γ ⟹ some (A 🡒 B)) (impR h)
  )
  (box : ∀ {Γ A} (h : ⊢ᵍᶜ[CK] (Γ ⟹ some A)), motive (Γ ⟹ some A) h → motive (□Γ ⟹ some (□A)) (box h))
  (dia : ∀ {Γ A B} (h : ⊢ᵍᶜ[CK] (insert A Γ ⟹ some B)),
    motive (insert A Γ ⟹ some B) h → motive (insert (◇A) (□Γ) ⟹ some (◇B)) (dia h)
  )
  (cut : ∀ {Γ₁ Γ₂ Δ A} (h₁ : ⊢ᵍᶜ[CK] (Γ₁ ⟹ some A)) (h₂ : ⊢ᵍᶜ[CK] (insert A Γ₂ ⟹ Δ)),
    motive (Γ₁ ⟹ some A) h₁ → motive (insert A Γ₂ ⟹ Δ) h₂ → motive (Γ₁ ∪ Γ₂ ⟹ Δ) (cut h₁ h₂)
  )
  : ∀ {S : Sequent} (h : ⊢ᵍᶜ[CK] S), motive S h := by
    rintro S ⟨h⟩;
    induction h with
    | axm A => apply axm;
    | botL => apply botL;
    | wkL h h' ih => apply wkL ⟨h⟩ h' ih;
    | wkR h ih => apply wkR ⟨h⟩ ih;
    | andL₁ h ih => apply andL₁ ⟨h⟩ ih;
    | andL₂ h ih => apply andL₂ ⟨h⟩ ih;
    | andR h₁ h₂ ih₁ ih₂ => apply andR ⟨h₁⟩ ⟨h₂⟩ ih₁ ih₂;
    | orL h₁ h₂ ih₁ ih₂ => apply orL ⟨h₁⟩ ⟨h₂⟩ ih₁ ih₂;
    | orR₁ h ih => apply orR₁ ⟨h⟩ ih;
    | orR₂ h ih => apply orR₂ ⟨h⟩ ih;
    | impL h₁ h₂ ih₁ ih₂ => apply impL ⟨h₁⟩ ⟨h₂⟩ ih₁ ih₂;
    | impR h ih => apply impR ⟨h⟩ ih;
    | box h ih => apply box ⟨h⟩ ih;
    | dia h ih => apply dia ⟨h⟩ ih;
    | cut h₁ h₂ ih₁ ih₂ => apply cut ⟨h₁⟩ ⟨h₂⟩ ih₁ ih₂;

end ProvableGentzenWithCut

end LogicCK

end
