module

public import NCML.Gentzen.Sequent
public import NCML.Hilbert.Basic
public import NCML.Hilbert.Logics

/-! This file defines the cut-free sequent calculus `GCK` and its cut-extended variant
`GCK + cut` for `LogicCK`, translates their proofs to and from Hilbert-style `CK`
derivations, and shows the two systems are equivalent. -/

@[expose] public section

open scoped BDFormulaFinset BDFormulaList

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
prefix:120 "⊢ᵍ[CK]! " => ProofGentzen


namespace ProofGentzen

variable {Γ : BDFormulaFinset} {Δ : Option BDFormula} {A B : BDFormula}

def union (A) (hΓ : A ∈ Γ := by grind) : ⊢ᵍ[CK]! (Γ ⟹ some A) := wkL (axm A)

def botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ[CK]! (Γ ⟹ Δ) := wkL botL

def andL (π : ⊢ᵍ[CK]! (insert A (insert B Γ) ⟹ Δ)) : ⊢ᵍ[CK]! (insert (A ⋏ B) Γ ⟹ Δ) := by
  have h₁ : ⊢ᵍ[CK]! (insert (A ⋏ B) (insert B Γ) ⟹ Δ) := andL₁ π;
  have h₂ : ⊢ᵍ[CK]! (insert B (insert (A ⋏ B) Γ) ⟹ Δ) := wkL h₁;
  have h₃ : ⊢ᵍ[CK]! (insert (A ⋏ B) (insert (A ⋏ B) Γ) ⟹ Δ) := andL₂ h₂;
  exact wkL h₃;

def verum : ⊢ᵍ[CK]! (Γ ⟹ some ⊤) := impR (wkL botL)

end ProofGentzen


abbrev ProvableGentzen (S : Sequent) : Prop := Nonempty (⊢ᵍ[CK]! S)
prefix:120 "⊢ᵍ[CK] " => ProvableGentzen
prefix:120 "⊬ᵍ[CK] " => λ S => ¬ProvableGentzen S

namespace ProvableGentzen

variable {Γ Γ' : BDFormulaFinset} {Δ : Option BDFormula} {A B : BDFormula}

lemma axm (A : BDFormula) : ⊢ᵍ[CK] ({A} ⟹ some A) := ⟨ProofGentzen.axm A⟩
lemma botL : ⊢ᵍ[CK] ({⊥} ⟹ Δ) := ⟨ProofGentzen.botL⟩
lemma wkL (h : ⊢ᵍ[CK] (Γ ⟹ Δ)) (h' : Γ ⊆ Γ' := by grind) : ⊢ᵍ[CK] (Γ' ⟹ Δ) := ⟨ProofGentzen.wkL h.some h'⟩
lemma wkR (h : ⊢ᵍ[CK] (Γ ⟹ none)) : ⊢ᵍ[CK] (Γ ⟹ some A) := ⟨ProofGentzen.wkR h.some⟩
lemma andL₁ (h : ⊢ᵍ[CK] (insert A Γ ⟹ Δ)) : ⊢ᵍ[CK] (insert (A ⋏ B) Γ ⟹ Δ) := ⟨ProofGentzen.andL₁ h.some⟩
lemma andL₂ (h : ⊢ᵍ[CK] (insert B Γ ⟹ Δ)) : ⊢ᵍ[CK] (insert (A ⋏ B) Γ ⟹ Δ) := ⟨ProofGentzen.andL₂ h.some⟩
lemma andR (h₁ : ⊢ᵍ[CK] (Γ ⟹ some A)) (h₂ : ⊢ᵍ[CK] (Γ ⟹ some B)) : ⊢ᵍ[CK] (Γ ⟹ some (A ⋏ B)) := ⟨ProofGentzen.andR h₁.some h₂.some⟩
lemma orL (h₁ : ⊢ᵍ[CK] (insert A Γ ⟹ Δ)) (h₂ : ⊢ᵍ[CK] (insert B Γ ⟹ Δ)) : ⊢ᵍ[CK] (insert (A ⋎ B) Γ ⟹ Δ) := ⟨ProofGentzen.orL h₁.some h₂.some⟩
lemma orR₁ (h : ⊢ᵍ[CK] (Γ ⟹ some A)) : ⊢ᵍ[CK] (Γ ⟹ some (A ⋎ B)) := ⟨ProofGentzen.orR₁ h.some⟩
lemma orR₂ (h : ⊢ᵍ[CK] (Γ ⟹ some B)) : ⊢ᵍ[CK] (Γ ⟹ some (A ⋎ B)) := ⟨ProofGentzen.orR₂ h.some⟩
lemma impL (h₁ : ⊢ᵍ[CK] (Γ ⟹ some A)) (h₂ : ⊢ᵍ[CK] (insert B Γ ⟹ Δ)) : ⊢ᵍ[CK] (insert (A 🡒 B) Γ ⟹ Δ) := ⟨ProofGentzen.impL h₁.some h₂.some⟩
lemma impR (h : ⊢ᵍ[CK] (insert A Γ ⟹ some B)) : ⊢ᵍ[CK] (Γ ⟹ some (A 🡒 B)) := ⟨ProofGentzen.impR h.some⟩
lemma box (h : ⊢ᵍ[CK] (Γ ⟹ some A)) : ⊢ᵍ[CK] (□Γ ⟹ some (□A)) := ⟨ProofGentzen.box h.some⟩
lemma dia (h : ⊢ᵍ[CK] (insert A Γ ⟹ some B)) : ⊢ᵍ[CK] (insert (◇A) (□Γ) ⟹ some (◇B)) := ⟨ProofGentzen.dia h.some⟩

lemma union (A) (hΓ : A ∈ Γ := by grind) : ⊢ᵍ[CK] (Γ ⟹ some A) := ⟨ProofGentzen.union A hΓ⟩
@[grind =>] lemma botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᵍ[CK] (Γ ⟹ Δ) := ⟨ProofGentzen.botL_mem h⟩
lemma andL (h : ⊢ᵍ[CK] (insert A (insert B Γ) ⟹ Δ)) : ⊢ᵍ[CK] (insert (A ⋏ B) Γ ⟹ Δ) := ⟨ProofGentzen.andL h.some⟩
lemma verum : ⊢ᵍ[CK] (Γ ⟹ some ⊤) := ⟨ProofGentzen.verum⟩

@[induction_eliminator]
lemma rec
  {motive : (S : Sequent) → ⊢ᵍ[CK] S → Prop}
  (axm : ∀ A, motive ({A} ⟹ some A) (ProvableGentzen.axm A))
  (botL : ∀ {Δ}, motive ({⊥} ⟹ Δ) ProvableGentzen.botL)
  (wkL : ∀ {Γ Γ' Δ} (h : ⊢ᵍ[CK] (Γ ⟹ Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹ Δ) h → motive (Γ' ⟹ Δ) (wkL h h'))
  (wkR : ∀ {Γ A} (h : ⊢ᵍ[CK] (Γ ⟹ none)), motive (Γ ⟹ none) h → motive (Γ ⟹ some A) (wkR h))
  (andL₁ : ∀ {Γ Δ A B} (h : ⊢ᵍ[CK] (insert A Γ ⟹ Δ)),
    motive (insert A Γ ⟹ Δ) h → motive (insert (A ⋏ B) Γ ⟹ Δ) (andL₁ h)
  )
  (andL₂ : ∀ {Γ Δ A B} (h : ⊢ᵍ[CK] (insert B Γ ⟹ Δ)),
    motive (insert B Γ ⟹ Δ) h → motive (insert (A ⋏ B) Γ ⟹ Δ) (andL₂ h)
  )
  (andR : ∀ {Γ A B} (h₁ : ⊢ᵍ[CK] (Γ ⟹ some A)) (h₂ : ⊢ᵍ[CK] (Γ ⟹ some B)),
    motive (Γ ⟹ some A) h₁ → motive (Γ ⟹ some B) h₂ → motive (Γ ⟹ some (A ⋏ B)) (andR h₁ h₂)
  )
  (orL : ∀ {Γ Δ A B} (h₁ : ⊢ᵍ[CK] (insert A Γ ⟹ Δ)) (h₂ : ⊢ᵍ[CK] (insert B Γ ⟹ Δ)),
    motive (insert A Γ ⟹ Δ) h₁ → motive (insert B Γ ⟹ Δ) h₂ → motive (insert (A ⋎ B) Γ ⟹ Δ) (orL h₁ h₂)
  )
  (orR₁ : ∀ {Γ A B} (h : ⊢ᵍ[CK] (Γ ⟹ some A)), motive (Γ ⟹ some A) h → motive (Γ ⟹ some (A ⋎ B)) (orR₁ h))
  (orR₂ : ∀ {Γ A B} (h : ⊢ᵍ[CK] (Γ ⟹ some B)), motive (Γ ⟹ some B) h → motive (Γ ⟹ some (A ⋎ B)) (orR₂ h))
  (impL : ∀ {Γ Δ A B} (h₁ : ⊢ᵍ[CK] (Γ ⟹ some A)) (h₂ : ⊢ᵍ[CK] (insert B Γ ⟹ Δ)),
    motive (Γ ⟹ some A) h₁ → motive (insert B Γ ⟹ Δ) h₂ → motive (insert (A 🡒 B) Γ ⟹ Δ) (impL h₁ h₂)
  )
  (impR : ∀ {Γ A B} (h : ⊢ᵍ[CK] (insert A Γ ⟹ some B)),
    motive (insert A Γ ⟹ some B) h → motive (Γ ⟹ some (A 🡒 B)) (impR h)
  )
  (box : ∀ {Γ A} (h : ⊢ᵍ[CK] (Γ ⟹ some A)), motive (Γ ⟹ some A) h → motive (□Γ ⟹ some (□A)) (box h))
  (dia : ∀ {Γ A B} (h : ⊢ᵍ[CK] (insert A Γ ⟹ some B)),
    motive (insert A Γ ⟹ some B) h → motive (insert (◇A) (□Γ) ⟹ some (◇B)) (dia h)
  )
  : ∀ {S : Sequent} (h : ⊢ᵍ[CK] S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

lemma iff_unprovableGentzen_isEmpty_ProofGentzen {S : Sequent} : (⊬ᵍ[CK] S) ↔ (IsEmpty (⊢ᵍ[CK]! S)) := by
  simp [ProvableGentzen];

end ProvableGentzen

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

/-- The Hilbert-style translation `⋀Γ 🡒 A` of a sequent `Γ ⟹ some A`, or `⋀Γ 🡒 ⊥` if the
succedent is `none`. -/
noncomputable def Sequent.toFormula (S : Sequent) : BDFormula := ⋀S.ant 🡒 S.suc.getD ⊥

section

open ProvableBDHilbert

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

namespace LogicCK

namespace ProvableGentzenWithCut

variable {Γ : BDFormulaFinset} {A B C : BDFormula}

lemma union (A) (hΓ : A ∈ Γ := by grind) : ⊢ᵍᶜ[CK] (Γ ⟹ some A) := wkL (axm A)

lemma mdp (h₁ : ⊢ᵍᶜ[CK] (Γ ⟹ some (A 🡒 B))) (h₂ : ⊢ᵍᶜ[CK] (Γ ⟹ some A)) :
    ⊢ᵍᶜ[CK] (Γ ⟹ some B) := by
  have e : ⊢ᵍᶜ[CK] (insert (A 🡒 B) Γ ⟹ some B) := impL h₂ (union B);
  have h := cut h₁ e;
  rwa [Finset.union_self] at h;

lemma imply₁ : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (A 🡒 B 🡒 A)) :=
  impR (impR (union A))

lemma imply₂ : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some ((A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 A 🡒 C)) := by
  apply impR; apply impR; apply impR;
  have p₁ : ⊢ᵍᶜ[CK] (insert (B 🡒 C) ({A, B} : BDFormulaFinset) ⟹ some C) := impL (union B) (union C);
  have p₂ : ⊢ᵍᶜ[CK] (insert B ({A, B 🡒 C} : BDFormulaFinset) ⟹ some C) := wkL p₁;
  have p₃ : ⊢ᵍᶜ[CK] (insert (A 🡒 B) ({A, B 🡒 C} : BDFormulaFinset) ⟹ some C) := impL (union A) p₂;
  have p₄ : ⊢ᵍᶜ[CK] (insert (B 🡒 C) ({A, A 🡒 B} : BDFormulaFinset) ⟹ some C) := wkL p₃;
  have p₅ : ⊢ᵍᶜ[CK] (insert (A 🡒 B 🡒 C) ({A, A 🡒 B} : BDFormulaFinset) ⟹ some C) := impL (union A) p₄;
  exact wkL p₅

lemma andElim₁ : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (A ⋏ B 🡒 A)) :=
  impR (andL₁ (axm A))

lemma andElim₂ : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (A ⋏ B 🡒 B)) :=
  impR (andL₂ (axm B))

lemma andIntro : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (A 🡒 B 🡒 A ⋏ B)) :=
  impR (impR (andR (union A) (union B)))

lemma orIntro₁ : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (A 🡒 A ⋎ B)) :=
  impR (orR₁ (axm A))

lemma orIntro₂ : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (B 🡒 A ⋎ B)) :=
  impR (orR₂ (axm B))

lemma orElim : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some ((A 🡒 C) 🡒 (B 🡒 C) 🡒 (A ⋎ B 🡒 C))) := by
  apply impR; apply impR; apply impR;
  have p₁ : ⊢ᵍᶜ[CK] (insert (A 🡒 C) ({A} : BDFormulaFinset) ⟹ some C) := impL (union A) (union C);
  have q₁ : ⊢ᵍᶜ[CK] (insert A ({B 🡒 C, A 🡒 C} : BDFormulaFinset) ⟹ some C) := wkL p₁;
  have p₂ : ⊢ᵍᶜ[CK] (insert (B 🡒 C) ({B} : BDFormulaFinset) ⟹ some C) := impL (union B) (union C);
  have q₂ : ⊢ᵍᶜ[CK] (insert B ({B 🡒 C, A 🡒 C} : BDFormulaFinset) ⟹ some C) := wkL p₂;
  exact wkL (orL q₁ q₂)

lemma efq : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some ((⊥ : BDFormula) 🡒 A)) :=
  impR botL

private lemma kPremise : ⊢ᵍᶜ[CK] (({A, A 🡒 B} : BDFormulaFinset) ⟹ some B) :=
  wkL (impL (union A) (union B) : ⊢ᵍᶜ[CK] (insert (A 🡒 B) ({A} : BDFormulaFinset) ⟹ some B))

lemma kBox : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (□(A 🡒 B) 🡒 □A 🡒 □B)) := by
  apply impR; apply impR;
  simpa [BDFormulaFinset.box, Finset.image_insert, Finset.image_singleton, Finset.image_empty]
    using box kPremise

lemma kDia : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (□(A 🡒 B) 🡒 ◇A 🡒 ◇B)) := by
  apply impR; apply impR;
  simpa [BDFormulaFinset.box, Finset.image_singleton] using dia kPremise

lemma nec (h : ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some A)) :
    ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some (□A)) := by
  simpa using box h

lemma of_provable : (⊢ʰ[CK;∅] A) → ⊢ᵍᶜ[CK] ((∅ : BDFormulaFinset) ⟹ some A) := by
  intro h;
  induction h with
  | axm hmem => simp at hmem;
  | imply₁ => exact imply₁;
  | imply₂ => exact imply₂;
  | andElim₁ => exact andElim₁;
  | andElim₂ => exact andElim₂;
  | andIntro => exact andIntro;
  | orIntro₁ => exact orIntro₁;
  | orIntro₂ => exact orIntro₂;
  | orElim => exact orElim;
  | efq => exact efq;
  | kBox => exact kBox;
  | kDia => exact kDia;
  | mdp h₁ h₂ ih₁ ih₂ => exact mdp ih₁ ih₂;
  | nec h ih => exact nec ih;

lemma lconj_of_forall_mem {L : BDFormulaList} (h : ∀ B ∈ L, B ∈ Γ) :
    ⊢ᵍᶜ[CK] (Γ ⟹ some (⋀L)) := by
  induction L with
  | nil => exact of_without_cut ProvableGentzen.verum;
  | cons B L ih =>
    exact andR (union B (h B (by grind))) (ih (by grind));

lemma fconj : ⊢ᵍᶜ[CK] (Γ ⟹ some (⋀Γ)) := by
  apply lconj_of_forall_mem;
  intro B hB;
  exact Finset.mem_toList.mp hB;

lemma ofHilbert (h : ⊢ʰ[CK;∅] (⋀Γ 🡒 A)) : ⊢ᵍᶜ[CK] (Γ ⟹ some A) := by
  have d := of_provable h;
  have e : ⊢ᵍᶜ[CK] (insert (⋀Γ 🡒 A) Γ ⟹ some A) := impL fconj (union A);
  have c := cut d e;
  rwa [Finset.empty_union] at c;

/-- - [Sat26, Proposition 4.18]
- [Dal25, Theorem 6.3] -/
theorem iff_hilbert : ⊢ᵍᶜ[CK] (Γ ⟹ some A) ↔ ⊢ʰ[CK;∅] (⋀Γ 🡒 A) := ⟨toHilbert, ofHilbert⟩

end ProvableGentzenWithCut

end LogicCK

end
