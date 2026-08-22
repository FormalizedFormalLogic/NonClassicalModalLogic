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

notation:120 "⊢ᴳ[CK]! " S:121 => ProofGentzen S


namespace ProofGentzen

variable {Γ : BDFormulaFinset} {Δ : Option BDFormula} {A B : BDFormula}

def union (A) (hΓ : A ∈ Γ := by grind) : ⊢ᴳ[CK]! (Γ ⟹ some A) := wkL (axm A)

def botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᴳ[CK]! (Γ ⟹ Δ) := wkL botL

def andL (π : ⊢ᴳ[CK]! (insert A (insert B Γ) ⟹ Δ)) : ⊢ᴳ[CK]! (insert (A ⋏ B) Γ ⟹ Δ) := by
  have h₁ : ⊢ᴳ[CK]! (insert (A ⋏ B) (insert B Γ) ⟹ Δ) := andL₁ π;
  have h₂ : ⊢ᴳ[CK]! (insert B (insert (A ⋏ B) Γ) ⟹ Δ) := wkL h₁;
  have h₃ : ⊢ᴳ[CK]! (insert (A ⋏ B) (insert (A ⋏ B) Γ) ⟹ Δ) := andL₂ h₂;
  exact wkL h₃;

def verum : ⊢ᴳ[CK]! (Γ ⟹ some ⊤) := impR (wkL botL)

end ProofGentzen


abbrev ProvableGentzen (S : Sequent) : Prop := Nonempty (⊢ᴳ[CK]! S)
notation:120 "⊢ᴳ[CK] " S:121 => ProvableGentzen S
notation:120 "⊬ᴳ[CK] " S:121 => ¬ ProvableGentzen S

namespace ProvableGentzen

variable {Γ Γ' : BDFormulaFinset} {Δ : Option BDFormula} {A B : BDFormula}

lemma axm (A : BDFormula) : ⊢ᴳ[CK] ({A} ⟹ some A) := ⟨ProofGentzen.axm A⟩
lemma botL : ⊢ᴳ[CK] ({⊥} ⟹ Δ) := ⟨ProofGentzen.botL⟩
lemma wkL (π : ⊢ᴳ[CK] (Γ ⟹ Δ)) (h : Γ ⊆ Γ' := by grind) : ⊢ᴳ[CK] (Γ' ⟹ Δ) := ⟨ProofGentzen.wkL π.some h⟩
lemma wkR (π : ⊢ᴳ[CK] (Γ ⟹ none)) : ⊢ᴳ[CK] (Γ ⟹ some A) := ⟨ProofGentzen.wkR π.some⟩
lemma andL₁ (π : ⊢ᴳ[CK] (insert A Γ ⟹ Δ)) : ⊢ᴳ[CK] (insert (A ⋏ B) Γ ⟹ Δ) := ⟨ProofGentzen.andL₁ π.some⟩
lemma andL₂ (π : ⊢ᴳ[CK] (insert B Γ ⟹ Δ)) : ⊢ᴳ[CK] (insert (A ⋏ B) Γ ⟹ Δ) := ⟨ProofGentzen.andL₂ π.some⟩
lemma andR (π₁ : ⊢ᴳ[CK] (Γ ⟹ some A)) (π₂ : ⊢ᴳ[CK] (Γ ⟹ some B)) : ⊢ᴳ[CK] (Γ ⟹ some (A ⋏ B)) :=
  ⟨ProofGentzen.andR π₁.some π₂.some⟩
lemma orL (π₁ : ⊢ᴳ[CK] (insert A Γ ⟹ Δ)) (π₂ : ⊢ᴳ[CK] (insert B Γ ⟹ Δ)) : ⊢ᴳ[CK] (insert (A ⋎ B) Γ ⟹ Δ) :=
  ⟨ProofGentzen.orL π₁.some π₂.some⟩
lemma orR₁ (π : ⊢ᴳ[CK] (Γ ⟹ some A)) : ⊢ᴳ[CK] (Γ ⟹ some (A ⋎ B)) := ⟨ProofGentzen.orR₁ π.some⟩
lemma orR₂ (π : ⊢ᴳ[CK] (Γ ⟹ some B)) : ⊢ᴳ[CK] (Γ ⟹ some (A ⋎ B)) := ⟨ProofGentzen.orR₂ π.some⟩
lemma impL (π₁ : ⊢ᴳ[CK] (Γ ⟹ some A)) (π₂ : ⊢ᴳ[CK] (insert B Γ ⟹ Δ)) : ⊢ᴳ[CK] (insert (A 🡒 B) Γ ⟹ Δ) :=
  ⟨ProofGentzen.impL π₁.some π₂.some⟩
lemma impR (π : ⊢ᴳ[CK] (insert A Γ ⟹ some B)) : ⊢ᴳ[CK] (Γ ⟹ some (A 🡒 B)) := ⟨ProofGentzen.impR π.some⟩
lemma box (π : ⊢ᴳ[CK] (Γ ⟹ some A)) : ⊢ᴳ[CK] (□Γ ⟹ some (□A)) := ⟨ProofGentzen.box π.some⟩
lemma dia (π : ⊢ᴳ[CK] (insert A Γ ⟹ some B)) : ⊢ᴳ[CK] (insert (◇A) (□Γ) ⟹ some (◇B)) := ⟨ProofGentzen.dia π.some⟩

lemma union (A) (hΓ : A ∈ Γ := by grind) : ⊢ᴳ[CK] (Γ ⟹ some A) := ⟨ProofGentzen.union A hΓ⟩
@[grind =>] lemma botL_mem (h : ⊥ ∈ Γ := by grind) : ⊢ᴳ[CK] (Γ ⟹ Δ) := ⟨ProofGentzen.botL_mem h⟩
lemma andL (π : ⊢ᴳ[CK] (insert A (insert B Γ) ⟹ Δ)) : ⊢ᴳ[CK] (insert (A ⋏ B) Γ ⟹ Δ) := ⟨ProofGentzen.andL π.some⟩
lemma verum : ⊢ᴳ[CK] (Γ ⟹ some ⊤) := ⟨ProofGentzen.verum⟩

@[induction_eliminator]
lemma rec
  {motive : (S : Sequent) → ⊢ᴳ[CK] S → Prop}
  (axm : ∀ A, motive ({A} ⟹ some A) (ProvableGentzen.axm A))
  (botL : ∀ {Δ}, motive ({⊥} ⟹ Δ) ProvableGentzen.botL)
  (wkL : ∀ {Γ Γ' Δ} (h : ⊢ᴳ[CK] (Γ ⟹ Δ)) (h' : Γ ⊆ Γ'), motive (Γ ⟹ Δ) h → motive (Γ' ⟹ Δ) (wkL h h'))
  (wkR : ∀ {Γ A} (h : ⊢ᴳ[CK] (Γ ⟹ none)), motive (Γ ⟹ none) h → motive (Γ ⟹ some A) (wkR h))
  (andL₁ : ∀ {Γ Δ A B} (h : ⊢ᴳ[CK] (insert A Γ ⟹ Δ)),
    motive (insert A Γ ⟹ Δ) h → motive (insert (A ⋏ B) Γ ⟹ Δ) (andL₁ h)
  )
  (andL₂ : ∀ {Γ Δ A B} (h : ⊢ᴳ[CK] (insert B Γ ⟹ Δ)),
    motive (insert B Γ ⟹ Δ) h → motive (insert (A ⋏ B) Γ ⟹ Δ) (andL₂ h)
  )
  (andR : ∀ {Γ A B} (h₁ : ⊢ᴳ[CK] (Γ ⟹ some A)) (h₂ : ⊢ᴳ[CK] (Γ ⟹ some B)),
    motive (Γ ⟹ some A) h₁ → motive (Γ ⟹ some B) h₂ → motive (Γ ⟹ some (A ⋏ B)) (andR h₁ h₂)
  )
  (orL : ∀ {Γ Δ A B} (h₁ : ⊢ᴳ[CK] (insert A Γ ⟹ Δ)) (h₂ : ⊢ᴳ[CK] (insert B Γ ⟹ Δ)),
    motive (insert A Γ ⟹ Δ) h₁ → motive (insert B Γ ⟹ Δ) h₂ → motive (insert (A ⋎ B) Γ ⟹ Δ) (orL h₁ h₂)
  )
  (orR₁ : ∀ {Γ A B} (h : ⊢ᴳ[CK] (Γ ⟹ some A)), motive (Γ ⟹ some A) h → motive (Γ ⟹ some (A ⋎ B)) (orR₁ h))
  (orR₂ : ∀ {Γ A B} (h : ⊢ᴳ[CK] (Γ ⟹ some B)), motive (Γ ⟹ some B) h → motive (Γ ⟹ some (A ⋎ B)) (orR₂ h))
  (impL : ∀ {Γ Δ A B} (h₁ : ⊢ᴳ[CK] (Γ ⟹ some A)) (h₂ : ⊢ᴳ[CK] (insert B Γ ⟹ Δ)),
    motive (Γ ⟹ some A) h₁ → motive (insert B Γ ⟹ Δ) h₂ → motive (insert (A 🡒 B) Γ ⟹ Δ) (impL h₁ h₂)
  )
  (impR : ∀ {Γ A B} (h : ⊢ᴳ[CK] (insert A Γ ⟹ some B)),
    motive (insert A Γ ⟹ some B) h → motive (Γ ⟹ some (A 🡒 B)) (impR h)
  )
  (box : ∀ {Γ A} (h : ⊢ᴳ[CK] (Γ ⟹ some A)), motive (Γ ⟹ some A) h → motive (□Γ ⟹ some (□A)) (box h))
  (dia : ∀ {Γ A B} (h : ⊢ᴳ[CK] (insert A Γ ⟹ some B)),
    motive (insert A Γ ⟹ some B) h → motive (insert (◇A) (□Γ) ⟹ some (◇B)) (dia h)
  )
  : ∀ {S : Sequent} (h : ⊢ᴳ[CK] S), motive S h := by
    rintro S ⟨h⟩;
    induction h <;> grind;

lemma iff_unprovableGentzen_isEmpty_ProofGentzen {S : Sequent} : (⊬ᴳ[CK] S) ↔ (IsEmpty (⊢ᴳ[CK]! S)) := by
  simp [ProvableGentzen];

end ProvableGentzen

end LogicCK

end
