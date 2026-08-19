module

public import NCML.Formula
public import Mathlib.Tactic

@[expose] public section

open NCML BDFormula

inductive ProofBDHilbert (𝔸 : Set BDFormula) : BDFormula → Type
  | axm       {A}     : A ∈ 𝔸 → ProofBDHilbert 𝔸 A
  | imply₁    {A B}   : ProofBDHilbert 𝔸 (A 🡒 B 🡒 A)
  | imply₂    {A B C} : ProofBDHilbert 𝔸 ((A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 A 🡒 C)
  | andElim₁  {A B}   : ProofBDHilbert 𝔸 (A ⋏ B 🡒 A)
  | andElim₂  {A B}   : ProofBDHilbert 𝔸 (A ⋏ B 🡒 B)
  | andIntro  {A B}   : ProofBDHilbert 𝔸 (A 🡒 B 🡒 A ⋏ B)
  | orIntro₁  {A B}   : ProofBDHilbert 𝔸 (A 🡒 A ⋎ B)
  | orIntro₂  {A B}   : ProofBDHilbert 𝔸 (B 🡒 A ⋎ B)
  | orElim    {A B C} : ProofBDHilbert 𝔸 ((A 🡒 C) 🡒 (B 🡒 C) 🡒 (A ⋎ B 🡒 C))
  | efq       {A}     : ProofBDHilbert 𝔸 (⊥ 🡒 A)
  | kBox      {A B}   : ProofBDHilbert 𝔸 (□(A 🡒 B) 🡒 □A 🡒 □B)
  | kDia      {A B}   : ProofBDHilbert 𝔸 (□(A 🡒 B) 🡒 ◇A 🡒 ◇B)
  | mp        {A B}   : ProofBDHilbert 𝔸 (A 🡒 B) → ProofBDHilbert 𝔸 A → ProofBDHilbert 𝔸 B
  | nec       {A}     : ProofBDHilbert 𝔸 A → ProofBDHilbert 𝔸 (□A)

abbrev ProvableBDHilbert (𝔸 : Set BDFormula) (A : BDFormula) := Nonempty (ProofBDHilbert 𝔸 A)

namespace ProvableBDHilbert

variable {𝔸 𝔸₁ 𝔸₂ : Set BDFormula} {A B C D : BDFormula} {Γ Γ₁ Γ₂ : BDFormulaList}

notation:50 "⊢ᴴ[CK;" 𝔸 "] " A:51 => ProvableBDHilbert 𝔸 A

lemma axm (h : A ∈ 𝔸) : ⊢ᴴ[CK;𝔸] A := ⟨ProofBDHilbert.axm h⟩
@[simp, grind .] lemma imply₁ : ⊢ᴴ[CK;𝔸] A 🡒 B 🡒 A := ⟨ProofBDHilbert.imply₁⟩
@[simp, grind .] lemma imply₂ : ⊢ᴴ[CK;𝔸] (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 A 🡒 C := ⟨ProofBDHilbert.imply₂⟩
@[simp, grind .] lemma andElim₁ : ⊢ᴴ[CK;𝔸] A ⋏ B 🡒 A := ⟨ProofBDHilbert.andElim₁⟩
@[simp, grind .] lemma andElim₂ : ⊢ᴴ[CK;𝔸] A ⋏ B 🡒 B := ⟨ProofBDHilbert.andElim₂⟩
@[simp, grind .] lemma andIntro : ⊢ᴴ[CK;𝔸] A 🡒 B 🡒 A ⋏ B := ⟨ProofBDHilbert.andIntro⟩
@[simp, grind .] lemma orIntro₁ : ⊢ᴴ[CK;𝔸] A 🡒 A ⋎ B := ⟨ProofBDHilbert.orIntro₁⟩
@[simp, grind .] lemma orIntro₂ : ⊢ᴴ[CK;𝔸] B 🡒 A ⋎ B := ⟨ProofBDHilbert.orIntro₂⟩
@[simp, grind .] lemma orElim : ⊢ᴴ[CK;𝔸] (A 🡒 C) 🡒 (B 🡒 C) 🡒 (A ⋎ B 🡒 C) := ⟨ProofBDHilbert.orElim⟩
@[simp, grind .] lemma efq : ⊢ᴴ[CK;𝔸] ⊥ 🡒 A := ⟨ProofBDHilbert.efq⟩
@[simp, grind .] lemma kBox : ⊢ᴴ[CK;𝔸] □(A 🡒 B) 🡒 □A 🡒 □B := ⟨ProofBDHilbert.kBox⟩
@[simp, grind .] lemma kDia : ⊢ᴴ[CK;𝔸] □(A 🡒 B) 🡒 ◇A 🡒 ◇B := ⟨ProofBDHilbert.kDia⟩

@[grind =>]
lemma mp : (⊢ᴴ[CK;𝔸] A 🡒 B) → (⊢ᴴ[CK;𝔸] A) → (⊢ᴴ[CK;𝔸] B) :=
  fun ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofBDHilbert.mp h₁ h₂⟩

@[grind <=]
lemma nec : (⊢ᴴ[CK;𝔸] A) → (⊢ᴴ[CK;𝔸] □A) :=
  fun ⟨h⟩ => ⟨ProofBDHilbert.nec h⟩

lemma imp_trans (h₁ : ⊢ᴴ[CK;𝔸] A 🡒 B) (h₂ : ⊢ᴴ[CK;𝔸] B 🡒 C) : ⊢ᴴ[CK;𝔸] A 🡒 C :=
  mp (mp imply₂ (mp imply₁ h₂)) h₁

@[grind .] lemma imp_id : ⊢ᴴ[CK;𝔸] A 🡒 A := mp (mp imply₂ (imply₁ (B := A 🡒 A))) (imply₁ (B := A))

@[grind .] lemma verum : ⊢ᴴ[CK;𝔸] ⊤ := imp_id

lemma dhyp (h : ⊢ᴴ[CK;𝔸] B) : ⊢ᴴ[CK;𝔸] A 🡒 B := mp imply₁ h

lemma mp_ctx (h₁ : ⊢ᴴ[CK;𝔸] A 🡒 B 🡒 C) (h₂ : ⊢ᴴ[CK;𝔸] A 🡒 B) : ⊢ᴴ[CK;𝔸] A 🡒 C :=
  mp (mp imply₂ h₁) h₂

lemma mp_ctx₂ (h₁ : ⊢ᴴ[CK;𝔸] A 🡒 B 🡒 C 🡒 D) (h₂ : ⊢ᴴ[CK;𝔸] A 🡒 B 🡒 C) : ⊢ᴴ[CK;𝔸] A 🡒 B 🡒 D :=
  mp_ctx (imp_trans h₁ imply₂) h₂

lemma imp_comp_left (h : ⊢ᴴ[CK;𝔸] B 🡒 C) : ⊢ᴴ[CK;𝔸] (A 🡒 B) 🡒 (A 🡒 C) := mp imply₂ (dhyp h)

lemma imp_comp_right (h : ⊢ᴴ[CK;𝔸] A 🡒 B) : ⊢ᴴ[CK;𝔸] (B 🡒 C) 🡒 (A 🡒 C) :=
  mp_ctx (imp_trans imply₁ imply₂) (dhyp h)

lemma and_intro_ctx (h₁ : ⊢ᴴ[CK;𝔸] A 🡒 B) (h₂ : ⊢ᴴ[CK;𝔸] A 🡒 C) : ⊢ᴴ[CK;𝔸] A 🡒 B ⋏ C :=
  mp_ctx (imp_trans h₁ andIntro) h₂

lemma box_mono (h : ⊢ᴴ[CK;𝔸] A 🡒 B) : ⊢ᴴ[CK;𝔸] □A 🡒 □B := mp kBox (nec h)

@[grind .] lemma box_or_inl : ⊢ᴴ[CK;𝔸] □A 🡒 □(A ⋎ B) := box_mono orIntro₁

@[grind .] lemma box_or_inr : ⊢ᴴ[CK;𝔸] □B 🡒 □(A ⋎ B) := box_mono orIntro₂

@[grind .] lemma box_and_intro : ⊢ᴴ[CK;𝔸] □A 🡒 □B 🡒 □(A ⋏ B) := imp_trans (mp kBox (nec andIntro)) kBox

@[grind .]
lemma imp_bot_imp_box_bot : ⊢ᴴ[CK;𝔸] (A 🡒 ⊥) 🡒 (A 🡒 □⊥) := imp_comp_left (efq (A := □⊥))

open scoped BDFormulaList

lemma conj_append_left : ⊢ᴴ[CK;𝔸] ⋀(Γ₁ ++ Γ₂) 🡒 ⋀Γ₁ := by
  induction Γ₁ with
  | nil => exact dhyp verum;
  | cons A Γ₁ ih => exact and_intro_ctx andElim₁ (imp_trans andElim₂ ih);

lemma conj_append_right : ⊢ᴴ[CK;𝔸] ⋀(Γ₁ ++ Γ₂) 🡒 ⋀Γ₂ := by
  induction Γ₁ with
  | nil => exact imp_id;
  | cons A Γ₁ ih => exact imp_trans andElim₂ ih;

lemma conj_box : ⊢ᴴ[CK;𝔸] ⋀□Γ 🡒 □⋀Γ := by
  induction Γ with
  | nil => exact dhyp (nec verum);
  | cons A Γ ih => exact mp_ctx (imp_trans andElim₁ box_and_intro) (imp_trans andElim₂ ih);

@[induction_eliminator]
lemma rec
    {motive : (A : BDFormula) → (⊢ᴴ[CK;𝔸] A) → Prop}
    (axm       : ∀ {A} (h : A ∈ 𝔸), motive A (axm h))
    (imply₁    : ∀ {A B} (h : ⊢ᴴ[CK;𝔸] A 🡒 B 🡒 A), motive _ h)
    (imply₂    : ∀ {A B C} (h : ⊢ᴴ[CK;𝔸] (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 A 🡒 C), motive _ h)
    (andElim₁  : ∀ {A B} (h : ⊢ᴴ[CK;𝔸] A ⋏ B 🡒 A), motive _ h)
    (andElim₂  : ∀ {A B} (h : ⊢ᴴ[CK;𝔸] A ⋏ B 🡒 B), motive _ h)
    (andIntro  : ∀ {A B} (h : ⊢ᴴ[CK;𝔸] A 🡒 B 🡒 A ⋏ B), motive _ h)
    (orIntro₁  : ∀ {A B} (h : ⊢ᴴ[CK;𝔸] A 🡒 A ⋎ B), motive _ h)
    (orIntro₂  : ∀ {A B} (h : ⊢ᴴ[CK;𝔸] B 🡒 A ⋎ B), motive _ h)
    (orElim    : ∀ {A B C} (h : ⊢ᴴ[CK;𝔸] (A 🡒 C) 🡒 (B 🡒 C) 🡒 (A ⋎ B 🡒 C)), motive _ h)
    (efq       : ∀ {A} (h : ⊢ᴴ[CK;𝔸] ⊥ 🡒 A), motive _ h)
    (kBox      : ∀ {A B} (h : ⊢ᴴ[CK;𝔸] □(A 🡒 B) 🡒 □A 🡒 □B), motive _ h)
    (kDia      : ∀ {A B} (h : ⊢ᴴ[CK;𝔸] □(A 🡒 B) 🡒 ◇A 🡒 ◇B), motive _ h)
    (mp        : ∀ {A B} (h₁ : ⊢ᴴ[CK;𝔸] A 🡒 B) (h₂ : ⊢ᴴ[CK;𝔸] A), motive _ h₁ → motive _ h₂ → motive _ (mp h₁ h₂))
    (nec       : ∀ {A} (h : ⊢ᴴ[CK;𝔸] A), motive A h → motive _ (nec h)) :
    ∀ {A} (h : ⊢ᴴ[CK;𝔸] A), motive _ h := by
  rintro A ⟨h⟩;
  induction h with
  | axm hmem => exact axm hmem;
  | imply₁ => exact imply₁ _;
  | imply₂ => exact imply₂ _;
  | andElim₁ => exact andElim₁ _;
  | andElim₂ => exact andElim₂ _;
  | andIntro => exact andIntro _;
  | orIntro₁ => exact orIntro₁ _;
  | orIntro₂ => exact orIntro₂ _;
  | orElim => exact orElim _;
  | efq => exact efq _;
  | kBox => exact kBox _;
  | kDia => exact kDia _;
  | mp h₁ h₂ ih₁ ih₂ => exact mp ⟨h₁⟩ ⟨h₂⟩ ih₁ ih₂;
  | nec h ih => exact nec ⟨h⟩ ih;

theorem monotone (h : 𝔸₁ ⊆ 𝔸₂) : ⊢ᴴ[CK;𝔸₁] A → ⊢ᴴ[CK;𝔸₂] A := by
  intro p;
  induction p with
  | axm hmem   => exact axm (h hmem);
  | imply₁     => exact imply₁;
  | imply₂     => exact imply₂;
  | andElim₁   => exact andElim₁;
  | andElim₂   => exact andElim₂;
  | andIntro   => exact andIntro;
  | orIntro₁   => exact orIntro₁;
  | orIntro₂   => exact orIntro₂;
  | orElim     => exact orElim;
  | efq        => exact efq;
  | kBox       => exact kBox;
  | kDia       => exact kDia;
  | mp _ _ ih₁ ih₂ => exact mp ih₁ ih₂;
  | nec _ ih   => exact nec ih;

abbrev logic (𝔸 : Set BDFormula) : BDLogic := { A | ⊢ᴴ[CK;𝔸] A }

@[simp]
lemma mem_logic : A ∈ logic 𝔸 ↔ ⊢ᴴ[CK;𝔸] A := Iff.rfl

theorem logic_monotone (h : 𝔸₁ ⊆ 𝔸₂) : logic 𝔸₁ ⊆ logic 𝔸₂ := fun _ => monotone h

end ProvableBDHilbert

end
