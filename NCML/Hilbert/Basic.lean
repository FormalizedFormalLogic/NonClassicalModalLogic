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

variable {𝔸 : Set BDFormula} {A B C : BDFormula}

/-- Local shorthand for `ProvableBDHilbert`, kept out of the exported API. -/
local notation:50 𝔸:51 " ⊢ " A:51 => ProvableBDHilbert 𝔸 A

lemma axm (h : A ∈ 𝔸) : 𝔸 ⊢ A := ⟨ProofBDHilbert.axm h⟩
@[simp, grind .] lemma imply₁ : 𝔸 ⊢ A 🡒 B 🡒 A := ⟨ProofBDHilbert.imply₁⟩
@[simp, grind .] lemma imply₂ : 𝔸 ⊢ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 A 🡒 C := ⟨ProofBDHilbert.imply₂⟩
@[simp, grind .] lemma andElim₁ : 𝔸 ⊢ A ⋏ B 🡒 A := ⟨ProofBDHilbert.andElim₁⟩
@[simp, grind .] lemma andElim₂ : 𝔸 ⊢ A ⋏ B 🡒 B := ⟨ProofBDHilbert.andElim₂⟩
@[simp, grind .] lemma andIntro : 𝔸 ⊢ A 🡒 B 🡒 A ⋏ B := ⟨ProofBDHilbert.andIntro⟩
@[simp, grind .] lemma orIntro₁ : 𝔸 ⊢ A 🡒 A ⋎ B := ⟨ProofBDHilbert.orIntro₁⟩
@[simp, grind .] lemma orIntro₂ : 𝔸 ⊢ B 🡒 A ⋎ B := ⟨ProofBDHilbert.orIntro₂⟩
@[simp, grind .] lemma orElim : 𝔸 ⊢ (A 🡒 C) 🡒 (B 🡒 C) 🡒 (A ⋎ B 🡒 C) := ⟨ProofBDHilbert.orElim⟩
@[simp, grind .] lemma efq : 𝔸 ⊢ ⊥ 🡒 A := ⟨ProofBDHilbert.efq⟩
@[simp, grind .] lemma kBox : 𝔸 ⊢ □(A 🡒 B) 🡒 □A 🡒 □B := ⟨ProofBDHilbert.kBox⟩
@[simp, grind .] lemma kDia : 𝔸 ⊢ □(A 🡒 B) 🡒 ◇A 🡒 ◇B := ⟨ProofBDHilbert.kDia⟩

@[grind =>] lemma mp : (𝔸 ⊢ A 🡒 B) → (𝔸 ⊢ A) → (𝔸 ⊢ B) :=
  fun ⟨h₁⟩ ⟨h₂⟩ => ⟨ProofBDHilbert.mp h₁ h₂⟩

@[grind <=] lemma nec : (𝔸 ⊢ A) → (𝔸 ⊢ □A) :=
  fun ⟨h⟩ => ⟨ProofBDHilbert.nec h⟩

lemma imp_trans (h₁ : 𝔸 ⊢ A 🡒 B) (h₂ : 𝔸 ⊢ B 🡒 C) : 𝔸 ⊢ A 🡒 C :=
  mp (mp imply₂ (mp imply₁ h₂)) h₁

/-- Custom eliminator for `ProvableBDHilbert`, letting `induction` work directly on a
`ProvableBDHilbert`-typed hypothesis without first destructuring the underlying `Nonempty`. -/
@[induction_eliminator]
lemma rec
    {motive : (A : BDFormula) → (𝔸 ⊢ A) → Prop}
    (axm       : ∀ {A} (h : A ∈ 𝔸), motive A (axm h))
    (imply₁    : ∀ {A B} (h : 𝔸 ⊢ A 🡒 B 🡒 A), motive _ h)
    (imply₂    : ∀ {A B C} (h : 𝔸 ⊢ (A 🡒 B 🡒 C) 🡒 (A 🡒 B) 🡒 A 🡒 C), motive _ h)
    (andElim₁  : ∀ {A B} (h : 𝔸 ⊢ A ⋏ B 🡒 A), motive _ h)
    (andElim₂  : ∀ {A B} (h : 𝔸 ⊢ A ⋏ B 🡒 B), motive _ h)
    (andIntro  : ∀ {A B} (h : 𝔸 ⊢ A 🡒 B 🡒 A ⋏ B), motive _ h)
    (orIntro₁  : ∀ {A B} (h : 𝔸 ⊢ A 🡒 A ⋎ B), motive _ h)
    (orIntro₂  : ∀ {A B} (h : 𝔸 ⊢ B 🡒 A ⋎ B), motive _ h)
    (orElim    : ∀ {A B C} (h : 𝔸 ⊢ (A 🡒 C) 🡒 (B 🡒 C) 🡒 (A ⋎ B 🡒 C)), motive _ h)
    (efq       : ∀ {A} (h : 𝔸 ⊢ ⊥ 🡒 A), motive _ h)
    (kBox      : ∀ {A B} (h : 𝔸 ⊢ □(A 🡒 B) 🡒 □A 🡒 □B), motive _ h)
    (kDia      : ∀ {A B} (h : 𝔸 ⊢ □(A 🡒 B) 🡒 ◇A 🡒 ◇B), motive _ h)
    (mp        : ∀ {A B} (h₁ : 𝔸 ⊢ A 🡒 B) (h₂ : 𝔸 ⊢ A), motive _ h₁ → motive _ h₂ → motive _ (mp h₁ h₂))
    (nec       : ∀ {A} (h : 𝔸 ⊢ A), motive A h → motive _ (nec h)) :
    ∀ {A} (h : 𝔸 ⊢ A), motive _ h := by
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

theorem monotone {𝔸 𝔸₁ : Set BDFormula} (h : 𝔸 ⊆ 𝔸₁) {A} : (𝔸 ⊢ A) → (𝔸₁ ⊢ A) := by
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

abbrev logic (𝔸 : Set BDFormula) : BDLogic := {A | 𝔸 ⊢ A}

@[simp] lemma mem_logic {𝔸 : Set BDFormula} {A} : A ∈ logic 𝔸 ↔ 𝔸 ⊢ A := Iff.rfl

theorem logic_monotone {𝔸 𝔸₁ : Set BDFormula} (h : 𝔸 ⊆ 𝔸₁) : logic 𝔸 ⊆ logic 𝔸₁ :=
  fun _ => monotone h

end ProvableBDHilbert

end
