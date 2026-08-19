module

public import NCML.CK.Confluence
public import NCML.Hilbert.Logics
public import NCML.Hilbert.Theory
public import Mathlib.Data.SetLike.Basic

@[expose] public section

/-!
# Canonical model for `CKB`

- [Pac24, Section 3.2]
-/

namespace CK

open NCML BDFormula

/-- A CKB-theory: a set of formulas that contains every theorem of `CKB`, is closed under `MP`,
is prime, and is consistent.

- [Pac24, Section 3.2]
-/
structure CKBTheory where
  carrier : BDFormulaSet
  logicCKB_subset : LogicCKB ⊆ carrier
  mdp : ∀ {A B}, A 🡒 B ∈ carrier → A ∈ carrier → B ∈ carrier
  prime : ∀ {A B}, A ⋎ B ∈ carrier → A ∈ carrier ∨ B ∈ carrier
  consistent : ⊥ ∉ carrier

namespace CKBTheory

instance : SetLike CKBTheory BDFormula where
  coe Γ := Γ.carrier
  coe_injective p q h := by cases p; cases q; congr;

@[simp] lemma mem_carrier {Γ : CKBTheory} {A} : A ∈ Γ.carrier ↔ A ∈ Γ := Iff.rfl

@[ext] theorem ext {Γ Δ : CKBTheory} (h : ∀ A, A ∈ Γ ↔ A ∈ Δ) : Γ = Δ := SetLike.ext h

/-- Lindenbaum lemma for CKB-theories: an MP-closed set of formulas that contains every theorem of
`CKB` and misses `A` extends to a CKB-theory still missing `A`.

Pac24 does not isolate this statement: it is the Zorn step run inline in the implication case of
Lemma 19, and again in Lemma 20.

- [Pac24, Lemma 19, Lemma 20]
-/
lemma exists_extending {X : BDFormulaSet} {A : BDFormula}
  (hlog : LogicCKB ⊆ X) (hmp : X.MpClosed) (hA : A ∉ X) :
  ∃ Γ : CKBTheory, X ⊆ Γ.carrier ∧ A ∉ Γ.carrier := by
  obtain ⟨Y, hXY, hmax⟩ :=
    exists_maximal_mpClosed_avoiding (Z := {A}) hmp (by rintro B rfl; exact hA);
  obtain ⟨-, hmpY, havoid⟩ := hmax.prop;
  have hAY : A ∉ Y := havoid A rfl;
  have hlogY : LogicCKB ⊆ Y := hlog.trans hXY;
  have h₁ : ∀ {B}, B ∉ Y → (B 🡒 A) ∈ Y := by
    intro B hB;
    obtain ⟨C, hC, h⟩ := exists_imp_mem_of_maximal hlog hmax hB;
    exact Set.mem_singleton_iff.mp hC ▸ h;
  have h₂ : ∀ {B C}, B ⋎ C ∈ Y → B ∈ Y ∨ C ∈ Y := by
    intro B C hBC;
    by_contra hc;
    exact hAY <| BDFormulaSet.or_elim_mem hlogY hmpY (h₁ fun h => hc (Or.inl h))
      (h₁ fun h => hc (Or.inr h)) hBC;
  have h₃ : ⊥ ∉ Y := fun h =>
    hAY <| hmpY (BDFormulaSet.provable_mem hlogY ProvableBDHilbert.efq) h;
  exact ⟨⟨Y, hlogY, hmpY, h₂, h₃⟩, hXY, hAY⟩;

end CKBTheory

/-- - [Pac24, Section 3.2] -/
def canonicalModel : Model CKBTheory where
  iRel' Γ Δ := Γ.carrier ⊆ Δ.carrier
  mRel' Γ Δ := Γ.carrier.prebox ⊆ Δ.carrier ∧ Δ.carrier ⊆ Γ.carrier.predia
  Fallible' _ := False
  fallible_iRel' h _ := h.elim
  fallible_mRel' h _ := h.elim
  fallible_exists_mRel' h := h.elim
  val Γ a := (#a) ∈ Γ.carrier
  val_persistent h IΓΔ := IΓΔ h
  fallible_val h := h.elim

/-- - [Pac24, Lemma 15] -/
instance : canonicalModel.SymmetricMRel where
  symm_mRel {Γ Δ} := by
    rintro ⟨h₁, h₂⟩;
    constructor;
    · intro A hA;
      have h₃ : (◇(□A) 🡒 A) ∈ LogicCKB := ProvableBDHilbert.axm (Or.inr ⟨A, rfl⟩);
      exact Γ.mdp (Γ.logicCKB_subset h₃) (h₂ hA);
    · intro A hA;
      have h₃ : (A 🡒 □◇A) ∈ LogicCKB := ProvableBDHilbert.axm (Or.inl ⟨A, rfl⟩);
      exact h₁ (Γ.mdp (Γ.logicCKB_subset h₃) hA);

section BackwardConfluence

variable {X Y : BDFormulaSet} {Δ : CKBTheory} {A B : BDFormula}

/-- The formulas a theory `Γ` with `Γ ⊏ Δ` must avoid: `⊥`, because `Γ` is consistent, and `□C`
for every `C ∉ Δ`, because `Γ.carrier.prebox ⊆ Δ.carrier`. -/
private abbrev CKBTheory.forbidden (Δ : CKBTheory) : BDFormulaSet :=
  {⊥} ∪ (□·) '' {C | C ∉ Δ.carrier}

/-- Avoiding `Δ.forbidden` is what makes a set a candidate `mRel`-predecessor of `Δ`. -/
private lemma prebox_subset_of_avoid (h : ∀ B ∈ Δ.forbidden, B ∉ X) : X.prebox ⊆ Δ.carrier := by
  intro C hC;
  by_contra hc;
  exact h (□C) (Or.inr ⟨C, hc, rfl⟩) hC;

/-- A formula missing from a maximal set avoiding `Δ.forbidden` implies a boxed formula missing
from `Δ`. The `⊥` branch of the dichotomy is normalized into this shape through `⊢ ⊥ 🡒 □⊥`. -/
private lemma exists_box_imp_mem (hlog : LogicCKB ⊆ X)
  (hmax : Maximal (fun Y => X ⊆ Y ∧ Y.MpClosed ∧ ∀ B ∈ Δ.forbidden, B ∉ Y) Y) (hA : A ∉ Y) :
  ∃ C ∉ Δ.carrier, (A 🡒 □C) ∈ Y := by
  obtain ⟨hXY, hmpY, -⟩ := hmax.prop;
  obtain ⟨C, hC, h⟩ := exists_imp_mem_of_maximal hlog hmax hA;
  rcases hC with rfl | ⟨C, hC, rfl⟩;
  · exact ⟨⊥, Δ.consistent, hmpY (BDFormulaSet.provable_mem (hlog.trans hXY)
      ProvableBDHilbert.imp_bot_imp_box_bot) h⟩;
  · exact ⟨C, hC, h⟩;

/-- A maximal MP-closed set avoiding `Δ.forbidden` is prime.

The cited proof of this step argues classically, deriving `∼A ∈ Y` from `A ∉ Y`, which is not
available intuitionistically. The argument used here instead pulls the primeness of `Δ` back
through `□`: a disjunct missing from `Y` implies some `□C` with `C ∉ Δ`, and `□(C ⋎ D) ∈ Y` then
forces `C ⋎ D ∈ Δ`.

- [Pac24, Lemma 16] -/
private lemma prime_of_maximal (hlog : LogicCKB ⊆ X)
  (hmax : Maximal (fun Y => X ⊆ Y ∧ Y.MpClosed ∧ ∀ B ∈ Δ.forbidden, B ∉ Y) Y)
  (h : A ⋎ B ∈ Y) : A ∈ Y ∨ B ∈ Y := by
  by_contra hc;
  obtain ⟨hXY, hmpY, havoid⟩ := hmax.prop;
  obtain ⟨C, hC, h₁⟩ := exists_box_imp_mem hlog hmax fun hA => hc (Or.inl hA);
  obtain ⟨D, hD, h₂⟩ := exists_box_imp_mem hlog hmax fun hB => hc (Or.inr hB);
  have h₃ : C ⋎ D ∈ Δ.carrier :=
    prebox_subset_of_avoid havoid (BDFormulaSet.box_or_mem (hlog.trans hXY) hmpY h₁ h₂ h);
  exact (Δ.prime h₃).elim hC hD;

end BackwardConfluence

/-- The predecessor of `Δ₁` is a maximal MP-closed extension of the MP-closure of
`Γ.carrier ∪ ◇''Δ₁.carrier` avoiding `Δ₁.forbidden`. The hypothesis `Δ.carrier ⊆ Γ.carrier.predia`
is not needed, matching the cited proof.

Two corrections to that proof. Its Zorn poset does not require its members to be closed under
modus ponens, and without that requirement the complement of the forbidden set is a maximum
element of the poset which is not a theory; the poset used here carries MP-closedness. And its
primeness argument does not go through as written, being classical; `prime_of_maximal` replaces
it.

- [Pac24, Lemma 16] -/
instance : canonicalModel.BackwardConfluent where
  backward_confluent {Γ Δ Δ₁} := by
    rintro ⟨MΓΔ, -⟩ IΔΔ₁;
    have hdia : ∀ B ∈ Γ.carrier, ◇B ∈ Δ₁.carrier := fun B hB =>
      IΔΔ₁ (MΓΔ (BDFormulaSet.box_dia_mem Γ.logicCKB_subset Γ.mdp hB));
    have hlog : LogicCKB ⊆ (show BDFormulaSet from MPClosure (Γ.carrier ∪ (◇·) '' Δ₁.carrier)) :=
      logic_subset_mpClosure (Γ.logicCKB_subset.trans Set.subset_union_left);
    have havoid : ∀ B ∈ Δ₁.forbidden,
        B ∉ (show BDFormulaSet from MPClosure (Γ.carrier ∪ (◇·) '' Δ₁.carrier)) := by
      rintro B (rfl | ⟨C, hC, rfl⟩) hB;
      · exact bot_not_mem_mpClosure Γ.logicCKB_subset Γ.mdp Δ₁.logicCKB_subset Δ₁.mdp hdia
          Δ₁.consistent hB;
      · exact hC (mem_of_box_mem_mpClosure Γ.logicCKB_subset Γ.mdp Δ₁.logicCKB_subset Δ₁.mdp
          hdia hB);
    obtain ⟨Y, hsub, hmax⟩ := exists_maximal_mpClosed_avoiding (MPClosure.mpClosed _) havoid;
    obtain ⟨-, hmpY, havoidY⟩ := hmax.prop;
    exact ⟨⟨Y, hlog.trans hsub, hmpY, fun h => prime_of_maximal hlog hmax h,
        havoidY ⊥ (Or.inl rfl)⟩,
      fun B hB => hsub (MPClosure.base (Or.inl hB)), prebox_subset_of_avoid havoidY,
      fun B hB => hsub (MPClosure.base (Or.inr ⟨B, hB, rfl⟩))⟩;

instance : canonicalModel.ForwardConfluent :=
  Model.forwardConfluent_iff_backwardConfluent_of_symmetricMRel.mpr inferInstance

/-- - [Pac24, Lemma 17] -/
instance : canonicalModel.IsIKB where
  not_fallible _ h := h.elim

section TruthLemma

variable {Γ : CKBTheory} {A B : BDFormula}

/-- The implication case of the truth lemma, right-to-left.

- [Pac24, Lemma 19]
-/
private lemma forces_imply_of_mem
  (ihA : ∀ {Δ : CKBTheory}, Δ ⊩[canonicalModel] A ↔ A ∈ Δ.carrier)
  (ihB : ∀ {Δ : CKBTheory}, Δ ⊩[canonicalModel] B ↔ B ∈ Δ.carrier)
  (h : A 🡒 B ∈ Γ.carrier) : Γ ⊩[canonicalModel] (A 🡒 B) :=
  fun Δ IΓΔ hΔA => ihB.mpr (Δ.mdp (IΓΔ h) (ihA.mp hΔA))

/-- The implication case of the truth lemma, left-to-right. Contrapositively, a theory missing
`A 🡒 B` extends to one containing `A` and missing `B`, namely a Lindenbaum extension of
`Γ.carrier.impSet A`.

- [Pac24, Lemma 19]
-/
private lemma mem_of_forces_imply
  (ihA : ∀ {Δ : CKBTheory}, Δ ⊩[canonicalModel] A ↔ A ∈ Δ.carrier)
  (ihB : ∀ {Δ : CKBTheory}, Δ ⊩[canonicalModel] B ↔ B ∈ Δ.carrier)
  (h : Γ ⊩[canonicalModel] (A 🡒 B)) : A 🡒 B ∈ Γ.carrier := by
  by_contra hc;
  have hsub : Γ.carrier ⊆ Γ.carrier.impSet A :=
    BDFormulaSet.subset_impSet Γ.logicCKB_subset Γ.mdp;
  obtain ⟨Δ, hXΔ, hBΔ⟩ := CKBTheory.exists_extending (Γ.logicCKB_subset.trans hsub)
    (BDFormulaSet.impSet_mpClosed Γ.logicCKB_subset Γ.mdp) hc;
  exact hBΔ <| ihB.mp <| h Δ (hsub.trans hXΔ) <|
    ihA.mpr <| hXΔ <| BDFormulaSet.self_mem_impSet Γ.logicCKB_subset;

/-- Truth lemma for the canonical model: a CKB-theory forces exactly the formulas it contains.

- [Pac24, Lemma 19]
-/
theorem truth_lemma {Γ : CKBTheory} {A : BDFormula} : Γ ⊩[canonicalModel] A ↔ A ∈ Γ.carrier := by
  induction A generalizing Γ with
  | atom a => exact Iff.rfl;
  | falsum => exact ⟨False.elim, fun h => (Γ.consistent h).elim⟩;
  | and A B ihA ihB =>
    constructor;
    · rintro ⟨hA, hB⟩;
      exact BDFormulaSet.and_mem Γ.logicCKB_subset Γ.mdp (ihA.mp hA) (ihB.mp hB);
    · intro h;
      exact ⟨ihA.mpr (Γ.mdp (Γ.logicCKB_subset ProvableBDHilbert.andElim₁) h),
        ihB.mpr (Γ.mdp (Γ.logicCKB_subset ProvableBDHilbert.andElim₂) h)⟩;
  | or A B ihA ihB =>
    constructor;
    · rintro (hA | hB);
      · exact Γ.mdp (Γ.logicCKB_subset ProvableBDHilbert.orIntro₁) (ihA.mp hA);
      · exact Γ.mdp (Γ.logicCKB_subset ProvableBDHilbert.orIntro₂) (ihB.mp hB);
    · intro h;
      exact (Γ.prime h).imp ihA.mpr ihB.mpr;
  | imply A B ihA ihB => exact ⟨mem_of_forces_imply ihA ihB, forces_imply_of_mem ihA ihB⟩;
  -- The two open cases are the halves that must produce an `mRel`-successor of `Γ`, and each needs
  -- its own Zorn construction: the `□` case that of [Pac24, Lemma 18], the `◇` case one resting on
  -- the diamond principle.
  | box A ih => sorry
  | dia A ih =>
    constructor;
    · intro h;
      obtain ⟨Δ, MΓΔ, hΔA⟩ := h Γ Set.Subset.rfl;
      exact MΓΔ.2 (ih.mp hΔA);
    · sorry

end TruthLemma

end CK

end
