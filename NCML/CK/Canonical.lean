module

public import NCML.CK.Confluence
public import NCML.Hilbert.Logics
public import NCML.Hilbert.Theory

@[expose] public section

/-!
# Canonical model for `CKB`

The worlds are the `CKB`-theories (`NCML.CKBTheory`): sets of formulas containing every theorem of
`CKB`, closed under modus ponens, prime and consistent.

- [Pac24, Section 3.2]
-/

namespace CK

open NCML BDFormula
open scoped NCML.BDFormulaSet

namespace CKBTheory

instance (Γ : CKBTheory) : Γ.1.CKB := Γ.2

/-- Lindenbaum lemma for CKB-theories: an MP-closed set of formulas that contains every theorem of
`CKB` and misses `A` extends to a CKB-theory still missing `A`.

Pac24 does not isolate this statement: it is the Zorn step run inline in the implication case of
Lemma 19, and again in Lemma 20.

- [Pac24, Lemma 19, Lemma 20]
-/
lemma exists_extending {T : BDTheory} {A : BDFormula} [T.Of LogicCKB] [T.Mdp] (hA : A ∉ T) :
  ∃ Γ : CKBTheory, T ⊆ Γ.1 ∧ A ∉ Γ.1 := by
  obtain ⟨Y, hTY, hmax⟩ :=
    exists_maximal_mdpClosed_avoiding (Z := {A}) (by rintro B rfl; exact hA);
  -- `hmdpY` and `hlogY` are unused by name: they are what instance resolution picks up below.
  obtain ⟨-, hmdpY, havoid⟩ := hmax.prop;
  have hAY : A ∉ Y := havoid A rfl;
  have hlogY : Y.Of LogicCKB := ⟨(T.subset (L := LogicCKB)).trans hTY⟩;
  have h₁ : ∀ {B}, B ∉ Y → (B 🡒 A) ∈ Y := by
    intro B hB;
    obtain ⟨C, hC, h⟩ := exists_imp_mem_of_maximal (𝔸 := ∅) (T := T) hmax hB;
    exact Set.mem_singleton_iff.mp hC ▸ h;
  have h₂ : Y.Prime := by
    constructor;
    intro B C hBC;
    by_contra hc;
    exact hAY <| BDTheory.or_elim_mem (𝔸 := ∅) (h₁ fun h => hc (Or.inl h))
      (h₁ fun h => hc (Or.inr h)) hBC;
  have h₃ : Y.Consistent :=
    ⟨fun h => hAY <| Y.mdp (BDTheory.provable_mem (𝔸 := ∅) ProvableBDHilbert.efq) h⟩;
  have hckb : Y.CKB := ⟨⟩;
  exact ⟨⟨Y, hckb⟩, hTY, hAY⟩;

end CKBTheory

/-- - [Pac24, Section 3.2] -/
def canonicalModel : Model CKBTheory where
  iRel' Γ Δ := Γ.1 ⊆ Δ.1
  -- Supplied by hand: `CKBTheory` is a subtype, and no `IsPreorder` instance for `⊆` on it is
  -- found by unification with the `Preorder`-derived one.
  iRel_preorder := { refl := fun _ => subset_rfl, trans := fun _ _ _ h₁ h₂ => h₁.trans h₂ }
  mRel' Γ Δ := BDFormulaSet.prebox Γ.1 ⊆ Δ.1 ∧ Δ.1 ⊆ BDFormulaSet.predia Γ.1
  Fallible' _ := False
  fallible_iRel' h _ := h.elim
  fallible_mRel' h _ := h.elim
  fallible_exists_mRel' h := h.elim
  val Γ a := (#a) ∈ Γ.1
  val_persistent h IΓΔ := IΓΔ h
  fallible_val h := h.elim

/-- - [Pac24, Lemma 15] -/
instance : canonicalModel.SymmetricMRel where
  symm_mRel {Γ Δ} := by
    rintro ⟨h₁, h₂⟩;
    constructor;
    · intro A hA;
      exact BDTheory.mem_of_dia_box_mem (T := Γ.1) (h₂ hA);
    · intro A hA;
      exact h₁ (BDTheory.box_dia_mem (T := Γ.1) hA);

section BackwardConfluence

variable {T Y : BDTheory} {Δ : CKBTheory} {A B : BDFormula}

/-- The formulas a theory `Γ` with `Γ ⊏ Δ` must avoid: `⊥`, because `Γ` is consistent, and `□C`
for every `C ∉ Δ`, because `Γ.1.prebox ⊆ Δ.1`. -/
private abbrev CKBTheory.forbidden (Δ : CKBTheory) : BDTheory := {⊥} ∪ □{C | C ∉ Δ.1}

/-- Avoiding `Δ.forbidden` is what makes a set a candidate `mRel`-predecessor of `Δ`. -/
private lemma prebox_subset_of_avoid (h : ∀ B ∈ CKBTheory.forbidden Δ, B ∉ T) :
  BDFormulaSet.prebox T ⊆ Δ.1 := by
  intro C hC;
  by_contra hc;
  exact h (□C) (Or.inr ⟨C, hc, rfl⟩) hC;

/-- A formula missing from a maximal set avoiding `Δ.forbidden` implies a boxed formula missing
from `Δ`. The `⊥` branch of the dichotomy is normalized into this shape through `⊢ ⊥ 🡒 □⊥`. -/
private lemma exists_box_imp_mem [T.Of LogicCKB]
  (hmax : Maximal (fun Y : BDTheory => T ⊆ Y ∧ Y.Mdp ∧ ∀ B ∈ CKBTheory.forbidden Δ, B ∉ Y) Y)
  (hA : A ∉ Y) :
  ∃ C ∉ Δ.1, (A 🡒 □C) ∈ Y := by
  -- `hmdpY` and `hlogY` are unused by name: they are what instance resolution picks up below.
  obtain ⟨hTY, hmdpY, -⟩ := hmax.prop;
  have hlogY : Y.Of LogicCKB := ⟨(T.subset (L := LogicCKB)).trans hTY⟩;
  obtain ⟨C, hC, h⟩ := exists_imp_mem_of_maximal (𝔸 := ∅) (T := T) hmax hA;
  rcases hC with rfl | ⟨C, hC, rfl⟩;
  · exact ⟨⊥, Δ.1.consistent, Y.mdp (BDTheory.provable_mem (𝔸 := ∅)
      ProvableBDHilbert.imp_bot_imp_box_bot) h⟩;
  · exact ⟨C, hC, h⟩;

/-- A maximal MP-closed set avoiding `Δ.forbidden` is prime.

The cited proof of this step argues classically, deriving `∼A ∈ Y` from `A ∉ Y`, which is not
available intuitionistically. The argument used here instead pulls the primeness of `Δ` back
through `□`: a disjunct missing from `Y` implies some `□C` with `C ∉ Δ`, and `□(C ⋎ D) ∈ Y` then
forces `C ⋎ D ∈ Δ`.

- [Pac24, Lemma 16] -/
private lemma prime_of_maximal [T.Of LogicCKB]
  (hmax : Maximal (fun Y : BDTheory => T ⊆ Y ∧ Y.Mdp ∧ ∀ B ∈ CKBTheory.forbidden Δ, B ∉ Y) Y)
  (h : A ⋎ B ∈ Y) : A ∈ Y ∨ B ∈ Y := by
  by_contra hc;
  obtain ⟨hTY, hmdpY, havoid⟩ := hmax.prop;
  have hlogY : Y.Of LogicCKB := ⟨(T.subset (L := LogicCKB)).trans hTY⟩;
  obtain ⟨C, hC, h₁⟩ := exists_box_imp_mem hmax fun hA => hc (Or.inl hA);
  obtain ⟨D, hD, h₂⟩ := exists_box_imp_mem hmax fun hB => hc (Or.inr hB);
  have h₃ : C ⋎ D ∈ Δ.1 :=
    prebox_subset_of_avoid havoid (BDTheory.box_or_mem (𝔸 := ∅) (T := Y) h₁ h₂ h);
  exact (Δ.1.prime h₃).elim hC hD;

end BackwardConfluence

/-- The predecessor of `Δ₁` is a maximal MP-closed extension of the MP-closure of
`Γ.1 ∪ ◇Δ₁.1` avoiding `Δ₁.forbidden`. The hypothesis `Δ.1 ⊆ Γ.1.predia` is not needed, matching
the cited proof.

Two corrections to that proof. Its Zorn poset does not require its members to be closed under
modus ponens, and without that requirement the complement of the forbidden set is a maximum
element of the poset which is not a theory; the poset used here carries MP-closedness. And its
primeness argument does not go through as written, being classical; `prime_of_maximal` replaces
it.

- [Pac24, Lemma 16] -/
instance : canonicalModel.BackwardConfluent where
  backward_confluent {Γ Δ Δ₁} := by
    rintro ⟨MΓΔ, -⟩ IΔΔ₁;
    have hdia : ∀ B ∈ Γ.1, ◇B ∈ Δ₁.1 := fun B hB =>
      IΔΔ₁ (MΓΔ (BDTheory.box_dia_mem (T := Γ.1) hB));
    have hlog : (BDTheory.MdpClosure (Γ.1 ∪ ◇Δ₁.1)).Of LogicCKB :=
      ⟨(Γ.1.subset (L := LogicCKB)).trans
        (Set.subset_union_left.trans BDTheory.subset_mpClosure)⟩;
    have havoid : ∀ B ∈ CKBTheory.forbidden Δ₁, B ∉ BDTheory.MdpClosure (Γ.1 ∪ ◇Δ₁.1) := by
      rintro B (rfl | ⟨C, hC, rfl⟩) hB;
      · exact bot_not_mem_mpClosure hdia hB;
      · exact hC (mem_of_box_mem_mpClosure hdia hB);
    obtain ⟨Y, hsub, hmax⟩ := exists_maximal_mdpClosed_avoiding havoid;
    obtain ⟨-, hmdpY, havoidY⟩ := hmax.prop;
    have hlogY : Y.Of LogicCKB := ⟨hlog.subset.trans hsub⟩;
    have hprime : Y.Prime := ⟨fun h => prime_of_maximal hmax h⟩;
    have hcons : Y.Consistent := ⟨havoidY ⊥ (Or.inl rfl)⟩;
    have hckb : Y.CKB := ⟨⟩;
    exact ⟨⟨Y, hckb⟩,
      fun B hB => hsub (.base (Or.inl hB)), prebox_subset_of_avoid havoidY,
      fun B hB => hsub (.base (Or.inr ⟨B, hB, rfl⟩))⟩;

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
  (ihA : ∀ {Δ : CKBTheory}, Δ ⊩[canonicalModel] A ↔ A ∈ Δ.1)
  (ihB : ∀ {Δ : CKBTheory}, Δ ⊩[canonicalModel] B ↔ B ∈ Δ.1)
  (h : A 🡒 B ∈ Γ.1) : Γ ⊩[canonicalModel] (A 🡒 B) :=
  fun Δ IΓΔ hΔA => ihB.mpr (Δ.1.mdp (IΓΔ h) (ihA.mp hΔA))

/-- The implication case of the truth lemma, left-to-right. Contrapositively, a theory missing
`A 🡒 B` extends to one containing `A` and missing `B`, namely a Lindenbaum extension of
`Γ.1.impSet A`.

- [Pac24, Lemma 19]
-/
private lemma mem_of_forces_imply
  (ihA : ∀ {Δ : CKBTheory}, Δ ⊩[canonicalModel] A ↔ A ∈ Δ.1)
  (ihB : ∀ {Δ : CKBTheory}, Δ ⊩[canonicalModel] B ↔ B ∈ Δ.1)
  (h : Γ ⊩[canonicalModel] (A 🡒 B)) : A 🡒 B ∈ Γ.1 := by
  by_contra hc;
  -- `hmdp` and `hlog` are unused by name: they are what `exists_extending` resolves against.
  have hsub : Γ.1 ⊆ Γ.1.impSet A := BDTheory.subset_impSet (𝔸 := ∅);
  have hmdp : (Γ.1.impSet A).Mdp := BDTheory.impSet_mdpClosed (𝔸 := ∅);
  have hlog : (Γ.1.impSet A).Of LogicCKB := ⟨(Γ.1.subset (L := LogicCKB)).trans hsub⟩;
  obtain ⟨Δ, hXΔ, hBΔ⟩ := CKBTheory.exists_extending (T := Γ.1.impSet A) (A := B) hc;
  exact hBΔ <| ihB.mp <| h Δ (hsub.trans hXΔ) <|
    ihA.mpr <| hXΔ <| BDTheory.self_mem_impSet (𝔸 := ∅);

/-- Truth lemma for the canonical model: a CKB-theory forces exactly the formulas it contains.

- [Pac24, Lemma 19]
-/
theorem truth_lemma {Γ : CKBTheory} {A : BDFormula} : Γ ⊩[canonicalModel] A ↔ A ∈ Γ.1 := by
  induction A generalizing Γ with
  | atom a => exact Iff.rfl;
  | falsum => exact ⟨False.elim, fun h => (Γ.1.consistent h).elim⟩;
  | and A B ihA ihB =>
    constructor;
    · rintro ⟨hA, hB⟩;
      exact BDTheory.and_mem (𝔸 := ∅) (ihA.mp hA) (ihB.mp hB);
    · intro h;
      constructor;
      . exact ihA.mpr (Γ.1.mdp (Γ.1.subset (L := LogicCK) ProvableBDHilbert.andElim₁) h);
      . exact ihB.mpr (Γ.1.mdp (Γ.1.subset (L := LogicCK) ProvableBDHilbert.andElim₂) h);
  | or A B ihA ihB =>
    constructor;
    · rintro (hA | hB);
      · exact Γ.1.mdp (Γ.1.subset (L := LogicCK) ProvableBDHilbert.orIntro₁) (ihA.mp hA);
      · exact Γ.1.mdp (Γ.1.subset (L := LogicCK) ProvableBDHilbert.orIntro₂) (ihB.mp hB);
    · intro h;
      rcases Γ.1.prime h <;> grind;
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
