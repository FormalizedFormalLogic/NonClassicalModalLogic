module

public import NCML.Hilbert.Logics
public import NCML.Hilbert.Theory
public import NCML.CK.Confluence
public import NCML.CK.Soundness

@[expose] public section

/-!
# `CKB` and `IKB` prove the same formulas

The canonical model for `CKB` (`CK.CKBcanonicalModel`), whose worlds are the `CKB`-theories
(`CKBTheory`).

- [Pac24, Theorem 13, Section 3.2]
-/

namespace CK

open BDFormula
open scoped BDFormulaSet

namespace CKBTheory

instance (T : CKBTheory) : T.1.CKB := T.2

/-- Lindenbaum lemma for CKB-theories: an MP-closed set of formulas containing every theorem of
`CKB` and missing `A` extends to a CKB-theory still missing `A`. -/
lemma exists_extending {T : BDTheory} {A : BDFormula} [T.Of LogicCKB] [T.Mdp] (hA : A ∉ T) :
  ∃ T₁ : CKBTheory, T ⊆ T₁.1 ∧ A ∉ T₁.1 := by
  obtain ⟨Y, hTY, hmax⟩ :=
    exists_maximal_mdpClosed_avoiding (L := LogicCKB) (Z := {A}) (by rintro B rfl; exact hA);
  obtain ⟨-, hmdpY, hlogY, havoid⟩ := hmax.prop;
  have hAY : A ∉ Y := havoid A rfl;
  have h₁ : ∀ {B}, B ∉ Y → (B 🡒 A) ∈ Y := by
    intro B hB;
    obtain ⟨C, rfl, h⟩ := exists_imp_mem_of_maximal hmax hB;
    exact h;
  exact ⟨⟨Y, {
    prime := by
      intro B C hBC;
      by_contra! hc;
      exact hAY <| BDTheory.or_elim_mem (𝔸 := ∅) (h₁ hc.1) (h₁ hc.2) hBC;
    consistent := fun h => hAY <| Y.mdp (BDTheory.provable_mem (𝔸 := ∅) .efq) h
  }⟩, hTY, hAY⟩;

end CKBTheory

/-- - [Pac24, Section 3.2] -/
def CKBcanonicalModel : Model CKBTheory where
  iRel' T U := T.1 ⊆ U.1
  iRel_preorder := {
    refl := fun _ => subset_rfl,
    trans := fun _ _ _ => subset_trans
  }
  mRel' T U := □⁻¹T.1 ⊆ U.1 ∧ U.1 ⊆ ◇⁻¹T.1
  Fallible' _ := False
  fallible_iRel' h _ := h.elim
  fallible_mRel' h _ := h.elim
  fallible_exists_mRel' h := h.elim
  val T a := (#a) ∈ T.1
  val_persistent h ITU := ITU h
  fallible_val h := h.elim

/-- - [Pac24, Lemma 15] -/
instance : CKBcanonicalModel.SymmetricMRel where
  symm_mRel {T U} := by
    rintro ⟨h₁, h₂⟩;
    constructor;
    · intro A hA;
      exact BDTheory.mem_of_dia_box_mem (T := T.1) (h₂ hA);
    · intro A hA;
      exact h₁ (BDTheory.box_dia_mem (T := T.1) hA);

section BackwardConfluence

variable {T Y : BDTheory} {U : CKBTheory} {A B : BDFormula}

/-- The formulas a theory `T` with `T ⊏ U` must avoid: `⊥` and `□C` for every `C ∉ U`. -/
private abbrev CKBTheory.forbidden (U : CKBTheory) : BDTheory := {⊥} ∪ □{C | C ∉ U.1}

private lemma prebox_subset_of_avoid (h : ∀ B ∈ CKBTheory.forbidden U, B ∉ T) :
  □⁻¹T ⊆ U.1 := by
  intro C hC;
  by_contra! hc;
  exact h (□C) (Or.inr ⟨C, hc, rfl⟩) hC;

/-- A formula missing from a maximal set avoiding `U.forbidden` implies a boxed formula missing
from `U`. -/
private lemma exists_box_imp_mem
  (hmax : Maximal
    (fun Y : BDTheory => T ⊆ Y ∧ Y.Mdp ∧ Y.Of LogicCKB ∧ ∀ B ∈ CKBTheory.forbidden U, B ∉ Y) Y)
  (hA : A ∉ Y) :
  ∃ C ∉ U.1, (A 🡒 □C) ∈ Y := by
  obtain ⟨-, hmdpY, hlogY, -⟩ := hmax.prop;
  obtain ⟨C, rfl | ⟨C, hC, rfl⟩, h⟩ := exists_imp_mem_of_maximal hmax hA;
  · exact ⟨⊥, U.1.consistent, Y.mdp (BDTheory.provable_mem (𝔸 := ∅)
      ProvableBDHilbert.imp_bot_imp_box_bot) h⟩;
  · exact ⟨C, hC, h⟩;

/-- A maximal MP-closed set avoiding `U.forbidden` is prime. -/
private lemma prime_of_maximal
  (hmax : Maximal
    (fun Y : BDTheory => T ⊆ Y ∧ Y.Mdp ∧ Y.Of LogicCKB ∧ ∀ B ∈ CKBTheory.forbidden U, B ∉ Y) Y)
  (h : A ⋎ B ∈ Y) : A ∈ Y ∨ B ∈ Y := by
  by_contra! hc;
  obtain ⟨-, hmdpY, hlogY, havoid⟩ := hmax.prop;
  obtain ⟨C, hC, h₁⟩ := exists_box_imp_mem hmax hc.1;
  obtain ⟨D, hD, h₂⟩ := exists_box_imp_mem hmax hc.2;
  exact (U.1.prime <| prebox_subset_of_avoid havoid <|
    BDTheory.box_or_mem (𝔸 := ∅) (T := Y) h₁ h₂ h).elim hC hD;

end BackwardConfluence

/-- A CKB-theory `T` with `◇B ∈ U` for every `B ∈ T` extends to a CKB-theory `T₁` with
`□⁻¹T₁ ⊆ U` and `U ⊆ ◇⁻¹T₁`. -/
lemma CKBTheory.exists_mRel_extending {T U : CKBTheory} (hdia : ∀ B ∈ T.1, ◇B ∈ U.1) :
  ∃ T₁ : CKBTheory, T.1 ⊆ T₁.1 ∧ □⁻¹T₁.1 ⊆ U.1 ∧ U.1 ⊆ ◇⁻¹T₁.1 := by
  have hlog : (BDTheory.mdpClosure (T.1 ∪ ◇U.1)).Of LogicCKB :=
    ⟨(T.1.subset (L := LogicCKB)).trans
      (Set.subset_union_left.trans BDTheory.subset_mdpClosure)⟩;
  have havoid : ∀ B ∈ CKBTheory.forbidden U, B ∉ BDTheory.mdpClosure (T.1 ∪ ◇U.1) := by
    rintro B (rfl | ⟨C, hC, rfl⟩) hB;
    · exact bot_not_mem_mdpClosure hdia hB;
    · exact hC (mem_of_box_mem_mdpClosure hdia hB);
  obtain ⟨Y, hsub, hmax⟩ := exists_maximal_mdpClosed_avoiding (L := LogicCKB) havoid;
  obtain ⟨-, hmdpY, -, havoidY⟩ := hmax.prop;
  use ⟨Y, {
    prime := prime_of_maximal hmax,
    consistent := havoidY ⊥ (Or.inl rfl),
    subset := hlog.subset.trans hsub
  }⟩;
  and_intros;
  . exact fun B hB => hsub (.base (Or.inl hB));
  . exact prebox_subset_of_avoid havoidY;
  . exact fun B hB => hsub (.base (Or.inr ⟨B, hB, rfl⟩));

/-- - [Pac24, Lemma 16] -/
instance : CKBcanonicalModel.BackwardConfluent where
  backward_confluent {T T₁ U} := by
    rintro ⟨MTT₁, -⟩ IT₁U;
    exact CKBTheory.exists_mRel_extending
      fun B hB => IT₁U (MTT₁ (BDTheory.box_dia_mem (T := T.1) hB));

instance : CKBcanonicalModel.ForwardConfluent :=
  Model.forwardConfluent_iff_backwardConfluent_of_symmetricMRel.mpr inferInstance

/-- - [Pac24, Lemma 17] -/
instance : CKBcanonicalModel.IsIKB where
  not_fallible _ h := h.elim

section Diamond

variable {T Y : BDTheory} {U : CKBTheory} {A B : BDFormula}

/-- The formulas a theory `T` with `U ⊏ T` must avoid: those `C` with `◇C ∉ U`. -/
private abbrev CKBTheory.diaForbidden (U : CKBTheory) : BDTheory := {C | ◇C ∉ U.1}

/-- A maximal MP-closed set avoiding `U.diaForbidden` is prime. -/
private lemma prime_of_maximal_dia
  (hmax : Maximal
    (fun Y : BDTheory => T ⊆ Y ∧ Y.Mdp ∧ Y.Of LogicCKB ∧ ∀ B ∈ CKBTheory.diaForbidden U, B ∉ Y) Y)
  (h : A ⋎ B ∈ Y) : A ∈ Y ∨ B ∈ Y := by
  by_contra! hc;
  obtain ⟨-, hmdpY, hlogY, havoid⟩ := hmax.prop;
  obtain ⟨C, hC, h₁⟩ := exists_imp_mem_of_maximal hmax hc.1;
  obtain ⟨D, hD, h₂⟩ := exists_imp_mem_of_maximal hmax hc.2;
  have h₃ : (A 🡒 C ⋎ D) ∈ Y :=
    Y.mdp (BDTheory.provable_mem (𝔸 := ∅)
      (ProvableBDHilbert.imp_comp_left ProvableBDHilbert.orIntro₁)) h₁;
  have h₄ : (B 🡒 C ⋎ D) ∈ Y :=
    Y.mdp (BDTheory.provable_mem (𝔸 := ∅)
      (ProvableBDHilbert.imp_comp_left ProvableBDHilbert.orIntro₂)) h₂;
  have h₅ : C ⋎ D ∈ Y := BDTheory.or_elim_mem (𝔸 := ∅) h₃ h₄ h;
  exact havoid (C ⋎ D) (fun hmem => (BDTheory.dia_or_mem hmem).elim hC hD) h₅;

/-- A CKB-theory containing `◇A` has a `⊏`-successor containing `A`. -/
private lemma exists_mRel_of_dia_mem (h : ◇A ∈ U.1) :
  ∃ T₁ : CKBTheory, □⁻¹U.1 ⊆ T₁.1 ∧ T₁.1 ⊆ ◇⁻¹U.1 ∧ A ∈ T₁.1 := by
  have havoid : ∀ B ∈ CKBTheory.diaForbidden U, B ∉ BDTheory.impSet (□⁻¹U.1) A := by
    intro B hB hmem;
    have h₁ : (◇A 🡒 ◇B) ∈ U.1 :=
      U.1.mdp (U.1.subset (L := LogicCK) (ProvableBDHilbert.kDia (A := A) (B := B))) hmem;
    exact hB (U.1.mdp h₁ h);
  obtain ⟨Y, hXY, hmax⟩ := exists_maximal_mdpClosed_avoiding (L := LogicCKB) havoid;
  obtain ⟨-, hmdpY, hlogY, havoidY⟩ := hmax.prop;
  use ⟨Y, {
    prime := prime_of_maximal_dia hmax,
    consistent := havoidY ⊥ (BDTheory.dia_bot_not_mem (T := U.1))
  }⟩;
  and_intros;
  . exact (BDTheory.subset_impSet (𝔸 := ∅)).trans hXY;
  . intro B hB;
    by_contra! hc;
    exact havoidY B hc hB;
  . exact hXY (BDTheory.self_mem_impSet (𝔸 := ∅));

end Diamond

/-- Truth lemma for the canonical model: a CKB-theory forces exactly the formulas it contains.

- [Pac24, Lemma 19]
-/
lemma truthlemma {T : CKBTheory} {A : BDFormula} : T ⊩[CKBcanonicalModel] A ↔ A ∈ T.1 := by
  induction A generalizing T with
  | atom a => exact Iff.rfl;
  | falsum => exact ⟨False.elim, fun h => (T.1.consistent h).elim⟩;
  | and A B ihA ihB =>
    constructor;
    · rintro ⟨hA, hB⟩;
      exact BDTheory.and_mem (𝔸 := ∅) (ihA.mp hA) (ihB.mp hB);
    · intro h;
      constructor;
      . exact ihA.mpr (T.1.mdp (T.1.subset (L := LogicCK) .andElim₁) h);
      . exact ihB.mpr (T.1.mdp (T.1.subset (L := LogicCK) .andElim₂) h);
  | or A B ihA ihB =>
    constructor;
    · rintro (hA | hB);
      · exact T.1.mdp (T.1.subset (L := LogicCK) .orIntro₁) (ihA.mp hA);
      · exact T.1.mdp (T.1.subset (L := LogicCK) .orIntro₂) (ihB.mp hB);
    · intro h;
      rcases T.1.prime h <;> grind;
  | imply A B ihA ihB =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨T₁, hXT₁, hBT₁⟩ := CKBTheory.exists_extending (T := T.1.impSet A) (A := B) hc;
      exact hBT₁
        <| ihB.mp
        <| h T₁ ((BDTheory.subset_impSet (𝔸 := ∅)).trans hXT₁)
        <| ihA.mpr
        <| hXT₁
        <| BDTheory.self_mem_impSet (𝔸 := ∅);
    · intro h T₁ ITT₁ hT₁A;
      exact ihB.mpr (T₁.1.mdp (ITT₁ h) (ihA.mp hT₁A));
  | box A ih =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨U, hsub, hAU⟩ := CKBTheory.exists_extending (T := □⁻¹T.1) (A := A) hc;
      obtain ⟨T₁, ITT₁, h₁, h₂⟩ := CKBTheory.exists_mRel_extending (T := T) (U := U)
        fun B hB => hsub (BDTheory.box_dia_mem (T := T.1) hB);
      exact hAU (ih.mp (h T₁ U ITT₁ ⟨h₁, h₂⟩));
    · intro h T₁ U ITT₁ MT₁U;
      exact ih.mpr (MT₁U.1 (ITT₁ h));
  | dia A ih =>
    constructor;
    · intro h;
      obtain ⟨U, MTU, hUA⟩ := h T Set.Subset.rfl;
      exact MTU.2 (ih.mp hUA);
    · intro h T₁ ITT₁;
      obtain ⟨U, h₁, h₂, h₃⟩ := exists_mRel_of_dia_mem (U := T₁) (ITT₁ h);
      exact ⟨U, ⟨h₁, h₂⟩, ih.mpr h₃⟩;

end CK

/-- - [Pac24, Theorem 13] -/
theorem CKB_IKB_TFAE : List.TFAE [
  A ∈ LogicCKB,
  A ∈ LogicIKB,
  ∀ {κ : Type 0}, ∀ M : CK.Model κ, [M.IsCKB] → M ⊧ A,
  ∀ {κ : Type 0}, ∀ M : CK.Model κ, [M.IsIKB] → M ⊧ A,
] := by
  tfae_have 1 → 2 := by apply LogicCKB.subset_IKB;
  tfae_have 3 → 4 := fun h _ M _ => h M
  tfae_have 1 → 3 := fun h _ M _ => CK.Model.valid_of_mem_LogicCKB h
  tfae_have 2 → 4 := fun h _ M _ => CK.Model.valid_of_mem_LogicIKB h
  tfae_have 4 → 1 := by
    contrapose!;
    intro h;
    obtain ⟨T, -, hAT⟩ := CK.CKBTheory.exists_extending (T := LogicCKB) h;
    exact ⟨_, CK.CKBcanonicalModel, inferInstance, fun hM => hAT (CK.truthlemma.mp (hM T))⟩;
  tfae_finish

/-- - [Pac24, Theorem 13] -/
theorem eq_CKB_IKB : LogicCKB = LogicIKB := by
  ext A;
  apply CKB_IKB_TFAE.out 1 2;

end
