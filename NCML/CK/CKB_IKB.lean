module

public import NCML.Hilbert.Logics
public import NCML.Hilbert.Theory
public import NCML.CK.Confluence
public import NCML.CK.Soundness

@[expose] public section

/-!
# `CKB` and `IKB` prove the same formulas

The canonical model for `CKB` (`CK.CKBcanonicalModel`), whose worlds are the `CKB`-theories
(`NCML.CKBTheory`).

- [Pac24, Theorem 13, Section 3.2]
-/

namespace CK

open NCML BDFormula
open scoped NCML.BDFormulaSet

namespace CKBTheory

instance (Γ : CKBTheory) : Γ.1.CKB := Γ.2

/-- Lindenbaum lemma for CKB-theories: an MP-closed set of formulas containing every theorem of
`CKB` and missing `A` extends to a CKB-theory still missing `A`.

- [Pac24, Lemma 19, Lemma 20]
-/
lemma exists_extending {T : BDTheory} {A : BDFormula} [T.Of LogicCKB] [T.Mdp] (hA : A ∉ T) :
  ∃ Γ : CKBTheory, T ⊆ Γ.1 ∧ A ∉ Γ.1 := by
  obtain ⟨Y, hTY, hmax⟩ := exists_maximal_mdpClosed_avoiding (Z := {A}) (by rintro B rfl; exact hA);
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
def CKBcanonicalModel : Model CKBTheory where
  iRel' Γ Δ := Γ.1 ⊆ Δ.1
  iRel_preorder := {
    refl := fun _ => subset_rfl,
    trans := fun _ _ _ h₁ h₂ => h₁.trans h₂
  }
  mRel' Γ Δ := □⁻¹Γ.1 ⊆ Δ.1 ∧ Δ.1 ⊆ ◇⁻¹Γ.1
  Fallible' _ := False
  fallible_iRel' h _ := h.elim
  fallible_mRel' h _ := h.elim
  fallible_exists_mRel' h := h.elim
  val Γ a := (#a) ∈ Γ.1
  val_persistent h IΓΔ := IΓΔ h
  fallible_val h := h.elim

/-- - [Pac24, Lemma 15] -/
instance : CKBcanonicalModel.SymmetricMRel where
  symm_mRel {Γ Δ} := by
    rintro ⟨h₁, h₂⟩;
    constructor;
    · intro A hA;
      exact BDTheory.mem_of_dia_box_mem (T := Γ.1) (h₂ hA);
    · intro A hA;
      exact h₁ (BDTheory.box_dia_mem (T := Γ.1) hA);

section BackwardConfluence

variable {T Y : BDTheory} {Δ : CKBTheory} {A B : BDFormula}

/-- The formulas a theory `Γ` with `Γ ⊏ Δ` must avoid: `⊥` and `□C` for every `C ∉ Δ`. -/
private abbrev CKBTheory.forbidden (Δ : CKBTheory) : BDTheory := {⊥} ∪ □{C | C ∉ Δ.1}

private lemma prebox_subset_of_avoid (h : ∀ B ∈ CKBTheory.forbidden Δ, B ∉ T) :
  □⁻¹T ⊆ Δ.1 := by
  intro C hC;
  by_contra hc;
  exact h (□C) (Or.inr ⟨C, hc, rfl⟩) hC;

/-- A formula missing from a maximal set avoiding `Δ.forbidden` implies a boxed formula missing
from `Δ`. -/
private lemma exists_box_imp_mem [T.Of LogicCKB]
  (hmax : Maximal (fun Y : BDTheory => T ⊆ Y ∧ Y.Mdp ∧ ∀ B ∈ CKBTheory.forbidden Δ, B ∉ Y) Y)
  (hA : A ∉ Y) :
  ∃ C ∉ Δ.1, (A 🡒 □C) ∈ Y := by
  obtain ⟨hTY, hmdpY, -⟩ := hmax.prop;
  have hlogY : Y.Of LogicCKB := ⟨(T.subset (L := LogicCKB)).trans hTY⟩;
  obtain ⟨C, hC, h⟩ := exists_imp_mem_of_maximal (𝔸 := ∅) (T := T) hmax hA;
  rcases hC with rfl | ⟨C, hC, rfl⟩;
  · exact ⟨⊥, Δ.1.consistent, Y.mdp (BDTheory.provable_mem (𝔸 := ∅)
      ProvableBDHilbert.imp_bot_imp_box_bot) h⟩;
  · exact ⟨C, hC, h⟩;

/-- A maximal MP-closed set avoiding `Δ.forbidden` is prime.

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

/-- A CKB-theory `Γ` with `◇B ∈ Θ` for every `B ∈ Γ` extends to a CKB-theory `Δ` with
`□⁻¹Δ ⊆ Θ` and `Θ ⊆ ◇⁻¹Δ`.

- [Pac24, Lemma 16] -/
lemma CKBTheory.exists_mRel_extending {Γ Θ : CKBTheory} (hdia : ∀ B ∈ Γ.1, ◇B ∈ Θ.1) :
  ∃ Δ : CKBTheory, Γ.1 ⊆ Δ.1 ∧ □⁻¹Δ.1 ⊆ Θ.1 ∧ Θ.1 ⊆ ◇⁻¹Δ.1 := by
  have hlog : (BDTheory.MdpClosure (Γ.1 ∪ ◇Θ.1)).Of LogicCKB :=
    ⟨(Γ.1.subset (L := LogicCKB)).trans
      (Set.subset_union_left.trans BDTheory.subset_mpClosure)⟩;
  have havoid : ∀ B ∈ CKBTheory.forbidden Θ, B ∉ BDTheory.MdpClosure (Γ.1 ∪ ◇Θ.1) := by
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

/-- - [Pac24, Lemma 16] -/
instance : CKBcanonicalModel.BackwardConfluent where
  backward_confluent {Γ Δ Δ₁} := by
    rintro ⟨MΓΔ, -⟩ IΔΔ₁;
    exact CKBTheory.exists_mRel_extending fun B hB =>
      IΔΔ₁ (MΓΔ (BDTheory.box_dia_mem (T := Γ.1) hB));

instance : CKBcanonicalModel.ForwardConfluent :=
  Model.forwardConfluent_iff_backwardConfluent_of_symmetricMRel.mpr inferInstance

/-- - [Pac24, Lemma 17] -/
instance : CKBcanonicalModel.IsIKB where
  not_fallible _ h := h.elim

section Diamond

variable {T Y : BDTheory} {Γ : CKBTheory} {A B : BDFormula}

/-- The formulas a theory `Δ` with `Γ ⊏ Δ` must avoid: those `C` with `◇C ∉ Γ`. -/
private abbrev CKBTheory.diaForbidden (Γ : CKBTheory) : BDTheory := {C | ◇C ∉ Γ.1}

/-- A maximal MP-closed set avoiding `Γ.diaForbidden` is prime. -/
private lemma prime_of_maximal_dia [T.Of LogicCKB]
  (hmax : Maximal (fun Y : BDTheory => T ⊆ Y ∧ Y.Mdp ∧ ∀ B ∈ CKBTheory.diaForbidden Γ, B ∉ Y) Y)
  (h : A ⋎ B ∈ Y) : A ∈ Y ∨ B ∈ Y := by
  by_contra hc;
  obtain ⟨hTY, hmdpY, havoid⟩ := hmax.prop;
  have hlogY : Y.Of LogicCKB := ⟨(T.subset (L := LogicCKB)).trans hTY⟩;
  obtain ⟨C, hC, h₁⟩ := exists_imp_mem_of_maximal (𝔸 := ∅) (T := T) hmax fun hA => hc (Or.inl hA);
  obtain ⟨D, hD, h₂⟩ := exists_imp_mem_of_maximal (𝔸 := ∅) (T := T) hmax fun hB => hc (Or.inr hB);
  have h₃ : (A 🡒 C ⋎ D) ∈ Y :=
    Y.mdp (BDTheory.provable_mem (𝔸 := ∅)
      (ProvableBDHilbert.imp_comp_left ProvableBDHilbert.orIntro₁)) h₁;
  have h₄ : (B 🡒 C ⋎ D) ∈ Y :=
    Y.mdp (BDTheory.provable_mem (𝔸 := ∅)
      (ProvableBDHilbert.imp_comp_left ProvableBDHilbert.orIntro₂)) h₂;
  have h₅ : C ⋎ D ∈ Y := BDTheory.or_elim_mem (𝔸 := ∅) h₃ h₄ h;
  exact havoid (C ⋎ D) (fun hmem => (BDTheory.dia_or_mem hmem).elim hC hD) h₅;

/-- A CKB-theory containing `◇A` has a `⊏`-successor containing `A`.

- [Pac24, Lemma 19] -/
private lemma exists_mRel_of_dia_mem (h : ◇A ∈ Γ.1) :
  ∃ Δ : CKBTheory, □⁻¹Γ.1 ⊆ Δ.1 ∧ Δ.1 ⊆ ◇⁻¹Γ.1 ∧ A ∈ Δ.1 := by
  have hmdpX : BDTheory.Mdp (BDTheory.impSet (□⁻¹Γ.1) A) :=
    BDTheory.impSet_mdpClosed (𝔸 := ∅);
  have hsub : □⁻¹Γ.1 ⊆ BDTheory.impSet (□⁻¹Γ.1) A :=
    BDTheory.subset_impSet (𝔸 := ∅);
  have hlogX : BDTheory.Of LogicCKB (BDTheory.impSet (□⁻¹Γ.1) A) :=
    ⟨(BDTheory.subset (L := LogicCKB) (T := □⁻¹Γ.1)).trans hsub⟩;
  have havoid : ∀ B ∈ CKBTheory.diaForbidden Γ, B ∉ BDTheory.impSet (□⁻¹Γ.1) A := by
    intro B hB hmem;
    have h₁ : (◇A 🡒 ◇B) ∈ Γ.1 :=
      Γ.1.mdp (Γ.1.subset (L := LogicCK) (ProvableBDHilbert.kDia (A := A) (B := B))) hmem;
    exact hB (Γ.1.mdp h₁ h);
  obtain ⟨Y, hXY, hmax⟩ := exists_maximal_mdpClosed_avoiding havoid;
  obtain ⟨-, hmdpY, havoidY⟩ := hmax.prop;
  have hlogY : Y.Of LogicCKB := ⟨hlogX.subset.trans hXY⟩;
  have hprime : Y.Prime := ⟨fun hor => prime_of_maximal_dia hmax hor⟩;
  have hcons : Y.Consistent := ⟨havoidY ⊥ (BDTheory.dia_bot_not_mem (T := Γ.1))⟩;
  have hckb : Y.CKB := ⟨⟩;
  have hpredia : Y ⊆ ◇⁻¹Γ.1 := by
    intro B hB;
    by_contra hc;
    exact havoidY B hc hB;
  exact ⟨⟨Y, hckb⟩, hsub.trans hXY, hpredia,
    hXY (BDTheory.self_mem_impSet (𝔸 := ∅))⟩;

end Diamond

/-- Truth lemma for the canonical model: a CKB-theory forces exactly the formulas it contains.

- [Pac24, Lemma 18, Lemma 19]
-/
theorem truthlemma {Γ : CKBTheory} {A : BDFormula} : Γ ⊩[CKBcanonicalModel] A ↔ A ∈ Γ.1 := by
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
  | imply A B ihA ihB =>
    constructor;
    · intro h;
      by_contra hc;
      have hsub : Γ.1 ⊆ Γ.1.impSet A := BDTheory.subset_impSet (𝔸 := ∅);
      have hmdp : (Γ.1.impSet A).Mdp := BDTheory.impSet_mdpClosed (𝔸 := ∅);
      have hlog : (Γ.1.impSet A).Of LogicCKB := ⟨(Γ.1.subset (L := LogicCKB)).trans hsub⟩;
      obtain ⟨Δ, hXΔ, hBΔ⟩ := CKBTheory.exists_extending (T := Γ.1.impSet A) (A := B) hc;
      exact hBΔ <| ihB.mp <| h Δ (hsub.trans hXΔ) <|
        ihA.mpr <| hXΔ <| BDTheory.self_mem_impSet (𝔸 := ∅);
    · intro h;
      exact fun Δ IΓΔ hΔA => ihB.mpr (Δ.1.mdp (IΓΔ h) (ihA.mp hΔA));
  | box A ih =>
    constructor;
    · intro h;
      by_contra hc;
      obtain ⟨Θ, hsub, hAΘ⟩ := CKBTheory.exists_extending (T := □⁻¹Γ.1) (A := A) hc;
      obtain ⟨Δ, IΓΔ, h₁, h₂⟩ := CKBTheory.exists_mRel_extending (Γ := Γ) (Θ := Θ)
        fun B hB => hsub (BDTheory.box_dia_mem (T := Γ.1) hB);
      exact hAΘ (ih.mp (h Δ Θ IΓΔ ⟨h₁, h₂⟩));
    · intro h Δ Θ IΓΔ MΔΘ;
      exact ih.mpr (MΔΘ.1 (IΓΔ h));
  | dia A ih =>
    constructor;
    · intro h;
      obtain ⟨Δ, MΓΔ, hΔA⟩ := h Γ Set.Subset.rfl;
      exact MΓΔ.2 (ih.mp hΔA);
    · intro h Δ IΓΔ;
      obtain ⟨Θ, h₁, h₂, h₃⟩ := exists_mRel_of_dia_mem (Γ := Δ) (IΓΔ h);
      exact ⟨Θ, ⟨h₁, h₂⟩, ih.mpr h₃⟩;

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
    obtain ⟨Γ, -, hAΓ⟩ := CK.CKBTheory.exists_extending (T := LogicCKB) h;
    exact ⟨_, CK.CKBcanonicalModel, inferInstance, fun hM => hAΓ (CK.truthlemma.mp (hM Γ))⟩;
  tfae_finish

end
