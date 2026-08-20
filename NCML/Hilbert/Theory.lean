module

public import NCML.Hilbert.Logics
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Zorn

@[expose] public section

open BDFormula BDFormulaList ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

abbrev BDTheory := Set BDFormula



namespace BDTheory

class Mdp (T : BDTheory) where
  mdp {A B} : (A 🡒 B) ∈ T → A ∈ T → B ∈ T
export Mdp (mdp)

class Prime (T : BDTheory) where
  prime {A B} : A ⋎ B ∈ T → A ∈ T ∨ B ∈ T
export Prime (prime)

class Consistent (T : BDTheory) where
  consistent : ⊥ ∉ T
export Consistent (consistent)

class Of (L : BDLogic) (T : BDTheory) where
  subset : L ⊆ T
export Of (subset)

attribute [grind =>] mdp prime
attribute [grind .] consistent

variable {𝔸 : Set BDFormula} {T : BDTheory} {A B C D : BDFormula}

instance logic_mdp : Mdp (logic 𝔸) := ⟨ProvableBDHilbert.mdp⟩

instance logic_of : Of (logic 𝔸) (logic 𝔸) := ⟨subset_rfl⟩

lemma provable_mem [T.Of (logic 𝔸)] (h : ⊢ᴴ[CK;𝔸] A) : A ∈ T :=
  subset (L := (ProvableBDHilbert.logic 𝔸)) h

lemma and_mem [T.Of (logic 𝔸)] [T.Mdp] (hA : A ∈ T) (hB : B ∈ T) : A ⋏ B ∈ T :=
  mdp (mdp (provable_mem (𝔸 := 𝔸) andIntro) hA) hB

lemma lconj_mem [T.Of (logic 𝔸)] [T.Mdp]
  {Γ : BDFormulaList} (h : ∀ A ∈ Γ, A ∈ T) : ⋀Γ ∈ T := by
  induction Γ with
  | nil => exact provable_mem (𝔸 := 𝔸) verum;
  | cons A Γ ih =>
    apply and_mem (𝔸 := 𝔸);
    . simp_all;
    . exact ih (by grind);

lemma or_elim_mem [T.Of (logic 𝔸)] [T.Mdp]
  (hAC : (A 🡒 C) ∈ T) (hBC : (B 🡒 C) ∈ T) (hAB : (A ⋎ B) ∈ T) : C ∈ T :=
  mdp (mdp (mdp (provable_mem (𝔸 := 𝔸) orElim) hAC) hBC) hAB

lemma box_or_mem [T.Of (logic 𝔸)] [T.Mdp]
  (h₁ : (A 🡒 □C) ∈ T) (h₂ : (B 🡒 □D) ∈ T) (h : (A ⋎ B) ∈ T) : □(C ⋎ D) ∈ T := by
  exact
    or_elim_mem (𝔸 := 𝔸)
    (mdp (provable_mem (𝔸 := 𝔸) (imp_comp_left box_or_inl)) h₁)
    (mdp (provable_mem (𝔸 := 𝔸) (imp_comp_left box_or_inr)) h₂)
    h;

/-- An mdp-closed theory of `logic 𝔸` containing `⊥` is the whole formula set. -/
lemma eq_univ_of_bot_mem [T.Of (logic 𝔸)] [T.Mdp] (h : ⊥ ∈ T) : T = Set.univ :=
  Set.eq_univ_of_forall fun _ => mdp (T := T) (provable_mem (𝔸 := 𝔸) efq) h

section CKB

class CKB (T : BDTheory) extends T.Mdp, T.Prime, T.Consistent, T.Of LogicCKB where

instance [T.Of LogicCKB] : T.Of LogicCK := ⟨LogicCK.subset_CKB.trans (subset (L := LogicCKB))⟩

lemma box_dia_mem [T.CKB] (hA : A ∈ T) : □◇A ∈ T := by
  apply mdp ?_ hA;
  apply T.subset (L := LogicCKB);
  apply ProvableBDHilbert.axm;
  grind;

lemma mem_of_dia_box_mem [T.CKB] (h : ◇(□A) ∈ T) : A ∈ T := by
  apply mdp ?_ h;
  apply T.subset (L := LogicCKB);
  apply ProvableBDHilbert.axm;
  grind;

instance prebox_mdp [T.Of LogicCK] [T.Mdp] : Mdp (□⁻¹T) :=
  ⟨fun hAB hA => mdp (T := T) (mdp (T := T) (provable_mem (𝔸 := ∅) kBox) hAB) hA⟩

-- Not an instance: the axiom set `𝔸` behind `T.Of (logic 𝔸)` cannot be recovered from the goal.
lemma prebox_of' [T.Of (logic 𝔸)] : Of (logic 𝔸) (□⁻¹T) :=
  ⟨fun _ hA => T.subset (L := logic 𝔸) (nec hA)⟩

instance prebox_of [T.Of LogicCKB] : Of LogicCKB (□⁻¹T) :=
  ⟨fun _ hA => T.subset (L := LogicCKB) (nec hA)⟩

lemma dia_or_mem [T.CKB] (h : ◇(A ⋎ B) ∈ T) : ◇A ∈ T ∨ ◇B ∈ T :=
  prime (mdp (T.subset (L := LogicCKB) LogicCKB.provable_DP) h)

lemma dia_bot_not_mem [T.CKB] : ◇(⊥ : BDFormula) ∉ T :=
  fun h => T.consistent (mdp (T.subset (L := LogicCKB) LogicCKB.provable_N) h)

end CKB

instance [T.Of LogicCKTDia] : T.Of LogicCK :=
  ⟨LogicCK.subset_CKTDia.trans (subset (L := LogicCKTDia))⟩

end BDTheory


abbrev CKBTheory := { T : BDTheory // T.CKB }


inductive BDTheory.mdpClosure (T : BDTheory) : BDTheory
  | base {A} : A ∈ T → mdpClosure T A
  | mdp {A B} : mdpClosure T (A 🡒 B) → mdpClosure T A → mdpClosure T B

namespace BDTheory

variable {T T₁ T₂ : BDTheory} {X Y : BDFormulaSet} {𝔸 : Set BDFormula} {A : BDFormula}

lemma subset_mdpClosure : T ⊆ T.mdpClosure := fun _ => mdpClosure.base

instance : T.mdpClosure.Mdp := ⟨.mdp⟩


lemma mono_mdpClosure (h : T₁ ⊆ T₂): T₁.mdpClosure ⊆ T₂.mdpClosure := by
  intro A hA;
  induction hA with
  | base hA => exact .base (h hA);
  | mdp _ _ ih₁ ih₂ => exact .mdp ih₁ ih₂;

lemma logic_subset_mdpClosure [T.Of (logic 𝔸)] : T.mdpClosure.Of (ProvableBDHilbert.logic 𝔸) :=
  ⟨T.subset.trans subset_mdpClosure⟩

/-- Finite characterization of the MP-closure of `T ∪ ◇Y`: every member `A` of the closure is
already derivable from finitely many `◇B` with `B ∈ Y` together with a single `C ∈ T`. -/
lemma exists_finite_char [T.Of (logic 𝔸)] [T.Mdp] (h : A ∈ mdpClosure (T ∪ ◇Y)) :
  ∃ Γ : BDFormulaList, (∀ B ∈ Γ, B ∈ Y) ∧
  ∃ C ∈ T, ⊢ᴴ[CK;𝔸] (⋀◇Γ 🡒 C 🡒 A) := by
  induction h with
  | base hA =>
    rcases hA with hA | ⟨B, hB, rfl⟩;
    · use [];
      constructor;
      . tauto;
      . exact ⟨_, hA, dhyp imp_id⟩
    · use [B];
      constructor;
      . grind;
      . use ⊤;
        constructor;
        . exact provable_mem (𝔸 := 𝔸) verum;
        . exact imp_trans andElim₁ imply₁;
  | mdp _ _ ih₁ ih₂ =>
    obtain ⟨Γ₁, hΓ₁, C₁, hC₁, d₁⟩ := ih₁;
    obtain ⟨Γ₂, hΓ₂, C₂, hC₂, d₂⟩ := ih₂;
    use Γ₁ ++ Γ₂;
    constructor;
    . grind;
    . use C₁ ⋏ C₂;
      constructor;
      . exact and_mem (𝔸 := 𝔸) hC₁ hC₂;
      . rw [dia_append];
        have t₁ := imp_trans (lconj_append_left (Γ₁ := ◇Γ₁) (Γ₂ := ◇Γ₂)) d₁;
        have t₂ := imp_trans (lconj_append_right (Γ₁ := ◇Γ₁) (Γ₂ := ◇Γ₂)) d₂;
        exact mdp_ctx₂
          (imp_trans t₁ (imp_comp_right andElim₁))
          (imp_trans t₂ (imp_comp_right andElim₂));

/-- Finite characterization of the MP-closure of a union `T₁ ∪ T₂`: every member `A` of the
closure is entailed from a single `D ∈ T₁` and a single `E ∈ T₂`. -/
lemma mdpClosure_union_finite_char [T₁.Of (logic 𝔸)] [T₁.Mdp] [T₂.Of (logic 𝔸)] [T₂.Mdp]
  (h : A ∈ mdpClosure (T₁ ∪ T₂)) : ∃ D ∈ T₁, ∃ E ∈ T₂, ⊢ᴴ[CK;𝔸] D 🡒 E 🡒 A := by
  induction h with
  | base hA =>
    rcases hA with hA | hA;
    · exact ⟨_, hA, ⊤, provable_mem (𝔸 := 𝔸) verum, imply₁⟩;
    · exact ⟨⊤, provable_mem (𝔸 := 𝔸) verum, _, hA, dhyp imp_id⟩;
  | mdp _ _ ih₁ ih₂ =>
    obtain ⟨D₁, hD₁, E₁, hE₁, d₁⟩ := ih₁;
    obtain ⟨D₂, hD₂, E₂, hE₂, d₂⟩ := ih₂;
    exact ⟨D₁ ⋏ D₂, and_mem (𝔸 := 𝔸) hD₁ hD₂, E₁ ⋏ E₂, and_mem (𝔸 := 𝔸) hE₁ hE₂,
      mdp_ctx₂ (imp_trans (imp_trans andElim₁ d₁) (imp_comp_right andElim₁))
               (imp_trans (imp_trans andElim₂ d₂) (imp_comp_right andElim₂))⟩;

end BDTheory


/-- The union of a chain of MP-closed theories is MP-closed. -/
lemma MdpClosed_sUnion_of_chain {c : Set BDTheory} (hc : IsChain (· ⊆ ·) c)
  (h : ∀ T ∈ c, T.Mdp) : BDTheory.Mdp (⋃₀ c) := by
  constructor;
  rintro A B ⟨T₁, hT₁c, hAB⟩ ⟨T₂, hT₂c, hA⟩;
  rcases hc.total hT₁c hT₂c with hsub | hsub;
  · exact ⟨T₂, hT₂c, (h T₂ hT₂c).mdp (hsub hAB) hA⟩;
  · exact ⟨T₁, hT₁c, (h T₁ hT₁c).mdp hAB (hsub hA)⟩;

/-! ## The implication set -/

namespace BDTheory

/-- The formulas `B` with `A 🡒 B ∈ T`, i.e. `T` "under the assumption `A`". -/
def impSet (T : BDTheory) (A : BDFormula) : BDTheory := { B | (A 🡒 B) ∈ T }

@[simp, grind =]
lemma mem_impSet {T : BDTheory} {A B} : B ∈ T.impSet A ↔ (A 🡒 B) ∈ T := Iff.rfl

section

variable {L : BDLogic} {𝔸 : Set BDFormula} {T : BDTheory} {A : BDFormula}

-- `(T := T)` is required here and in `impSet_mdpClosed`: otherwise `mdp` resolves against
-- `T.impSet A` instead of `T`.
lemma subset_impSet [T.Of (logic 𝔸)] [T.Mdp] : T ⊆ T.impSet A :=
  fun _ hB => mdp (T := T) (provable_mem (𝔸 := 𝔸) imply₁) hB

lemma self_mem_impSet [T.Of (logic 𝔸)] : A ∈ T.impSet A := by
  show (A 🡒 A) ∈ T;
  exact provable_mem (𝔸 := 𝔸) imp_id;

-- Not an instance: the axiom set `𝔸` behind `T.Of (logic 𝔸)` cannot be recovered from the goal.
lemma impSet_mdpClosed [T.Of (logic 𝔸)] [T.Mdp] : (T.impSet A).Mdp :=
  ⟨fun hBC hB => mdp (T := T) (mdp (T := T) (provable_mem (𝔸 := 𝔸) imply₂) hBC) hB⟩

instance impSet_mdp [T.Of LogicCK] [T.Mdp] : (T.impSet A).Mdp := impSet_mdpClosed (𝔸 := ∅)

instance impSet_of [T.Of LogicCK] [T.Mdp] [T.Of L] : (T.impSet A).Of L :=
  ⟨subset.trans (subset_impSet (𝔸 := ∅))⟩

end

end BDTheory

/-! ## Maximal MP-closed theories avoiding a set of forbidden formulas -/

section Maximal

variable {L : BDLogic} {𝔸 : Set BDFormula} {T Y Z : BDTheory} {A : BDFormula}

/-- Every MP-closed theory `T` of `L` disjoint from `Z` extends to a maximal MP-closed theory of
`L` still disjoint from `Z`. -/
lemma exists_maximal_mdpClosed_avoiding [T.Mdp] [T.Of L] (hdisj : ∀ A ∈ Z, A ∉ T) :
  ∃ Y : BDTheory, T ⊆ Y ∧
  Maximal (fun Y : BDTheory => T ⊆ Y ∧ Y.Mdp ∧ Y.Of L ∧ ∀ A ∈ Z, A ∉ Y) Y := by
  refine zorn_subset_nonempty _ ?_ T ⟨subset_rfl, ‹T.Mdp›, ‹T.Of L›, hdisj⟩;
  rintro c hcS hchain ⟨Y₀, hY₀⟩;
  refine ⟨⋃₀ c, ⟨(hcS hY₀).1.trans (Set.subset_sUnion_of_mem hY₀),
    MdpClosed_sUnion_of_chain hchain fun W hW => (hcS hW).2.1,
    ⟨(hcS hY₀).2.2.1.subset.trans (Set.subset_sUnion_of_mem hY₀)⟩, ?_⟩,
    fun W hW => Set.subset_sUnion_of_mem hW⟩;
  rintro A hA ⟨W, hW, hAW⟩;
  exact (hcS hW).2.2.2 A hA hAW;

/-- If `Y` is maximal among the MP-closed extensions of `T` avoiding `Z`, then every `A ∉ Y` is
refuted by some forbidden formula: `A 🡒 B ∈ Y` for some `B ∈ Z`. -/
lemma exists_imp_mem_of_maximal
  (hmax : Maximal (fun Y : BDTheory => T ⊆ Y ∧ Y.Mdp ∧ Y.Of (logic 𝔸) ∧ ∀ B ∈ Z, B ∉ Y) Y)
  (hA : A ∉ Y) :
  ∃ B ∈ Z, (A 🡒 B) ∈ Y := by
  obtain ⟨hTY, hmdpY, hlogY, -⟩ := hmax.prop;
  have hsub := BDTheory.subset_impSet (𝔸 := 𝔸) (T := Y) (A := A);
  by_contra! hc;
  exact hA (hmax.le_of_ge
    ⟨hTY.trans hsub, BDTheory.impSet_mdpClosed (𝔸 := 𝔸), ⟨hlogY.subset.trans hsub⟩, hc⟩
    hsub (BDTheory.self_mem_impSet (𝔸 := 𝔸)));

/-- A set `Z` of formulas is ⋎-directed (over `𝔸`) if every two members' disjunction is subsumed
by a common member of `Z`. -/
def OrDirected (𝔸 : Set BDFormula) (Z : BDFormulaSet) : Prop :=
  ∀ C ∈ Z, ∀ D ∈ Z, ∃ E ∈ Z, ⊢ᴴ[CK;𝔸] C ⋎ D 🡒 E

end Maximal

/-! ## CKB-specific consequences of the MP-closure -/

section CKB

variable {T U : BDTheory} {A : BDFormula}

/-- If `□A` belongs to the MP-closure of `T ∪ ◇U`, then `A` belongs to `U`. -/
lemma mem_of_box_mem_mdpClosure [T.Of LogicCKB] [T.Mdp] [U.CKB]
  (hdia : ∀ B ∈ T, ◇B ∈ U) (h : □A ∈ BDTheory.mdpClosure (T ∪ ◇U)) : A ∈ U := by
  obtain ⟨Γ, hΓ, C, hC, d⟩ := BDTheory.exists_finite_char (𝔸 := ∅) h;
  have d₁ : (⋀□◇Γ 🡒 ◇C 🡒 ◇(□A)) ∈ LogicCK :=
    imp_trans (imp_trans lconj_box (mdp kBox (nec d))) kDia;
  have h₁ : ⋀□◇Γ ∈ U := by
    apply BDTheory.lconj_mem (𝔸 := ∅);
    intro B hB;
    simp at hB;
    obtain ⟨B, hB, rfl⟩ := hB;
    exact BDTheory.box_dia_mem (hΓ B hB);
  exact BDTheory.mem_of_dia_box_mem (U.mdp (U.mdp (U.subset (L := LogicCK) d₁) h₁) (hdia C hC));

/-- The MP-closure of `T ∪ ◇U` is consistent whenever `U` is. -/
lemma bot_not_mem_mdpClosure [T.Of LogicCKB] [T.Mdp] [U.CKB] (hdia : ∀ B ∈ T, ◇B ∈ U) :
  ⊥ ∉ BDTheory.mdpClosure (T ∪ ◇U) := fun h =>
  U.consistent
    <| mem_of_box_mem_mdpClosure hdia
    <| .mdp (.base (Or.inl (T.subset (L := LogicCK) (efq (A := □⊥))))) h

end CKB

end
