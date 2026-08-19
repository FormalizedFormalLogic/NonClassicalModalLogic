module

public import NCML.Hilbert.Logics
public import NCML.Hilbert.Propositional
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Zorn

@[expose] public section

namespace NCML

open BDFormula BDFormulaList ProvableBDHilbert
open scoped BDFormulaSet

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

lemma provable_mem [T.Of (logic 𝔸)] (h : ⊢ᴴ[CK;𝔸] A) : A ∈ T :=
  subset (L := (ProvableBDHilbert.logic 𝔸)) h

lemma and_mem [T.Of (logic 𝔸)] [T.Mdp] (hA : A ∈ T) (hB : B ∈ T) : A ⋏ B ∈ T :=
  mdp (mdp (provable_mem (𝔸 := 𝔸) andIntro) hA) hB

lemma conj_mem [T.Of (logic 𝔸)] [T.Mdp]
  {Γ : BDFormulaList} (h : ∀ A ∈ Γ, A ∈ T) : Γ.conj ∈ T := by
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

instance prebox_mdp [T.Of LogicCK] [T.Mdp] : Mdp (BDFormulaSet.prebox T) :=
  ⟨fun hAB hA => mdp (T := T) (mdp (T := T) (provable_mem (𝔸 := ∅) kBox) hAB) hA⟩

instance prebox_of [T.Of LogicCKB] : Of LogicCKB (BDFormulaSet.prebox T) :=
  ⟨fun _ hA => T.subset (L := LogicCKB) (nec hA)⟩

lemma dia_or_mem [T.CKB] (h : ◇(A ⋎ B) ∈ T) : ◇A ∈ T ∨ ◇B ∈ T :=
  prime (mdp (T.subset (L := LogicCKB) LogicCKB.provable_DP) h)

lemma dia_bot_not_mem [T.CKB] : ◇(⊥ : BDFormula) ∉ T :=
  fun h => T.consistent (mdp (T.subset (L := LogicCKB) LogicCKB.provable_N) h)

end CKB

end BDTheory


abbrev CKBTheory := { T : BDTheory // T.CKB }


inductive BDTheory.MdpClosure (T : BDTheory) : BDTheory
  | base {A} : A ∈ T → MdpClosure T A
  | mdp {A B} : MdpClosure T (A 🡒 B) → MdpClosure T A → MdpClosure T B

namespace BDTheory

variable {T T₁ T₂ : BDTheory} {X Y : BDFormulaSet} {𝔸 : Set BDFormula} {A : BDFormula}

lemma subset_mpClosure : T ⊆ T.MdpClosure := fun _ => MdpClosure.base

instance : T.MdpClosure.Mdp := ⟨fun hAB hA => .mdp hAB hA⟩


lemma mono_MdpClosure (h : T₁ ⊆ T₂): T₁.MdpClosure ⊆ T₂.MdpClosure := by
  intro A hA;
  induction hA with
  | base hA => exact .base (h hA);
  | mdp _ _ ih₁ ih₂ => exact .mdp ih₁ ih₂;

lemma logic_subset_mpClosure [T.Of (logic 𝔸)] : T.MdpClosure.Of (ProvableBDHilbert.logic 𝔸) := by
  constructor;
  trans T;
  . exact T.subset;
  . exact subset_mpClosure;

/-- Finite characterization of the MP-closure of `T ∪ ◇Y`: every member `A` of the closure is
already derivable from finitely many `◇B` with `B ∈ Y` together with a single `C ∈ T`. -/
lemma exists_finite_char [T.Of (logic 𝔸)] [T.Mdp] (h : A ∈ MdpClosure (T ∪ ◇Y)) :
  ∃ Γ : BDFormulaList, (∀ B ∈ Γ, B ∈ Y) ∧
  ∃ C ∈ T, ⊢ᴴ[CK;𝔸] (conj (Γ.map (◇·)) 🡒 C 🡒 A) := by
  induction h with
  | base hA =>
    rcases hA with hA | ⟨B, hB, rfl⟩;
    · use [];
      constructor;
      . tauto;
      . exact ⟨_, hA, dhyp id_⟩
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
      . rw [List.map_append];
        have t₁ := imp_trans (conj_append_left (Γ₁ := Γ₁.map (◇·)) (Γ₂ := Γ₂.map (◇·))) d₁;
        have t₂ := imp_trans (conj_append_right (Γ₁ := Γ₁.map (◇·)) (Γ₂ := Γ₂.map (◇·))) d₂;
        exact mp_ctx₂
          (imp_trans t₁ (imp_comp_right andElim₁))
          (imp_trans t₂ (imp_comp_right andElim₂));

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

@[simp, grind]
lemma mem_impSet {T : BDTheory} {A B} : B ∈ T.impSet A ↔ (A 🡒 B) ∈ T := Iff.rfl

section

variable {𝔸 : Set BDFormula} {T : BDTheory} {A : BDFormula}

-- `(T := T)` is required here and in `impSet_mdpClosed`: otherwise `mdp` resolves against
-- `T.impSet A` instead of `T`.
lemma subset_impSet [T.Of (logic 𝔸)] [T.Mdp] : T ⊆ T.impSet A :=
  fun _ hB => mdp (T := T) (provable_mem (𝔸 := 𝔸) imply₁) hB

lemma self_mem_impSet [T.Of (logic 𝔸)] : A ∈ T.impSet A := by
  show (A 🡒 A) ∈ T;
  exact provable_mem (𝔸 := 𝔸) id_;

-- Not an instance: the axiom set `𝔸` behind `T.Of (logic 𝔸)` cannot be recovered from the goal.
lemma impSet_mdpClosed [T.Of (logic 𝔸)] [T.Mdp] : (T.impSet A).Mdp :=
  ⟨fun hBC hB => mdp (T := T) (mdp (T := T) (provable_mem (𝔸 := 𝔸) imply₂) hBC) hB⟩

end

end BDTheory

/-! ## Maximal MP-closed theories avoiding a set of forbidden formulas -/

section Maximal

variable {𝔸 : Set BDFormula} {T Y Z : BDTheory} {A : BDFormula}

/-- Every MP-closed `T` disjoint from `Z` extends to a maximal MP-closed theory still disjoint
from `Z`. -/
lemma exists_maximal_mdpClosed_avoiding [T.Mdp] (hdisj : ∀ A ∈ Z, A ∉ T) :
  ∃ Y : BDTheory, T ⊆ Y ∧
  Maximal (fun Y : BDTheory => T ⊆ Y ∧ Y.Mdp ∧ ∀ A ∈ Z, A ∉ Y) Y := by
  refine zorn_subset_nonempty _ ?_ T ⟨subset_rfl, ‹T.Mdp›, hdisj⟩;
  rintro c hcS hchain ⟨Y₀, hY₀⟩;
  refine ⟨⋃₀ c, ⟨(hcS hY₀).1.trans (Set.subset_sUnion_of_mem hY₀),
    MdpClosed_sUnion_of_chain hchain fun W hW => (hcS hW).2.1, ?_⟩,
    fun W hW => Set.subset_sUnion_of_mem hW⟩;
  rintro A hA ⟨W, hW, hAW⟩;
  exact (hcS hW).2.2 A hA hAW;

/-- If `Y` is maximal among the MP-closed extensions of `T` avoiding `Z`, then every `A ∉ Y` is
refuted by some forbidden formula: `A 🡒 B ∈ Y` for some `B ∈ Z`. -/
lemma exists_imp_mem_of_maximal [T.Of (logic 𝔸)]
  (hmax : Maximal (fun Y : BDTheory => T ⊆ Y ∧ Y.Mdp ∧ ∀ B ∈ Z, B ∉ Y) Y) (hA : A ∉ Y) :
  ∃ B ∈ Z, (A 🡒 B) ∈ Y := by
  obtain ⟨hTY, hmdp, -⟩ := hmax.prop;
  have hlogY : Y.Of (logic 𝔸) := ⟨T.subset.trans hTY⟩;
  have hsub := BDTheory.subset_impSet (𝔸 := 𝔸) (T := Y) (A := A);
  by_contra hc;
  exact hA (hmax.le_of_ge ⟨hTY.trans hsub, BDTheory.impSet_mdpClosed (𝔸 := 𝔸),
    fun B hB hmem => hc ⟨B, hB, hmem⟩⟩ hsub (BDTheory.self_mem_impSet (𝔸 := 𝔸)));

end Maximal

/-! ## CKB-specific consequences of the MP-closure -/

section CKB

variable {T Y : BDTheory} {A : BDFormula}

/-- If `□A` belongs to the MP-closure of `T ∪ ◇Y`, then `A` belongs to `Y`.

- [Pac24, Lemma 16] -/
lemma mem_of_box_mem_mpClosure [T.Of LogicCKB] [T.Mdp] [Y.CKB]
  (hdia : ∀ B ∈ T, ◇B ∈ Y) (h : □A ∈ BDTheory.MdpClosure (T ∪ ◇Y)) : A ∈ Y := by
  obtain ⟨Γ, hΓ, C, hC, d⟩ := BDTheory.exists_finite_char (𝔸 := ∅) h;
  have d₁ : (conj ((Γ.map (◇·) : BDFormulaList).map (□·)) 🡒 ◇C 🡒 ◇(□A)) ∈ LogicCK :=
    imp_trans (imp_trans conj_box (mp kBox (nec d))) kDia;
  have h₁ : conj ((Γ.map (◇·) : BDFormulaList).map (□·)) ∈ Y := by
    apply BDTheory.conj_mem (𝔸 := ∅);
    intro B hB;
    simp [List.map_map] at hB;
    obtain ⟨B, hB, rfl⟩ := hB;
    exact BDTheory.box_dia_mem (hΓ B hB);
  exact BDTheory.mem_of_dia_box_mem (Y.mdp (Y.mdp (Y.subset (L := LogicCK) d₁) h₁) (hdia C hC));

/-- The MP-closure of `T ∪ ◇Y` is consistent whenever `Y` is.

- [Pac24, Lemma 16] -/
lemma bot_not_mem_mpClosure [T.Of LogicCKB] [T.Mdp] [Y.CKB] (hdia : ∀ B ∈ T, ◇B ∈ Y) :
  ⊥ ∉ BDTheory.MdpClosure (T ∪ ◇Y) := fun h =>
  Y.consistent
    <| mem_of_box_mem_mpClosure hdia
    <| .mdp (.base (Or.inl (T.subset (L := LogicCK) (efq (A := □⊥))))) h

end CKB

end NCML

end
