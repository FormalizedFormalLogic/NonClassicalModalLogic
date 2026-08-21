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

variable {L : BDLogic} {T : BDTheory} {A B C D : BDFormula}

instance logic_mdp [BDLogic.Mdp L] : Mdp L := ⟨BDLogic.mdp⟩

instance of_self : Of T T := ⟨subset_rfl⟩

-- Not an instance: the logic `L` behind `T.Of L` cannot be recovered from the goal.
lemma of_logicCK [L.CK] [T.Of L] : T.Of LogicCK :=
  ⟨(BDLogic.logicCK_subset (L := L)).trans (subset (L := L) (T := T))⟩

lemma provable_mem [T.Of LogicCK] (h : A ∈ LogicCK) : A ∈ T := subset (L := LogicCK) h

lemma and_mem [T.Of LogicCK] [T.Mdp] (hA : A ∈ T) (hB : B ∈ T) : A ⋏ B ∈ T :=
  mdp (mdp (provable_mem andIntro) hA) hB

lemma lconj_mem [T.Of LogicCK] [T.Mdp] {Γ : BDFormulaList} (h : ∀ A ∈ Γ, A ∈ T) : ⋀Γ ∈ T := by
  induction Γ with
  | nil => exact provable_mem verum;
  | cons A Γ ih =>
    apply and_mem;
    . simp_all;
    . exact ih (by grind);

lemma or_elim_mem [T.Of LogicCK] [T.Mdp]
  (hAC : (A 🡒 C) ∈ T) (hBC : (B 🡒 C) ∈ T) (hAB : (A ⋎ B) ∈ T) : C ∈ T :=
  mdp (mdp (mdp (provable_mem orElim) hAC) hBC) hAB

lemma box_or_mem [T.Of LogicCK] [T.Mdp]
  (h₁ : (A 🡒 □C) ∈ T) (h₂ : (B 🡒 □D) ∈ T) (h : (A ⋎ B) ∈ T) : □(C ⋎ D) ∈ T :=
  or_elim_mem
    (mdp (provable_mem (imp_comp_left box_or_inl)) h₁)
    (mdp (provable_mem (imp_comp_left box_or_inr)) h₂)
    h

lemma eq_univ_of_bot_mem [T.Of LogicCK] [T.Mdp] (h : ⊥ ∈ T) : T = Set.univ :=
  Set.eq_univ_of_forall fun _ => mdp (T := T) (provable_mem efq) h

instance prebox_mdp [T.Of LogicCK] [T.Mdp] : Mdp (□⁻¹T) :=
  ⟨fun hAB hA => mdp (T := T) (mdp (T := T) (provable_mem kBox) hAB) hA⟩

instance prebox_of [L.Nec] [T.Of L] : Of L (□⁻¹T) :=
  ⟨fun _ hA => subset (L := L) (T := T) (BDLogic.nec hA)⟩

section CKB

class CKB (T : BDTheory) extends T.Mdp, T.Prime, T.Consistent, T.Of LogicCKB where

instance [T.Of LogicCKB] : T.Of LogicCK := of_logicCK (L := LogicCKB)

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

lemma dia_or_mem [T.CKB] (h : ◇(A ⋎ B) ∈ T) : ◇A ∈ T ∨ ◇B ∈ T :=
  prime (mdp (T.subset (L := LogicCKB) LogicCKB.provable_DP) h)

lemma dia_bot_not_mem [T.CKB] : ◇(⊥ : BDFormula) ∉ T :=
  fun h => T.consistent (mdp (T.subset (L := LogicCKB) LogicCKB.provable_N) h)

end CKB

instance [T.Of LogicCKTDia] : T.Of LogicCK := of_logicCK (L := LogicCKTDia)

end BDTheory


abbrev CKBTheory := { T : BDTheory // T.CKB }


inductive BDTheory.mdpClosure (T : BDTheory) : BDTheory
  | base {A} : A ∈ T → mdpClosure T A
  | mdp {A B} : mdpClosure T (A 🡒 B) → mdpClosure T A → mdpClosure T B

namespace BDTheory

variable {T T₁ T₂ : BDTheory} {X Y : BDFormulaSet} {L : BDLogic} {A : BDFormula}

lemma subset_mdpClosure : T ⊆ T.mdpClosure := fun _ => mdpClosure.base

instance : T.mdpClosure.Mdp := ⟨.mdp⟩


lemma mono_mdpClosure (h : T₁ ⊆ T₂): T₁.mdpClosure ⊆ T₂.mdpClosure := by
  intro A hA;
  induction hA with
  | base hA => exact .base (h hA);
  | mdp _ _ ih₁ ih₂ => exact .mdp ih₁ ih₂;

instance mdpClosure_of [T.Of L] : T.mdpClosure.Of L :=
  ⟨(subset (L := L) (T := T)).trans subset_mdpClosure⟩

/-- Finite characterization of the MP-closure of `T ∪ ◇Y`: every member `A` of the closure is
already derivable from finitely many `◇B` with `B ∈ Y` together with a single `C ∈ T`. -/
lemma exists_finite_char [T.Of LogicCK] [T.Mdp] (h : A ∈ mdpClosure (T ∪ ◇Y)) :
  ∃ Γ : BDFormulaList, (∀ B ∈ Γ, B ∈ Y) ∧
  ∃ C ∈ T, (⋀◇Γ 🡒 C 🡒 A) ∈ LogicCK := by
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
        . exact provable_mem verum;
        . exact imp_trans andElim₁ imply₁;
  | mdp _ _ ih₁ ih₂ =>
    obtain ⟨Γ₁, hΓ₁, C₁, hC₁, d₁⟩ := ih₁;
    obtain ⟨Γ₂, hΓ₂, C₂, hC₂, d₂⟩ := ih₂;
    use Γ₁ ++ Γ₂;
    constructor;
    . grind;
    . use C₁ ⋏ C₂;
      constructor;
      . exact and_mem hC₁ hC₂;
      . rw [dia_append];
        have t₁ := imp_trans (lconj_append_left (Γ₁ := ◇Γ₁) (Γ₂ := ◇Γ₂)) d₁;
        have t₂ := imp_trans (lconj_append_right (Γ₁ := ◇Γ₁) (Γ₂ := ◇Γ₂)) d₂;
        exact mdp_ctx₂
          (imp_trans t₁ (imp_comp_right andElim₁))
          (imp_trans t₂ (imp_comp_right andElim₂));

/-- Finite characterization of the MP-closure of a union `T₁ ∪ T₂`: every member `A` of the
closure is entailed from a single `D ∈ T₁` and a single `E ∈ T₂`. -/
lemma mdpClosure_union_finite_char [T₁.Of LogicCK] [T₁.Mdp] [T₂.Of LogicCK] [T₂.Mdp]
  (h : A ∈ mdpClosure (T₁ ∪ T₂)) : ∃ D ∈ T₁, ∃ E ∈ T₂, (D 🡒 E 🡒 A) ∈ LogicCK := by
  induction h with
  | base hA =>
    rcases hA with hA | hA;
    · exact ⟨_, hA, ⊤, provable_mem verum, imply₁⟩;
    · exact ⟨⊤, provable_mem verum, _, hA, dhyp imp_id⟩;
  | mdp _ _ ih₁ ih₂ =>
    obtain ⟨D₁, hD₁, E₁, hE₁, d₁⟩ := ih₁;
    obtain ⟨D₂, hD₂, E₂, hE₂, d₂⟩ := ih₂;
    refine ⟨D₁ ⋏ D₂, ?_, E₁ ⋏ E₂, ?_, ?_⟩;
    . exact and_mem hD₁ hD₂
    . exact and_mem hE₁ hE₂
    . exact mdp_ctx₂
              (imp_trans (imp_trans andElim₁ d₁) (imp_comp_right andElim₁))
              (imp_trans (imp_trans andElim₂ d₂) (imp_comp_right andElim₂));

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

variable {L : BDLogic} {T : BDTheory} {A : BDFormula}

-- `(T := T)` is required here and in `impSet_mdp`: otherwise `mdp` resolves against
-- `T.impSet A` instead of `T`.
lemma subset_impSet [T.Of LogicCK] [T.Mdp] : T ⊆ T.impSet A :=
  fun _ hB => mdp (T := T) (provable_mem imply₁) hB

lemma self_mem_impSet [T.Of LogicCK] : A ∈ T.impSet A := provable_mem (T := T) imp_id

instance impSet_mdp [T.Of LogicCK] [T.Mdp] : (T.impSet A).Mdp :=
  ⟨fun hBC hB => mdp (T := T) (mdp (T := T) (provable_mem imply₂) hBC) hB⟩

instance impSet_of [T.Of LogicCK] [T.Mdp] [T.Of L] : (T.impSet A).Of L :=
  ⟨subset.trans subset_impSet⟩

end

end BDTheory

/-! ## Maximal MP-closed theories avoiding a set of forbidden formulas -/

section Maximal

variable {L : BDLogic} {T Y Z : BDTheory} {A B : BDFormula}

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
lemma exists_imp_mem_of_maximal [L.CK]
  (hmax : Maximal (fun Y : BDTheory => T ⊆ Y ∧ Y.Mdp ∧ Y.Of L ∧ ∀ B ∈ Z, B ∉ Y) Y)
  (hA : A ∉ Y) :
  ∃ B ∈ Z, (A 🡒 B) ∈ Y := by
  obtain ⟨hTY, hmdpY, hlogY, -⟩ := hmax.prop;
  have := BDTheory.of_logicCK (L := L) (T := Y);
  have hsub := BDTheory.subset_impSet (T := Y) (A := A);
  by_contra! hc;
  exact hA (hmax.le_of_ge
    ⟨hTY.trans hsub, BDTheory.impSet_mdp, ⟨hlogY.subset.trans hsub⟩, hc⟩
    hsub BDTheory.self_mem_impSet);

/-- A set `Z` of formulas is ⋎-directed (over `L`) if every two members' disjunction is subsumed
by a common member of `Z`. -/
def OrDirected (L : BDLogic) (Z : BDFormulaSet) : Prop :=
  ∀ C ∈ Z, ∀ D ∈ Z, ∃ E ∈ Z, (C ⋎ D 🡒 E) ∈ L

/-- A maximal MP-closed extension of `T` avoiding an ⋎-directed `Z` is prime. -/
lemma prime_of_maximal_avoiding_orDirected [L.CK] (hdir : OrDirected L Z)
  (hmax : Maximal (fun Y : BDTheory => T ⊆ Y ∧ Y.Mdp ∧ Y.Of L ∧ ∀ B ∈ Z, B ∉ Y) Y)
  (h : A ⋎ B ∈ Y) : A ∈ Y ∨ B ∈ Y := by
  by_contra! hc;
  obtain ⟨-, hmdpY, hlogY, havoid⟩ := hmax.prop;
  have := BDTheory.of_logicCK (L := L) (T := Y);
  obtain ⟨C, hC, h₁⟩ := exists_imp_mem_of_maximal hmax hc.1;
  obtain ⟨D, hD, h₂⟩ := exists_imp_mem_of_maximal hmax hc.2;
  have h₃ : (A 🡒 C ⋎ D) ∈ Y := Y.mdp (BDTheory.provable_mem (imp_comp_left orIntro₁)) h₁;
  have h₄ : (B 🡒 C ⋎ D) ∈ Y := Y.mdp (BDTheory.provable_mem (imp_comp_left orIntro₂)) h₂;
  have h₅ : C ⋎ D ∈ Y := BDTheory.or_elim_mem h₃ h₄ h;
  obtain ⟨E, hE, hCD⟩ := hdir C hC D hD;
  exact havoid E hE (Y.mdp (hlogY.subset hCD) h₅);

/-- General prime Lindenbaum lemma: an MP-closed theory of `L` disjoint from an ⋎-directed `Z`
extends to a prime MP-closed theory of `L` still disjoint from `Z`. -/
lemma exists_prime_mdpClosed_avoiding [L.CK] [T.Mdp] [T.Of L]
  (hdir : OrDirected L Z) (hdisj : ∀ B ∈ Z, B ∉ T) :
  ∃ Y : BDTheory, T ⊆ Y ∧ Y.Mdp ∧ Y.Prime ∧ Y.Of L ∧ ∀ B ∈ Z, B ∉ Y := by
  obtain ⟨Y, hTY, hmax⟩ := exists_maximal_mdpClosed_avoiding (L := L) hdisj;
  obtain ⟨-, hmdpY, hlogY, havoid⟩ := hmax.prop;
  exact ⟨Y, hTY, hmdpY, ⟨prime_of_maximal_avoiding_orDirected hdir hmax⟩, hlogY, havoid⟩;

end Maximal

/-! ## Disjunctive avoid sets -/

section Disj

/-- The disjunctions of nonempty finite sublists of `Θ`. -/
def disjSet (Θ : BDFormulaSet) : BDFormulaSet :=
  { B | ∃ K : BDFormulaList, K ≠ [] ∧ (∀ A ∈ K, A ∈ Θ) ∧ B = ⋁K }

/-- The `◇`-images of `disjSet Θ`. -/
def diaDisjSet (Θ : BDFormulaSet) : BDFormulaSet := ◇(disjSet Θ)

variable {L : BDLogic} [L.CK] {B : BDFormula}

lemma orDirected_singleton : OrDirected L {B} := by
  rintro C rfl D rfl;
  exact ⟨D, rfl, BDLogic.logicCK_subset (or_imp imp_id imp_id)⟩;

variable {Θ : BDFormulaSet}

lemma orDirected_disjSet : OrDirected L (disjSet Θ) := by
  rintro C ⟨K₁, hK₁ne, hK₁sub, rfl⟩ D ⟨K₂, hK₂ne, hK₂sub, rfl⟩;
  refine ⟨⋁(K₁ ++ K₂), ⟨K₁ ++ K₂, by simp [hK₁ne], ?_, rfl⟩,
    BDLogic.logicCK_subset (or_imp ldisj_append_left ldisj_append_right)⟩;
  intro A hA;
  rcases List.mem_append.mp hA with hA | hA;
  · exact hK₁sub A hA;
  · exact hK₂sub A hA;

variable {X : BDFormulaSet}

lemma orDirected_of_or_mem (hor : ∀ {B C}, B ∈ X → C ∈ X → B ⋎ C ∈ X) : OrDirected L X := by
  rintro C hC D hD;
  exact ⟨C ⋎ D, hor hC hD, BDLogic.logicCK_subset imp_id⟩;

/-- A set of formulas closed under `⋎` and under provably stronger formulas contains the
disjunctions of its nonempty finite sublists. -/
lemma disjSet_subset_of_or_mem
  (hor : ∀ {B C}, B ∈ X → C ∈ X → B ⋎ C ∈ X)
  (himp : ∀ {B C}, (B 🡒 C) ∈ LogicCK → C ∈ X → B ∈ X) :
  disjSet X ⊆ X := by
  rintro B ⟨K, hne, hsub, rfl⟩;
  induction K with
  | nil => exact absurd rfl hne;
  | cons C K ih =>
    rcases eq_or_ne K [] with rfl | hK;
    · exact himp (BDLogic.logicCK_subset (or_imp imp_id efq)) (hsub C (by simp));
    · exact hor (hsub C (by simp)) (ih hK fun A hA => hsub A (by simp [hA]));

@[simp]
lemma disjSet_empty : disjSet (∅ : BDFormulaSet) = ∅ := by
  ext B;
  simp only [Set.mem_empty_iff_false, iff_false];
  rintro ⟨K, hne, hsub, rfl⟩;
  cases K with
  | nil => exact hne rfl;
  | cons C K => exact hsub C (by simp);

@[simp]
lemma diaDisjSet_empty : diaDisjSet (∅ : BDFormulaSet) = ∅ := by
  simp [diaDisjSet, BDFormulaSet.dia];

lemma orDirected_diaDisjSet : OrDirected L (diaDisjSet Θ) := by
  rintro C ⟨B₁, ⟨K₁, hK₁ne, hK₁sub, rfl⟩, rfl⟩ D ⟨B₂, ⟨K₂, hK₂ne, hK₂sub, rfl⟩, rfl⟩;
  refine ⟨◇(⋁(K₁ ++ K₂)), ⟨⋁(K₁ ++ K₂), ⟨K₁ ++ K₂, by simp [hK₁ne], ?_, rfl⟩, rfl⟩,
    BDLogic.logicCK_subset (or_imp (dia_mono ldisj_append_left) (dia_mono ldisj_append_right))⟩;
  intro A hA;
  rcases List.mem_append.mp hA with hA | hA;
  · exact hK₁sub A hA;
  · exact hK₂sub A hA;

end Disj

/-! ## CKB-specific consequences of the MP-closure -/

section CKB

variable {T U : BDTheory} {A : BDFormula}

/-- If `□A` belongs to the MP-closure of `T ∪ ◇U`, then `A` belongs to `U`. -/
lemma mem_of_box_mem_mdpClosure [T.Of LogicCKB] [T.Mdp] [U.CKB]
  (hdia : ∀ B ∈ T, ◇B ∈ U) (h : □A ∈ BDTheory.mdpClosure (T ∪ ◇U)) : A ∈ U := by
  obtain ⟨Γ, hΓ, C, hC, d⟩ := BDTheory.exists_finite_char h;
  have d₁ : (⋀□◇Γ 🡒 ◇C 🡒 ◇(□A)) ∈ LogicCK :=
    imp_trans (imp_trans lconj_box (mdp kBox (nec d))) kDia;
  have h₁ : ⋀□◇Γ ∈ U := by
    apply BDTheory.lconj_mem;
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
