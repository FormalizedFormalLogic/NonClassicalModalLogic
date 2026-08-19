module

public import NCML.Hilbert.Logics
public import NCML.Hilbert.Propositional
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.Zorn

@[expose] public section

/-!
# MP-closed sets of formulas

Sets of formulas closed under modus ponens (`BDFormulaSet.MdpClosed`), the MP-closure of a set
(`MPClosure`), and the implication set of a theory (`BDFormulaSet.impSet`), the relative deduction
lemma used to build maximal MP-closed sets.

These combine into the two ingredients of a Lindenbaum-style construction, both stated relative to
an arbitrary set `Z` of forbidden formulas: the existence of a maximal MP-closed extension avoiding
`Z` (`exists_maximal_mdpClosed_avoiding`), and the dichotomy that a formula missing from such a
maximal set implies some forbidden formula (`exists_imp_mem_of_maximal`).

For `CKB`, the closure of `X ∪ ◇''Y` is analysed further: a boxed member of it already belongs to
`Y` (`mem_of_box_mem_mpClosure`), and the closure is consistent whenever `Y` is
(`bot_not_mem_mpClosure`).
-/

namespace NCML

open BDFormula BDFormulaList ProvableBDHilbert

namespace BDFormulaSet

/-- `X` is closed under modus ponens. -/
class MdpClosed (X : BDFormulaSet) : Prop where
  mdp : ∀ {A B}, (A 🡒 B) ∈ X → A ∈ X → B ∈ X

export MdpClosed (mdp)

section General

variable {𝔸 : Set BDFormula} {X : BDFormulaSet} {A B C D : BDFormula}

lemma provable_mem (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) (h : ProvableBDHilbert 𝔸 A) : A ∈ X :=
  hlog h

lemma and_mem (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) [X.MdpClosed] (hA : A ∈ X) (hB : B ∈ X) :
    A ⋏ B ∈ X :=
  mdp (mdp (provable_mem hlog andIntro) hA) hB

lemma conj_mem (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) [X.MdpClosed] {Γ : BDFormulaList}
    (h : ∀ A ∈ Γ, A ∈ X) : Γ.conj ∈ X := by
  induction Γ with
  | nil => exact provable_mem hlog verum;
  | cons A Γ ih => exact and_mem hlog (h A (by simp)) (ih fun B hB => h B (by simp [hB]));

lemma or_elim_mem (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) [X.MdpClosed]
    (hAC : (A 🡒 C) ∈ X) (hBC : (B 🡒 C) ∈ X) (hAB : (A ⋎ B) ∈ X) : C ∈ X :=
  mdp (mdp (mdp (provable_mem hlog orElim) hAC) hBC) hAB

/-- Disjunction elimination through a `□`: two implications into boxed formulas, applied to a
disjunction, yield the box of the disjunction. A routine closure lemma in the family of
`or_elim_mem`, not isolated as a result anywhere in the literature. -/
lemma box_or_mem (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) [X.MdpClosed]
    (h₁ : (A 🡒 □C) ∈ X) (h₂ : (B 🡒 □D) ∈ X) (h : (A ⋎ B) ∈ X) : □(C ⋎ D) ∈ X :=
  or_elim_mem hlog (mdp (provable_mem hlog (imp_comp_left box_or_inl)) h₁)
    (mdp (provable_mem hlog (imp_comp_left box_or_inr)) h₂) h

end General

section CKB

variable {X : BDFormulaSet} {A : BDFormula}

lemma box_dia_mem (hlog : LogicCKB ⊆ X) [X.MdpClosed] (hA : A ∈ X) : □◇A ∈ X :=
  mdp (hlog (ProvableBDHilbert.axm (Or.inl ⟨A, rfl⟩))) hA

lemma mem_of_dia_box_mem (hlog : LogicCKB ⊆ X) [X.MdpClosed] (h : ◇(□A) ∈ X) : A ∈ X :=
  mdp (hlog (ProvableBDHilbert.axm (Or.inr ⟨A, rfl⟩))) h

end CKB

end BDFormulaSet

/-! ## MP-closure -/

/-- The closure of `X` under modus ponens. -/
inductive MPClosure (X : BDFormulaSet) : BDFormula → Prop
  | base {A} : A ∈ X → MPClosure X A
  | mp {A B} : MPClosure X (A 🡒 B) → MPClosure X A → MPClosure X B

lemma subset_mpClosure (X : BDFormulaSet) : X ⊆ MPClosure X := fun _ => MPClosure.base

instance MPClosure.mdpClosed (X : BDFormulaSet) : BDFormulaSet.MdpClosed (MPClosure X) :=
  ⟨fun hAB hA => MPClosure.mp hAB hA⟩

lemma MPClosure.mono {X Y : BDFormulaSet} (h : X ⊆ Y) {A} (hA : MPClosure X A) : MPClosure Y A := by
  induction hA with
  | base hA => exact MPClosure.base (h hA);
  | mp _ _ ih₁ ih₂ => exact MPClosure.mp ih₁ ih₂;

lemma logic_subset_mpClosure {𝔸 : Set BDFormula} {X : BDFormulaSet}
    (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) : ProvableBDHilbert.logic 𝔸 ⊆ MPClosure X :=
  hlog.trans (subset_mpClosure X)

/-- Finite characterization of the MP-closure of `X ∪ ◇''Y`: every member `A` of the closure is
already derivable from finitely many `◇B` with `B ∈ Y` together with a single `C ∈ X`. -/
lemma MPClosure.exists_finite_char {𝔸 : Set BDFormula} {X Y : BDFormulaSet} {A : BDFormula}
    (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) [X.MdpClosed]
    (h : MPClosure (X ∪ (◇·) '' Y) A) :
    ∃ Γ : BDFormulaList, (∀ B ∈ Γ, B ∈ Y) ∧
      ∃ C ∈ X, ProvableBDHilbert 𝔸 (conj (Γ.map (◇·)) 🡒 C 🡒 A) := by
  induction h with
  | base hA =>
    rcases hA with hA | ⟨B, hB, rfl⟩;
    · exact ⟨[], by simp, _, hA, dhyp id_⟩;
    · exact ⟨[B], by simpa using hB, ⊤, BDFormulaSet.provable_mem hlog verum,
        imp_trans andElim₁ imply₁⟩;
  | mp _ _ ih₁ ih₂ =>
    obtain ⟨Γ₁, hΓ₁, C₁, hC₁, d₁⟩ := ih₁;
    obtain ⟨Γ₂, hΓ₂, C₂, hC₂, d₂⟩ := ih₂;
    have t₁ := imp_trans (conj_append_left (Γ₁ := Γ₁.map (◇·)) (Γ₂ := Γ₂.map (◇·))) d₁;
    have t₂ := imp_trans (conj_append_right (Γ₁ := Γ₁.map (◇·)) (Γ₂ := Γ₂.map (◇·))) d₂;
    refine ⟨Γ₁ ++ Γ₂, by grind, C₁ ⋏ C₂, BDFormulaSet.and_mem hlog hC₁ hC₂, ?_⟩;
    rw [List.map_append];
    exact mp_ctx₂ (imp_trans t₁ (imp_comp_right andElim₁))
      (imp_trans t₂ (imp_comp_right andElim₂));

/-- The union of a chain of MP-closed sets is MP-closed: given `(A 🡒 B) ∈ X₁` and `A ∈ X₂` with
`X₁, X₂` in the chain, one of `X₁ ⊆ X₂` or `X₂ ⊆ X₁` holds, so both facts land in the larger set
and MP-closedness of that set finishes the argument. -/
lemma MdpClosed_sUnion_of_chain {c : Set BDFormulaSet} (hc : IsChain (· ⊆ ·) c)
    (h : ∀ X ∈ c, BDFormulaSet.MdpClosed X) : BDFormulaSet.MdpClosed (⋃₀ c) := by
  constructor;
  rintro A B ⟨X₁, hX₁c, hAB⟩ ⟨X₂, hX₂c, hA⟩;
  rcases hc.total hX₁c hX₂c with hsub | hsub;
  · exact ⟨X₂, hX₂c, (h X₂ hX₂c).mdp (hsub hAB) hA⟩;
  · exact ⟨X₁, hX₁c, (h X₁ hX₁c).mdp hAB (hsub hA)⟩;

/-! ## The implication set -/

namespace BDFormulaSet

/-- The formulas `B` with `A 🡒 B ∈ X`, i.e. `X` "under the assumption `A`". -/
def impSet (X : BDFormulaSet) (A : BDFormula) : BDFormulaSet := { B | (A 🡒 B) ∈ X }

@[simp, grind]
lemma mem_impSet {X : BDFormulaSet} {A B} : B ∈ X.impSet A ↔ (A 🡒 B) ∈ X := Iff.rfl

section

variable {𝔸 : Set BDFormula} {X : BDFormulaSet} {A : BDFormula}

-- Here and in `impSet_mdpClosed`, `(X := X)` is required: the expected type is a membership in
-- `X.impSet A`, so `mdp` would otherwise be resolved for `X.impSet A` rather than for `X`.
lemma subset_impSet (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) [X.MdpClosed] : X ⊆ X.impSet A :=
  fun _ hB => mdp (X := X) (provable_mem hlog imply₁) hB

lemma self_mem_impSet (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) : A ∈ X.impSet A := by
  show (A 🡒 A) ∈ X;
  exact provable_mem hlog id_;

-- Not an instance: the axiom set `𝔸` behind `hlog` cannot be recovered from the goal.
lemma impSet_mdpClosed (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X) [X.MdpClosed] :
    (X.impSet A).MdpClosed :=
  ⟨fun hBC hB => mdp (X := X) (mdp (X := X) (provable_mem hlog imply₂) hBC) hB⟩

end

end BDFormulaSet

/-! ## Maximal MP-closed sets avoiding a set of forbidden formulas -/

section Maximal

variable {𝔸 : Set BDFormula} {X Y Z : BDFormulaSet} {A : BDFormula}

/-- Every MP-closed `X` disjoint from `Z` extends to a maximal MP-closed set still disjoint
from `Z`. -/
lemma exists_maximal_mdpClosed_avoiding [X.MdpClosed] (hdisj : ∀ A ∈ Z, A ∉ X) :
    ∃ Y, X ⊆ Y ∧ Maximal (fun Y => X ⊆ Y ∧ Y.MdpClosed ∧ ∀ A ∈ Z, A ∉ Y) Y := by
  refine zorn_subset_nonempty _ ?_ X ⟨subset_rfl, ‹X.MdpClosed›, hdisj⟩;
  rintro c hcS hchain ⟨Y₀, hY₀⟩;
  refine ⟨⋃₀ c, ⟨(hcS hY₀).1.trans (Set.subset_sUnion_of_mem hY₀),
    MdpClosed_sUnion_of_chain hchain fun W hW => (hcS hW).2.1, ?_⟩,
    fun W hW => Set.subset_sUnion_of_mem hW⟩;
  rintro A hA ⟨W, hW, hAW⟩;
  exact (hcS hW).2.2 A hA hAW;

/-- If `Y` is maximal among the MP-closed extensions of `X` avoiding `Z`, then every `A ∉ Y` is
refuted by some forbidden formula: `A 🡒 B ∈ Y` for some `B ∈ Z`. -/
lemma exists_imp_mem_of_maximal (hlog : ProvableBDHilbert.logic 𝔸 ⊆ X)
    (hmax : Maximal (fun Y => X ⊆ Y ∧ Y.MdpClosed ∧ ∀ B ∈ Z, B ∉ Y) Y) (hA : A ∉ Y) :
    ∃ B ∈ Z, (A 🡒 B) ∈ Y := by
  -- `hmp` is unused by name, but is what instance resolution picks up below.
  obtain ⟨hXY, hmp, -⟩ := hmax.prop;
  have hlogY := hlog.trans hXY;
  have hsub := BDFormulaSet.subset_impSet (A := A) hlogY;
  by_contra hc;
  exact hA (hmax.le_of_ge ⟨hXY.trans hsub, BDFormulaSet.impSet_mdpClosed hlogY,
    fun B hB hmem => hc ⟨B, hB, hmem⟩⟩ hsub (BDFormulaSet.self_mem_impSet hlogY));

end Maximal

/-! ## CKB-specific consequences of the MP-closure -/

section CKB

variable {X Y : BDFormulaSet} {A : BDFormula}

/-- If `□A` belongs to the MP-closure of `X ∪ ◇''Y`, then `A` belongs to `Y`.

This is the derivation chain forming the first half of the cited proof.

- [Pac24, Lemma 16] -/
lemma mem_of_box_mem_mpClosure (hXl : LogicCKB ⊆ X) [X.MdpClosed] (hYl : LogicCKB ⊆ Y)
    [Y.MdpClosed] (hdia : ∀ B ∈ X, ◇B ∈ Y) (h : MPClosure (X ∪ (◇·) '' Y) (□A)) : A ∈ Y := by
  obtain ⟨Γ, hΓ, C, hC, d⟩ := MPClosure.exists_finite_char hXl h;
  have d₁ : (conj ((Γ.map (◇·)).map (□·)) 🡒 ◇C 🡒 ◇(□A)) ∈ LogicCKB :=
    imp_trans (imp_trans conj_box (mp kBox (nec d))) kDia;
  have h₁ : conj ((Γ.map (◇·)).map (□·)) ∈ Y := by
    refine BDFormulaSet.conj_mem hYl ?_;
    intro B hB;
    simp [List.map_map] at hB;
    obtain ⟨B, hB, rfl⟩ := hB;
    exact BDFormulaSet.box_dia_mem hYl (hΓ B hB);
  exact BDFormulaSet.mem_of_dia_box_mem hYl
    (BDFormulaSet.mdp (BDFormulaSet.mdp (hYl d₁) h₁) (hdia C hC));

/-- The MP-closure of `X ∪ ◇''Y` is consistent whenever `Y` is.

- [Pac24, Lemma 16] -/
lemma bot_not_mem_mpClosure (hXl : LogicCKB ⊆ X) [X.MdpClosed] (hYl : LogicCKB ⊆ Y)
    [Y.MdpClosed] (hdia : ∀ B ∈ X, ◇B ∈ Y) (hbot : ⊥ ∉ Y) :
    ⊥ ∉ (show BDFormulaSet from MPClosure (X ∪ (◇·) '' Y)) := fun h =>
  hbot <| mem_of_box_mem_mpClosure hXl hYl hdia <|
    MPClosure.mp (MPClosure.base (Or.inl (hXl (efq (A := □⊥))))) h

end CKB

end NCML

end
