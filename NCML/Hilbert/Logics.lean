module

public import NCML.Hilbert.Basic

@[expose] public section

open NCML BDFormula

abbrev LogicCK : BDLogic := ProvableBDHilbert.logic ∅

abbrev LogicCKB : BDLogic := ProvableBDHilbert.logic (
  { A 🡒 □◇A | (A) } ∪
  { ◇(□A) 🡒 A | (A) }
)

abbrev LogicIK : BDLogic := ProvableBDHilbert.logic (
  { (◇A 🡒 □B) 🡒 □(A 🡒 B) | (A) (B) } ∪
  { ◇(A ⋎ B) 🡒 ◇A ⋎ ◇B | (A) (B) } ∪
  { ∼◇⊥ }
)

abbrev LogicIKB : BDLogic := ProvableBDHilbert.logic (
  { (◇A 🡒 □B) 🡒 □(A 🡒 B) | (A) (B) } ∪
  { ◇(A ⋎ B) 🡒 ◇A ⋎ ◇B | (A) (B) } ∪
  { ∼◇⊥ } ∪
  { A 🡒 □◇A | (A) } ∪
  { ◇(□A) 🡒 A | (A) }
)

theorem LogicCK.subset_CKB : LogicCK ⊆ LogicCKB := .logic_monotone (by grind)
theorem LogicCK.subset_IK : LogicCK ⊆ LogicIK := .logic_monotone (by grind)
theorem LogicIK.subset_IKB : LogicIK ⊆ LogicIKB := .logic_monotone (by grind)


namespace LogicCKB

open ProvableBDHilbert

theorem subset_IKB : LogicCKB ⊆ LogicIKB := .logic_monotone (by grind)

/-- - [Pac24, Theorem 3] -/
theorem provable_N : (∼◇⊥) ∈ LogicCKB := by
  have h1 : (⊥ 🡒 □⊥) ∈ LogicCKB := efq;
  have h2 : (□(⊥ 🡒 □⊥)) ∈ LogicCKB := nec h1;
  have h3 : (◇⊥ 🡒 ◇(□⊥)) ∈ LogicCKB := mdp kDia h2;
  have h4 : (◇(□⊥) 🡒 ⊥) ∈ LogicCKB := axm (by grind);
  exact imp_trans h3 h4;

/-- - [Pac24, Theorem 3] -/
theorem provable_DP : (◇(A ⋎ B) 🡒 ◇A ⋎ ◇B) ∈ LogicCKB := by
  have h₁ : (A 🡒 □◇A) ∈ LogicCKB := axm (by grind);
  have h₂ : (B 🡒 □◇B) ∈ LogicCKB := axm (by grind);
  have h₃ : (◇(□(◇A ⋎ ◇B)) 🡒 ◇A ⋎ ◇B) ∈ LogicCKB := axm (by grind);
  have h₄ : (□◇A 🡒 □(◇A ⋎ ◇B)) ∈ LogicCKB := box_mono orIntro₁;
  have h₅ : (□◇B 🡒 □(◇A ⋎ ◇B)) ∈ LogicCKB := box_mono orIntro₂;
  have h₆ : (A 🡒 □(◇A ⋎ ◇B)) ∈ LogicCKB := imp_trans h₁ h₄;
  have h₇ : (B 🡒 □(◇A ⋎ ◇B)) ∈ LogicCKB := imp_trans h₂ h₅;
  have h₈ : (A ⋎ B 🡒 □(◇A ⋎ ◇B)) ∈ LogicCKB := mdp (mdp orElim h₆) h₇;
  have h₉ : (◇(A ⋎ B) 🡒 ◇(□(◇A ⋎ ◇B))) ∈ LogicCKB := mdp kDia (nec h₈);
  exact imp_trans h₉ h₃;

end LogicCKB

end
