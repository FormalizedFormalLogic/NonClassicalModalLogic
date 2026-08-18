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
theorem LogicCKB.subset_IKB : LogicCKB ⊆ LogicIKB := .logic_monotone (by grind)
theorem LogicIK.subset_IKB : LogicIK ⊆ LogicIKB := .logic_monotone (by grind)

open ProvableBDHilbert in
/-- - [Pac24, Theorem 3] -/
theorem LogicCKB.provable_N : (∼◇⊥) ∈ LogicCKB := by
  have h1 : (⊥ 🡒 □⊥) ∈ LogicCKB := efq;
  have h2 : (□(⊥ 🡒 □⊥)) ∈ LogicCKB := nec h1;
  have h3 : (◇⊥ 🡒 ◇(□⊥)) ∈ LogicCKB := mp kDia h2;
  have h4 : (◇(□⊥) 🡒 ⊥) ∈ LogicCKB := axm (by grind);
  exact imp_trans h3 h4;

end
