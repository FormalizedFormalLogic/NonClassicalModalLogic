module

public import NCML.Hilbert.Basic

@[expose] public section

open BDFormula

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

abbrev LogicCKTBox : BDLogic := ProvableBDHilbert.logic { □A 🡒 A | (A) }

abbrev LogicCKTDia : BDLogic := ProvableBDHilbert.logic { A 🡒 ◇A | (A) }

abbrev LogicCKD : BDLogic := ProvableBDHilbert.logic { □A 🡒 ◇A | (A) }

theorem LogicCK.subset_CKB : LogicCK ⊆ LogicCKB := .logic_monotone (by grind)
theorem LogicCK.subset_IK : LogicCK ⊆ LogicIK := .logic_monotone (by grind)
theorem LogicIK.subset_IKB : LogicIK ⊆ LogicIKB := .logic_monotone (by grind)
theorem LogicCK.subset_CKTBox : LogicCK ⊆ LogicCKTBox := .logic_monotone (by grind)
theorem LogicCK.subset_CKTDia : LogicCK ⊆ LogicCKTDia := .logic_monotone (by grind)
theorem LogicCK.subset_CKD : LogicCK ⊆ LogicCKD := .logic_monotone (by grind)

theorem ProvableBDHilbert.provable_D_of_diaTop
    {𝔸 : Set BDFormula} {A : BDFormula} (h : ⊢ᴴ[CK;𝔸] (◇⊤ : BDFormula)) :
    ⊢ᴴ[CK;𝔸] □A 🡒 ◇A :=
  ProvableBDHilbert.mdp_ctx (ProvableBDHilbert.imp_trans (ProvableBDHilbert.box_mono
    ProvableBDHilbert.imply₁) ProvableBDHilbert.kDia) (ProvableBDHilbert.dhyp h)


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


namespace LogicCKTBox

open ProvableBDHilbert

theorem provable_TBox : (□A 🡒 A) ∈ LogicCKTBox := axm (by grind)

theorem provable_not_box_bot : (∼□⊥) ∈ LogicCKTBox := provable_TBox (A := ⊥)

end LogicCKTBox


namespace LogicCKTDia

open ProvableBDHilbert

theorem provable_TDia : (A 🡒 ◇A) ∈ LogicCKTDia := axm (by grind)

theorem provable_diaTop : (◇⊤) ∈ LogicCKTDia := mdp (provable_TDia (A := ⊤)) verum

theorem provable_D : (□A 🡒 ◇A) ∈ LogicCKTDia := provable_D_of_diaTop provable_diaTop

end LogicCKTDia


namespace LogicCKD

open ProvableBDHilbert

theorem provable_D : (□A 🡒 ◇A) ∈ LogicCKD := axm (by grind)

theorem provable_diaTop : (◇⊤) ∈ LogicCKD := mdp (provable_D (A := ⊤)) (nec verum)

end LogicCKD

end
