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

abbrev LogicCKT : BDLogic := ProvableBDHilbert.logic (
  { □A 🡒 A | (A) } ∪
  { A 🡒 ◇A | (A) }
)

abbrev LogicCKD : BDLogic := ProvableBDHilbert.logic { □A 🡒 ◇A | (A) }

abbrev LogicCKPDia : BDLogic := ProvableBDHilbert.logic { ◇⊤ }

abbrev LogicCK4Box : BDLogic := ProvableBDHilbert.logic { □A 🡒 □□A | (A) }

abbrev LogicCK4Dia : BDLogic := ProvableBDHilbert.logic { ◇◇A 🡒 ◇A | (A) }

abbrev LogicCK4 : BDLogic := ProvableBDHilbert.logic (
  { □A 🡒 □□A | (A) } ∪
  { ◇◇A 🡒 ◇A | (A) }
)

abbrev LogicCS4 : BDLogic := ProvableBDHilbert.logic (
  { □A 🡒 A | (A) } ∪
  { A 🡒 ◇A | (A) } ∪
  { □A 🡒 □□A | (A) } ∪
  { ◇◇A 🡒 ◇A | (A) }
)

namespace BDLogic

class CK (L : BDLogic) : Prop extends Mdp L, Nec L where
  logicCK_subset : LogicCK ⊆ L
export CK (logicCK_subset)

instance {𝔸 : Set BDFormula} : CK (ProvableBDHilbert.logic 𝔸) where
  logicCK_subset := ProvableBDHilbert.logic_monotone (Set.empty_subset 𝔸)

end BDLogic

lemma LogicCK.subset_CKB : LogicCK ⊆ LogicCKB := .logic_monotone (by grind)
lemma LogicCK.subset_IK : LogicCK ⊆ LogicIK := .logic_monotone (by grind)
lemma LogicIK.subset_IKB : LogicIK ⊆ LogicIKB := .logic_monotone (by grind)
lemma LogicCK.subset_CKTBox : LogicCK ⊆ LogicCKTBox := .logic_monotone (by grind)
lemma LogicCK.subset_CKTDia : LogicCK ⊆ LogicCKTDia := .logic_monotone (by grind)
lemma LogicCK.subset_CKT : LogicCK ⊆ LogicCKT := .logic_monotone (by grind)
lemma LogicCK.subset_CKD : LogicCK ⊆ LogicCKD := .logic_monotone (by grind)
lemma LogicCK.subset_CKPDia : LogicCK ⊆ LogicCKPDia := .logic_monotone (by grind)
lemma LogicCK.subset_CK4Box : LogicCK ⊆ LogicCK4Box := .logic_monotone (by grind)
lemma LogicCK.subset_CK4Dia : LogicCK ⊆ LogicCK4Dia := .logic_monotone (by grind)
lemma LogicCK.subset_CK4 : LogicCK ⊆ LogicCK4 := .logic_monotone (by grind)
lemma LogicCK.subset_CS4 : LogicCK ⊆ LogicCS4 := .logic_monotone (by grind)

lemma ProvableBDHilbert.provable_D_of_PDia
    {𝔸 : Set BDFormula} {A : BDFormula} (h : ⊢ᴴ[CK;𝔸] (◇⊤ : BDFormula)) :
    ⊢ᴴ[CK;𝔸] □A 🡒 ◇A :=
  ProvableBDHilbert.mdp_ctx (ProvableBDHilbert.imp_trans (ProvableBDHilbert.box_mono
    ProvableBDHilbert.imply₁) ProvableBDHilbert.kDia) (ProvableBDHilbert.dhyp h)


namespace LogicCKPDia

@[simp, grind .] lemma provable_PDia : (◇⊤) ∈ LogicCKPDia := ProvableBDHilbert.axm rfl

end LogicCKPDia


namespace LogicCKB

open ProvableBDHilbert

lemma subset_IKB : LogicCKB ⊆ LogicIKB := .logic_monotone (by grind)

/-- - [Pac24, Theorem 3] -/
@[simp, grind .] lemma provable_N : (∼◇⊥) ∈ LogicCKB := by
  have h1 : (⊥ 🡒 □⊥) ∈ LogicCKB := efq;
  have h2 : (□(⊥ 🡒 □⊥)) ∈ LogicCKB := nec h1;
  have h3 : (◇⊥ 🡒 ◇(□⊥)) ∈ LogicCKB := mdp kDia h2;
  have h4 : (◇(□⊥) 🡒 ⊥) ∈ LogicCKB := axm (by grind);
  exact imp_trans h3 h4;

/-- - [Pac24, Theorem 3] -/
@[simp, grind .] lemma provable_DP : (◇(A ⋎ B) 🡒 ◇A ⋎ ◇B) ∈ LogicCKB := by
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

@[simp, grind .] lemma provable_TBox : (□A 🡒 A) ∈ LogicCKTBox := axm (by grind)
@[simp, grind .] lemma provable_not_box_bot : (∼□⊥) ∈ LogicCKTBox := provable_TBox (A := ⊥)

end LogicCKTBox


namespace LogicCKTDia

open ProvableBDHilbert

@[simp, grind .] lemma provable_TDia : (A 🡒 ◇A) ∈ LogicCKTDia := axm (by grind)
@[simp, grind .] lemma provable_PDia : (◇⊤) ∈ LogicCKTDia := mdp provable_TDia verum
@[simp, grind .] lemma provable_D : (□A 🡒 ◇A) ∈ LogicCKTDia := provable_D_of_PDia provable_PDia

end LogicCKTDia


namespace LogicCKT

open ProvableBDHilbert

@[simp, grind .] lemma provable_TBox : (□A 🡒 A) ∈ LogicCKT := axm (by grind)
@[simp, grind .] lemma provable_TDia : (A 🡒 ◇A) ∈ LogicCKT := axm (by grind)

end LogicCKT


namespace LogicCKD

open ProvableBDHilbert

@[simp, grind .] lemma provable_D : □A 🡒 ◇A ∈ LogicCKD := axm (by grind)

@[simp, grind .] lemma provable_PDia : ◇⊤ ∈ LogicCKD := mdp (provable_D) (nec verum)

lemma subset_CKTDia : LogicCKD ⊆ LogicCKTDia := by
  intro A;
  apply provable_of_provable_axioms;
  rintro _ ⟨B, rfl⟩;
  exact LogicCKTDia.provable_D;

lemma eq_CKPDia : LogicCKD = LogicCKPDia := by
  apply Set.Subset.antisymm;
  . intro;
    apply provable_of_provable_axioms;
    rintro _ ⟨B, rfl⟩;
    exact provable_D_of_PDia (axm rfl)
  . intro;
    apply provable_of_provable_axioms;
    rintro B rfl;
    apply provable_PDia;

end LogicCKD


namespace LogicCK4Box

open ProvableBDHilbert

@[simp, grind .] lemma provable_FourBox : (□A 🡒 □□A) ∈ LogicCK4Box := axm (by grind)

end LogicCK4Box


namespace LogicCK4Dia

open ProvableBDHilbert

@[simp, grind .] lemma provable_FourDia : (◇◇A 🡒 ◇A) ∈ LogicCK4Dia := axm (by grind)

end LogicCK4Dia


namespace LogicCK4

open ProvableBDHilbert

@[simp, grind .] lemma provable_FourBox : (□A 🡒 □□A) ∈ LogicCK4 := axm (by grind)
@[simp, grind .] lemma provable_FourDia : (◇◇A 🡒 ◇A) ∈ LogicCK4 := axm (by grind)

end LogicCK4


namespace LogicCS4

open ProvableBDHilbert

@[simp, grind .] lemma provable_TBox : (□A 🡒 A) ∈ LogicCS4 := axm (by grind)
@[simp, grind .] lemma provable_TDia : (A 🡒 ◇A) ∈ LogicCS4 := axm (by grind)
@[simp, grind .] lemma provable_FourBox : (□A 🡒 □□A) ∈ LogicCS4 := axm (by grind)
@[simp, grind .] lemma provable_FourDia : (◇◇A 🡒 ◇A) ∈ LogicCS4 := axm (by grind)

end LogicCS4

end
