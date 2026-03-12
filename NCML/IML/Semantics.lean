module

public import NCML.Formula
public import Mathlib.Order.Basic
public import Mathlib.Tactic

@[expose] public section

namespace NCML.IML

variable {κ : Type*} [Nonempty κ]

structure KripkeFrame (κ : Type*) [Nonempty κ] where
  iRel : κ → κ → Prop
  [iRel_paorder : IsPartialOrder _ iRel]
  mRel : κ → κ → Prop

namespace KripkeFrame

abbrev World (_ : KripkeFrame κ) := κ

abbrev mRel' {F : KripkeFrame κ} : F.World → F.World → Prop := F.mRel
infixl:80 " ⊏ " => KripkeFrame.mRel'

abbrev iRel' {F : KripkeFrame κ} : F.World → F.World → Prop := F.iRel
infixl:80 " ≼ " => KripkeFrame.iRel'

class MRelLifting (F : KripkeFrame κ) where
  mRel_lifting : ∀ x₁ x₂ y₂ : F.World, x₁ ≼ x₂ → x₂ ⊏ y₂ → ∃ y₁, y₁ ≼ y₂ ∧ x₁ ⊏ y₁
export MRelLifting (mRel_lifting)

class MixConfluent (F : KripkeFrame κ) where
  mix_confluent : ∀ x₁ x₂ y₁ : F.World, x₁ ≼ x₂ → x₁ ⊏ y₁ → ∃ y₂, y₁ ≼ y₂ ∧ x₂ ⊏ y₂
export MixConfluent (mix_confluent)

end KripkeFrame


structure KripkeModel (κ : Type*) [Nonempty κ] extends KripkeFrame κ where
  val : κ → Nat → Prop
  val_persistent : ∀ {x₁ x₂ : toKripkeFrame.World} {a}, val x₁ a → x₁ ≼ x₂ → val x₂ a

namespace KripkeModel

variable {M : KripkeModel κ} {x₁ x₂ y₁ y₂ : M.World}
variable {φ ψ : BDFormula}

instance : IsPartialOrder M.World M.iRel := M.iRel_paorder
instance : IsTrans M.World M.iRel := inferInstance

@[grind]
def ExtrinsicForces {M : KripkeModel κ} (x₁ : M.World) : BDFormula → Prop
  | .atom a    => M.val x₁ a
  | .falsum    => False
  | .and φ ψ   => M.ExtrinsicForces x₁ φ ∧ M.ExtrinsicForces x₁ ψ
  | .or φ ψ    => M.ExtrinsicForces x₁ φ ∨ M.ExtrinsicForces x₁ ψ
  | .imply φ ψ => ∀ x₂, x₁ ≼ x₂ → M.ExtrinsicForces x₂ φ → M.ExtrinsicForces x₂ ψ
  | .box φ     => ∀ y₁, x₁ ⊏ y₁ → M.ExtrinsicForces y₁ φ
  | .dia φ     => ∃ y₁, x₁ ⊏ y₁ ∧ M.ExtrinsicForces y₁ φ
infixl:80 " ⊩ᵉ " => ExtrinsicForces

@[grind]
def IntrinsicForces {M : KripkeModel κ} (x₁ : M.World) : BDFormula → Prop
  | .atom a    => M.val x₁ a
  | .falsum    => False
  | .and φ ψ   => M.IntrinsicForces x₁ φ ∧ M.IntrinsicForces x₁ ψ
  | .or φ ψ    => M.IntrinsicForces x₁ φ ∨ M.IntrinsicForces x₁ ψ
  | .imply φ ψ => ∀ x₂, x₁ ≼ x₂ → M.IntrinsicForces x₂ φ → M.IntrinsicForces x₂ ψ
  | .box φ     => ∀ x₂, x₁ ≼ x₂ → ∀ y₂, x₂ ⊏ y₂ → M.IntrinsicForces y₂ φ
  | .dia φ     => ∀ x₂, x₁ ≼ x₂ → ∃ y₂, x₂ ⊏ y₂ ∧ M.IntrinsicForces y₂ φ
infixl:80 " ⊩ⁱ " => IntrinsicForces

lemma formula_persistent_intrinsicForces : x₁ ⊩ⁱ φ → x₁ ≼ x₂ → x₂ ⊩ⁱ φ := by
  intro h Ix₁x₂;
  induction φ generalizing x₂ with
  | atom a => apply M.val_persistent h Ix₁x₂;
  | imply φ ψ ihφ ihψ =>
    intro x₃ Ix₂x₃ hx₃φ;
    apply h x₃ (Trans.trans Ix₁x₂ Ix₂x₃) hx₃φ;
  | box φ ihφ =>
    intro x₃ Ix₂x₃ y₃ Mx₃y₃;
    exact h x₃ (Trans.trans Ix₁x₂ Ix₂x₃) _ Mx₃y₃;
  | dia φ ihφ =>
    intro x₃ Ix₂x₃;
    obtain ⟨y₁, Mx₃y₁, hy₁φ⟩ := h x₃ (Trans.trans Ix₁x₂ Ix₂x₃);
    use y₁;
  | _ => grind;

lemma diaFree_formula_persistent_exrinsicForces [M.MRelLifting] (hφ : φ.diaFree) : x₁ ⊩ᵉ φ → x₁ ≼ x₂ → x₂ ⊩ᵉ φ := by
  intro h Ix₁x₂;
  induction φ generalizing x₁ x₂ with
  | atom a => apply M.val_persistent h Ix₁x₂;
  | and | or | falsum | dia => grind;
  | imply φ ψ ihφ ihψ =>
    intro x₃ Ix₂x₃ hx₃φ;
    apply h x₃ (Trans.trans Ix₁x₂ Ix₂x₃) hx₃φ;
  | box φ ihφ =>
    intro y₂ Mx₂y₂;
    obtain ⟨y₁, Iy₁y₂, Mx₁y₁⟩ := M.mRel_lifting _ _ _ Ix₁x₂ Mx₂y₂;
    apply ihφ (by grind) (h y₁ Mx₁y₁) Iy₁y₂;

lemma boxFree_formula_persistent_exrinsicForces [M.MixConfluent] (hφ : φ.boxFree) : x₁ ⊩ᵉ φ → x₁ ≼ x₂ → x₂ ⊩ᵉ φ := by
  intro h Ix₁x₂;
  induction φ generalizing x₁ x₂ with
  | atom a => apply M.val_persistent h Ix₁x₂;
  | and | or | falsum | box => grind;
  | imply φ ψ ihφ ihψ =>
    intro x₃ Ix₂x₃ hx₃φ;
    apply h x₃ (Trans.trans Ix₁x₂ Ix₂x₃) hx₃φ;
  | dia φ ihφ =>
    obtain ⟨y₁, Mx₁y₁, hy₁⟩ := h;
    obtain ⟨y₂, Iy₁y₂, My₁y₂⟩ := M.mix_confluent _ _ _ Ix₁x₂ Mx₁y₁;
    use y₂;
    constructor;
    . assumption;
    . exact ihφ (by grind) hy₁ Iy₁y₂;

lemma formula_persistent_exrinsicForces [M.MRelLifting] [M.MixConfluent] : x₁ ⊩ᵉ φ → x₁ ≼ x₂ → x₂ ⊩ᵉ φ := by
  intro h Ix₁x₂;
  induction φ generalizing x₁ x₂ with
  | atom a => apply M.val_persistent h Ix₁x₂;
  | and | or | falsum => grind;
  | imply φ ψ ihφ ihψ =>
    intro x₃ Ix₂x₃ hx₃φ;
    apply h x₃ (Trans.trans Ix₁x₂ Ix₂x₃) hx₃φ;
  | box φ ihφ =>
    intro y₂ Mx₂y₂;
    obtain ⟨y₁, Iy₁y₂, Mx₁y₁⟩ := M.mRel_lifting _ _ _ Ix₁x₂ Mx₂y₂;
    apply ihφ (h y₁ Mx₁y₁) Iy₁y₂;
  | dia φ ihφ =>
    obtain ⟨y₁, Mx₁y₁, hy₁⟩ := h;
    obtain ⟨y₂, Iy₁y₂, My₁y₂⟩ := M.mix_confluent _ _ _ Ix₁x₂ Mx₁y₁;
    use y₂;
    constructor;
    . assumption;
    . exact ihφ hy₁ Iy₁y₂;


def ExtrinsicValid (M : KripkeModel κ) (φ : BDFormula) := ∀ x : M.World, x ⊩ᵉ φ
infixl:80 " ⊧ᵉ " => ExtrinsicValid

def IntrinsicValid (M : KripkeModel κ) (φ : BDFormula) := ∀ x : M.World, x ⊩ᵉ φ
infixl:80 " ⊧ⁱ " => IntrinsicValid

end KripkeModel


namespace KripkeFrame

def ExtrinsicValid (F : KripkeFrame κ) (φ : BDFormula) := ∀ V hV, (KripkeModel.mk F V hV) ⊧ᵉ φ
infixl:80 " ⊧ᵉ " => ExtrinsicValid

def IntrinsicValid (F : KripkeFrame κ) (φ : BDFormula) := ∀ V hV, (KripkeModel.mk F V hV) ⊧ᵉ φ
infixl:80 " ⊧ⁱ " => IntrinsicValid

end KripkeFrame


def logicExtrinsic := { φ : BDFormula | ∀ κ : Type*, [Nonempty κ] → ∀ M : KripkeModel κ, [M.MRelLifting] → [M.MixConfluent] → M ⊧ᵉ φ }
def logicIntrinsic := { φ : BDFormula | ∀ κ : Type*, [Nonempty κ] → ∀ M : KripkeModel κ, M ⊧ⁱ φ }

lemma wwwww {M : KripkeModel κ} [M.MRelLifting] [M.MixConfluent] {x₁ : M.World} {φ} : x₁ ⊩ᵉ φ ↔ x₁ ⊩ⁱ φ := by
  induction φ generalizing x₁ with
  | box φ ihφ =>
    constructor;
    . intro h y₁ Ix₁y₁ y₂ My₁y₂;
      exact ihφ.mp $ KripkeModel.formula_persistent_exrinsicForces h Ix₁y₁ y₂ My₁y₂;
    . intro h y₁ Mx₁y₁;
      exact ihφ.mpr $ h x₁ (refl x₁) y₁ Mx₁y₁;
  | dia φ ihφ =>
    constructor;
    . rintro ⟨y₁, Mx₁y₁, h⟩ x₂ Ix₁x₂;
      obtain ⟨y₂, Iy₁y₂, Mx₁y₂⟩ := M.mix_confluent x₁ x₂ y₁ Ix₁x₂ Mx₁y₁;
      use y₂;
      constructor;
      . assumption;
      . exact ihφ.mp $ KripkeModel.formula_persistent_exrinsicForces h Iy₁y₂;
    . rintro h;
      obtain ⟨y₁, Mx₁y₁, h⟩ := h x₁ (refl _)
      use y₁;
      constructor;
      . assumption;
      . exact ihφ.mpr h;
  | _ => grind;

theorem logicIntrinsic_subset_logicExtrinsic : logicIntrinsic.{u} ⊆ logicExtrinsic.{u} := by
  dsimp [logicIntrinsic, logicExtrinsic, KripkeModel.IntrinsicValid, KripkeModel.ExtrinsicValid];
  grind [wwwww];


end NCML.IML

end
