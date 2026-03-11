module

public import NCML.Formula
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Use

@[expose] public section

namespace NCML

variable {κ : Type*} [Nonempty κ]

structure IMLKripkeFrame (κ : Type*) [Nonempty κ] where
  iRel : κ → κ → Prop
  [iRel_paorder : IsPartialOrder _ iRel]
  mRel : κ → κ → Prop

namespace IMLKripkeFrame

abbrev World (_ : IMLKripkeFrame κ) := κ

abbrev mRel' {F : IMLKripkeFrame κ} : F.World → F.World → Prop := F.mRel
infixl:80 " ⊏ " => IMLKripkeFrame.mRel'

abbrev iRel' {F : IMLKripkeFrame κ} : F.World → F.World → Prop := F.iRel
infixl:80 " ≼ " => IMLKripkeFrame.iRel'

class MRelLifting (F : IMLKripkeFrame κ) where
  mRel_lifting : ∀ {x₁ x₂ y₂ : F.World}, x₁ ≼ x₂ → x₂ ⊏ y₂ → ∃ y₁, y₁ ≼ y₂ ∧ x₁ ⊏ y₁
export MRelLifting (mRel_lifting)

class MixConfluent (F : IMLKripkeFrame κ) where
  mix_confluent : ∀ {x₁ x₂ y₁ : F.World}, x₁ ≼ x₂ → x₁ ⊏ y₁ → ∃ y₂, y₁ ≼ y₂ ∧ x₂ ⊏ y₂
export MixConfluent (mix_confluent)

end IMLKripkeFrame


structure IMLKripkeModel (κ : Type*) [Nonempty κ] extends IMLKripkeFrame κ where
  val : κ → Nat → Prop
  val_persistent : ∀ {x₁ x₂ : toIMLKripkeFrame.World} {a}, val x₁ a → x₁ ≼ x₂ → val x₂ a

namespace IMLKripkeModel

variable {M : IMLKripkeModel κ} {x₁ x₂ y₁ y₂ : M.World}
variable {φ ψ : BDFormula}

instance : IsPartialOrder M.World M.iRel := M.iRel_paorder
instance : IsTrans M.World M.iRel := inferInstance

@[grind]
def ExtrinsicForces {M : IMLKripkeModel κ} (x₁ : M.World) : BDFormula → Prop
  | .atom a    => M.val x₁ a
  | .falsum    => False
  | .and φ ψ   => M.ExtrinsicForces x₁ φ ∧ M.ExtrinsicForces x₁ ψ
  | .or φ ψ    => M.ExtrinsicForces x₁ φ ∨ M.ExtrinsicForces x₁ ψ
  | .imply φ ψ => ∀ x₂, x₁ ≼ x₂ → M.ExtrinsicForces x₂ φ → M.ExtrinsicForces x₂ ψ
  | .box φ     => ∀ y₁, x₁ ⊏ y₁ → M.ExtrinsicForces y₁ φ
  | .dia φ     => ∃ y₁, x₁ ⊏ y₁ ∧ M.ExtrinsicForces y₁ φ
infixl:80 " ⊩ᵉ " => ExtrinsicForces

@[grind]
def IntrinsicForces {M : IMLKripkeModel κ} (x₁ : M.World) : BDFormula → Prop
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
    obtain ⟨y₁, Iy₁y₂, Mx₁y₁⟩ := M.mRel_lifting Ix₁x₂ Mx₂y₂;
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
    obtain ⟨y₂, Iy₁y₂, My₁y₂⟩ := M.mix_confluent Ix₁x₂ Mx₁y₁;
    use y₂;
    constructor;
    . assumption;
    . exact ihφ (by grind) hy₁ Iy₁y₂;

end IMLKripkeModel

end NCML

end
