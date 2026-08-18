module

public import NCML.Formula
public import Mathlib.Order.Basic
public import Mathlib.Tactic

@[expose] public section

namespace CK

open NCML

/-- - [Pac24, Definition 4] -/
structure Model (κ : Type*) where
  iRel' : κ → κ → Prop
  [iRel_preorder : IsPreorder _ iRel']
  mRel' : κ → κ → Prop
  Fallible' : κ → Prop
  fallible_iRel' : ∀ {x y}, Fallible' x → iRel' x y → Fallible' y
  fallible_mRel' : ∀ {x y}, Fallible' x → mRel' x y → Fallible' y
  val : κ → Nat → Prop
  val_persistent : ∀ {x y} {a}, val x a → iRel' x y → val y a
  fallible_val : ∀ {x} {a}, Fallible' x → val x a

attribute [grind =>] Model.val_persistent

namespace Model

variable {κ : Type*}

abbrev World (_ : Model κ) := κ

abbrev iRel {M : Model κ} : M.World → M.World → Prop := M.iRel'
infixl:80 " ≼ " => Model.iRel

abbrev mRel {M : Model κ} : M.World → M.World → Prop := M.mRel'
infixl:80 " ⊏ " => Model.mRel

variable {M : Model κ}

instance : IsPreorder M.World M.iRel := M.iRel_preorder
instance : IsTrans M.World M.iRel := inferInstance

abbrev Fallible {M : Model κ} : M.World → Prop := M.Fallible'

@[grind =>]
lemma fallible_iRel {x y : M.World} (h : M.Fallible x) (Ixy : x ≼ y) : M.Fallible y :=
  M.fallible_iRel' h Ixy

@[grind =>]
lemma fallible_mRel {x y : M.World} (h : M.Fallible x) (Mxy : x ⊏ y) : M.Fallible y :=
  M.fallible_mRel' h Mxy

variable {x y z : M.World} {A B : BDFormula}

/-- - [Pac24, Definition 4] -/
@[grind]
def Forces (M : Model κ) (x : M.World) : BDFormula → Prop
  | #a    => M.val x a
  | ⊥     => M.Fallible x
  | A ⋏ B => M.Forces x A ∧ M.Forces x B
  | A ⋎ B => M.Forces x A ∨ M.Forces x B
  | A 🡒 B => ∀ y, x ≼ y → M.Forces y A → M.Forces y B
  | □A    => ∀ y z, x ≼ y → y ⊏ z → M.Forces z A
  | ◇A    => ∀ y, x ≼ y → ∃ z, y ⊏ z ∧ M.Forces z A

notation:80 x:81 " ⊩[" M "] " A:81 => Forces M x A

/-- Routine consequence of `Model`'s conditions. -/
lemma Forces.persistent (h : x ⊩[_] A) (Ixy : x ≼ y) : y ⊩[_] A := by
  induction A generalizing y with
  | imply A B _ _ =>
    intro y₁ Iyy₁ hy₁A;
    exact h y₁ (Trans.trans Ixy Iyy₁) hy₁A;
  | box A _ =>
    intro y₁ z₁ Iyy₁ My₁z₁;
    exact h y₁ z₁ (Trans.trans Ixy Iyy₁) My₁z₁;
  | dia A _ =>
    intro y₁ Iyy₁;
    exact h y₁ (Trans.trans Ixy Iyy₁);
  | _ => grind;

/-- Routine consequence of `Model`'s conditions. -/
lemma Forces.of_fallible_of_diaFree (hA : A.diaFree) (h : M.Fallible x) : x ⊩[_] A := by
  induction A generalizing x <;> grind [Model.fallible_val];

def Valid (M : Model κ) (A : BDFormula) := ∀ x : M.World, x ⊩[M] A
infixl:80 " ⊧ " => Valid

end Model

end CK

end
