module

public import NCML.Formula
public import Mathlib.Order.Basic
public import Mathlib.Tactic

@[expose] public section

namespace CK

variable {κ : Type*}

/-- - [Pac24, Definition 4] -/
structure Frame (κ : Type*) where
  iRel' : κ → κ → Prop
  [iRel_preorder : IsPreorder _ iRel']
  mRel' : κ → κ → Prop
  Fallible' : κ → Prop
  fallible_iRel' : ∀ {x y}, Fallible' x → iRel' x y → Fallible' y
  fallible_mRel' : ∀ {x y}, Fallible' x → mRel' x y → Fallible' y
  fallible_exists_mRel' : ∀ {x}, Fallible' x → ∃ y, mRel' x y

namespace Frame

variable {F : Frame κ}

abbrev World (_ : Frame κ) := κ

abbrev iRel : F.World → F.World → Prop := F.iRel'
infixl:80 " ≼ " => Frame.iRel

abbrev mRel : F.World → F.World → Prop := F.mRel'
infixl:80 " ⊏ " => Frame.mRel

instance : IsPreorder F.World F.iRel := F.iRel_preorder
instance : IsTrans F.World F.iRel := inferInstance

variable {x y : F.World}

abbrev Fallible : F.World → Prop := F.Fallible'

@[grind =>]
lemma fallible_iRel (h : F.Fallible x) (Ixy : x ≼ y) : F.Fallible y :=
  F.fallible_iRel' h Ixy

@[grind =>]
lemma fallible_mRel (h : F.Fallible x) (Mxy : x ⊏ y) : F.Fallible y :=
  F.fallible_mRel' h Mxy

@[grind =>]
lemma fallible_exists_mRel (h : F.Fallible x) : ∃ y, x ⊏ y :=
  F.fallible_exists_mRel' h

end Frame

/-- - [Pac24, Definition 4] -/
structure Model (κ : Type*) extends Frame κ where
  val : toFrame.World → Nat → Prop
  val_persistent : ∀ {x y} {a}, val x a → x ≼ y → val y a
  fallible_val : ∀ {x} {a}, toFrame.Fallible x → val x a

attribute [grind =>] Model.val_persistent

variable {M : Model κ} {x y : M.World} {A : BDFormula}

/-- - [Pac24, Definition 4] -/
@[grind]
def Forces (M : Model κ) (x : M.World) : BDFormula → Prop
  | #a    => M.val x a
  | ⊥     => M.Fallible x
  | A ⋏ B => Forces M x A ∧ Forces M x B
  | A ⋎ B => Forces M x A ∨ Forces M x B
  | A 🡒 B => ∀ y, x ≼ y → Forces M y A → Forces M y B
  | □A    => ∀ y z, x ≼ y → y ⊏ z → Forces M z A
  | ◇A    => ∀ y, x ≼ y → ∃ z, y ⊏ z ∧ Forces M z A
notation:80 x:81 " ⊩[" M "] " A:81 => Forces M x A

abbrev NotForces (M : Model κ) (x : M.World) (A : BDFormula) : Prop := ¬Forces M x A
notation:80 x:81 " ⊮[" M "] " A:81 => NotForces M x A

@[simp, grind .]
lemma forces_top : x ⊩[_] ⊤ := fun _ _ h => h

@[grind =>]
lemma forces_persistent (h : x ⊩[_] A) (Ixy : x ≼ y) : y ⊩[_] A := by
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

@[grind =>]
lemma forces_of_fallible (h : M.Fallible x) : x ⊩[_] A := by
  induction A generalizing x with
  | dia A ih =>
    intro y Ixy;
    have hy : M.Fallible y := M.fallible_iRel h Ixy;
    obtain ⟨z, Myz⟩ := M.fallible_exists_mRel hy;
    exact ⟨z, Myz, ih (M.fallible_mRel hy Myz)⟩;
  | _ => grind [Model.fallible_val];

def Model.Valid (M : Model κ) (A : BDFormula) := ∀ x : M.World, x ⊩[M] A
infixl:80 " ⊧ " => Model.Valid

def Frame.Valid (F : Frame κ) (A : BDFormula) : Prop :=
  ∀ val val_persistent fallible_val, (Model.mk F val val_persistent fallible_val) ⊧ A
infixl:80 " ⊧ " => Frame.Valid

lemma Model.valid_of_toFrame_valid {M : Model κ} {A : BDFormula} (h : M.toFrame ⊧ A) : M ⊧ A :=
  h M.val M.val_persistent M.fallible_val

end CK

end
