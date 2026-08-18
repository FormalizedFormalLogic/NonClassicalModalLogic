module

public import NCML.Formula
public import Mathlib.Order.Basic
public import Mathlib.Tactic

@[expose] public section

namespace NCML.CK

/-- A CK-frame (Definition 4, frame part): a set of worlds `κ`, an
intuitionistic (reflexive, transitive) relation `iRel`, a modal relation
`mRel`, and a set `Fallible` of fallible worlds, closed forward along both
`iRel` and `mRel`. -/
structure Frame (κ : Type*) where
  iRel : κ → κ → Prop
  [iRel_preorder : IsPreorder _ iRel]
  mRel : κ → κ → Prop
  Fallible : κ → Prop
  fallible_iRel : ∀ {x y}, Fallible x → iRel x y → Fallible y
  fallible_mRel : ∀ {x y}, Fallible x → mRel x y → Fallible y

namespace Frame

variable {κ : Type*}

abbrev World (_ : Frame κ) := κ

abbrev iRel' {F : Frame κ} : F.World → F.World → Prop := F.iRel
infixl:80 " ≼ " => Frame.iRel'

abbrev mRel' {F : Frame κ} : F.World → F.World → Prop := F.mRel
infixl:80 " ⊏ " => Frame.mRel'

variable {F : Frame κ}

instance : IsPreorder F.World F.iRel := F.iRel_preorder
instance : IsTrans F.World F.iRel := inferInstance

end Frame

/-- A CK-model (Definition 4): a `Frame` together with a valuation `val` that
is persistent along `iRel` (condition (i)) and holds at every atom in
`Fallible` worlds (condition (ii)). -/
structure Model (κ : Type*) extends Frame κ where
  val : κ → Nat → Prop
  val_persistent : ∀ {x y : toFrame.World} {a}, val x a → x ≼ y → val y a
  fallible_val : ∀ {x : toFrame.World} {a}, Fallible x → val x a

namespace Model

variable {κ : Type*} {M : Model κ} {x y z : M.World} {A B : BDFormula}

/-- The forcing relation for CK-models (Definition 4). The `dia` clause is
guarded by `iRel`: `M,x⊨◇A` iff `∀y. x⪯y → ∃z. yRz ∧ M,z⊨A`. This guard must
not be dropped, or Proposition 6 below becomes a triviality. -/
@[grind]
def Forces {M : Model κ} (x : M.World) : BDFormula → Prop
  | .atom a    => M.val x a
  | .falsum    => M.Fallible x
  | .and A B   => M.Forces x A ∧ M.Forces x B
  | .or A B    => M.Forces x A ∨ M.Forces x B
  | .imply A B => ∀ y, x ≼ y → M.Forces y A → M.Forces y B
  | .box A     => ∀ y z, x ≼ y → y ⊏ z → M.Forces z A
  | .dia A     => ∀ y, x ≼ y → ∃ z, y ⊏ z ∧ M.Forces z A

infixl:80 " ⊩ " => Forces

/-- Persistence of the forcing relation along `iRel` (a basic consequence of
Definition 4, used pervasively below). -/
lemma Forces.persistent (h : x ⊩ A) (hxy : x ≼ y) : y ⊩ A := by
  induction A generalizing y with
  | atom a => exact M.val_persistent h hxy
  | falsum => exact M.fallible_iRel h hxy
  | imply A B _ _ =>
    intro z hyz hzA
    exact h z (Trans.trans hxy hyz) hzA
  | box A _ =>
    intro z w hyz hzw
    exact h z w (Trans.trans hxy hyz) hzw
  | dia A _ =>
    intro z hyz
    exact h z (Trans.trans hxy hyz)
  | _ => grind

/-- At a fallible world, every `diaFree` formula is forced. The proof uses
all three closure conditions bundled in Definition 4/`Model`: `fallible_val`,
`fallible_iRel`, and `fallible_mRel`.

Note: the unrestricted statement (dropping `diaFree`) is *false* in general:
Definition 4 imposes no seriality on `mRel` at fallible worlds, so a model
where `mRel` is empty has a fallible world that fails to force e.g. `◇⊤`. -/
lemma Forces.of_fallible_of_diaFree (hA : A.diaFree) (h : M.Fallible x) : x ⊩ A := by
  induction A generalizing x with
  | atom a => exact M.fallible_val h
  | imply A B _ ihB =>
    intro y hxy _
    exact ihB hA.2 (M.fallible_iRel h hxy)
  | box A ihA =>
    intro y z hxy hyz
    exact ihA hA (M.fallible_mRel (M.fallible_iRel h hxy) hyz)
  | _ => grind

/-- Validity of a formula in a CK-model. -/
def Valid (M : Model κ) (A : BDFormula) := ∀ x : M.World, x ⊩ A
infixl:80 " ⊧ " => Valid

end Model

end NCML.CK

end
