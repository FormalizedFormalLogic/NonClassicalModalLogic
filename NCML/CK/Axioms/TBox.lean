module

public import NCML.CK.Semantics

@[expose] public section

namespace CK

open Model.Forces

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

/-- Condition (refl°): every world is fallible or lies in the composite
relation `R° := ≼ ∘ ⊏ ∘ ≼` to itself. -/
class ReflexiveMComp (M : Model κ) : Prop where
  reflexive_mComp : ∀ x : M.World, M.Fallible x ∨ ∃ y z, x ≼ y ∧ y ⊏ z ∧ z ≼ x

export ReflexiveMComp (reflexive_mComp)

/-- Condition (refl°⁺): every world has an `≼`-successor with an `⊏`-edge back to it. -/
class ReturningMRel (M : Model κ) : Prop where
  returning_mRel : ∀ x : M.World, ∃ y, x ≼ y ∧ y ⊏ x

export ReturningMRel (returning_mRel)

instance [M.ReturningMRel] : M.ReflexiveMComp where
  reflexive_mComp x := by
    obtain ⟨y, Ixy, Myx⟩ := returning_mRel x;
    right;
    exact ⟨y, x, Ixy, Myx, refl x⟩;

theorem valid_TBox_of_reflexiveMComp [M.ReflexiveMComp] : M ⊧ (□A 🡒 A) := by
  intro x y Ixy hyBoxA;
  rcases reflexive_mComp y with hFallible | ⟨y₁, z₁, Iyy₁, My₁z₁, Iz₁y⟩;
  · exact of_fallible hFallible;
  · exact persistent (hyBoxA y₁ z₁ Iyy₁ My₁z₁) Iz₁y;

end Model

end CK

end
