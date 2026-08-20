module

public import NCML.CK.Canonical

@[expose] public section

open ProvableBDHilbert

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

theorem valid_of_mem_LogicCKTBox [M.ReflexiveMComp] (hA : A ∈ LogicCKTBox) : M ⊧ A :=
  valid_of_mem_logic (by rintro B ⟨C, rfl⟩; exact valid_TBox_of_reflexiveMComp) hA

end Model

/-- The canonical model of a logic proving `T□` has an `≼`-successor with an `⊏`-edge back to
every pair. -/
lemma returningMRel_canonicalModel {𝔸 : Set BDFormula} (h𝔸 : ∀ A : BDFormula, (□A 🡒 A) ∈ logic 𝔸) :
  (canonicalModel 𝔸).ReturningMRel where
  returning_mRel w :=
    ⟨w.erase, CanonicalPair.iRel_erase,
      fun _ hA => w.th.mdp (BDTheory.provable_mem (h𝔸 _)) hA, by simp⟩

instance : (canonicalModel { □A 🡒 A | (A) }).ReturningMRel :=
  returningMRel_canonicalModel fun _ => LogicCKTBox.provable_TBox

end CK

/-- The model characterization of `CK + T□`: a formula is a theorem of `CK + T□` exactly when it is
valid on every CK-model whose `≼ ∘ ⊏ ∘ ≼` is reflexive up to fallibility, equivalently on every
CK-model in which every world has an `≼`-successor with an `⊏`-edge back to it.

- [Pac24, Problem in §4]
-/
theorem LogicCKTBox_TFAE {A : BDFormula} : List.TFAE [
  A ∈ LogicCKTBox,
  ∀ {κ : Type 0}, ∀ M : CK.Model κ, [M.ReflexiveMComp] → M ⊧ A,
  ∀ {κ : Type 0}, ∀ M : CK.Model κ, [M.ReturningMRel] → M ⊧ A,
] := by
  tfae_have 1 → 2 := fun h _ M _ => CK.Model.valid_of_mem_LogicCKTBox h
  tfae_have 2 → 3 := fun h _ M _ => h M
  tfae_have 3 → 1 := by
    contrapose!;
    intro h;
    obtain ⟨w, hw⟩ := CK.exists_not_forces_of_not_mem h;
    exact ⟨_, CK.canonicalModel _, inferInstance, fun hM => hw (hM w)⟩;
  tfae_finish

end
