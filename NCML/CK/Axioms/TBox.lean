module

public import NCML.CK.Canonical

@[expose] public section

open ProvableBDHilbert

namespace CK

open Model.Forces

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

class ReflexiveMComp (M : Model κ) : Prop where
  reflexive_mComp : ∀ x : M.World, M.Fallible x ∨ ∃ y z, x ≼ y ∧ y ⊏ z ∧ z ≼ x

export ReflexiveMComp (reflexive_mComp)

class ReturningMRel (M : Model κ) : Prop where
  returning_mRel : ∀ x : M.World, ∃ y, x ≼ y ∧ y ⊏ x

export ReturningMRel (returning_mRel)

instance [M.ReturningMRel] : M.ReflexiveMComp where
  reflexive_mComp x := by
    obtain ⟨y, Ixy, Myx⟩ := returning_mRel x;
    right;
    exact ⟨y, x, Ixy, Myx, refl x⟩;

lemma valid_TBox_of_reflexiveMComp [M.ReflexiveMComp] : M ⊧ (□A 🡒 A) := by
  intro x y Ixy hyBoxA;
  rcases reflexive_mComp y with hFallible | ⟨y₁, z₁, Iyy₁, My₁z₁, Iz₁y⟩;
  · exact of_fallible hFallible;
  · exact persistent (hyBoxA y₁ z₁ Iyy₁ My₁z₁) Iz₁y;

lemma valid_of_mem_LogicCKTBox [M.ReflexiveMComp] (hA : A ∈ LogicCKTBox) : M ⊧ A :=
  valid_of_mem_logic (by rintro B ⟨C, rfl⟩; exact valid_TBox_of_reflexiveMComp) hA

end Model

variable {L : BDLogic} [L.CK]

lemma returningMRel_canonicalModel (hTBox : ∀ {A}, (□A 🡒 A) ∈ L) :
  (canonicalModel L).ReturningMRel where
  returning_mRel P :=
    ⟨P.erase, CanonicalPair.iRel_erase,
      fun _ hA => P.theory.mdp (P.theory.subset (L := L) hTBox) hA, by simp⟩

end CK

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
    obtain ⟨P, hw⟩ := CK.exists_not_forces_of_not_mem h;
    exact ⟨_, CK.canonicalModel LogicCKTBox, CK.returningMRel_canonicalModel (by grind),
      fun hM => hw (hM P)⟩;
  tfae_finish

end
