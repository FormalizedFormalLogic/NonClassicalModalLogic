module

public import NCML.CK.Canonical

@[expose] public section

open ProvableBDHilbert

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class ReflexiveMComp (F : Frame κ) : Prop where
  reflexive_mComp : ∀ x : F.World, F.Fallible x ∨ ∃ y z, x ≼ y ∧ y ⊏ z ∧ z ≼ x

export ReflexiveMComp (reflexive_mComp)

class ReturningMRel (F : Frame κ) : Prop where
  returning_mRel : ∀ x : F.World, ∃ y, x ≼ y ∧ y ⊏ x

export ReturningMRel (returning_mRel)

instance [F.ReturningMRel] : F.ReflexiveMComp where
  reflexive_mComp x := by
    obtain ⟨y, Ixy, Myx⟩ := returning_mRel x;
    right;
    exact ⟨y, x, Ixy, Myx, refl x⟩;

end Frame

namespace Model

open CK.Frame

lemma valid_TBox_of_reflexiveMComp [M.ReflexiveMComp] : M ⊧ (□A 🡒 A) := by
  intro x y Ixy hyBoxA;
  rcases reflexive_mComp y with hFallible | ⟨y₁, z₁, Iyy₁, My₁z₁, Iz₁y⟩;
  · exact forces_of_fallible hFallible;
  · exact forces_persistent (hyBoxA y₁ z₁ Iyy₁ My₁z₁) Iz₁y;

lemma valid_of_mem_LogicCKTBox [M.ReflexiveMComp] (hA : A ∈ LogicCKTBox) : M ⊧ A :=
  valid_of_mem_logic (by rintro B ⟨C, rfl⟩; exact valid_TBox_of_reflexiveMComp) hA

end Model

namespace Frame

variable {F : Frame κ}

lemma valid_TBox_of_reflexiveMComp [F.ReflexiveMComp] : F ⊧ (□A 🡒 A) :=
  fun _ _ _ => Model.valid_TBox_of_reflexiveMComp

lemma reflexiveMComp_of_valid_TBox (h : F ⊧ (□(#0) 🡒 #0)) : F.ReflexiveMComp where
  reflexive_mComp x := by
    let M : Model κ := {
      toFrame := F,
      val := fun y _ => (∃ z w, x ≼ z ∧ z ⊏ w ∧ w ≼ y) ∨ F.Fallible y,
      val_persistent := by
        rintro y z a (⟨w, v, Ixw, Mwv, Ivy⟩ | hy) Iyz;
        . left;
          exact ⟨w, v, Ixw, Mwv, Trans.trans Ivy Iyz⟩;
        . right;
          exact F.fallible_iRel hy Iyz;
      fallible_val := by
        rintro y a hy;
        right;
        exact hy;
    }
    have hxBoxA : x ⊩[M] □(#0) := fun y z Ixy Myz => Or.inl ⟨y, z, Ixy, Myz, refl z⟩;
    obtain ⟨y, z, Ixy, Myz, Izx⟩ | hx :=
      h M.val M.val_persistent M.fallible_val x x (refl x) hxBoxA;
    . right;
      exact ⟨y, z, Ixy, Myz, Izx⟩;
    . left;
      exact hx;

/-- `T□` defines the frames on which `≼ ∘ ⊏ ∘ ≼` is reflexive away from the fallible worlds. -/
theorem reflexiveMComp_TFAE : List.TFAE [
  F.ReflexiveMComp,
  ∀ A : BDFormula, F ⊧ (□A 🡒 A),
  F ⊧ (□(#0) 🡒 #0),
] := by
  tfae_have 1 → 2 := by intro h A; exact valid_TBox_of_reflexiveMComp;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := reflexiveMComp_of_valid_TBox
  tfae_finish

end Frame

variable {L : BDLogic} [L.CK]

lemma returningMRel_canonicalModel (hTBox : ∀ {A}, (□A 🡒 A) ∈ L) : (canonicalModel L).ReturningMRel where
  returning_mRel P := ⟨
    P.erase,
    CanonicalPair.iRel_erase,
    fun _ hA => P.theory.mdp (P.theory.subset (L := L) hTBox) hA,
    by simp
  ⟩

end CK

theorem LogicCKTBox_TFAE {A : BDFormula} : List.TFAE [
  A ∈ LogicCKTBox,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.ReflexiveMComp] → F ⊧ A,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.ReturningMRel] → F ⊧ A,
] := by
  tfae_have 1 → 2 := fun h _ F _ V V_per V_fal => CK.Model.valid_of_mem_LogicCKTBox h
  tfae_have 2 → 3 := fun h _ F _ => h F
  tfae_have 3 → 1 := by
    contrapose!;
    intro h;
    obtain ⟨P, h₁⟩ := CK.exists_not_forces_of_not_mem h;
    refine ⟨_, (CK.canonicalModel LogicCKTBox).toFrame, ?_⟩;
    and_intros;
    . exact CK.returningMRel_canonicalModel (by grind);
    . by_contra! hF;
      exact h₁ $ CK.Model.valid_of_toFrame_valid hF P;
  tfae_finish

end
