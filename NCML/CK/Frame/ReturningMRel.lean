module

public import NCML.CK.Frame.ReflexiveMComp

@[expose] public section

namespace CK

variable {κ : Type*}

namespace Frame

variable {F : Frame κ}

class ReturningMRel (F : Frame κ) : Prop where
  returning_mRel : ∀ x : F.World, ∃ y, x ≼ y ∧ y ⊏ x

export ReturningMRel (returning_mRel)

instance [F.ReturningMRel] : F.ReflexiveMComp where
  reflexive_mComp x := by
    obtain ⟨y, Ixy, Myx⟩ := returning_mRel x;
    right;
    exact ⟨y, x, Ixy, Myx, refl x⟩;

end Frame

end CK

end
