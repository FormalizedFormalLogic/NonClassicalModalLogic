module

public import NCML.CK.Frame.TDia

@[expose] public section

namespace CK

variable {κ : Type*}

namespace Frame

variable {F : Frame κ}

class StrictlyAscendingMRel (F : Frame κ) : Prop where
  strictly_ascending_mRel : ∀ x : F.World, ∃ z, x ⊏ z ∧ x ≼ z

export StrictlyAscendingMRel (strictly_ascending_mRel)

instance [F.StrictlyAscendingMRel] : F.TDia where
  tDia x := by
    obtain ⟨z, Mxz, Ixz⟩ := strictly_ascending_mRel x;
    exact ⟨z, Mxz, fun _ => Ixz⟩;

end Frame

end CK

end
