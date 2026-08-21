module

public import NCML.CK.Frame.ReturningMRel
public import NCML.CK.Frame.StrictlyAscendingMRel

@[expose] public section

namespace CK

variable {κ : Type*}

namespace Frame

variable {F : Frame κ}

class ReflexiveMRel (F : Frame κ) : Prop where
  refl_mRel : ∀ x : F.World, x ⊏ x

export ReflexiveMRel (refl_mRel)

instance [F.ReflexiveMRel] : F.ReturningMRel where
  returning_mRel x := ⟨x, refl x, refl_mRel x⟩

instance [F.ReflexiveMRel] : F.StrictlyAscendingMRel where
  strictly_ascending_mRel x := ⟨x, refl_mRel x, refl x⟩

end Frame

end CK

end
