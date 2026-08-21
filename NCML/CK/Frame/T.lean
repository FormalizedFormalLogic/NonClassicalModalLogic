module

public import NCML.CK.Frame.ReturningMRel
public import NCML.CK.Frame.StrictlyAscendingMRel

@[expose] public section

namespace CK

variable {κ : Type*}

namespace Frame

variable {F : Frame κ}

class T (F : Frame κ) : Prop where
  t : ∀ x : F.World, ∃ y, x ≼ y ∧ x ⊏ y ∧ y ⊏ x

export T (t)

instance [F.T] : F.ReturningMRel where
  returning_mRel x := by
    obtain ⟨y, Ixy, -, Myx⟩ := t x;
    exact ⟨y, Ixy, Myx⟩;

instance [F.T] : F.StrictlyAscendingMRel where
  strictly_ascending_mRel x := by
    obtain ⟨y, Ixy, Mxy, -⟩ := t x;
    exact ⟨y, Mxy, Ixy⟩;

end Frame

end CK

end
