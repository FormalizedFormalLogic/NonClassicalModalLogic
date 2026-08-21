module

public import NCML.CK.Semantics

@[expose] public section

namespace CK

variable {κ : Type*}

namespace Frame

variable {F : Frame κ}

class TransitiveMRel (F : Frame κ) : Prop where
  trans_mRel : ∀ {x y z : F.World}, x ⊏ y → y ⊏ z → x ⊏ z

export TransitiveMRel (trans_mRel)

end Frame

end CK

end
