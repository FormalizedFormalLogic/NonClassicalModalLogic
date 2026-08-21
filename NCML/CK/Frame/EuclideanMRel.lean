module

public import NCML.CK.Frame.SymmetricMRel
public import NCML.CK.Frame.TransitiveMRel

@[expose] public section

namespace CK

variable {κ : Type*}

namespace Frame

variable {F : Frame κ}

class EuclideanMRel (F : Frame κ) : Prop where
  eucl_mRel : ∀ {x y z : F.World}, x ⊏ y → x ⊏ z → y ⊏ z

export EuclideanMRel (eucl_mRel)

instance [F.SymmetricMRel] [F.TransitiveMRel] : F.EuclideanMRel where
  eucl_mRel Mxy Mxz := trans_mRel (symm_mRel Mxy) Mxz

instance [F.SymmetricMRel] [F.EuclideanMRel] : F.TransitiveMRel where
  trans_mRel Mxy Myz := eucl_mRel (symm_mRel Mxy) Myz

end Frame

end CK

end
