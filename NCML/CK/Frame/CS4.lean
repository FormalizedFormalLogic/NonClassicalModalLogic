module

public import NCML.CK.Frame.ReflexiveMRel
public import NCML.CK.Frame.TransitiveMRel
public import NCML.CK.Frame.BackwardConfluent
public import NCML.CK.Frame.T
public import NCML.CK.Frame.Four

@[expose] public section

namespace CK

variable {κ : Type*}

namespace Frame

variable {F : Frame κ}

/-- - [BDF21, Definition II.7] -/
class CS4 (F : Frame κ) : Prop extends ReflexiveMRel F, TransitiveMRel F, BackwardConfluent F

instance [F.CS4] : F.T where
instance [F.CS4] : F.Four where

end Frame

end CK

end
