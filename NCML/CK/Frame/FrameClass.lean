module

public import NCML.CK.Frame.BackwardConfluent

@[expose] public section

namespace CK

variable {κ : Type*}

namespace Frame

variable {F : Frame κ}

/-- - [Pac24, Definition 7] -/
class IsCKB (F : Frame κ) : Prop extends SymmetricMRel F, ForwardConfluent F, BackwardConfluent F

/-- - [Pac24, Definition 7] -/
class IsIK (F : Frame κ) : Prop extends ForwardConfluent F, BackwardConfluent F where
  not_fallible : ∀ x : F.World, ¬ F.Fallible x

/-- - [Pac24, Definition 7] -/
class IsIKB (F : Frame κ) : Prop extends IsIK F, SymmetricMRel F

instance [F.IsIKB] : F.IsCKB where

end Frame

end CK

end
