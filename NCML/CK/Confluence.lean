module

public import NCML.CK.Semantics

@[expose] public section

namespace NCML.CK

open Model

variable {κ : Type*} {F : Frame κ}

/-- Forward confluence (Definition 5): if `x R y` and `x ⪯ x'`, there is `y'`
with `y ⪯ y'` and `x' R y'`. -/
class ForwardConfluent (F : Frame κ) : Prop where
  forward_confluent : ∀ {x y x' : F.World}, x ⊏ y → x ≼ x' → ∃ y', y ≼ y' ∧ x' ⊏ y'

export ForwardConfluent (forward_confluent)

/-- Backward confluence (Definition 5): if `x R y` and `y ⪯ y'`, there is `x'`
with `x ⪯ x'` and `x' R y'`. -/
class BackwardConfluent (F : Frame κ) : Prop where
  backward_confluent : ∀ {x y y' : F.World}, x ⊏ y → y ≼ y' → ∃ x', x ≼ x' ∧ x' ⊏ y'

export BackwardConfluent (backward_confluent)

/-- Symmetry of the modal relation `mRel`. -/
class SymmetricMRel (F : Frame κ) : Prop where
  symm_mRel : ∀ {x y : F.World}, x ⊏ y → y ⊏ x

export SymmetricMRel (symm_mRel)

/-- `CKB`-frames (Definition 7): `mRel` is symmetric, forward confluent, and
backward confluent. -/
class IsCKB (F : Frame κ) : Prop extends SymmetricMRel F, ForwardConfluent F, BackwardConfluent F

/-- `IK`-frames (Definition 7): no fallible worlds, and `mRel` is forward and
backward confluent. -/
class IsIK (F : Frame κ) : Prop extends ForwardConfluent F, BackwardConfluent F where
  not_fallible : ∀ x : F.World, ¬ F.Fallible x

/-- `IKB`-frames (Definition 7): `IK`-frames with `mRel` symmetric,
equivalently `CKB`-frames without fallible worlds. -/
class IsIKB (F : Frame κ) : Prop extends IsIK F, SymmetricMRel F

/-- Proposition 6: if `mRel` is forward confluent, `◇A` can be evaluated
directly through `mRel`, without going through the `iRel`-guard. -/
theorem Model.dia_iff_forward {M : Model κ} [ForwardConfluent M.toFrame]
    {x : M.World} {A : BDFormula} : x ⊩ ◇A ↔ ∃ y, x ⊏ y ∧ y ⊩ A := by
  constructor
  · intro h
    exact h x (refl x)
  · rintro ⟨y, hxy, hyA⟩ x' hxx'
    obtain ⟨y', hyy', hx'y'⟩ := forward_confluent hxy hxx'
    exact ⟨y', hx'y', Model.Forces.persistent hyA hyy'⟩

/-- Proposition 10: for a CK-frame with symmetric `mRel`, forward confluence
and backward confluence are equivalent. -/
theorem forwardConfluent_iff_backwardConfluent_of_symm [SymmetricMRel F] :
    ForwardConfluent F ↔ BackwardConfluent F := by
  constructor
  · intro h
    refine ⟨fun {x y y'} hxy hyy' => ?_⟩
    obtain ⟨w, hxw, hy'w⟩ := h.forward_confluent (symm_mRel hxy) hyy'
    exact ⟨w, hxw, symm_mRel hy'w⟩
  · intro h
    refine ⟨fun {x y x'} hxy hxx' => ?_⟩
    obtain ⟨w, hyw, hwx'⟩ := h.backward_confluent (symm_mRel hxy) hxx'
    exact ⟨w, hyw, symm_mRel hwx'⟩

end NCML.CK

end
