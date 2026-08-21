module

public import NCML.CK.Frame.SymmetricMRel
public import NCML.CK.Frame.ForwardConfluent

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A B : BDFormula}

namespace Frame

variable {F : Frame κ}

/-- - [Pac24, Definition 5] -/
class BackwardConfluent (F : Frame κ) : Prop where
  backward_confluent : ∀ {x y z : F.World}, x ⊏ y → y ≼ z → ∃ w, x ≼ w ∧ w ⊏ z

export BackwardConfluent (backward_confluent)

/-- - [Pac24, Proposition 10] -/
lemma forwardConfluent_iff_backwardConfluent_of_symmetricMRel [F.SymmetricMRel] :
  F.ForwardConfluent ↔ F.BackwardConfluent := by
  constructor;
  · intro h;
    constructor;
    intro x y z Mxy Iyz;
    obtain ⟨w, Ixw, Mzw⟩ := h.forward_confluent (symm_mRel Mxy) Iyz;
    exact ⟨w, Ixw, symm_mRel Mzw⟩;
  · intro h;
    constructor;
    intro x y z Mxy Ixz;
    obtain ⟨w, Iyw, Mwz⟩ := h.backward_confluent (symm_mRel Mxy) Ixz;
    exact ⟨w, Iyw, symm_mRel Mwz⟩;

/--
- [dGSC25]
- [Pac24, Theorem 11]
- [Pac24, Corollary 12]
-/
lemma valid_FS_of_forwardConfluent_of_backwardConfluent [F.ForwardConfluent] [F.BackwardConfluent] :
  F ⊧ ((◇A 🡒 □B) 🡒 □(A 🡒 B)) := by
  intro V V_per V_fal x y Ixy hy z w Iyz Mzw v Iwv hvA;
  obtain ⟨u, Izu, Muv⟩ := backward_confluent Mzw Iwv;
  have huDiaA : u ⊩[_] ◇A := by
    intro x₁ Iux₁;
    obtain ⟨y₁, Ivy₁, Mx₁y₁⟩ := forward_confluent Muv Iux₁;
    exact ⟨y₁, Mx₁y₁, forces_persistent hvA Ivy₁⟩;
  exact hy u (Trans.trans Iyz Izu) huDiaA u v (refl u) Muv;

end Frame

end CK

end
