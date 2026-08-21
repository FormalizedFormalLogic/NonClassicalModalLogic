module

public import NCML.CK.Semantics

@[expose] public section

namespace CK

variable {κ : Type*}

namespace Frame

variable {F : Frame κ}

class SymmetricMRel (F : Frame κ) : Prop where
  symm_mRel : ∀ {x y : F.World}, x ⊏ y → y ⊏ x

export SymmetricMRel (symm_mRel)

/--
- [dGSC25]
- [Pac24, Theorem 11]
- [Pac24, Corollary 12]
-/
lemma frameValidate_N_of_frame_SymmetricMRel [F.SymmetricMRel] : F ⊧ ∼◇⊥ := by
  intro V V_per V_fal x y _ hy;
  obtain ⟨z, Myz, hz⟩ := hy y (refl y);
  exact F.fallible_mRel hz (symm_mRel Myz);

end Frame

end CK

end
