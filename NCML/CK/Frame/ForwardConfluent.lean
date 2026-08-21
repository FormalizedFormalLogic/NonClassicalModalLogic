module

public import NCML.CK.Semantics

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A B : BDFormula}

namespace Frame

variable {F : Frame κ}

/-- - [Pac24, Definition 5] -/
class ForwardConfluent (F : Frame κ) : Prop where
  forward_confluent : ∀ {x y z : F.World}, x ⊏ y → x ≼ z → ∃ w, y ≼ w ∧ z ⊏ w

export ForwardConfluent (forward_confluent)

end Frame

namespace Model

open CK.Frame

variable {M : Model κ}
variable {x : M.World}

/-- - [Pac24, Proposition 6] -/
lemma dia_iff_forward_of_forwardConfluent [M.ForwardConfluent] : x ⊩[_] ◇A ↔ ∃ y, x ⊏ y ∧ y ⊩[_] A := by
  constructor;
  · intro h;
    exact h x (refl x);
  · rintro ⟨y, Mxy, hyA⟩ z Ixz;
    obtain ⟨w, Iyw, Mzw⟩ := forward_confluent Mxy Ixz;
    exact ⟨w, Mzw, forces_persistent hyA Iyw⟩;

end Model

namespace Frame

variable {F : Frame κ}

/--
- [dGSC25]
- [Pac24, Theorem 11]
- [Pac24, Corollary 12]
-/
lemma frameValidate_DP_of_frame_ForwardConfluent [F.ForwardConfluent] :
  F ⊧ (◇(A ⋎ B) 🡒 (◇A ⋎ ◇B)) := by
  intro V V_per V_fal x y _ hy;
  grind [Model.dia_iff_forward_of_forwardConfluent];

end Frame

end CK

end
