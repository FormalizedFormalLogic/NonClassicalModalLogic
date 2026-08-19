module

public import NCML.CK.Semantics

@[expose] public section

namespace CK

open NCML

variable {κ : Type*} {M : Model κ}
variable {x : M.World} {A B : BDFormula}


namespace Model

/-- - [Pac24, Definition 5] -/
class ForwardConfluent (M : Model κ) : Prop where
  forward_confluent : ∀ {x y x₁ : M.World}, x ⊏ y → x ≼ x₁ → ∃ y₁, y ≼ y₁ ∧ x₁ ⊏ y₁

export ForwardConfluent (forward_confluent)

/-- - [Pac24, Definition 5] -/
class BackwardConfluent (M : Model κ) : Prop where
  backward_confluent : ∀ {x y y₁ : M.World}, x ⊏ y → y ≼ y₁ → ∃ x₁, x ≼ x₁ ∧ x₁ ⊏ y₁

export BackwardConfluent (backward_confluent)

class SymmetricMRel (M : Model κ) : Prop where
  symm_mRel : ∀ {x y : M.World}, x ⊏ y → y ⊏ x

export SymmetricMRel (symm_mRel)

/-- - [Pac24, Definition 7] -/
class IsCKB (M : Model κ) : Prop extends SymmetricMRel M, ForwardConfluent M, BackwardConfluent M

/-- - [Pac24, Definition 7] -/
class IsIK (M : Model κ) : Prop extends ForwardConfluent M, BackwardConfluent M where
  not_fallible : ∀ x : M.World, ¬ M.Fallible x

/-- - [Pac24, Definition 7] -/
class IsIKB (M : Model κ) : Prop extends IsIK M, SymmetricMRel M


/-- - [Pac24, Proposition 6] -/
theorem dia_iff_forward_of_forwardConfluent [M.ForwardConfluent] : x ⊩[_] ◇A ↔ ∃ y, x ⊏ y ∧ y ⊩[_] A := by
  constructor;
  · intro h;
    exact h x (refl x);
  · rintro ⟨y, Mxy, hyA⟩ x₁ Ixx₁;
    obtain ⟨y₁, Iyy₁, Mx₁y₁⟩ := forward_confluent Mxy Ixx₁;
    exact ⟨y₁, Mx₁y₁, Model.Forces.persistent hyA Iyy₁⟩;

/-- - [Pac24, Proposition 10] -/
theorem forwardConfluent_iff_backwardConfluent_of_symmetricMRel [M.SymmetricMRel] :
  M.ForwardConfluent ↔ M.BackwardConfluent := by
  constructor;
  · intro h;
    constructor;
    intro x y y₁ Mxy Iyy₁;
    obtain ⟨x₁, Ixx₁, My₁x₁⟩ := h.forward_confluent (symm_mRel Mxy) Iyy₁;
    use x₁;
    constructor;
    . assumption;
    . exact symm_mRel My₁x₁;
  · intro h;
    constructor;
    intro x y x₁ Mxy Ixx₁;
    obtain ⟨y₁, Iyy₁, My₁x₁⟩ := h.backward_confluent (symm_mRel Mxy) Ixx₁;
    use y₁;
    constructor;
    . assumption;
    . exact symm_mRel My₁x₁;

/--
- [dGSC25]
- [Pac24, Theorem 11]
-/
theorem forces_N_of_symmetricMRel [M.SymmetricMRel] : x ⊩[_] ∼◇⊥ := by
  intro y _ hy;
  obtain ⟨z, Myz, hz⟩ := hy y (refl y);
  exact M.fallible_mRel hz (symm_mRel Myz);

/--
- [Pac24, Corollary 12]
-/
lemma valid_N_of_symmetricMRel [M.SymmetricMRel] : M ⊧ ∼◇⊥ := fun
  _ => forces_N_of_symmetricMRel


/--
- [dGSC25]
- [Pac24, Theorem 11]
-/
theorem forces_DP_of_forwardConfluent [M.ForwardConfluent] : x ⊩[_] (◇(A ⋎ B) 🡒 (◇A ⋎ ◇B)) := by
  intro y _ hy;
  obtain ⟨z, Myz, hz⟩ := Model.dia_iff_forward_of_forwardConfluent.mp hy;
  rcases hz with hz | hz;
  · exact Or.inl (Model.dia_iff_forward_of_forwardConfluent.mpr ⟨z, Myz, hz⟩);
  · exact Or.inr (Model.dia_iff_forward_of_forwardConfluent.mpr ⟨z, Myz, hz⟩);

/--
- [Pac24, Corollary 12]
-/
lemma valid_DP_of_forwardConfluent [M.ForwardConfluent] : M ⊧ (◇(A ⋎ B) 🡒 (◇A ⋎ ◇B)) := fun
  _ => forces_DP_of_forwardConfluent

/--
- [dGSC25]
- [Pac24, Theorem 11]
-/
theorem forces_FS_of_forwardConfluent_of_backwardConfluent [M.ForwardConfluent] [M.BackwardConfluent] :
  x ⊩[_] ((◇A 🡒 □B) 🡒 □(A 🡒 B)) := by
  intro y Ixy hy v u Iyv Mvu w Iuw hwA;
  obtain ⟨v₁, Ivv₁, Mv₁w⟩ := backward_confluent Mvu Iuw;
  have hv₁diaA : v₁ ⊩[_] ◇A := by
    intro v₂ Iv₁v₂;
    obtain ⟨w₁, Iww₁, Mv₂w₁⟩ := forward_confluent Mv₁w Iv₁v₂;
    exact ⟨w₁, Mv₂w₁, Model.Forces.persistent hwA Iww₁⟩;
  exact hy v₁ (Trans.trans Iyv Ivv₁) hv₁diaA v₁ w (refl v₁) Mv₁w;

/--
- [Pac24, Corollary 12]
-/
lemma valid_FS_of_forwardConfluent_of_backwardConfluent [M.ForwardConfluent] [M.BackwardConfluent] : M ⊧ ((◇A 🡒 □B) 🡒 □(A 🡒 B)) := fun
  _ => forces_FS_of_forwardConfluent_of_backwardConfluent

/--
- [Pac24, Lemma 14]
-/
theorem forces_BDia_of_symmetricMRel_of_forwardConfluent [M.SymmetricMRel] [M.ForwardConfluent] :
  x ⊩[_] (◇(□A) 🡒 A) := by
  intro y _ hy;
  obtain ⟨z, Myz, hz⟩ := Model.dia_iff_forward_of_forwardConfluent.mp hy;
  exact hz z y (refl z) (symm_mRel Myz);

/--
- [Pac24, Lemma 14]
-/
lemma valid_BDia_of_symmetricMRel_of_forwardConfluent [M.SymmetricMRel] [M.ForwardConfluent] : M ⊧ (◇(□A) 🡒 A) := fun
  _ => forces_BDia_of_symmetricMRel_of_forwardConfluent

/--
- [Pac24, Lemma 14]
-/
theorem forces_BBox_of_symmetricMRel_of_forwardConfluent [M.SymmetricMRel] [M.ForwardConfluent] :
  x ⊩[_] (A 🡒 □◇A) := by
  grind [forward_confluent, symm_mRel];

/--
- [Pac24, Lemma 14]
-/
lemma valid_BBox_of_symmetricMRel_of_forwardConfluent [M.SymmetricMRel] [M.ForwardConfluent] : M ⊧ (A 🡒 □◇A) := fun
  _ => forces_BBox_of_symmetricMRel_of_forwardConfluent

end Model

end CK

end
