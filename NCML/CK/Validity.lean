module

public import NCML.CK.Confluence

@[expose] public section

namespace NCML.CK

open Model BDFormula

variable {κ : Type*} {M : Model κ} {A B : BDFormula}

/-- The axiom schema `N := ∼◇⊥`. -/
abbrev N : BDFormula := ∼◇⊥

/-- The axiom schema `DP := ◇(A ⋎ B) 🡒 (◇A ⋎ ◇B)`. -/
abbrev DP (A B : BDFormula) : BDFormula := ◇(A ⋎ B) 🡒 (◇A ⋎ ◇B)

/-- The axiom schema `FS := (◇A 🡒 □B) 🡒 □(A 🡒 B)`. -/
abbrev FS (A B : BDFormula) : BDFormula := (◇A 🡒 □B) 🡒 □(A 🡒 B)

/-- Theorem 11, part 1 (de Groot–Shillito–Clouston): in a CK-model with
symmetric `mRel`, `N` is forced everywhere. -/
theorem Model.forces_N [SymmetricMRel M.toFrame] (x : M.World) : x ⊩ N := by
  intro y _ hy
  obtain ⟨z, hyz, hz⟩ := hy y (refl y)
  exact M.fallible_mRel hz (symm_mRel hyz)

/-- Theorem 11, part 2 (de Groot–Shillito–Clouston): in a CK-model with
forward confluent `mRel`, `DP` is forced everywhere. -/
theorem Model.forces_DP [ForwardConfluent M.toFrame] (x : M.World) (A B : BDFormula) :
    x ⊩ DP A B := by
  intro y _ hy
  obtain ⟨z, hyz, hz⟩ := Model.dia_iff_forward.mp hy
  rcases hz with hz | hz
  · exact Or.inl (Model.dia_iff_forward.mpr ⟨z, hyz, hz⟩)
  · exact Or.inr (Model.dia_iff_forward.mpr ⟨z, hyz, hz⟩)

/-- Theorem 11, part 2 (de Groot–Shillito–Clouston): in a CK-model with
forward and backward confluent `mRel`, `FS` is forced everywhere. -/
theorem Model.forces_FS [ForwardConfluent M.toFrame] [BackwardConfluent M.toFrame]
    (x : M.World) (A B : BDFormula) : x ⊩ FS A B := by
  intro y hxy hy v u hyv hvu w huw hwA
  obtain ⟨v₁, hvv₁, hv₁w⟩ := backward_confluent hvu huw
  have hv₁diaA : v₁ ⊩ ◇A := by
    intro v₁' hv₁v₁'
    obtain ⟨w', hww', hv₁'w'⟩ := forward_confluent hv₁w hv₁v₁'
    exact ⟨w', hv₁'w', Model.Forces.persistent hwA hww'⟩
  exact hy v₁ (Trans.trans hyv hvv₁) hv₁diaA v₁ w (refl v₁) hv₁w

/-- Validity of a formula across all CKB-models. -/
def CKBValid (A : BDFormula) : Prop := ∀ {κ : Type*} (M : Model κ) [IsCKB M.toFrame], M ⊧ A

/-- Corollary 12: `N` is CKB-valid. -/
theorem ckbValid_N : CKBValid N := fun M _ x => M.forces_N x

/-- Corollary 12: `DP` is CKB-valid. -/
theorem ckbValid_DP (A B : BDFormula) : CKBValid (DP A B) := fun M _ x => M.forces_DP x A B

/-- Corollary 12: `FS` is CKB-valid. -/
theorem ckbValid_FS (A B : BDFormula) : CKBValid (FS A B) := fun M _ x => M.forces_FS x A B

end NCML.CK

end
