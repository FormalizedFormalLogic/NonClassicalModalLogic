module

public import NCML.CK.Canonical
public import NCML.CK.Soundness

@[expose] public section

/-- - [MdP05, Theorem 1] -/
theorem LogicCK.mem_iff_valid {A : BDFormula} :
  A ∈ LogicCK ↔ ∀ {κ : Type 0}, ∀ M : CK.Model κ, M ⊧ A := by
  constructor;
  · intro h _ M;
    exact CK.Model.valid_of_mem_LogicCK h;
  · contrapose!;
    intro h;
    obtain ⟨P, h₁⟩ := CK.exists_not_forces_of_not_mem (L := LogicCK) h;
    exact ⟨_, CK.canonicalModel LogicCK, fun hM => h₁ (hM P)⟩;

end
