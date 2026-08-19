module

public import NCML.Hilbert.Logics
public import NCML.CK.Confluence
public import NCML.CK.Soundness

@[expose] public section

/-- - [Pac24, Theorem 13] -/
theorem CKB_IKB_TFAE : List.TFAE [
  A ∈ LogicCKB,
  A ∈ LogicIKB,
  ∀ {κ : Type u}, ∀ M : CK.Model κ, [M.IsCKB] → M ⊧ A,
  ∀ {κ : Type u}, ∀ M : CK.Model κ, [M.IsIKB] → M ⊧ A,
] := by
  tfae_have 1 → 2 := by apply LogicCKB.subset_IKB;
  tfae_have 3 → 4 := fun h _ M _ => h M
  tfae_have 1 → 3 := fun h _ M _ => CK.Model.valid_of_mem_LogicCKB h
  tfae_have 2 → 4 := fun h _ M _ => CK.Model.valid_of_mem_LogicIKB h
  tfae_have 4 → 1 := by sorry
  tfae_finish

end
