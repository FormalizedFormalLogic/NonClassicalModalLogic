module

public import NCML.Hilbert.Basic

@[expose] public section

namespace NCML.Hilbert

open BDFormula

/-- The dual `B` axiom schemas (`B□` and `B◇`), as instance sets over all formulas. -/
inductive BAxioms : Set BDFormula
  | bBox (A : BDFormula) : BAxioms (A 🡒 □◇A)
  | bDia (A : BDFormula) : BAxioms (◇(□A) 🡒 A)

/-- The `IK` axiom schemas `FS`, `DP`, and `N`, as instance sets over all formulas. -/
inductive IKAxioms : Set BDFormula
  | fs (A B : BDFormula) : IKAxioms ((◇A 🡒 □B) 🡒 □(A 🡒 B))
  | dp (A B : BDFormula) : IKAxioms (◇(A ⋎ B) 🡒 ◇A ⋎ ◇B)
  | n                    : IKAxioms (∼◇⊥)

/-- `CK`, the least logic containing all intuitionistic tautologies together with `K□` and `K◇`. -/
abbrev CK : Set BDFormula := theLogic ∅

/-- `CKB := CK + {B□, B◇}` (Definition 2). -/
abbrev CKB : Set BDFormula := theLogic BAxioms

/-- `IK := CK + {FS, DP, N}` (Definition 2). -/
abbrev IK : Set BDFormula := theLogic IKAxioms

/-- `IKB := IK + {B□, B◇} = CKB + {FS, DP, N}` (Definition 2). -/
abbrev IKB : Set BDFormula := theLogic (IKAxioms ∪ BAxioms)

theorem CK_subset_CKB : CK ⊆ CKB := theLogic_monotone (Set.empty_subset _)
theorem CK_subset_IK : CK ⊆ IK := theLogic_monotone (Set.empty_subset _)
theorem CKB_subset_IKB : CKB ⊆ IKB := theLogic_monotone (Set.subset_union_right)
theorem IK_subset_IKB : IK ⊆ IKB := theLogic_monotone (Set.subset_union_left)

end NCML.Hilbert

end
