module

public import NCML.Hilbert.Logics

@[expose] public section

namespace NCML.Hilbert

open BDFormula

/--
Theorem 3 (Arisaka, Das, Straßburger): `CKB ⊢ N`.
As `⊥ 🡒 □⊥` is a tautology, `CKB ⊢ ◇⊥ 🡒 ◇□⊥` by `Nec` and `K◇`.
But `◇□⊥ 🡒 ⊥` is an instance of `B◇`, so `CKB ⊢ ◇⊥ 🡒 ⊥`, i.e. `CKB ⊢ N`.
-/
theorem CKB_derives_N : (∼◇⊥) ∈ CKB := by
  have h1 : Derivation BAxioms (⊥ 🡒 □⊥) := Derivation.efq
  have h2 : Derivation BAxioms (□(⊥ 🡒 □⊥)) := Derivation.nec h1
  have h3 : Derivation BAxioms (◇⊥ 🡒 ◇(□⊥)) := Derivation.mp Derivation.kDia h2
  have h4 : Derivation BAxioms (◇(□⊥) 🡒 ⊥) := Derivation.axm (BAxioms.bDia ⊥)
  exact imp_trans h3 h4

end NCML.Hilbert

end
