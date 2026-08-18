module

public import NCML.CK.Confluence

@[expose] public section

namespace NCML.CK

open Model BDFormula

/-- The axiom schema `B□ := A 🡒 □◇A`. -/
abbrev BBox (A : BDFormula) : BDFormula := A 🡒 □◇A

/-- The three-point model of Proposition 9/Figure 2: `w := 0`, `v := 1`,
`v' := 2`, with `⪯ := diagonal ∪ {(v, v')}`, `∼ := {(w, v), (v, w)}` symmetric,
`V(a) := {w}`, and no fallible worlds. `v'` has no `mRel`-successor. -/
def counterModel : Model (Fin 3) where
  iRel x y := x = y ∨ (x = 1 ∧ y = 2)
  iRel_preorder := { refl := by grind, trans := by grind }
  mRel x y := (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)
  Fallible _ := False
  fallible_iRel := by grind
  fallible_mRel := by grind
  val x a := match a with
    | 0 => x = 0
    | _ => True
  val_persistent := by grind
  fallible_val := by grind

/-- The counterexample model's `mRel` is symmetric. -/
instance : SymmetricMRel counterModel.toFrame where
  symm_mRel := by grind [counterModel]

/-- The counterexample model's `mRel` is not forward confluent: `1 R 0` and
`1 ⪯ 2`, but `2` has no `mRel`-successor at all. -/
theorem counterModel_not_forwardConfluent : ¬ ForwardConfluent counterModel.toFrame := by
  rintro ⟨h⟩
  obtain ⟨y', -, hy'⟩ := h (x := 1) (y := 0) (x' := 2) (by grind [counterModel]) (by grind [counterModel])
  simp only [counterModel, Frame.mRel'] at hy'
  omega

/-- Proposition 9: `w := 0` forces `a` but does not force `□◇a`, so `B□`
fails at `w`, even though `mRel` is symmetric (and `W⊥ = ∅`). -/
theorem counterModel_not_forces_bBox :
    ¬ (0 : counterModel.World) ⊩ BBox (#0) := by
  intro h
  have h0 : (0 : counterModel.World) ⊩ (#0 : BDFormula) := by
    show counterModel.val 0 0
    grind [counterModel]
  have hbox : (0 : counterModel.World) ⊩ □◇(#0) := h 0 (by grind [counterModel]) h0
  have h1 : (1 : counterModel.World) ⊩ ◇(#0) :=
    hbox 0 1 (by grind [counterModel]) (by grind [counterModel])
  obtain ⟨z, hz, hzA⟩ := h1 2 (by grind [counterModel])
  simp only [counterModel, Frame.mRel'] at hz
  omega

/-- Proposition 9: `B□` is not valid over CK-models with symmetric `mRel`,
even without fallible worlds. -/
theorem exists_symmetric_not_forces_bBox :
    ∃ (κ : Type) (M : Model κ), SymmetricMRel M.toFrame ∧ ∃ x : M.World, ¬ x ⊩ BBox (#0) :=
  ⟨Fin 3, counterModel, inferInstance, 0, counterModel_not_forces_bBox⟩

end NCML.CK

end
