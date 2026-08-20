module

public import NCML.CK.Semantics
public import NCML.CK.Confluence
public import NCML.CK.Axioms.D
public import NCML.CK.Axioms.TDia
public import NCML.CK.Axioms.TBox
public import NCML.Hilbert.Logics

@[expose] public section

namespace CK

variable {κ : Type*} {M : Model κ}

namespace Model

theorem valid_of_mem_logic (h𝔸 : ∀ B ∈ 𝔸, M ⊧ B) (hA : A ∈ ProvableBDHilbert.logic 𝔸) : M ⊧ A := by
  replace hA : ProvableBDHilbert 𝔸 A := hA;
  intro x;
  induction hA generalizing x with
  | axm h => apply h𝔸 _ h;
  | imply₂ =>
    intro y _ hyABC z Iyz hzAB w Izw hwA;
    exact hyABC w (Trans.trans Iyz Izw) hwA w (refl _) $ hzAB w Izw hwA;
  | kBox =>
    intro y Ixy hyAB z Iyz hzA z₁ u₁ Izz₁ Mz₁u₁;
    exact hyAB z₁ u₁ (Trans.trans Iyz Izz₁) Mz₁u₁ u₁ (refl _) $ hzA z₁ u₁ Izz₁ Mz₁u₁;
  | kDia =>
    intro y Ixy hyAB z Iyz hzDiaA z₁ Izz₁;
    obtain ⟨u₁, Mz₁u₁, huA⟩ := hzDiaA z₁ Izz₁;
    use u₁;
    constructor;
    . exact Mz₁u₁;
    . exact (hyAB z₁ u₁ (Trans.trans Iyz Izz₁) Mz₁u₁) u₁ (refl _) huA;
  | mdp _ _ ihAB ihA => exact ihAB x x (refl _) (ihA x);
  | _ => grind;

theorem valid_of_mem_LogicCK (hA : A ∈ LogicCK) : M ⊧ A := valid_of_mem_logic (by simp) hA

/-- - [Pac24, Lemma 14] -/
theorem valid_of_mem_LogicCKB [M.IsCKB] (hA : A ∈ LogicCKB) : M ⊧ A :=
  valid_of_mem_logic (by
    rintro B (⟨C, rfl⟩ | ⟨C, rfl⟩);
    · exact valid_BBox_of_symmetricMRel_of_forwardConfluent;
    · exact valid_BDia_of_symmetricMRel_of_forwardConfluent;
  ) hA

/-- - [Pac24, Lemma 14] -/
theorem valid_of_mem_LogicIKB [M.IsIKB] (hA : A ∈ LogicIKB) : M ⊧ A :=
  valid_of_mem_logic (by
    rintro B ((((⟨C, D, rfl⟩ | ⟨C, D, rfl⟩) | rfl) | ⟨C, rfl⟩) | ⟨C, rfl⟩);
    · exact valid_FS_of_forwardConfluent_of_backwardConfluent;
    · exact valid_DP_of_forwardConfluent;
    · exact valid_N_of_symmetricMRel;
    · exact valid_BBox_of_symmetricMRel_of_forwardConfluent;
    · exact valid_BDia_of_symmetricMRel_of_forwardConfluent;
  ) hA

theorem valid_of_mem_LogicCKD [M.SerialMRel] (hA : A ∈ LogicCKD) : M ⊧ A := by
  sorry

theorem valid_of_mem_LogicCKPDia [M.SerialMRel] (hA : A ∈ LogicCKPDia) : M ⊧ A := by
  sorry

theorem valid_of_mem_LogicCKTDia [M.AscendingMRel] (hA : A ∈ LogicCKTDia) : M ⊧ A := by
  sorry

theorem valid_of_mem_LogicCKTBox [M.ReflexiveMComp] (hA : A ∈ LogicCKTBox) : M ⊧ A := by
  sorry

end Model

end CK

end
