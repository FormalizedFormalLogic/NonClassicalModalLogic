module

public import NCML.CK.Semantics
public import NCML.CK.Confluence
public import NCML.CK.Axioms.BBox
public import NCML.CK.Axioms.BDia
public import NCML.Hilbert.Logics

@[expose] public section

namespace CK

variable {κ : Type*} {M : Model κ}

namespace Model

open CK.Frame

lemma valid_of_mem_logic (h𝔸 : ∀ B ∈ 𝔸, M ⊧ B) (hA : A ∈ ProvableBDHilbert.logic 𝔸) : M ⊧ A := by
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

lemma valid_of_mem_LogicCK (hA : A ∈ LogicCK) : M ⊧ A := valid_of_mem_logic (by simp) hA

/-- - [Pac24, Lemma 14] -/
lemma valid_of_mem_LogicCKB [M.IsCKB] (hA : A ∈ LogicCKB) : M ⊧ A :=
  valid_of_mem_logic (by
    rintro B (⟨C, rfl⟩ | ⟨C, rfl⟩);
    · exact valid_of_toFrame_valid valid_BBox_of_circularMComp;
    · exact valid_of_toFrame_valid valid_BDia_of_returningMComp;
  ) hA

/-- - [Pac24, Lemma 14] -/
lemma valid_of_mem_LogicIKB [M.IsIKB] (hA : A ∈ LogicIKB) : M ⊧ A :=
  valid_of_mem_logic (by
    rintro B ((((⟨C, D, rfl⟩ | ⟨C, D, rfl⟩) | rfl) | ⟨C, rfl⟩) | ⟨C, rfl⟩);
    · exact valid_of_toFrame_valid valid_FS_of_forwardConfluent_of_backwardConfluent;
    · exact valid_of_toFrame_valid valid_DP_of_forwardConfluent;
    · exact valid_of_toFrame_valid valid_N_of_symmetricMRel;
    · exact valid_of_toFrame_valid valid_BBox_of_circularMComp;
    · exact valid_of_toFrame_valid valid_BDia_of_returningMComp;
  ) hA

end Model

end CK

end
