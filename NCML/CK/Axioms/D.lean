module

public import NCML.CK.Canonical

@[expose] public section

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

/-- `⊏` is serial: every world has an `⊏`-successor. -/
class SerialMRel (M : Model κ) : Prop where
  serial_mRel : ∀ x : M.World, ∃ y, x ⊏ y

export SerialMRel (serial_mRel)

theorem valid_D_of_serialMRel [M.SerialMRel] : M ⊧ (□A 🡒 ◇A) := by
  intro x y Ixy hyBoxA u Iyu;
  obtain ⟨z, Muz⟩ := serial_mRel u;
  exact ⟨z, Muz, hyBoxA u z Iyu Muz⟩;

theorem valid_PDia_of_serialMRel [M.SerialMRel] : M ⊧ ◇⊤ := by
  intro x y Ixy;
  obtain ⟨z, Mxz⟩ := serial_mRel y;
  exact ⟨z, Mxz, by grind⟩;

theorem valid_of_mem_LogicCKD [M.SerialMRel] (hA : A ∈ LogicCKD) : M ⊧ A :=
  valid_of_mem_logic (by rintro B ⟨C, rfl⟩; exact valid_D_of_serialMRel) hA

theorem valid_of_mem_LogicCKPDia [M.SerialMRel] (hA : A ∈ LogicCKPDia) : M ⊧ A :=
  valid_of_mem_logic (by rintro B rfl; exact valid_PDia_of_serialMRel) hA

end Model

/-- The canonical model of a logic proving `D` has a serial `⊏`. -/
lemma serialMRel_canonicalModel {𝔸 : Set BDFormula} (h𝔸 : ∀ A : BDFormula, (□A 🡒 ◇A) ∈ logic 𝔸) :
  (canonicalModel 𝔸).SerialMRel where
  serial_mRel w := by
    have := BDTheory.prebox_of' (𝔸 := 𝔸) (T := w.th);
    have h : ∀ C ∈ disjSet w.forb, C ∉ □⁻¹w.th := by
      rintro C ⟨K, hne, hsub, rfl⟩ hmem;
      exact w.avoid (◇(⋁K)) ⟨⋁K, ⟨K, hne, hsub, rfl⟩, rfl⟩
        (w.th.mdp (BDTheory.provable_mem (h𝔸 (⋁K))) hmem);
    obtain ⟨v, hXv, -, havoid⟩ :=
      CanonicalPair.exists_avoiding (𝔸 := 𝔸) (T := □⁻¹w.th) orDirected_disjSet h;
    exact ⟨v, CanonicalPair.mRel_of_avoid_disjSet hXv havoid⟩;

instance : (canonicalModel { □A 🡒 ◇A | (A) }).SerialMRel :=
  serialMRel_canonicalModel fun _ => LogicCKD.provable_D

end CK

/-- The model characterization of `CK + D`: a formula is a theorem of `CK + D` exactly when it is
valid on every CK-model with a serial `⊏`. -/
theorem LogicCKD.mem_iff_valid {A : BDFormula} :
  A ∈ LogicCKD ↔ ∀ {κ : Type 0}, ∀ M : CK.Model κ, [M.SerialMRel] → M ⊧ A := by
  constructor;
  · intro h _ M _;
    exact CK.Model.valid_of_mem_LogicCKD h;
  · contrapose!;
    intro h;
    obtain ⟨w, hw⟩ := CK.exists_not_forces_of_not_mem h;
    exact ⟨_, CK.canonicalModel _, inferInstance, fun hM => hw (hM w)⟩;

/-- The model characterization of `CK + PDia`: a formula is a theorem of `CK + PDia` exactly when
it is valid on every CK-model with a serial `⊏`. -/
theorem LogicCKPDia.mem_iff_valid {A : BDFormula} :
  A ∈ LogicCKPDia ↔ ∀ {κ : Type 0}, ∀ M : CK.Model κ, [M.SerialMRel] → M ⊧ A := by
  rw [← LogicCKD.eq_CKPDia];
  exact LogicCKD.mem_iff_valid;

end
