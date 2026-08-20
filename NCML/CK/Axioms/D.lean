module

public import NCML.CK.Canonical

@[expose] public section

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

class SerialMRel (M : Model κ) : Prop where
  serial_mRel : ∀ x : M.World, ∃ y, x ⊏ y

export SerialMRel (serial_mRel)

lemma valid_D_of_serialMRel [M.SerialMRel] : M ⊧ (□A 🡒 ◇A) := by
  intro x y Ixy hyBoxA u Iyu;
  obtain ⟨z, Muz⟩ := serial_mRel u;
  exact ⟨z, Muz, hyBoxA u z Iyu Muz⟩;

lemma valid_PDia_of_serialMRel [M.SerialMRel] : M ⊧ ◇⊤ := by
  intro x y Ixy;
  obtain ⟨z, Mxz⟩ := serial_mRel y;
  exact ⟨z, Mxz, by grind⟩;

lemma valid_of_mem_LogicCKD [M.SerialMRel] (hA : A ∈ LogicCKD) : M ⊧ A :=
  valid_of_mem_logic (by rintro B ⟨C, rfl⟩; exact valid_D_of_serialMRel) hA

lemma valid_of_mem_LogicCKPDia [M.SerialMRel] (hA : A ∈ LogicCKPDia) : M ⊧ A :=
  valid_of_mem_logic (by rintro B rfl; exact valid_PDia_of_serialMRel) hA

end Model

variable {𝔸 : Set BDFormula}

lemma serialMRel_canonicalModel (h𝔸 : ∀ {A}, (□A 🡒 ◇A) ∈ logic 𝔸) :
  (canonicalModel 𝔸).SerialMRel where
  serial_mRel w := by
    have := BDTheory.prebox_of' (𝔸 := 𝔸) (T := w.th);
    have h : ∀ C ∈ disjSet w.forb, C ∉ □⁻¹w.th := by
      rintro C ⟨K, hne, hsub, rfl⟩ hmem;
      exact w.avoid (◇(⋁K)) ⟨⋁K, ⟨K, hne, hsub, rfl⟩, rfl⟩
        (w.th.mdp (BDTheory.provable_mem (h𝔸)) hmem);
    obtain ⟨v, hXv, -, havoid⟩ :=
      CanonicalPair.exists_avoiding (𝔸 := 𝔸) (T := □⁻¹w.th) orDirected_disjSet h;
    exact ⟨v, CanonicalPair.mRel_of_avoid_disjSet hXv havoid⟩;

lemma serialMRel_canonicalModel_of_mem (h : ∀ {A}, □A 🡒 ◇A ∈ 𝔸) : (canonicalModel 𝔸).SerialMRel :=
  serialMRel_canonicalModel $ by tauto;

end CK

theorem LogicCKD_TFAE {A : BDFormula} : List.TFAE [
  A ∈ LogicCKD,
  A ∈ LogicCKPDia,
  ∀ {κ : Type 0}, ∀ M : CK.Model κ, [M.SerialMRel] → M ⊧ A,
] := by
  tfae_have 1 → 2 := LogicCKD.eq_CKPDia ▸ id
  tfae_have 2 → 3 := fun h _ M _ => CK.Model.valid_of_mem_LogicCKPDia h
  tfae_have 3 → 1 := by
    contrapose!;
    intro h;
    obtain ⟨w, hw⟩ := CK.exists_not_forces_of_not_mem h;
    exact ⟨_, CK.canonicalModel _, CK.serialMRel_canonicalModel_of_mem (by grind), fun hM => hw (hM w)⟩;
  tfae_finish

end
