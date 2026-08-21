module

public import NCML.CK.Frame.FourDia
public import NCML.CK.Canonical
public import NCML.CK.Soundness

@[expose] public section

namespace BDLogic

class FourDia (L : BDLogic) where
  fourDia {A} : (◇◇A 🡒 ◇A) ∈ L
export FourDia (fourDia)

end BDLogic

instance : LogicCK4Dia.FourDia := ⟨by grind⟩

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Model

open CK.Frame

lemma valid_of_mem_LogicCK4Dia [M.FourDia] (hA : A ∈ LogicCK4Dia) : M ⊧ A :=
  valid_of_mem_logic
    (by rintro B ⟨C, rfl⟩;
        exact valid_of_toFrame_valid frameValidate_FourDia_of_frame_FourDia) hA

end Model

namespace CanonicalPair

section

variable {L : BDLogic} [L.CK] {A B : BDFormula} {P : CanonicalPair L}

/-- The formulas that, together with `□⁻¹P.theory`, entail a disjunction of formulas forbidden
by `P`. -/
def blocked (P : CanonicalPair L) : BDFormulaSet :=
  { A | ∃ B : BDFormula, □B ∈ P.theory ∧ ∃ C ∈ disjSet P.forbidden, (A 🡒 B 🡒 C) ∈ LogicCK }

/-- The formulas that CK-entail `◇B` for some `B ∈ P.blocked`. -/
def diaBlocked (P : CanonicalPair L) : BDFormulaSet :=
  { A | ∃ B ∈ P.blocked, (A 🡒 ◇B) ∈ LogicCK }

private lemma or_mem_blocked (h₁ : A ∈ P.blocked) (h₂ : B ∈ P.blocked) : A ⋎ B ∈ P.blocked := by
  obtain ⟨B₁, hB₁, C₁, ⟨K₁, hK₁ne, hK₁sub, rfl⟩, d₁⟩ := h₁;
  obtain ⟨B₂, hB₂, C₂, ⟨K₂, hK₂ne, hK₂sub, rfl⟩, d₂⟩ := h₂;
  refine ⟨B₁ ⋏ B₂, P.theory.mdp (P.theory.mdp (BDTheory.provable_mem box_and_intro) hB₁) hB₂,
    ⋁(K₁ ++ K₂), ⟨K₁ ++ K₂, by simp [hK₁ne], ?_, rfl⟩, ?_⟩;
  · intro C hC;
    rcases List.mem_append.mp hC with hC | hC;
    · exact hK₁sub C hC;
    · exact hK₂sub C hC;
  · exact or_imp
      (imp_trans (imp_trans d₁ (imp_comp_right andElim₁)) (imp_comp_left ldisj_append_left))
      (imp_trans (imp_trans d₂ (imp_comp_right andElim₂)) (imp_comp_left ldisj_append_right));

omit [L.CK] in
private lemma mem_blocked_of_imp (h₁ : (A 🡒 B) ∈ LogicCK) (h₂ : B ∈ P.blocked) : A ∈ P.blocked := by
  obtain ⟨C, hC, D, hD, d⟩ := h₂;
  exact ⟨C, hC, D, hD, imp_trans h₁ d⟩;

private lemma disjSet_blocked_subset : disjSet P.blocked ⊆ P.blocked :=
  disjSet_subset_of_or_mem or_mem_blocked mem_blocked_of_imp

private lemma or_mem_diaBlocked (h₁ : A ∈ P.diaBlocked) (h₂ : B ∈ P.diaBlocked) :
  A ⋎ B ∈ P.diaBlocked := by
  obtain ⟨A₁, hA₁, dA⟩ := h₁;
  obtain ⟨B₁, hB₁, dB⟩ := h₂;
  exact ⟨A₁ ⋎ B₁, or_mem_blocked hA₁ hB₁,
    or_imp (imp_trans dA (dia_mono orIntro₁)) (imp_trans dB (dia_mono orIntro₂))⟩;

omit [L.CK] in
private lemma mem_diaBlocked_of_imp (h₁ : (A 🡒 B) ∈ LogicCK) (h₂ : B ∈ P.diaBlocked) :
  A ∈ P.diaBlocked := by
  obtain ⟨C, hC, d⟩ := h₂;
  exact ⟨C, hC, imp_trans h₁ d⟩;

private lemma disjSet_diaBlocked_subset : disjSet P.diaBlocked ⊆ P.diaBlocked :=
  disjSet_subset_of_or_mem or_mem_diaBlocked mem_diaBlocked_of_imp

private lemma orDirected_diaBlocked : OrDirected L P.diaBlocked :=
  orDirected_of_or_mem or_mem_diaBlocked

omit [L.CK] in
private lemma dia_mem_diaBlocked (h : A ∈ P.blocked) : ◇A ∈ P.diaBlocked := ⟨A, h, imp_id⟩

private lemma avoid_diaBlocked : ∀ A ∈ P.diaBlocked, A ∉ P.theory := by
  rintro A ⟨B, hB, d⟩ hmem;
  have h₁ : ◇B ∈ P.theory := P.theory.mdp (BDTheory.provable_mem d) hmem;
  obtain ⟨C, hC, D, hD, d₂⟩ := hB;
  have h₂ : ◇(C 🡒 D) ∈ P.theory := P.theory.mdp (BDTheory.provable_mem (dia_mono d₂)) h₁;
  have h₃ : (◇(C 🡒 D) 🡒 ◇D) ∈ P.theory := P.theory.mdp (BDTheory.provable_mem dia_mdp) hC;
  have h₄ : ◇D ∈ P.theory := P.theory.mdp h₃ h₂;
  obtain ⟨K, hne, hsub, rfl⟩ := hD;
  exact P.avoid (◇(⋁K)) ⟨⋁K, ⟨K, hne, hsub, rfl⟩, rfl⟩ h₄;

end

end CanonicalPair

end CK

end
