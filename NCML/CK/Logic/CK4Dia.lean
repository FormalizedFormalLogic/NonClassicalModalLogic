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

private lemma avoid_diaDisjSet_diaBlocked [L.FourDia] {T : BDTheory} [T.Mdp] [T.Of L]
  (h : ∀ A ∈ P.diaBlocked, A ∉ T) : ∀ A ∈ diaDisjSet P.diaBlocked, A ∉ T := by
  rintro A ⟨C, hC, rfl⟩ hmem;
  obtain ⟨D, hD, d⟩ := disjSet_diaBlocked_subset hC;
  have : T.Of LogicCK := BDTheory.of_logicCK (L := L);
  have h₁ : ◇◇D ∈ T := T.mdp (BDTheory.provable_mem (dia_mono d)) hmem;
  exact h (◇D) (dia_mem_diaBlocked hD) (T.mdp (T.subset L.fourDia) h₁);

private lemma avoid_diaDisjSet_blocked {T : BDTheory}
  (h : ∀ A ∈ P.diaBlocked, A ∉ T) : ∀ A ∈ diaDisjSet P.blocked, A ∉ T := by
  rintro A ⟨C, hC, rfl⟩;
  exact h (◇C) (dia_mem_diaBlocked (disjSet_blocked_subset hC));

private lemma avoid_disjSet_mdpClosure_union {P₁ : CanonicalPair L}
  (h : ∀ A ∈ P.blocked, A ∉ P₁.theory) :
  ∀ A ∈ disjSet P.forbidden, A ∉ BDTheory.mdpClosure (P₁.theory ∪ □⁻¹P.theory) := by
  rintro A ⟨K, hne, hsub, rfl⟩ hmem;
  obtain ⟨D, hD, E, hE, d⟩ := BDTheory.mdpClosure_union_finite_char hmem;
  exact h D ⟨E, hE, ⋁K, ⟨K, hne, hsub, rfl⟩, d⟩ hD;

end

end CanonicalPair

variable {L : BDLogic} [L.CK]

instance fourDia_canonicalModel [L.FourDia] : (canonicalModel L).FourDia where
  fourDia P := by
    obtain ⟨Y, hPY, hmdpY, hprimeY, hofY, havoidY⟩ :=
      exists_prime_mdpClosed_avoiding (L := L) (T := P.theory) (Z := P.diaBlocked)
        CanonicalPair.orDirected_diaBlocked CanonicalPair.avoid_diaBlocked;
    refine ⟨⟨Y, P.diaBlocked, CanonicalPair.avoid_diaDisjSet_diaBlocked havoidY⟩, hPY, ?_⟩;
    intro P₁ MQP₁;
    obtain ⟨Y₁, hP₁Y₁, hmdpY₁, hprimeY₁, hofY₁, havoidY₁⟩ :=
      exists_prime_mdpClosed_avoiding (L := L) (T := P₁.theory) (Z := P.diaBlocked)
        CanonicalPair.orDirected_diaBlocked MQP₁.2;
    refine ⟨⟨Y₁, P.blocked, CanonicalPair.avoid_diaDisjSet_blocked havoidY₁⟩, hP₁Y₁, ?_⟩;
    intro P₂ MQ₁P₂;
    have : BDTheory.Of L (P₂.theory ∪ □⁻¹P.theory) :=
      ⟨P₂.theory.subset.trans Set.subset_union_left⟩;
    obtain ⟨Q₂, h₁, -, havoid₂⟩ :=
      CanonicalPair.exists_avoiding (L := L)
        (T := BDTheory.mdpClosure (P₂.theory ∪ □⁻¹P.theory)) orDirected_disjSet
        (CanonicalPair.avoid_disjSet_mdpClosure_union MQ₁P₂.2);
    have h₂ : P₂.theory ∪ □⁻¹P.theory ⊆ Q₂.theory := BDTheory.subset_mdpClosure.trans h₁;
    exact ⟨Q₂,
      CanonicalPair.mRel_of_avoid_disjSet (Set.subset_union_right.trans h₂) havoid₂,
      fun _ => Set.subset_union_left.trans h₂⟩;

end CK

theorem LogicCK4Dia_TFAE {A : BDFormula} : List.TFAE [
  A ∈ LogicCK4Dia,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.FourDia] → F ⊧ A,
] := by
  tfae_have 1 → 2 := fun h _ F _ V V_per V_fal => CK.Model.valid_of_mem_LogicCK4Dia h
  tfae_have 2 → 1 := by
    contrapose!;
    intro h;
    obtain ⟨P, h₁⟩ := CK.exists_not_forces_of_not_mem h;
    refine ⟨_, (CK.canonicalModel LogicCK4Dia).toFrame, ?_⟩;
    and_intros;
    . infer_instance;
    . by_contra! hF;
      exact h₁ $ CK.Model.valid_of_toFrame_valid hF P;
  tfae_finish

end
