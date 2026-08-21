module

public import NCML.CK.Logic.CKTBox
public import NCML.CK.Logic.CKTDia
public import NCML.CK.Logic.CK4Box
public import NCML.CK.Logic.CK4Dia
public import NCML.CK.Frame.ReflexiveMRel
public import NCML.CK.Frame.TransitiveMRel
public import NCML.CK.Frame.BackwardConfluent

@[expose] public section

/-!
# The hereditary canonical model

For a logic `L`, the canonical model on `CanonicalPair L` whose `⊏` hands the forbidden set on to
every `⊏`-successor rather than blocking it, and its truth lemma.

- [BDF21, Definition IV.4]
-/

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

/-- The canonical model of `L` whose `⊏` hands `forbidden` on to every successor.

- [BDF21, Definition IV.4]
-/
def hereditaryCanonicalModel (L : BDLogic) [L.CK] : Model (CanonicalPair L) where
  iRel' X Y := X.theory ⊆ Y.theory
  iRel_preorder := {
    refl := fun _ => subset_rfl,
    trans := fun _ _ _ => subset_trans
  }
  mRel' X Y := □⁻¹X.theory ⊆ Y.theory ∧ X.forbidden ⊆ Y.forbidden
  Fallible' X := ⊥ ∈ X.theory
  fallible_iRel' h IXY := IXY h
  fallible_mRel' h MXY := MXY.1 (by rw [CanonicalPair.theory_eq_univ_of_bot_mem h]; trivial)
  fallible_exists_mRel' h :=
    ⟨CanonicalPair.univ L, Set.subset_univ _, by
      rw [CanonicalPair.forbidden_eq_empty_of_bot_mem h];
      exact Set.empty_subset _⟩
  val X a := (#a) ∈ X.theory
  val_persistent h IXY := IXY h
  fallible_val h := by rw [CanonicalPair.theory_eq_univ_of_bot_mem h]; trivial

namespace CanonicalPair

section

variable {L : BDLogic} [L.CK] {A : BDFormula} {X : CanonicalPair L}

lemma hereditary_exists_mRel_of_box_not_mem (h : □A ∉ X.theory) :
  ∃ Y : CanonicalPair L, (hereditaryCanonicalModel L).mRel X.erase Y ∧ A ∉ Y.theory := by
  obtain ⟨Y, h₁, -, havoid⟩ :=
    exists_avoiding (L := L) (T := □⁻¹X.theory) (Z := {A}) orDirected_singleton
      (by rintro C rfl; exact h);
  exact ⟨Y, ⟨h₁, by simp⟩, havoid A rfl⟩;

private lemma hereditary_avoid_diaDisjSet_impSet [L.FourDia] (h : ◇A ∈ X.theory) :
  ∀ C ∈ diaDisjSet X.forbidden, C ∉ BDTheory.impSet (□⁻¹X.theory) A := by
  rintro C ⟨D, hD, rfl⟩ hmem;
  have h₁ : (◇A 🡒 ◇◇D) ∈ X.theory := X.theory.mdp (BDTheory.provable_mem kDia) hmem;
  have h₂ : ◇◇D ∈ X.theory := X.theory.mdp h₁ h;
  exact X.avoid (◇D) ⟨D, hD, rfl⟩ (X.theory.mdp (X.theory.subset L.fourDia) h₂);

lemma hereditary_exists_mRel_of_dia_mem [L.FourDia] (h : ◇A ∈ X.theory) :
  ∃ Y : CanonicalPair L, (hereditaryCanonicalModel L).mRel X Y ∧ A ∈ Y.theory := by
  obtain ⟨Y, hY, hmdp, hprime, hof, havoid⟩ :=
    exists_prime_mdpClosed_avoiding (L := L) (T := BDTheory.impSet (□⁻¹X.theory) A)
      (Z := diaDisjSet X.forbidden) orDirected_diaDisjSet (hereditary_avoid_diaDisjSet_impSet h);
  exact ⟨⟨Y, X.forbidden, havoid⟩, ⟨BDTheory.subset_impSet.trans hY, subset_rfl⟩,
    hY BDTheory.self_mem_impSet⟩;

lemma hereditary_exists_iRel_of_dia_not_mem [L.TDia] (h : ◇A ∉ X.theory) :
  ∃ Y : CanonicalPair L, (hereditaryCanonicalModel L).iRel X Y ∧
  ∀ Z : CanonicalPair L, (hereditaryCanonicalModel L).mRel Y Z → A ∉ Z.theory := by
  refine ⟨⟨X.theory, {A}, avoid_diaDisjSet_of_dia_not_mem h⟩, subset_rfl, ?_⟩;
  intro Z MYZ;
  exact forbidden_not_mem_theory (MYZ.2 rfl);

end

section

variable {L : BDLogic} [L.CK] [L.TDia] [L.FourDia] {A : BDFormula} {X : CanonicalPair L}

/-- - [BDF21, Lemma IV.9] -/
lemma hereditary_truthlemma : X ⊩[hereditaryCanonicalModel L] A ↔ A ∈ X.theory := by
  induction A generalizing X with
  | atom a => exact Iff.rfl;
  | falsum => exact Iff.rfl;
  | and A B ihA ihB =>
    constructor;
    · rintro ⟨hA, hB⟩;
      exact BDTheory.and_mem (ihA.mp hA) (ihB.mp hB);
    · intro h;
      constructor;
      . exact ihA.mpr (X.theory.mdp (BDTheory.provable_mem andElim₁) h);
      . exact ihB.mpr (X.theory.mdp (BDTheory.provable_mem andElim₂) h);
  | or A B ihA ihB =>
    constructor;
    · rintro (hA | hB);
      · exact X.theory.mdp (BDTheory.provable_mem orIntro₁) (ihA.mp hA);
      · exact X.theory.mdp (BDTheory.provable_mem orIntro₂) (ihB.mp hB);
    · intro h;
      rcases X.theory.prime h <;> grind;
  | imply A B ihA ihB =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨Y, IXY, h₁, h₂⟩ := CanonicalPair.exists_iRel_of_imply_not_mem hc;
      exact h₂ (ihB.mp (h Y IXY (ihA.mpr h₁)));
    · intro h Y IXY h₁;
      exact ihB.mpr (Y.theory.mdp (IXY h) (ihA.mp h₁));
  | box A ih =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨Y, MXY, h₁⟩ := hereditary_exists_mRel_of_box_not_mem hc;
      exact h₁ (ih.mp (h X.erase Y CanonicalPair.iRel_erase MXY));
    · intro h Y Z IXY MYZ;
      exact ih.mpr (MYZ.1 (IXY h));
  | dia A ih =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨Y, IXY, hblock⟩ := hereditary_exists_iRel_of_dia_not_mem hc;
      obtain ⟨Z, MYZ, h₁⟩ := h Y IXY;
      exact hblock Z MYZ (ih.mp h₁);
    · intro h Y IXY;
      obtain ⟨Z, MYZ, h₁⟩ := hereditary_exists_mRel_of_dia_mem (IXY h);
      exact ⟨Z, MYZ, ih.mpr h₁⟩;

end

end CanonicalPair

section

variable {L : BDLogic} [L.CK] [L.TDia] [L.FourDia] {A : BDFormula}

lemma hereditary_exists_not_forces_of_not_mem (h : A ∉ L) :
  ∃ X : CanonicalPair L, X ⊮[hereditaryCanonicalModel L] A := by
  obtain ⟨X, -, -, havoid⟩ :=
    CanonicalPair.exists_avoiding (L := L) (T := L) (Z := {A}) orDirected_singleton
      (by rintro C rfl; exact h);
  exact ⟨X, fun h₁ => havoid A rfl (CanonicalPair.hereditary_truthlemma.mp h₁)⟩;

end

variable {L : BDLogic} [L.CK]

instance reflexiveMRel_hereditaryCanonicalModel [L.TBox] :
    (hereditaryCanonicalModel L).ReflexiveMRel where
  refl_mRel X := ⟨fun _ hA => X.theory.mdp (X.theory.subset L.tBox) hA, subset_rfl⟩

instance transitiveMRel_hereditaryCanonicalModel [L.FourBox] :
    (hereditaryCanonicalModel L).TransitiveMRel where
  trans_mRel {X _ _} MXY MYZ := ⟨
    fun _ hA => MYZ.1 (MXY.1 (X.theory.mdp (X.theory.subset L.fourBox) hA)),
    MXY.2.trans MYZ.2
  ⟩

/-- - [BDF21, Proposition IV.7] -/
instance backwardConfluent_hereditaryCanonicalModel :
    (hereditaryCanonicalModel L).BackwardConfluent where
  backward_confluent {X Y Z} MXY IYZ := by
    use X.erase;
    and_intros;
    . exact CanonicalPair.iRel_erase;
    . intro A hA;
      exact IYZ (MXY.1 hA);
    . tauto;

end CK

end
