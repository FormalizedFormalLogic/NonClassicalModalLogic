module

public import NCML.CK.Logic.CKTBox
public import NCML.CK.Logic.CKTDia
public import NCML.CK.Logic.CK4Box
public import NCML.CK.Logic.CK4Dia
public import NCML.CK.Frame.ReflexiveMRel
public import NCML.CK.Frame.TransitiveMRel
public import NCML.CK.Frame.BackwardConfluent
public import NCML.CK.Frame.CS4

@[expose] public section

/-!
# The hereditary canonical model

For a logic `L`, the canonical model on `CanonicalPair L` whose `⊏` hands the forbidden set on to
every `⊏`-successor rather than blocking it, and its truth lemma.

- [BDFD21, Definition IV.4]
-/

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

namespace CanonicalPair

variable {L : BDLogic} [L.CK] [L.FourDia] {A : BDFormula} {X : CanonicalPair L}

private lemma hereditary_avoid_diaDisjSet_impSet (h : ◇A ∈ X.theory) :
  ∀ C ∈ diaDisjSet X.forbidden, C ∉ BDTheory.impSet (□⁻¹X.theory) A := by
  rintro C ⟨D, hD, rfl⟩ hmem;
  have h₁ : (◇A 🡒 ◇◇D) ∈ X.theory := X.theory.mdp (BDTheory.provable_mem kDia) hmem;
  have h₂ : ◇◇D ∈ X.theory := X.theory.mdp h₁ h;
  exact X.avoid (◇D) ⟨D, hD, rfl⟩ (X.theory.mdp (X.theory.subset L.fourDia) h₂);

end CanonicalPair

/-- The `⊏` of the hereditary canonical model hands `forbidden` on to every successor.

- [BDFD21, Definition IV.4]
-/
def hereditaryCanonicalRel (L : BDLogic) [L.CK] [L.TDia] [L.FourDia] : CanonicalRel L where
  Rel X Y := X.forbidden ⊆ Y.forbidden
  rel_univ h := by
    rw [CanonicalPair.forbidden_eq_empty_of_bot_mem h];
    exact Set.empty_subset _
  exists_of_box_not_mem {X A} h := by
    obtain ⟨Y, h₁, -, havoid⟩ :=
      CanonicalPair.exists_avoiding (L := L) (T := □⁻¹X.theory) (Z := {A}) orDirected_singleton
        (by rintro C rfl; exact h);
    exact ⟨Y, ⟨h₁, by simp⟩, havoid A rfl⟩;
  exists_of_dia_mem {X A} h := by
    obtain ⟨Y, hY, hmdp, hprime, hof, havoid⟩ :=
      exists_prime_mdpClosed_avoiding (L := L) (T := BDTheory.impSet (□⁻¹X.theory) A)
        (Z := diaDisjSet X.forbidden) orDirected_diaDisjSet
        (CanonicalPair.hereditary_avoid_diaDisjSet_impSet h);
    exact ⟨⟨Y, X.forbidden, havoid⟩, ⟨BDTheory.subset_impSet.trans hY, subset_rfl⟩,
      hY BDTheory.self_mem_impSet⟩;
  exists_of_dia_not_mem {X A} h := by
    refine ⟨⟨X.theory, {A}, CanonicalPair.avoid_diaDisjSet_of_dia_not_mem h⟩, subset_rfl, ?_⟩;
    intro Z MYZ;
    exact CanonicalPair.forbidden_not_mem_theory (MYZ.2 rfl);

@[simp] lemma hereditaryCanonicalRel_rel {L : BDLogic} [L.CK] [L.TDia] [L.FourDia]
  {X Y : CanonicalPair L} :
  (hereditaryCanonicalRel L).Rel X Y ↔ X.forbidden ⊆ Y.forbidden := Iff.rfl

/-- The canonical model of `L` whose `⊏` hands `forbidden` on to every successor.

- [BDFD21, Definition IV.4]
-/
def hereditaryCanonicalModel (L : BDLogic) [L.CK] [L.TDia] [L.FourDia] :
  Model (CanonicalPair L) :=
  canonicalModelWith L (hereditaryCanonicalRel L)

variable {L : BDLogic} [L.CK] [L.TDia] [L.FourDia] {A : BDFormula} {X : CanonicalPair L}

/-- - [BDFD21, Lemma IV.9] -/
lemma hereditary_truthlemma : X ⊩[hereditaryCanonicalModel L] A ↔ A ∈ X.theory :=
  (hereditaryCanonicalRel L).truthlemma

lemma hereditary_exists_not_forces_of_not_mem (h : A ∉ L) :
  ∃ X : CanonicalPair L, X ⊮[hereditaryCanonicalModel L] A :=
  (hereditaryCanonicalRel L).exists_not_forces_of_not_mem h

instance reflexiveMRel_hereditaryCanonicalModel [L.TBox] :
    (hereditaryCanonicalModel L).ReflexiveMRel where
  refl_mRel X := ⟨fun _ hA => X.theory.mdp (X.theory.subset L.tBox) hA, subset_rfl⟩

instance transitiveMRel_hereditaryCanonicalModel [L.FourBox] :
    (hereditaryCanonicalModel L).TransitiveMRel where
  trans_mRel {X _ _} MXY MYZ := ⟨
    fun _ hA => MYZ.1 (MXY.1 (X.theory.mdp (X.theory.subset L.fourBox) hA)),
    Set.Subset.trans MXY.2 MYZ.2
  ⟩

/-- - [BDFD21, Proposition IV.7] -/
instance backwardConfluent_hereditaryCanonicalModel :
    (hereditaryCanonicalModel L).BackwardConfluent where
  backward_confluent {X Y Z} MXY IYZ := by
    use X.erase;
    and_intros;
    . exact CanonicalPair.iRel_erase;
    . intro A hA;
      exact IYZ (MXY.1 hA);
    . simp;

instance cs4_hereditaryCanonicalModel [L.TBox] [L.FourBox] :
    (hereditaryCanonicalModel L).CS4 where

end CK

end
