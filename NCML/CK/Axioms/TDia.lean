module

public import NCML.CK.Axioms.D

@[expose] public section

open ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

variable {κ : Type*} {M : Model κ}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class AscendingMRel (F : Frame κ) : Prop where
  ascending_mRel : ∀ x : F.World, ∃ z, x ⊏ z ∧ (x ≼ z ∨ F.Fallible z)

export AscendingMRel (ascending_mRel)

class StrictlyAscendingMRel (F : Frame κ) : Prop where
  strictly_ascending_mRel : ∀ x : F.World, ∃ z, x ⊏ z ∧ x ≼ z

export StrictlyAscendingMRel (strictly_ascending_mRel)

instance [F.StrictlyAscendingMRel] : F.AscendingMRel where
  ascending_mRel x := by
    obtain ⟨z, Mxz, Ixz⟩ := strictly_ascending_mRel x;
    refine ⟨z, Mxz, ?_⟩;
    left;
    exact Ixz;

instance [F.AscendingMRel] : F.SerialMRel where
  serial_mRel x := by
    obtain ⟨z, Mxz, _⟩ := ascending_mRel x;
    exact ⟨z, Mxz⟩;

end Frame

namespace Model

open CK.Frame

lemma valid_TDia_of_ascendingMRel [M.AscendingMRel] : M ⊧ (A 🡒 ◇A) := by
  intro x y Ixy hyA u Iyu;
  obtain ⟨z, Muz, hz⟩ := ascending_mRel u;
  have huA : u ⊩[_] A := forces_persistent hyA Iyu;
  rcases hz with Iuz | hzFallible;
  · exact ⟨z, Muz, forces_persistent huA Iuz⟩;
  · exact ⟨z, Muz, forces_of_fallible hzFallible⟩;

lemma valid_of_mem_LogicCKTDia [M.AscendingMRel] (hA : A ∈ LogicCKTDia) : M ⊧ A :=
  valid_of_mem_logic (by rintro B ⟨C, rfl⟩; exact valid_TDia_of_ascendingMRel) hA

end Model

namespace Frame

variable {F : Frame κ}

lemma valid_TDia_of_ascendingMRel [F.AscendingMRel] : F ⊧ (A 🡒 ◇A) :=
  fun _ _ _ => Model.valid_TDia_of_ascendingMRel

lemma ascendingMRel_of_valid_TDia (h : F ⊧ (#0 🡒 ◇(#0))) : F.AscendingMRel where
  ascending_mRel x := by
    let M : Model κ := {
      toFrame := F,
      val := fun y _ => x ≼ y ∨ F.Fallible y,
      val_persistent := by
        rintro y z a (Ixy | hy) Iyz;
        . left;
          exact Trans.trans Ixy Iyz;
        . right;
          exact F.fallible_iRel hy Iyz;
      fallible_val := by
        rintro y a hy;
        right;
        exact hy;
    }
    have hxA : x ⊩[M] (#0) := Or.inl (refl x);
    exact h M.val M.val_persistent M.fallible_val x x (refl x) hxA x (refl x);

/-- `T◇` defines the frames whose `⊏` is ascending. -/
theorem ascendingMRel_TFAE : List.TFAE [
  F.AscendingMRel,
  ∀ A : BDFormula, F ⊧ (A 🡒 ◇A),
  F ⊧ (#0 🡒 ◇(#0)),
] := by
  tfae_have 1 → 2 := by intro h A; exact valid_TDia_of_ascendingMRel;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := ascendingMRel_of_valid_TDia
  tfae_finish

end Frame

variable {L : BDLogic} [L.CK]

private lemma avoid_disjSet_mdpClosure (hTDia : ∀ {A}, (A 🡒 ◇A) ∈ L) (P : CanonicalPair L) :
  ∀ C ∈ disjSet P.forbidden, C ∉ BDTheory.mdpClosure (P.theory ∪ □⁻¹P.theory) := by
  rintro C ⟨K, hne, hsub, rfl⟩ hmem;
  obtain ⟨D, hD, E, hE, hDE⟩ := BDTheory.mdpClosure_union_finite_char hmem;
  have h₁ : □(D 🡒 ⋁K) ∈ P.theory :=
    P.theory.mdp (BDTheory.provable_mem (box_mono (mdp imp_swap hDE))) hE;
  have h₂ : (◇D 🡒 ◇(⋁K)) ∈ P.theory := P.theory.mdp (BDTheory.provable_mem kDia) h₁;
  have h₃ : ◇D ∈ P.theory := P.theory.mdp (P.theory.subset (L := L) hTDia) hD;
  exact P.avoid (◇(⋁K)) ⟨⋁K, ⟨K, hne, hsub, rfl⟩, rfl⟩ (P.theory.mdp h₂ h₃);

lemma strictlyAscendingMRel_canonicalModel (hTDia : ∀ {A}, (A 🡒 ◇A) ∈ L) :
  (canonicalModel L).StrictlyAscendingMRel where
  strictly_ascending_mRel P := by
    have : BDTheory.Of L (P.theory ∪ □⁻¹P.theory) :=
      ⟨(P.theory.subset (L := L)).trans Set.subset_union_left⟩;
    obtain ⟨P₁, h₁, -, havoid⟩ :=
      CanonicalPair.exists_avoiding (L := L) (T := BDTheory.mdpClosure (P.theory ∪ □⁻¹P.theory))
      orDirected_disjSet (avoid_disjSet_mdpClosure hTDia P);
    have h₂ : P.theory ∪ □⁻¹P.theory ⊆ P₁.theory := BDTheory.subset_mdpClosure.trans h₁;
    use P₁;
    constructor;
    . exact CanonicalPair.mRel_of_avoid_disjSet (Set.subset_union_right.trans h₂) havoid;
    . exact Set.subset_union_left.trans h₂;

end CK

theorem LogicCKTDia_TFAE {A : BDFormula} : List.TFAE [
  A ∈ LogicCKTDia,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.AscendingMRel] → F ⊧ A,
  ∀ {κ : Type 0}, ∀ F : CK.Frame κ, [F.StrictlyAscendingMRel] → F ⊧ A,
] := by
  tfae_have 1 → 2 := fun h _ F _ val vp fv => CK.Model.valid_of_mem_LogicCKTDia h
  tfae_have 2 → 3 := fun h _ F _ => h F
  tfae_have 3 → 1 := by
    contrapose!;
    intro h;
    obtain ⟨P, h₁⟩ := CK.exists_not_forces_of_not_mem h;
    refine ⟨_, (CK.canonicalModel LogicCKTDia).toFrame, ?_⟩;
    and_intros;
    . exact CK.strictlyAscendingMRel_canonicalModel (by grind);
    . by_contra! hF;
      exact h₁ $ CK.Model.valid_of_toFrame_valid hF P;
  tfae_finish

end
