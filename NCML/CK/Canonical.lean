module

public import NCML.CK.Semantics
public import NCML.CK.Soundness
public import NCML.Hilbert.Theory

@[expose] public section

/-!
# The pair canonical model

For a logic `L`, the canonical model whose worlds are the pairs `(T, Θ)` of a prime MP-closed
theory `T` of `L` and a set `Θ` of formulas omitted by every `⊏`-successor, its truth lemma, and
the completeness of `CK` for the class of all CK-models.

- [MdP05, Definition 3, Lemma 3, Theorem 1]
-/

open BDFormula ProvableBDHilbert
open scoped BDFormulaSet BDFormulaList

namespace CK

/-- A pair of a prime MP-closed theory `th` of `L` and a set `forb` of formulas none of whose
nonempty finite disjunctions is possible in `th`.

- [MdP05, Definition 2]
-/
structure CanonicalPair (L : BDLogic) where
  th : BDTheory
  forb : BDFormulaSet
  mdp : th.Mdp
  prime : th.Prime
  of : th.Of L
  avoid : ∀ B ∈ diaDisjSet forb, B ∉ th

namespace CanonicalPair

variable {L : BDLogic} {w : CanonicalPair L}

instance : w.th.Mdp := w.mdp

instance : w.th.Prime := w.prime

instance : w.th.Of L := w.of

instance [L.CK] : w.th.Of LogicCK := BDTheory.of_logicCK (L := L)

/-- The pair `(T, ∅)` of a prime MP-closed theory `T` of `L`. -/
def ofTheory (L : BDLogic) (T : BDTheory) [T.Mdp] [T.Prime] [T.Of L] : CanonicalPair L where
  th := T
  forb := ∅
  mdp := ‹_›
  prime := ‹_›
  of := ‹_›
  avoid := by simp

section

variable (L : BDLogic) (T : BDTheory) [T.Mdp] [T.Prime] [T.Of L]

@[simp] lemma ofTheory_th : (ofTheory L T).th = T := rfl

@[simp] lemma ofTheory_forb : (ofTheory L T).forb = ∅ := rfl

end

/-- An MP-closed theory of `L` disjoint from an ⋎-directed `Z` extends to the theory of a pair
with no forbidden formulas, still disjoint from `Z`. -/
lemma exists_avoiding [L.CK] {T : BDTheory} {Z : BDFormulaSet} [T.Mdp] [T.Of L]
  (hdir : OrDirected L Z) (hdisj : ∀ C ∈ Z, C ∉ T) :
  ∃ v : CanonicalPair L, T ⊆ v.th ∧ v.forb = ∅ ∧ ∀ C ∈ Z, C ∉ v.th := by
  obtain ⟨Y, hTY, hmdp, hprime, hof, havoid⟩ := exists_prime_mdpClosed_avoiding hdir hdisj;
  have := hmdp;
  have := hprime;
  have := hof;
  exact ⟨ofTheory L Y, hTY, rfl, havoid⟩;

/-- The pair of the set of all formulas and the empty set of forbidden formulas. -/
def univ (L : BDLogic) : CanonicalPair L where
  th := Set.univ
  forb := ∅
  mdp := ⟨fun _ _ => trivial⟩
  prime := ⟨fun _ => Or.inl trivial⟩
  of := ⟨fun _ _ => trivial⟩
  avoid := by simp

@[simp] lemma univ_th : (univ L).th = Set.univ := rfl

@[simp] lemma univ_forb : (univ L).forb = ∅ := rfl

variable [L.CK]

lemma th_eq_univ_of_bot_mem (h : ⊥ ∈ w.th) : w.th = Set.univ := BDTheory.eq_univ_of_bot_mem h

lemma forb_eq_empty_of_bot_mem (h : ⊥ ∈ w.th) : w.forb = ∅ := by
  ext B;
  simp only [Set.mem_empty_iff_false, iff_false];
  intro hB;
  exact w.avoid (◇(⋁[B])) ⟨⋁[B], ⟨[B], by simp, by simpa using hB, rfl⟩, rfl⟩
    (by rw [th_eq_univ_of_bot_mem h]; trivial);

lemma eq_univ_of_bot_mem (h : ⊥ ∈ w.th) : w = univ L := by
  have h₁ := th_eq_univ_of_bot_mem h;
  have h₂ := forb_eq_empty_of_bot_mem h;
  cases w;
  subst h₁;
  subst h₂;
  rfl;

end CanonicalPair

/-- The canonical model of `L`, whose worlds are the pairs of `CanonicalPair L`.

- [MdP05, Definition 3, Lemma 3]
-/
def canonicalModel (L : BDLogic) [L.CK] : Model (CanonicalPair L) where
  iRel' w v := w.th ⊆ v.th
  iRel_preorder := {
    refl := fun _ => subset_rfl,
    trans := fun _ _ _ => subset_trans
  }
  mRel' w v := □⁻¹w.th ⊆ v.th ∧ ∀ B ∈ w.forb, B ∉ v.th
  Fallible' w := ⊥ ∈ w.th
  fallible_iRel' h Iwv := Iwv h
  fallible_mRel' h Mwv := Mwv.1 (by rw [CanonicalPair.th_eq_univ_of_bot_mem h]; trivial)
  fallible_exists_mRel' h :=
    ⟨CanonicalPair.univ L, Set.subset_univ _, by
      rw [CanonicalPair.forb_eq_empty_of_bot_mem h];
      simp⟩
  val w a := (#a) ∈ w.th
  val_persistent h Iwv := Iwv h
  fallible_val h := by rw [CanonicalPair.th_eq_univ_of_bot_mem h]; trivial

namespace CanonicalPair

variable {L : BDLogic} {A B : BDFormula} {w : CanonicalPair L}

/-- The pair `w` with its forbidden formulas erased. -/
def erase (w : CanonicalPair L) : CanonicalPair L := ofTheory L w.th

@[simp] lemma erase_th : w.erase.th = w.th := rfl

@[simp] lemma erase_forb : w.erase.forb = ∅ := rfl

variable [L.CK]

lemma iRel_erase : (canonicalModel L).iRel w w.erase := subset_rfl

lemma exists_iRel_of_imply_not_mem (h : (A 🡒 B) ∉ w.th) :
  ∃ v : CanonicalPair L, (canonicalModel L).iRel w v ∧ A ∈ v.th ∧ B ∉ v.th := by
  obtain ⟨v, hXv, -, havoid⟩ :=
    exists_avoiding (L := L) (T := w.th.impSet A) (Z := {B}) orDirected_singleton
      (by rintro C rfl; exact h);
  exact ⟨v, BDTheory.subset_impSet.trans hXv, hXv BDTheory.self_mem_impSet, havoid B rfl⟩;

lemma exists_mRel_of_box_not_mem [L.Nec] (h : □A ∉ w.th) :
  ∃ v : CanonicalPair L, (canonicalModel L).mRel w.erase v ∧ A ∉ v.th := by
  obtain ⟨v, hXv, -, havoid⟩ :=
    exists_avoiding (L := L) (T := □⁻¹w.th) (Z := {A}) orDirected_singleton
      (by rintro C rfl; exact h);
  exact ⟨v, ⟨hXv, by simp⟩, havoid A rfl⟩;

lemma mRel_of_avoid_disjSet {v : CanonicalPair L} (hsub : □⁻¹w.th ⊆ v.th)
  (havoid : ∀ C ∈ disjSet w.forb, C ∉ v.th) : (canonicalModel L).mRel w v := by
  refine ⟨hsub, ?_⟩;
  intro B hB hBv;
  exact havoid (⋁[B]) ⟨[B], by simp, by simpa using hB, rfl⟩
    (v.th.mdp (BDTheory.provable_mem (imp_ldisj (by simp))) hBv);

private lemma avoid_disjSet_of_dia_mem (h : ◇A ∈ w.th) :
  ∀ C ∈ disjSet w.forb, C ∉ BDTheory.impSet (□⁻¹w.th) A := by
  rintro C ⟨K, hne, hsub, rfl⟩ hmem;
  have h₁ : (◇A 🡒 ◇(⋁K)) ∈ w.th := w.th.mdp (BDTheory.provable_mem kDia) hmem;
  exact w.avoid (◇(⋁K)) ⟨⋁K, ⟨K, hne, hsub, rfl⟩, rfl⟩ (w.th.mdp h₁ h);

lemma exists_mRel_of_dia_mem [L.Nec] (h : ◇A ∈ w.th) :
  ∃ v : CanonicalPair L, (canonicalModel L).mRel w v ∧ A ∈ v.th := by
  obtain ⟨v, hXv, -, havoid⟩ :=
    exists_avoiding (L := L) (T := BDTheory.impSet (□⁻¹w.th) A) (Z := disjSet w.forb)
      orDirected_disjSet (avoid_disjSet_of_dia_mem h);
  exact ⟨v, mRel_of_avoid_disjSet (BDTheory.subset_impSet.trans hXv) havoid,
    hXv BDTheory.self_mem_impSet⟩;

private lemma avoid_diaDisjSet_of_dia_not_mem (h : ◇A ∉ w.th) :
  ∀ C ∈ diaDisjSet {A}, C ∉ w.th := by
  rintro C ⟨D, ⟨K, hne, hsub, rfl⟩, rfl⟩ hmem;
  have h₁ : (◇(⋁K) 🡒 ◇A) ∈ LogicCK := dia_mono (ldisj_imp (by
    intro B hB;
    obtain rfl : B = A := hsub B hB;
    exact imp_id));
  exact h (w.th.mdp (BDTheory.provable_mem h₁) hmem);

lemma exists_iRel_of_dia_not_mem (h : ◇A ∉ w.th) :
  ∃ v : CanonicalPair L, (canonicalModel L).iRel w v ∧
  ∀ u : CanonicalPair L, (canonicalModel L).mRel v u → A ∉ u.th := by
  obtain ⟨Y, hXY, hmdp, hprime, hof, havoid⟩ :=
    exists_prime_mdpClosed_avoiding (L := L) (T := w.th) (Z := diaDisjSet {A})
      orDirected_diaDisjSet (avoid_diaDisjSet_of_dia_not_mem h);
  exact ⟨⟨Y, {A}, hmdp, hprime, hof, havoid⟩, hXY, fun _ Mvu => Mvu.2 A rfl⟩;

/-- - [MdP05, Lemma 3] -/
lemma truthlemma [L.Nec] : w ⊩[canonicalModel L] A ↔ A ∈ w.th := by
  induction A generalizing w with
  | atom a => exact Iff.rfl;
  | falsum => exact Iff.rfl;
  | and A B ihA ihB =>
    constructor;
    · rintro ⟨hA, hB⟩;
      exact BDTheory.and_mem (ihA.mp hA) (ihB.mp hB);
    · intro h;
      constructor;
      . exact ihA.mpr (w.th.mdp (BDTheory.provable_mem andElim₁) h);
      . exact ihB.mpr (w.th.mdp (BDTheory.provable_mem andElim₂) h);
  | or A B ihA ihB =>
    constructor;
    · rintro (hA | hB);
      · exact w.th.mdp (BDTheory.provable_mem orIntro₁) (ihA.mp hA);
      · exact w.th.mdp (BDTheory.provable_mem orIntro₂) (ihB.mp hB);
    · intro h;
      rcases w.th.prime h <;> grind;
  | imply A B ihA ihB =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨v, Iwv, hAv, hBv⟩ := exists_iRel_of_imply_not_mem hc;
      exact hBv (ihB.mp (h v Iwv (ihA.mpr hAv)));
    · intro h v Iwv hvA;
      exact ihB.mpr (v.th.mdp (Iwv h) (ihA.mp hvA));
  | box A ih =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨v, Mwv, hAv⟩ := exists_mRel_of_box_not_mem hc;
      exact hAv (ih.mp (h w.erase v iRel_erase Mwv));
    · intro h v u Iwv Mvu;
      exact ih.mpr (Mvu.1 (Iwv h));
  | dia A ih =>
    constructor;
    · intro h;
      by_contra! hc;
      obtain ⟨v, Iwv, hblock⟩ := exists_iRel_of_dia_not_mem hc;
      obtain ⟨u, Mvu, hAu⟩ := h v Iwv;
      exact hblock u Mvu (ih.mp hAu);
    · intro h v Iwv;
      obtain ⟨u, Mvu, hAu⟩ := exists_mRel_of_dia_mem (Iwv h);
      exact ⟨u, Mvu, ih.mpr hAu⟩;

end CanonicalPair

section

variable {L : BDLogic} [L.Mdp] [L.Nec] [L.CK] {A : BDFormula}

/-- - [MdP05, Theorem 2] -/
lemma exists_not_forces_of_not_mem (h : A ∉ L) :
  ∃ w : CanonicalPair L, w ⊮[canonicalModel L] A := by
  obtain ⟨w, -, -, havoid⟩ :=
    CanonicalPair.exists_avoiding (L := L) (T := L) (Z := {A}) orDirected_singleton
      (by rintro C rfl; exact h);
  exact ⟨w, fun hw => havoid A rfl (CanonicalPair.truthlemma.mp hw)⟩;

end

end CK

/-- - [MdP05, Theorem 1] -/
theorem LogicCK.mem_iff_valid {A : BDFormula} :
  A ∈ LogicCK ↔ ∀ {κ : Type 0}, ∀ M : CK.Model κ, M ⊧ A := by
  constructor;
  · intro h _ M;
    exact CK.Model.valid_of_mem_LogicCK h;
  · contrapose!;
    intro h;
    obtain ⟨w, hw⟩ := CK.exists_not_forces_of_not_mem (L := LogicCK) h;
    exact ⟨_, CK.canonicalModel LogicCK, fun hM => hw (hM w)⟩;

end
