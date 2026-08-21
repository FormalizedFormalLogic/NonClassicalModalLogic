module

public import NCML.CK.Semantics
public import NCML.Hilbert.Logics

@[expose] public section

namespace CK

variable {κ : Type*} {M : Model κ}

namespace Model

lemma valid_of_mem_logic (h𝔸 : ∀ B ∈ 𝔸, M ⊧ B) (hA : A ∈ ProvableBDHilbert.logic 𝔸) : M ⊧ A := by
  replace hA : ProvableBDHilbert 𝔸 A := hA;
  intro x;
  induction hA generalizing x with
  | axm h => apply h𝔸 _ h;
  | imply₂ =>
    intro y _ hyABC z Iyz hzAB w Izw hwA;
    exact hyABC w (Trans.trans Iyz Izw) hwA w (refl _) $ hzAB w Izw hwA;
  | kBox =>
    intro y Ixy hyAB z Iyz hzA w v Izw Mwv;
    exact hyAB w v (Trans.trans Iyz Izw) Mwv v (refl _) $ hzA w v Izw Mwv;
  | kDia =>
    intro y Ixy hyAB z Iyz hzDiaA w Izw;
    obtain ⟨v, Mwv, hvA⟩ := hzDiaA w Izw;
    use v;
    constructor;
    . exact Mwv;
    . exact (hyAB w v (Trans.trans Iyz Izw) Mwv) v (refl _) hvA;
  | mdp _ _ ihAB ihA => exact ihAB x x (refl _) (ihA x);
  | _ => grind;

lemma valid_of_mem_LogicCK (hA : A ∈ LogicCK) : M ⊧ A := valid_of_mem_logic (by simp) hA

end Model

end CK

end
