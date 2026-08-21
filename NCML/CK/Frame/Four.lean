module

public import NCML.CK.Frame.FourBox
public import NCML.CK.Frame.FourDia

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class Four (F : Frame κ) : Prop extends FourBox F, FourDia F

instance [F.TransitiveMRel] [F.BackwardConfluent] : F.Four where

lemma frameValidate_Four_of_frame_Four [F.Four] : F ⊧ ((□A 🡒 □□A) ⋏ (◇◇A 🡒 ◇A)) := by
  intro V V_per V_fal x;
  exact ⟨
    frameValidate_FourBox_of_frame_FourBox V V_per V_fal x,
    frameValidate_FourDia_of_frame_FourDia V V_per V_fal x
  ⟩;

lemma frame_Four_of_frameValidate_Four
    (h : F ⊧ ((□(#0) 🡒 □□(#0)) ⋏ (◇◇(#0) 🡒 ◇(#0)))) : F.Four where
  toFourBox := frame_FourBox_of_frameValidate_FourBox (fun V V_per V_fal x => (h V V_per V_fal x).1)
  toFourDia := frame_FourDia_of_frameValidate_FourDia (fun V V_per V_fal x => (h V V_per V_fal x).2)

theorem frame_Four_TFAE : List.TFAE [
  F.Four,
  ∀ A : BDFormula, F ⊧ ((□A 🡒 □□A) ⋏ (◇◇A 🡒 ◇A)),
  F ⊧ ((□(#0) 🡒 □□(#0)) ⋏ (◇◇(#0) 🡒 ◇(#0))),
] := by
  tfae_have 1 → 2 := by intro h A; exact frameValidate_Four_of_frame_Four;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := frame_Four_of_frameValidate_Four
  tfae_finish

end Frame

end CK

end
