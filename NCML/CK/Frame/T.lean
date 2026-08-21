module

public import NCML.CK.Frame.TBox
public import NCML.CK.Frame.TDia

@[expose] public section

namespace CK

variable {κ : Type*}
variable {A : BDFormula}

namespace Frame

variable {F : Frame κ}

class T (F : Frame κ) : Prop extends TBox F, TDia F

lemma frameValidate_T_of_frame_T [F.T] : F ⊧ ((□A 🡒 A) ⋏ (A 🡒 ◇A)) := by
  intro V V_per V_fal x;
  exact ⟨
    frameValidate_TBox_of_frame_TBox V V_per V_fal x,
    frameValidate_TDia_of_frame_TDia V V_per V_fal x
  ⟩;

lemma frame_T_of_frameValidate_T (h : F ⊧ ((□(#0) 🡒 #0) ⋏ (#0 🡒 ◇(#0)))) : F.T where
  toTBox := frame_TBox_of_frameValidate_TBox (fun V V_per V_fal x => (h V V_per V_fal x).1)
  toTDia := frame_TDia_of_frameValidate_TDia (fun V V_per V_fal x => (h V V_per V_fal x).2)

theorem frame_T_TFAE : List.TFAE [
  F.T,
  ∀ A : BDFormula, F ⊧ ((□A 🡒 A) ⋏ (A 🡒 ◇A)),
  F ⊧ ((□(#0) 🡒 #0) ⋏ (#0 🡒 ◇(#0))),
] := by
  tfae_have 1 → 2 := by intro h A; exact frameValidate_T_of_frame_T;
  tfae_have 2 → 3 := fun h => h _
  tfae_have 3 → 1 := frame_T_of_frameValidate_T
  tfae_finish

end Frame

end CK

end
