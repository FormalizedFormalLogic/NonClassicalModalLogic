module

public import NCML.Formula
public import Mathlib.Order.Basic
public import Mathlib.Tactic

@[expose] public section

namespace IML

variable {κ : Type*} [Nonempty κ]

structure KripkeFrame (κ : Type*) [Nonempty κ] where
  iRel : κ → κ → Prop
  [iRel_preorder : IsPreorder _ iRel]
  mRel : κ → κ → Prop

namespace KripkeFrame

abbrev World (_ : KripkeFrame κ) := κ

abbrev mRel' {F : KripkeFrame κ} : F.World → F.World → Prop := F.mRel
infixl:80 " ⊏ " => KripkeFrame.mRel'

abbrev iRel' {F : KripkeFrame κ} : F.World → F.World → Prop := F.iRel
infixl:80 " ≼ " => KripkeFrame.iRel'

class MRelLifting (F : KripkeFrame κ) where
  mRel_lifting : ∀ {x₁ x₂ y₂ : F.World}, x₁ ≼ x₂ → x₂ ⊏ y₂ → ∃ y₁, y₁ ≼ y₂ ∧ x₁ ⊏ y₁
export MRelLifting (mRel_lifting)

class MixConfluent (F : KripkeFrame κ) where
  mix_confluent : ∀ {x₁ x₂ y₁ : F.World}, x₁ ≼ x₂ → x₁ ⊏ y₁ → ∃ y₂, y₁ ≼ y₂ ∧ x₂ ⊏ y₂
export MixConfluent (mix_confluent)

end KripkeFrame


structure KripkeModel (κ : Type*) [Nonempty κ] extends KripkeFrame κ where
  val : κ → Nat → Prop
  val_persistent : ∀ {x₁ x₂ : toKripkeFrame.World} {a}, val x₁ a → x₁ ≼ x₂ → val x₂ a

namespace KripkeModel

variable {M : KripkeModel κ} {x₁ x₂ y₁ y₂ : M.World}
variable {φ ψ : BDFormula}

instance : IsPreorder M.World M.iRel := M.iRel_preorder
instance : IsTrans M.World M.iRel := inferInstance

@[grind]
def ExtrinsicForces {M : KripkeModel κ} (x₁ : M.World) : BDFormula → Prop
  | .atom a    => M.val x₁ a
  | .falsum    => False
  | .and φ ψ   => M.ExtrinsicForces x₁ φ ∧ M.ExtrinsicForces x₁ ψ
  | .or φ ψ    => M.ExtrinsicForces x₁ φ ∨ M.ExtrinsicForces x₁ ψ
  | .imply φ ψ => ∀ x₂, x₁ ≼ x₂ → M.ExtrinsicForces x₂ φ → M.ExtrinsicForces x₂ ψ
  | .box φ     => ∀ y₁, x₁ ⊏ y₁ → M.ExtrinsicForces y₁ φ
  | .dia φ     => ∃ y₁, x₁ ⊏ y₁ ∧ M.ExtrinsicForces y₁ φ
infixl:80 " ⊩ᵉ " => ExtrinsicForces

abbrev NotExtrinsicForces (x₁ : M.World) (φ) := ¬x₁ ⊩ᵉ φ
infixl:80 " ⊮ᵉ " => NotExtrinsicForces

lemma notExtrinsicForces_imp : x₁ ⊮ᵉ (φ 🡒 ψ) ↔ ∃ x₂, x₁ ≼ x₂ ∧ x₂ ⊩ᵉ φ ∧ x₂ ⊮ᵉ ψ := by grind;

lemma extrinsicForces_neg : x₁ ⊩ᵉ ∼φ ↔ ∀ x₂, x₁ ≼ x₂ → x₂ ⊮ᵉ φ := by grind;
lemma notExtrinsicForces_neg : x₁ ⊮ᵉ ∼φ ↔ ∃ x₂, x₁ ≼ x₂ ∧ x₂ ⊩ᵉ φ := by grind;

lemma notExtrinsticForces_box : x₁ ⊮ᵉ □φ ↔ ∃ y₁, x₁ ⊏ y₁ ∧ y₁ ⊮ᵉ φ := by grind;

@[simp, grind .] lemma extrinsicForces_top : x₁ ⊩ᵉ ⊤ := by grind;

@[grind]
def IntrinsicForces {M : KripkeModel κ} (x₁ : M.World) : BDFormula → Prop
  | .atom a    => M.val x₁ a
  | .falsum    => False
  | .and φ ψ   => M.IntrinsicForces x₁ φ ∧ M.IntrinsicForces x₁ ψ
  | .or φ ψ    => M.IntrinsicForces x₁ φ ∨ M.IntrinsicForces x₁ ψ
  | .imply φ ψ => ∀ x₂, x₁ ≼ x₂ → M.IntrinsicForces x₂ φ → M.IntrinsicForces x₂ ψ
  | .box φ     => ∀ x₂, x₁ ≼ x₂ → ∀ y₂, x₂ ⊏ y₂ → M.IntrinsicForces y₂ φ
  | .dia φ     => ∀ x₂, x₁ ≼ x₂ → ∃ y₂, x₂ ⊏ y₂ ∧ M.IntrinsicForces y₂ φ
infixl:80 " ⊩ⁱ " => IntrinsicForces

@[simp, grind .] lemma intrinsticForces_top : x₁ ⊩ⁱ ⊤ := by grind;

lemma formula_persistent_intrinsicForces : x₁ ⊩ⁱ φ → x₁ ≼ x₂ → x₂ ⊩ⁱ φ := by
  intro h Ix₁x₂;
  induction φ generalizing x₂ with
  | atom a => apply M.val_persistent h Ix₁x₂;
  | imply φ ψ ihφ ihψ =>
    intro x₃ Ix₂x₃ hx₃φ;
    apply h x₃ (Trans.trans Ix₁x₂ Ix₂x₃) hx₃φ;
  | box φ ihφ =>
    intro x₃ Ix₂x₃ y₃ Mx₃y₃;
    exact h x₃ (Trans.trans Ix₁x₂ Ix₂x₃) _ Mx₃y₃;
  | dia φ ihφ =>
    intro x₃ Ix₂x₃;
    obtain ⟨y₁, Mx₃y₁, hy₁φ⟩ := h x₃ (Trans.trans Ix₁x₂ Ix₂x₃);
    use y₁;
  | _ => grind;

lemma diaFree_formula_persistent_exrinsicForces [M.MRelLifting] (hφ : φ.diaFree) : x₁ ⊩ᵉ φ → x₁ ≼ x₂ → x₂ ⊩ᵉ φ := by
  intro h Ix₁x₂;
  induction φ generalizing x₁ x₂ with
  | atom a => apply M.val_persistent h Ix₁x₂;
  | and | or | falsum | dia => grind;
  | imply φ ψ ihφ ihψ =>
    intro x₃ Ix₂x₃ hx₃φ;
    apply h x₃ (Trans.trans Ix₁x₂ Ix₂x₃) hx₃φ;
  | box φ ihφ =>
    intro y₂ Mx₂y₂;
    obtain ⟨y₁, Iy₁y₂, Mx₁y₁⟩ := M.mRel_lifting Ix₁x₂ Mx₂y₂;
    apply ihφ (by grind) (h y₁ Mx₁y₁) Iy₁y₂;

lemma boxFree_formula_persistent_exrinsicForces [M.MixConfluent] (hφ : φ.boxFree) : x₁ ⊩ᵉ φ → x₁ ≼ x₂ → x₂ ⊩ᵉ φ := by
  intro h Ix₁x₂;
  induction φ generalizing x₁ x₂ with
  | atom a => apply M.val_persistent h Ix₁x₂;
  | and | or | falsum | box => grind;
  | imply φ ψ ihφ ihψ =>
    intro x₃ Ix₂x₃ hx₃φ;
    apply h x₃ (Trans.trans Ix₁x₂ Ix₂x₃) hx₃φ;
  | dia φ ihφ =>
    obtain ⟨y₁, Mx₁y₁, hy₁⟩ := h;
    obtain ⟨y₂, Iy₁y₂, My₁y₂⟩ := M.mix_confluent Ix₁x₂ Mx₁y₁;
    use y₂;
    constructor;
    . assumption;
    . exact ihφ (by grind) hy₁ Iy₁y₂;

lemma formula_persistent_exrinsicForces [M.MRelLifting] [M.MixConfluent] : x₁ ⊩ᵉ φ → x₁ ≼ x₂ → x₂ ⊩ᵉ φ := by
  intro h Ix₁x₂;
  induction φ generalizing x₁ x₂ with
  | atom a => apply M.val_persistent h Ix₁x₂;
  | and | or | falsum => grind;
  | imply φ ψ ihφ ihψ =>
    intro x₃ Ix₂x₃ hx₃φ;
    apply h x₃ (Trans.trans Ix₁x₂ Ix₂x₃) hx₃φ;
  | box φ ihφ =>
    intro y₂ Mx₂y₂;
    obtain ⟨y₁, Iy₁y₂, Mx₁y₁⟩ := M.mRel_lifting Ix₁x₂ Mx₂y₂;
    apply ihφ (h y₁ Mx₁y₁) Iy₁y₂;
  | dia φ ihφ =>
    obtain ⟨y₁, Mx₁y₁, hy₁⟩ := h;
    obtain ⟨y₂, Iy₁y₂, My₁y₂⟩ := M.mix_confluent Ix₁x₂ Mx₁y₁;
    use y₂;
    constructor;
    . assumption;
    . exact ihφ hy₁ Iy₁y₂;


def ExtrinsicValid (M : KripkeModel κ) (φ : BDFormula) := ∀ x : M.World, x ⊩ᵉ φ
infixl:80 " ⊧ᵉ " => ExtrinsicValid

def IntrinsicValid (M : KripkeModel κ) (φ : BDFormula) := ∀ x : M.World, x ⊩ⁱ φ
infixl:80 " ⊧ⁱ " => IntrinsicValid

end KripkeModel


namespace KripkeFrame

def ExtrinsicValid (F : KripkeFrame κ) (φ : BDFormula) := ∀ V hV, (KripkeModel.mk F V hV) ⊧ᵉ φ
infixl:80 " ⊧ᵉ " => ExtrinsicValid

def IntrinsicValid (F : KripkeFrame κ) (φ : BDFormula) := ∀ V hV, (KripkeModel.mk F V hV) ⊧ⁱ φ
infixl:80 " ⊧ⁱ " => IntrinsicValid

end KripkeFrame


abbrev logicExtrinsic := { φ : BDFormula | ∀ {κ : Type*}, [Nonempty κ] → ∀ M : KripkeModel κ, [M.MRelLifting] → [M.MixConfluent] → M ⊧ᵉ φ }
abbrev logicIntrinsic := { φ : BDFormula | ∀ {κ : Type*}, [Nonempty κ] → ∀ M : KripkeModel κ, M ⊧ⁱ φ }

lemma wwwww {M : KripkeModel κ} [M.MRelLifting] [M.MixConfluent] {x₁ : M.World} {φ} : x₁ ⊩ᵉ φ ↔ x₁ ⊩ⁱ φ := by
  induction φ generalizing x₁ with
  | box φ ihφ =>
    constructor;
    . intro h y₁ Ix₁y₁ y₂ My₁y₂;
      exact ihφ.mp $ KripkeModel.formula_persistent_exrinsicForces h Ix₁y₁ y₂ My₁y₂;
    . intro h y₁ Mx₁y₁;
      exact ihφ.mpr $ h x₁ (refl x₁) y₁ Mx₁y₁;
  | dia φ ihφ =>
    constructor;
    . rintro ⟨y₁, Mx₁y₁, h⟩ x₂ Ix₁x₂;
      obtain ⟨y₂, Iy₁y₂, Mx₁y₂⟩ := M.mix_confluent Ix₁x₂ Mx₁y₁;
      use y₂;
      constructor;
      . assumption;
      . exact ihφ.mp $ KripkeModel.formula_persistent_exrinsicForces h Iy₁y₂;
    . rintro h;
      obtain ⟨y₁, Mx₁y₁, h⟩ := h x₁ (refl _)
      use y₁;
      constructor;
      . assumption;
      . exact ihφ.mpr h;
  | _ => grind;

theorem logicIntrinsic_subset_logicExtrinsic : logicIntrinsic.{u} ⊆ logicExtrinsic.{u} := by
  simp only [logicIntrinsic, KripkeModel.IntrinsicValid, logicExtrinsic, KripkeModel.ExtrinsicValid, Set.setOf_subset_setOf];
  grind [wwwww];

@[simp, grind .]
lemma axiomCDia_mem_logicExtrinsic : ◇(φ ⋎ ψ) 🡒 (◇φ ⋎ ◇ψ) ∈ logicExtrinsic := by
  rintro κ _ M _ _ x₁ x₂ Ix₁x₂ ⟨y₂, Mx₂y₂, (hy₂φ | hy₂ψ)⟩ <;> grind;

lemma axiomCDia_notMem_logicIntrinsic : ◇(#0 ⋎ #1) 🡒 (◇(#0) ⋎ ◇(#1)) ∉ logicIntrinsic.{0} := by
  simp only [logicIntrinsic, Set.mem_setOf_eq, not_forall, KripkeModel.IntrinsicValid];
  use (Fin 4), inferInstance;
  use {
    iRel x y := x = y ∨ (x = 0 ∧ y = 1)
    iRel_preorder := { refl := by grind, trans := by grind; }
    mRel x y := match x, y with | 0, 2 | 1, 3 | 2, 2 | 3, 3 => True | _, _ => False
    val x a := match a with | 0 => x = 2 | 1 => x = 3 | _ => True
    val_persistent {x y a} hx Ixy := by grind;
  }, 0;
  dsimp [KripkeModel.IntrinsicForces]
  push_neg;
  refine ⟨0, ?_, ?_, ⟨1, ?_⟩, ⟨0, ?_⟩⟩ <;> grind;

theorem logicIntrinsic_ssubset_logicExtrinsic : logicIntrinsic.{0} ⊂ logicExtrinsic.{0} := by
  apply Set.ssubset_iff_exists.mpr;
  constructor;
  . exact logicIntrinsic_subset_logicExtrinsic;
  . use (◇(#0 ⋎ #1) 🡒 (◇(#0) ⋎ ◇(#1)));
    constructor;
    . exact axiomCDia_mem_logicExtrinsic;
    . exact axiomCDia_notMem_logicIntrinsic;


abbrev logicDiaFreeExtrinsic := { φ : BDFormula | φ.diaFree ∧ (∀ {κ : Type*}, [Nonempty κ] → ∀ M : KripkeModel κ, [M.MRelLifting] → M ⊧ᵉ φ) }

open KripkeModel

lemma dnBoxBot_mem_logicExtrinsic : (∼∼□⊥ 🡒 □⊥) ∈ logicExtrinsic := by
  rintro κ _ M _ _ x₁ x₂ Ix₁x₂ h y₂ Mx₂y₂;
  obtain ⟨x₃, Ix₂x₃, hx₃⟩ := notExtrinsicForces_neg.mp $ extrinsicForces_neg.mp h x₂ (refl _);
  obtain ⟨y₃, Iy₂y₃, Mx₃y₃⟩ := M.mix_confluent Ix₂x₃ Mx₂y₂;
  have : y₃ ⊩ᵉ ⊥ := hx₃ _ Mx₃y₃;
  contradiction;

lemma dnBoxBot_notMem_logicDiaFreeExtrinsic : (∼∼□⊥ 🡒 □⊥) ∉ logicDiaFreeExtrinsic.{0} := by
  simp only [logicDiaFreeExtrinsic, Set.mem_setOf_eq, not_and, not_forall, KripkeModel.ExtrinsicValid];
  intro _;
  use (Fin 5), inferInstance;
  use {
    iRel x y := x = y ∨ (match x, y with | 0, 1 | 1, 2 | 0, 2 | 3, 4 => True | _, _ => False),
    iRel_preorder := { refl := by tauto, trans := by grind; }
    mRel x y := (x = 0 ∧ y = 3) ∨ (x = 1 ∧ y = 4)
    val _ _ := True
    val_persistent := by tauto
  };
  refine ⟨?_, 0, ?_⟩;
  . constructor;
    rintro x₁ x₂ y₂ Ix₁x₂ (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩);
    . use 3; grind;
    . rcases Ix₁x₂ with (rfl | h);
      . use 4; grind;
      . use 3; grind;
  . apply notExtrinsicForces_imp.mpr;
    use 1;
    refine ⟨?_, ?_, ?_⟩;
    . tauto;
    . apply extrinsicForces_neg.mpr;
      intro x I1x;
      apply notExtrinsicForces_neg.mpr;
      use 2;
      grind;
    . apply notExtrinsticForces_box.mpr;
      use 4;
      tauto;

theorem logicDiaFreeExtrinsic_ssubset_logicExtrinsic : logicDiaFreeExtrinsic.{0} ⊂ logicExtrinsic.{0} := by
  apply Set.ssubset_iff_exists.mpr;
  constructor;
  . simp only [logicDiaFreeExtrinsic, logicExtrinsic, Set.setOf_subset_setOf];
    tauto;
  . use (∼∼□⊥ 🡒 □⊥);
    constructor;
    . exact dnBoxBot_mem_logicExtrinsic;
    . exact dnBoxBot_notMem_logicDiaFreeExtrinsic;

lemma diaFree_equiv {M : KripkeModel κ} [M.MRelLifting] {φ} (hφ : φ.diaFree) {x₁ : M.World} : x₁ ⊩ᵉ φ ↔ x₁ ⊩ⁱ φ := by
  induction φ generalizing x₁ with
  | box φ ihφ =>
    constructor;
    . intro h y₁ Ix₁y₁ y₂ My₁y₂;
      exact ihφ (by grind) |>.mp $ KripkeModel.diaFree_formula_persistent_exrinsicForces (by grind) h Ix₁y₁ y₂ My₁y₂;
    . intro h y₁ Mx₁y₁;
      exact ihφ (by grind) |>.mpr $ h x₁ (refl x₁) y₁ Mx₁y₁;
  | _ => grind;

lemma iff_mem_logicIntrinsic_mem_logicDiaFreeExtrinsic_of_diaFree (hφ : φ.diaFree) : (φ ∈ logicIntrinsic.{u}) ↔ φ ∈ logicDiaFreeExtrinsic.{u} := by
  simp only [Set.mem_setOf_eq]
  constructor;
  . intro h;
    constructor;
    . assumption;
    . intro κ _ M _ x;
      exact diaFree_equiv (by grind) |>.mpr $ h M x;
  . rintro ⟨_, h⟩ κ _ M x;
    let M' : KripkeModel κ := {
      iRel := M.iRel,
      mRel x y := M.mRel x y ∨ (∃ x', M.iRel x x' ∧ M.mRel x' y),
      val := M.val,
      val_persistent := M.val_persistent,
    };
    have : M'.MRelLifting := ⟨by
      rintro x₁ x₂ y₂ Ix₁x₂ Mx₂y₂;
      use y₂;
      constructor;
      . apply refl;
      . rcases Mx₂y₂ with (h | ⟨x₃, Ix₂x₃, Mx₃y₂⟩);
        . right; use x₂;
        . right;
          use x₃;
          constructor;
          . apply _root_.trans Ix₁x₂ Ix₂x₃;
          . assumption;
    ⟩
    have : ∀ ψ, ψ.diaFree → ∀ w, (M.IntrinsicForces w ψ ↔ M'.ExtrinsicForces w ψ) := by
      intro ψ hψ w;
      induction ψ generalizing w with
      | box ψ ih =>
        replace ih := ih (by grind);
        constructor;
        . rintro h v (Mwv | ⟨v', Iwv', Mv'v⟩);
          . exact ih _ |>.mp $ h w (refl _) v Mwv;
          . exact ih _ |>.mp $ h _ Iwv' v Mv'v;
        . grind;
      | _ => grind;
    exact this φ (by assumption) x |>.mpr $ h M' x;

lemma logicIntrinsic_boxRM_closed : (φ 🡒 ψ) ∈ logicIntrinsic.{u} → (□φ 🡒 □ψ) ∈ logicIntrinsic.{u} := by
  dsimp only [logicIntrinsic, Set.mem_setOf_eq, KripkeModel.IntrinsicValid];
  intro h _ _ M x₁ x₂ Ix₁x₂ hφ x₃ Ix₂x₃ y₃ Mx₃y₃;
  apply h M x₂ y₃ ?_ $ hφ x₃ Ix₂x₃ y₃ Mx₃y₃;
  sorry;

lemma logicExtrinsic_boxRM_closed : (φ 🡒 ψ) ∈ logicExtrinsic.{u} → (□φ 🡒 □ψ) ∈ logicExtrinsic.{u} := by
  dsimp only [logicExtrinsic, Set.mem_setOf_eq, KripkeModel.ExtrinsicValid];
  intro h _ _ M _ _ x₁ x₂ Ix₁x₂ hφ y₂ Mx₂y₂;
  apply h M y₂ y₂ (refl _) $ hφ y₂ Mx₂y₂;

lemma logicDiaFreeExtrinsic_boxRM_closed : (φ 🡒 ψ) ∈ logicDiaFreeExtrinsic.{u} → (□φ 🡒 □ψ) ∈ logicDiaFreeExtrinsic.{u} := by
  dsimp only [logicDiaFreeExtrinsic, Set.mem_setOf_eq, KripkeModel.ExtrinsicValid];
  rintro ⟨_, h⟩;
  constructor;
  . assumption;
  . intro _ _ M _ x₁ x₂ Ix₁x₂ hφ y₂ Mx₂y₂;
    apply h M y₂ y₂ (refl _) $ hφ y₂ Mx₂y₂;


lemma logicExtrinsic_diaRM_closed : (φ 🡒 ψ) ∈ logicExtrinsic.{u} → (◇φ 🡒 ◇ψ) ∈ logicExtrinsic.{u} := by
  dsimp only [logicExtrinsic, Set.mem_setOf_eq, KripkeModel.ExtrinsicValid];
  rintro h _ _ M _ _ x₁ x₂ Ix₁x₂ ⟨y₂, Mx₂y₂, hy₂ψ⟩;
  use y₂;
  constructor;
  . assumption;
  . exact h M y₂ _ (refl _) hy₂ψ;

lemma logicIntrinsic_diaRM_closed : (φ 🡒 ψ) ∈ logicIntrinsic.{u} → (◇φ 🡒 ◇ψ) ∈ logicIntrinsic.{u} := by
  dsimp only [logicIntrinsic, Set.mem_setOf_eq, KripkeModel.IntrinsicValid];
  intro h _ _ M x₁ x₂ Ix₁x₂ hφ x₃ Ix₂x₃;
  obtain ⟨y₃, Mx₃y₃, hy₃φ⟩ := hφ x₃ Ix₂x₃;
  use y₃;
  constructor;
  . assumption;
  . apply h M x₂ y₃ (by sorry) hy₃φ;

lemma boxTop_mem_logicExtrinsic : □⊤ ∈ logicExtrinsic := by
  rintro κ _ M _ _ x₁ y₁ Mx₁y₁;
  apply M.extrinsicForces_top;

lemma boxTop_mem_logicIntrinsic : □⊤ ∈ logicIntrinsic := by
  rintro κ _ M x₁ y₁ Mx₁y₁ y₂ Mx₁y₂;
  apply M.intrinsticForces_top;

lemma boxTop_mem_logicDiaFreeExtrinsic : □⊤ ∈ logicDiaFreeExtrinsic := by
  constructor;
  . grind;
  . rintro κ _ M _ _ x₁ y₁ Mx₁y₁;
    apply M.extrinsicForces_top;

lemma negDiaBot_mem_logicExtrinsic : ∼◇⊥ ∈ logicExtrinsic := by
  rintro κ _ M _ _ x₁ x₂ Ix₁x₂ ⟨y₂, Mx₂y₂, hy₂⟩;
  contradiction;

lemma negDiaBot_mem_logicIntrinsic : ∼◇⊥ ∈ logicIntrinsic := by
  rintro κ _ M x₁ x₂ Ix₁x₂ h;
  obtain ⟨y₂, Mx₁y₂, hy₂⟩ := h x₂ (refl _);
  contradiction;

end IML

end
