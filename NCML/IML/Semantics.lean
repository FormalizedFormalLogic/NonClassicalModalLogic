module

public import NCML.Formula
public import Mathlib.Order.Basic
public import Mathlib.Tactic

@[expose] public section

namespace IML

open NCML

structure Model (κ : Type*) where
  iRel' : κ → κ → Prop
  [iRel_preorder : IsPreorder _ iRel']
  mRel' : κ → κ → Prop
  val : κ → Nat → Prop
  val_persistent : ∀ {x₁ x₂} {a}, val x₁ a → iRel' x₁ x₂ → val x₂ a

attribute [grind =>] Model.val_persistent

namespace Model

variable {κ : Type*}

abbrev World (_ : Model κ) := κ

abbrev iRel {M : Model κ} : M.World → M.World → Prop := M.iRel'
infixl:80 " ≼ " => Model.iRel

abbrev mRel {M : Model κ} : M.World → M.World → Prop := M.mRel'
infixl:80 " ⊏ " => Model.mRel

variable {M : Model κ}

instance : IsPreorder M.World M.iRel := M.iRel_preorder
instance : IsTrans M.World M.iRel := inferInstance

class MRelLifting (M : Model κ) : Prop where
  mRel_lifting : ∀ {x₁ x₂ y₂ : M.World}, x₁ ≼ x₂ → x₂ ⊏ y₂ → ∃ y₁, y₁ ≼ y₂ ∧ x₁ ⊏ y₁
export MRelLifting (mRel_lifting)

class MixConfluent (M : Model κ) : Prop where
  mix_confluent : ∀ {x₁ x₂ y₁ : M.World}, x₁ ≼ x₂ → x₁ ⊏ y₁ → ∃ y₂, y₁ ≼ y₂ ∧ x₂ ⊏ y₂
export MixConfluent (mix_confluent)

variable {x₁ x₂ y₁ y₂ : M.World} {A B : BDFormula}

@[grind]
def ExtrinsicForces (M : Model κ) (x₁ : M.World) : BDFormula → Prop
  | #a    => M.val x₁ a
  | ⊥     => False
  | A ⋏ B => M.ExtrinsicForces x₁ A ∧ M.ExtrinsicForces x₁ B
  | A ⋎ B => M.ExtrinsicForces x₁ A ∨ M.ExtrinsicForces x₁ B
  | A 🡒 B => ∀ x₂, x₁ ≼ x₂ → M.ExtrinsicForces x₂ A → M.ExtrinsicForces x₂ B
  | □A    => ∀ y₁, x₁ ⊏ y₁ → M.ExtrinsicForces y₁ A
  | ◇A    => ∃ y₁, x₁ ⊏ y₁ ∧ M.ExtrinsicForces y₁ A

notation:80 x:81 " ⊩ᵉ[" M "] " A:81 => ExtrinsicForces M x A

abbrev NotExtrinsicForces (M : Model κ) (x₁ : M.World) (A : BDFormula) := ¬x₁ ⊩ᵉ[M] A

notation:80 x:81 " ⊮ᵉ[" M "] " A:81 => NotExtrinsicForces M x A

lemma notExtrinsicForces_imp : x₁ ⊮ᵉ[_] (A 🡒 B) ↔ ∃ x₂, x₁ ≼ x₂ ∧ x₂ ⊩ᵉ[_] A ∧ x₂ ⊮ᵉ[_] B := by grind;

lemma extrinsicForces_neg : x₁ ⊩ᵉ[_] ∼A ↔ ∀ x₂, x₁ ≼ x₂ → x₂ ⊮ᵉ[_] A := by grind;
lemma notExtrinsicForces_neg : x₁ ⊮ᵉ[_] ∼A ↔ ∃ x₂, x₁ ≼ x₂ ∧ x₂ ⊩ᵉ[_] A := by grind;

lemma notExtrinsicForces_box : x₁ ⊮ᵉ[_] □A ↔ ∃ y₁, x₁ ⊏ y₁ ∧ y₁ ⊮ᵉ[_] A := by grind;

@[simp, grind .] lemma extrinsicForces_top : x₁ ⊩ᵉ[_] ⊤ := by grind;

@[grind]
def IntrinsicForces (M : Model κ) (x₁ : M.World) : BDFormula → Prop
  | #a    => M.val x₁ a
  | ⊥     => False
  | A ⋏ B => M.IntrinsicForces x₁ A ∧ M.IntrinsicForces x₁ B
  | A ⋎ B => M.IntrinsicForces x₁ A ∨ M.IntrinsicForces x₁ B
  | A 🡒 B => ∀ x₂, x₁ ≼ x₂ → M.IntrinsicForces x₂ A → M.IntrinsicForces x₂ B
  | □A    => ∀ x₂, x₁ ≼ x₂ → ∀ y₂, x₂ ⊏ y₂ → M.IntrinsicForces y₂ A
  | ◇A    => ∀ x₂, x₁ ≼ x₂ → ∃ y₂, x₂ ⊏ y₂ ∧ M.IntrinsicForces y₂ A

notation:80 x:81 " ⊩ⁱ[" M "] " A:81 => IntrinsicForces M x A

@[simp, grind .] lemma intrinsicForces_top : x₁ ⊩ⁱ[_] ⊤ := by grind;

lemma IntrinsicForces.persistent : x₁ ⊩ⁱ[_] A → x₁ ≼ x₂ → x₂ ⊩ⁱ[_] A := by
  intro h Ix₁x₂;
  induction A generalizing x₂ with
  | atom a => apply M.val_persistent h Ix₁x₂;
  | imply A B ihA ihB =>
    intro x₃ Ix₂x₃ hx₃A;
    apply h x₃ (Trans.trans Ix₁x₂ Ix₂x₃) hx₃A;
  | box A ihA =>
    intro x₃ Ix₂x₃ y₃ Mx₃y₃;
    exact h x₃ (Trans.trans Ix₁x₂ Ix₂x₃) _ Mx₃y₃;
  | dia A ihA =>
    intro x₃ Ix₂x₃;
    obtain ⟨y₁, Mx₃y₁, hy₁A⟩ := h x₃ (Trans.trans Ix₁x₂ Ix₂x₃);
    use y₁;
  | _ => grind;

lemma ExtrinsicForces.persistent_of_diaFree [M.MRelLifting] (hA : A.diaFree) :
  x₁ ⊩ᵉ[_] A → x₁ ≼ x₂ → x₂ ⊩ᵉ[_] A := by
  intro h Ix₁x₂;
  induction A generalizing x₁ x₂ with
  | atom a => apply M.val_persistent h Ix₁x₂;
  | and | or | falsum | dia => grind;
  | imply A B ihA ihB =>
    intro x₃ Ix₂x₃ hx₃A;
    apply h x₃ (Trans.trans Ix₁x₂ Ix₂x₃) hx₃A;
  | box A ihA =>
    intro y₂ Mx₂y₂;
    obtain ⟨y₁, Iy₁y₂, Mx₁y₁⟩ := M.mRel_lifting Ix₁x₂ Mx₂y₂;
    apply ihA (by grind) (h y₁ Mx₁y₁) Iy₁y₂;

lemma ExtrinsicForces.persistent_of_boxFree [M.MixConfluent] (hA : A.boxFree) :
  x₁ ⊩ᵉ[_] A → x₁ ≼ x₂ → x₂ ⊩ᵉ[_] A := by
  intro h Ix₁x₂;
  induction A generalizing x₁ x₂ with
  | atom a => apply M.val_persistent h Ix₁x₂;
  | and | or | falsum | box => grind;
  | imply A B ihA ihB =>
    intro x₃ Ix₂x₃ hx₃A;
    apply h x₃ (Trans.trans Ix₁x₂ Ix₂x₃) hx₃A;
  | dia A ihA =>
    obtain ⟨y₁, Mx₁y₁, hy₁⟩ := h;
    obtain ⟨y₂, Iy₁y₂, Mx₂y₂⟩ := M.mix_confluent Ix₁x₂ Mx₁y₁;
    exact ⟨y₂, Mx₂y₂, ihA (by grind) hy₁ Iy₁y₂⟩;

lemma ExtrinsicForces.persistent [M.MRelLifting] [M.MixConfluent] :
  x₁ ⊩ᵉ[_] A → x₁ ≼ x₂ → x₂ ⊩ᵉ[_] A := by
  intro h Ix₁x₂;
  induction A generalizing x₁ x₂ with
  | atom a => apply M.val_persistent h Ix₁x₂;
  | and | or | falsum => grind;
  | imply A B ihA ihB =>
    intro x₃ Ix₂x₃ hx₃A;
    apply h x₃ (Trans.trans Ix₁x₂ Ix₂x₃) hx₃A;
  | box A ihA =>
    intro y₂ Mx₂y₂;
    obtain ⟨y₁, Iy₁y₂, Mx₁y₁⟩ := M.mRel_lifting Ix₁x₂ Mx₂y₂;
    apply ihA (h y₁ Mx₁y₁) Iy₁y₂;
  | dia A ihA =>
    obtain ⟨y₁, Mx₁y₁, hy₁⟩ := h;
    obtain ⟨y₂, Iy₁y₂, Mx₂y₂⟩ := M.mix_confluent Ix₁x₂ Mx₁y₁;
    exact ⟨y₂, Mx₂y₂, ihA hy₁ Iy₁y₂⟩;


def ExtrinsicValid (M : Model κ) (A : BDFormula) := ∀ x : M.World, x ⊩ᵉ[M] A
infixl:80 " ⊧ᵉ " => ExtrinsicValid

def IntrinsicValid (M : Model κ) (A : BDFormula) := ∀ x : M.World, x ⊩ⁱ[M] A
infixl:80 " ⊧ⁱ " => IntrinsicValid

end Model


open Model

variable {κ : Type*} {A B : BDFormula}

abbrev logicExtrinsic := { A : BDFormula | ∀ {κ : Type*}, ∀ M : Model κ, [M.MRelLifting] → [M.MixConfluent] → M ⊧ᵉ A }
abbrev logicIntrinsic := { A : BDFormula | ∀ {κ : Type*}, ∀ M : Model κ, M ⊧ⁱ A }

lemma extrinsicForces_iff_intrinsicForces {M : Model κ} [M.MRelLifting] [M.MixConfluent]
  {x₁ : M.World} {A} : x₁ ⊩ᵉ[_] A ↔ x₁ ⊩ⁱ[_] A := by
  induction A generalizing x₁ with
  | box A ihA =>
    constructor;
    . intro h y₁ Ix₁y₁ y₂ My₁y₂;
      exact ihA.mp $ ExtrinsicForces.persistent h Ix₁y₁ y₂ My₁y₂;
    . intro h y₁ Mx₁y₁;
      exact ihA.mpr $ h x₁ (refl x₁) y₁ Mx₁y₁;
  | dia A ihA =>
    constructor;
    . rintro ⟨y₁, Mx₁y₁, h⟩ x₂ Ix₁x₂;
      obtain ⟨y₂, Iy₁y₂, Mx₂y₂⟩ := M.mix_confluent Ix₁x₂ Mx₁y₁;
      exact ⟨y₂, Mx₂y₂, ihA.mp $ ExtrinsicForces.persistent h Iy₁y₂⟩;
    . rintro h;
      obtain ⟨y₁, Mx₁y₁, h⟩ := h x₁ (refl _);
      exact ⟨y₁, Mx₁y₁, ihA.mpr h⟩;
  | _ => grind;

theorem logicIntrinsic_subset_logicExtrinsic : logicIntrinsic.{u} ⊆ logicExtrinsic.{u} := by
  simp only [logicIntrinsic, IntrinsicValid, logicExtrinsic, ExtrinsicValid, Set.ofPred_subset_ofPred];
  grind [extrinsicForces_iff_intrinsicForces];

@[simp, grind .]
lemma axiomCDia_mem_logicExtrinsic : ◇(A ⋎ B) 🡒 (◇A ⋎ ◇B) ∈ logicExtrinsic := by
  rintro κ M _ _ x₁ x₂ Ix₁x₂ ⟨y₂, Mx₂y₂, (hy₂A | hy₂B)⟩ <;> grind;

lemma axiomCDia_notMem_logicIntrinsic : ◇(#0 ⋎ #1) 🡒 (◇(#0) ⋎ ◇(#1)) ∉ logicIntrinsic.{0} := by
  simp only [logicIntrinsic, Set.mem_ofPred_eq, not_forall, IntrinsicValid];
  use (Fin 4);
  use {
    iRel' x y := x = y ∨ (x = 0 ∧ y = 1)
    iRel_preorder := { refl := by grind, trans := by grind; }
    mRel' x y := match x, y with | 0, 2 | 1, 3 | 2, 2 | 3, 3 => True | _, _ => False
    val x a := match a with | 0 => x = 2 | 1 => x = 3 | _ => True
    val_persistent {x y a} hx Ixy := by grind;
  }, 0;
  dsimp [IntrinsicForces];
  push Not;
  refine ⟨0, ?_, ?_, ⟨1, ?_⟩, ⟨0, ?_⟩⟩ <;> grind;

theorem logicIntrinsic_ssubset_logicExtrinsic : logicIntrinsic.{0} ⊂ logicExtrinsic.{0} := by
  apply Set.ssubset_iff_exists.mpr;
  exact ⟨logicIntrinsic_subset_logicExtrinsic, ◇(#0 ⋎ #1) 🡒 (◇(#0) ⋎ ◇(#1)),
    axiomCDia_mem_logicExtrinsic, axiomCDia_notMem_logicIntrinsic⟩;


abbrev logicDiaFreeExtrinsic := { A : BDFormula | A.diaFree ∧ (∀ {κ : Type*}, ∀ M : Model κ, [M.MRelLifting] → M ⊧ᵉ A) }

lemma dnBoxBot_mem_logicExtrinsic : (∼∼□⊥ 🡒 □⊥) ∈ logicExtrinsic := by
  rintro κ M _ _ x₁ x₂ Ix₁x₂ h y₂ Mx₂y₂;
  obtain ⟨x₃, Ix₂x₃, hx₃⟩ := notExtrinsicForces_neg.mp $ extrinsicForces_neg.mp h x₂ (refl _);
  obtain ⟨y₃, Iy₂y₃, Mx₃y₃⟩ := M.mix_confluent Ix₂x₃ Mx₂y₂;
  have : y₃ ⊩ᵉ[_] ⊥ := hx₃ _ Mx₃y₃;
  contradiction;

lemma dnBoxBot_notMem_logicDiaFreeExtrinsic : (∼∼□⊥ 🡒 □⊥) ∉ logicDiaFreeExtrinsic.{0} := by
  simp only [logicDiaFreeExtrinsic, Set.mem_ofPred_eq, not_and, not_forall, ExtrinsicValid];
  intro _;
  use (Fin 5);
  use {
    iRel' x y := x = y ∨ (match x, y with | 0, 1 | 1, 2 | 0, 2 | 3, 4 => True | _, _ => False),
    iRel_preorder := { refl := by tauto, trans := by grind; }
    mRel' x y := (x = 0 ∧ y = 3) ∨ (x = 1 ∧ y = 4)
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
    and_intros;
    . tauto;
    . apply extrinsicForces_neg.mpr;
      intro x I1x;
      apply notExtrinsicForces_neg.mpr;
      use 2;
      grind;
    . apply notExtrinsicForces_box.mpr;
      use 4;
      tauto;

theorem logicDiaFreeExtrinsic_ssubset_logicExtrinsic : logicDiaFreeExtrinsic.{0} ⊂ logicExtrinsic.{0} := by
  apply Set.ssubset_iff_exists.mpr;
  constructor;
  . simp only [logicDiaFreeExtrinsic, logicExtrinsic, Set.ofPred_subset_ofPred];
    tauto;
  . exact ⟨∼∼□⊥ 🡒 □⊥, dnBoxBot_mem_logicExtrinsic, dnBoxBot_notMem_logicDiaFreeExtrinsic⟩;

lemma extrinsicForces_iff_intrinsicForces_of_diaFree {M : Model κ} [M.MRelLifting] {A}
  (hA : A.diaFree) {x₁ : M.World} : x₁ ⊩ᵉ[_] A ↔ x₁ ⊩ⁱ[_] A := by
  induction A generalizing x₁ with
  | box A ihA =>
    constructor;
    . intro h y₁ Ix₁y₁ y₂ My₁y₂;
      exact ihA (by grind) |>.mp $
        ExtrinsicForces.persistent_of_diaFree (by grind) h Ix₁y₁ y₂ My₁y₂;
    . intro h y₁ Mx₁y₁;
      exact ihA (by grind) |>.mpr $ h x₁ (refl x₁) y₁ Mx₁y₁;
  | _ => grind;

lemma iff_mem_logicIntrinsic_mem_logicDiaFreeExtrinsic_of_diaFree (hA : A.diaFree) :
  (A ∈ logicIntrinsic.{u}) ↔ A ∈ logicDiaFreeExtrinsic.{u} := by
  simp only [Set.mem_ofPred_eq];
  constructor;
  . intro h;
    and_intros;
    . assumption;
    . intro κ M _ x;
      exact extrinsicForces_iff_intrinsicForces_of_diaFree (by grind) |>.mpr $ h M x;
  . rintro ⟨_, h⟩ κ M x;
    let M' : Model κ := {
      iRel' := M.iRel',
      mRel' x y := M.mRel x y ∨ (∃ x₂, M.iRel x x₂ ∧ M.mRel x₂ y),
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
          exact ⟨x₃, _root_.trans Ix₁x₂ Ix₂x₃, Mx₃y₂⟩;
    ⟩
    have : ∀ B, B.diaFree → ∀ x₁, (x₁ ⊩ⁱ[M] B ↔ x₁ ⊩ᵉ[M'] B) := by
      intro B hB x₁;
      induction B generalizing x₁ with
      | box B ih =>
        replace ih := ih (by grind);
        constructor;
        . rintro h y₁ (Mx₁y₁ | ⟨x₂, Ix₁x₂, Mx₂y₁⟩);
          . exact ih _ |>.mp $ h x₁ (refl _) y₁ Mx₁y₁;
          . exact ih _ |>.mp $ h _ Ix₁x₂ y₁ Mx₂y₁;
        . grind;
      | _ => grind;
    exact this A (by assumption) x |>.mpr $ h M' x;

lemma logicIntrinsic_boxRM_closed : (A 🡒 B) ∈ logicIntrinsic.{u} → (□A 🡒 □B) ∈ logicIntrinsic.{u} := by
  dsimp only [logicIntrinsic, Set.mem_ofPred_eq, IntrinsicValid];
  intro h _ M x₁ x₂ Ix₁x₂ hA x₃ Ix₂x₃ y₃ Mx₃y₃;
  apply h M y₃ y₃ (refl _) $ hA x₃ Ix₂x₃ y₃ Mx₃y₃;

lemma logicExtrinsic_boxRM_closed : (A 🡒 B) ∈ logicExtrinsic.{u} → (□A 🡒 □B) ∈ logicExtrinsic.{u} := by
  dsimp only [logicExtrinsic, Set.mem_ofPred_eq, ExtrinsicValid];
  intro h _ M _ _ x₁ x₂ Ix₁x₂ hA y₂ Mx₂y₂;
  apply h M y₂ y₂ (refl _) $ hA y₂ Mx₂y₂;

lemma logicDiaFreeExtrinsic_boxRM_closed :
  (A 🡒 B) ∈ logicDiaFreeExtrinsic.{u} → (□A 🡒 □B) ∈ logicDiaFreeExtrinsic.{u} := by
  dsimp only [logicDiaFreeExtrinsic, Set.mem_ofPred_eq, ExtrinsicValid];
  rintro ⟨_, h⟩;
  constructor;
  . assumption;
  . intro _ M _ x₁ x₂ Ix₁x₂ hA y₂ Mx₂y₂;
    apply h M y₂ y₂ (refl _) $ hA y₂ Mx₂y₂;


lemma logicExtrinsic_diaRM_closed : (A 🡒 B) ∈ logicExtrinsic.{u} → (◇A 🡒 ◇B) ∈ logicExtrinsic.{u} := by
  dsimp only [logicExtrinsic, Set.mem_ofPred_eq, ExtrinsicValid];
  rintro h _ M _ _ x₁ x₂ Ix₁x₂ ⟨y₂, Mx₂y₂, hy₂B⟩;
  exact ⟨y₂, Mx₂y₂, h M y₂ _ (refl _) hy₂B⟩;

lemma logicIntrinsic_diaRM_closed : (A 🡒 B) ∈ logicIntrinsic.{u} → (◇A 🡒 ◇B) ∈ logicIntrinsic.{u} := by
  dsimp only [logicIntrinsic, Set.mem_ofPred_eq, IntrinsicValid];
  intro h _ M x₁ x₂ Ix₁x₂ hA x₃ Ix₂x₃;
  obtain ⟨y₃, Mx₃y₃, hy₃A⟩ := hA x₃ Ix₂x₃;
  exact ⟨y₃, Mx₃y₃, h M y₃ y₃ (refl _) hy₃A⟩;

lemma boxTop_mem_logicExtrinsic : □⊤ ∈ logicExtrinsic := by
  rintro κ M _ _ x₁ y₁ Mx₁y₁;
  apply M.extrinsicForces_top;

lemma boxTop_mem_logicIntrinsic : □⊤ ∈ logicIntrinsic := by
  rintro κ M x₁ y₁ Mx₁y₁ y₂ Mx₁y₂;
  apply M.intrinsicForces_top;

lemma boxTop_mem_logicDiaFreeExtrinsic : □⊤ ∈ logicDiaFreeExtrinsic := by
  constructor;
  . grind;
  . rintro κ M _ _ x₁ y₁ Mx₁y₁;
    apply M.extrinsicForces_top;

lemma negDiaBot_mem_logicExtrinsic : ∼◇⊥ ∈ logicExtrinsic := by
  rintro κ M _ _ x₁ x₂ Ix₁x₂ ⟨y₂, Mx₂y₂, hy₂⟩;
  contradiction;

lemma negDiaBot_mem_logicIntrinsic : ∼◇⊥ ∈ logicIntrinsic := by
  rintro κ M x₁ x₂ Ix₁x₂ h;
  obtain ⟨y₂, Mx₁y₂, hy₂⟩ := h x₂ (refl _);
  contradiction;

end IML

end
