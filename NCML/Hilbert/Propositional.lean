module

public import NCML.Hilbert.Basic

@[expose] public section

open NCML BDFormula

namespace ProvableBDHilbert

/-- Local shorthand for `ProvableBDHilbert`, kept out of the exported API. -/
local notation:50 𝔸:51 " ⊢ " A:51 => ProvableBDHilbert 𝔸 A

section Combinators

variable {𝔸 : Set BDFormula} {A B C D : BDFormula}

lemma id_ : 𝔸 ⊢ A 🡒 A := mp (mp imply₂ (imply₁ (B := A 🡒 A))) (imply₁ (B := A))

lemma verum : 𝔸 ⊢ ⊤ := id_

lemma dhyp (h : 𝔸 ⊢ B) : 𝔸 ⊢ A 🡒 B := mp imply₁ h

lemma mp_ctx (h₁ : 𝔸 ⊢ A 🡒 B 🡒 C) (h₂ : 𝔸 ⊢ A 🡒 B) : 𝔸 ⊢ A 🡒 C := mp (mp imply₂ h₁) h₂

lemma mp_ctx₂ (h₁ : 𝔸 ⊢ A 🡒 B 🡒 C 🡒 D) (h₂ : 𝔸 ⊢ A 🡒 B 🡒 C) : 𝔸 ⊢ A 🡒 B 🡒 D :=
  mp_ctx (imp_trans h₁ imply₂) h₂

lemma imp_comp_left (h : 𝔸 ⊢ B 🡒 C) : 𝔸 ⊢ (A 🡒 B) 🡒 (A 🡒 C) := mp imply₂ (dhyp h)

lemma imp_comp_right (h : 𝔸 ⊢ A 🡒 B) : 𝔸 ⊢ (B 🡒 C) 🡒 (A 🡒 C) :=
  mp_ctx (imp_trans imply₁ imply₂) (dhyp h)

lemma and_intro_ctx (h₁ : 𝔸 ⊢ A 🡒 B) (h₂ : 𝔸 ⊢ A 🡒 C) : 𝔸 ⊢ A 🡒 B ⋏ C :=
  mp_ctx (imp_trans h₁ andIntro) h₂

lemma box_mono (h : 𝔸 ⊢ A 🡒 B) : 𝔸 ⊢ □A 🡒 □B := mp kBox (nec h)

lemma box_or_inl : 𝔸 ⊢ □A 🡒 □(A ⋎ B) := box_mono orIntro₁

lemma box_or_inr : 𝔸 ⊢ □B 🡒 □(A ⋎ B) := box_mono orIntro₂

lemma box_and_intro : 𝔸 ⊢ □A 🡒 □B 🡒 □(A ⋏ B) := imp_trans (mp kBox (nec andIntro)) kBox

lemma imp_bot_imp_box_bot : 𝔸 ⊢ (A 🡒 ⊥) 🡒 (A 🡒 □⊥) := imp_comp_left (efq (A := □⊥))

end Combinators

end ProvableBDHilbert

section Lconj

/-- Conjunction of a list of formulas, right-folded with `⊤` as the base case. -/
def lconj (Γ : List BDFormula) : BDFormula := Γ.foldr (· ⋏ ·) ⊤

@[simp] lemma lconj_nil : lconj ([] : List BDFormula) = ⊤ := rfl

@[simp] lemma lconj_cons (A : BDFormula) (Γ : List BDFormula) :
  lconj (A :: Γ) = A ⋏ lconj Γ := rfl

open ProvableBDHilbert

local notation:50 𝔸:51 " ⊢ " A:51 => ProvableBDHilbert 𝔸 A

variable {𝔸 : Set BDFormula} {Γ Γ₁ Γ₂ : List BDFormula}

lemma lconj_append_left : 𝔸 ⊢ lconj (Γ₁ ++ Γ₂) 🡒 lconj Γ₁ := by
  induction Γ₁ with
  | nil => exact dhyp verum;
  | cons A Γ₁ ih => exact and_intro_ctx andElim₁ (imp_trans andElim₂ ih);

lemma lconj_append_right : 𝔸 ⊢ lconj (Γ₁ ++ Γ₂) 🡒 lconj Γ₂ := by
  induction Γ₁ with
  | nil => exact id_;
  | cons A Γ₁ ih => exact imp_trans andElim₂ ih;

lemma lconj_box : 𝔸 ⊢ lconj (Γ.map (□·)) 🡒 □(lconj Γ) := by
  induction Γ with
  | nil => exact dhyp (nec verum);
  | cons A Γ ih => exact mp_ctx (imp_trans andElim₁ box_and_intro) (imp_trans andElim₂ ih);

end Lconj

end
