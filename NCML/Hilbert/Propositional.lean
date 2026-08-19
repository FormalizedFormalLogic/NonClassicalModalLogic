module

public import NCML.Hilbert.Basic

@[expose] public section

open NCML BDFormula

namespace ProvableBDHilbert

section Combinators

variable {𝔸 : Set BDFormula} {A B C D : BDFormula}

lemma id_ : ⊢ᴴ[CK;𝔸] A 🡒 A := mp (mp imply₂ (imply₁ (B := A 🡒 A))) (imply₁ (B := A))

lemma verum : ⊢ᴴ[CK;𝔸] ⊤ := id_

lemma dhyp (h : ⊢ᴴ[CK;𝔸] B) : ⊢ᴴ[CK;𝔸] A 🡒 B := mp imply₁ h

lemma mp_ctx (h₁ : ⊢ᴴ[CK;𝔸] A 🡒 B 🡒 C) (h₂ : ⊢ᴴ[CK;𝔸] A 🡒 B) : ⊢ᴴ[CK;𝔸] A 🡒 C :=
  mp (mp imply₂ h₁) h₂

lemma mp_ctx₂ (h₁ : ⊢ᴴ[CK;𝔸] A 🡒 B 🡒 C 🡒 D) (h₂ : ⊢ᴴ[CK;𝔸] A 🡒 B 🡒 C) : ⊢ᴴ[CK;𝔸] A 🡒 B 🡒 D :=
  mp_ctx (imp_trans h₁ imply₂) h₂

lemma imp_comp_left (h : ⊢ᴴ[CK;𝔸] B 🡒 C) : ⊢ᴴ[CK;𝔸] (A 🡒 B) 🡒 (A 🡒 C) := mp imply₂ (dhyp h)

lemma imp_comp_right (h : ⊢ᴴ[CK;𝔸] A 🡒 B) : ⊢ᴴ[CK;𝔸] (B 🡒 C) 🡒 (A 🡒 C) :=
  mp_ctx (imp_trans imply₁ imply₂) (dhyp h)

lemma and_intro_ctx (h₁ : ⊢ᴴ[CK;𝔸] A 🡒 B) (h₂ : ⊢ᴴ[CK;𝔸] A 🡒 C) : ⊢ᴴ[CK;𝔸] A 🡒 B ⋏ C :=
  mp_ctx (imp_trans h₁ andIntro) h₂

lemma box_mono (h : ⊢ᴴ[CK;𝔸] A 🡒 B) : ⊢ᴴ[CK;𝔸] □A 🡒 □B := mp kBox (nec h)

lemma box_or_inl : ⊢ᴴ[CK;𝔸] □A 🡒 □(A ⋎ B) := box_mono orIntro₁

lemma box_or_inr : ⊢ᴴ[CK;𝔸] □B 🡒 □(A ⋎ B) := box_mono orIntro₂

lemma box_and_intro : ⊢ᴴ[CK;𝔸] □A 🡒 □B 🡒 □(A ⋏ B) := imp_trans (mp kBox (nec andIntro)) kBox

lemma imp_bot_imp_box_bot : ⊢ᴴ[CK;𝔸] (A 🡒 ⊥) 🡒 (A 🡒 □⊥) := imp_comp_left (efq (A := □⊥))

end Combinators

end ProvableBDHilbert

section Conj

open ProvableBDHilbert BDFormulaList

variable {𝔸 : Set BDFormula} {Γ Γ₁ Γ₂ : BDFormulaList}

lemma conj_append_left : ⊢ᴴ[CK;𝔸] conj (Γ₁ ++ Γ₂) 🡒 conj Γ₁ := by
  induction Γ₁ with
  | nil => exact dhyp verum;
  | cons A Γ₁ ih => exact and_intro_ctx andElim₁ (imp_trans andElim₂ ih);

lemma conj_append_right : ⊢ᴴ[CK;𝔸] conj (Γ₁ ++ Γ₂) 🡒 conj Γ₂ := by
  induction Γ₁ with
  | nil => exact id_;
  | cons A Γ₁ ih => exact imp_trans andElim₂ ih;

lemma conj_box : ⊢ᴴ[CK;𝔸] conj (Γ.map (□·)) 🡒 □(conj Γ) := by
  induction Γ with
  | nil => exact dhyp (nec verum);
  | cons A Γ ih => exact mp_ctx (imp_trans andElim₁ box_and_intro) (imp_trans andElim₂ ih);

end Conj

end
