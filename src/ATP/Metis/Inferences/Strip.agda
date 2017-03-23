------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Strip inference rule.
------------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module ATP.Metis.Inferences.Strip (n : ℕ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Data.Prop.Theorems.Negation n using (¬-⊤ ; ¬-⊥₁)

open import Function using (id)

------------------------------------------------------------------------------

strip : Prop → Prop
strip (Var x) = (Var x)
strip (¬ ⊤)   = ⊥
strip (¬ ⊥)   = ⊤
strip (¬ φ)   = ¬ φ
strip (φ₁ ∨ φ₂ ∨ φ₃)   = (¬ φ₁) ∧ (¬ φ₂) ⇒ φ₃
strip (φ ∨ ψ)          = (¬ φ) ⇒ ψ
strip (φ₁ ⇒ (φ₂ ⇒ φ₃)) = φ₁ ∧ strip (φ₂ ⇒ φ₃)
strip φ = φ


postulate
  atp-step-strip :
      ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ strip φ


atp-strip : ∀ {Γ : Ctxt} {φ : Prop} → Γ ⊢ φ → Γ ⊢ strip φ
atp-strip {Γ} {Var x}          = id
atp-strip {Γ} {φ₁ ⇒ (φ₂ ⇒ φ₃)} = atp-step-strip
atp-strip {Γ} {¬ ⊤}            = ¬-⊤
atp-strip {Γ} {¬ ⊥}            = ¬-⊥₁
atp-strip {Γ} {φ}              = atp-step-strip
