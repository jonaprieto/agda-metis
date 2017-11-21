{-
-- Def.
data Polarity : Set where
  ⊕ : Polarity
  ⊖ : Polarity

data nnf-Cases : PropFormula  → Set where

  case₁ : (φ₁ φ₂ : PropFormula) → nnf-Cases (φ₁ ∧ φ₂)
  case₂ : (φ₁ φ₂ : PropFormula) → nnf-Cases (φ₁ ∨ φ₂)
  case₃ : (φ₁ φ₂ : PropFormula) → nnf-Cases (φ₁ ⊃ φ₂)
  case₄ : (φ : PropFormula)     → nnf-Cases (¬ φ)
  case₅ : (φ : PropFormula)     → nnf-Cases ⊥
  case₆ : (φ : PropFormula)     → nnf-Cases ⊤
  other : (φ : PropFormula)     → nnf-Cases φ

nnf-cases : (φ : PropFormula) → nnf-Cases φ
nnf-cases (φ₁ ∧ φ₂) = case₁ _ _
nnf-cases (φ₁ ∨ φ₂) = case₂ _ _
nnf-cases (φ₁ ⊃ φ₂) = case₃ _ _
nnf-cases (¬ φ)     = case₄ _
nnf-cases ⊥         = case₅ ⊥
nnf-cases ⊤         = case₆ ⊤
nnf-cases φ         = other _

-- Def.
nnf₀ : Polarity → PropFormula → PropFormula
nnf₀ ⊕ φ
  with nnf-cases φ
nnf₀ ⊕ .(φ₁ ∧ φ₂) | case₁ φ₁ φ₂ = simplify-∧ (assoc-∧ (nnf₀ ⊕ φ₁ ∧ nnf₀ ⊕ φ₂))
nnf₀ ⊕ .(φ₁ ∨ φ₂) | case₂ φ₁ φ₂ = simplify-∨ (assoc-∨ (nnf₀ ⊕ φ₁ ∨ nnf₀ ⊕ φ₂))
nnf₀ ⊕ .(φ₁ ⊃ φ₂) | case₃ φ₁ φ₂ = simplify-∨ (assoc-∨ (nnf₀ ⊖ φ₁ ∨ nnf₀ ⊕ φ₂))
nnf₀ ⊕ .(¬ φ)     | case₄ φ     = nnf₀ ⊖ φ
nnf₀ ⊕ .(⊥)       | case₅ φ     = ⊥
nnf₀ ⊕ .(⊤)       | case₆ φ     = ⊤
nnf₀ ⊕ φ          | other .φ    = φ
nnf₀ ⊖ φ
  with nnf-cases φ
nnf₀ ⊖ .(φ₁ ∧ φ₂) | case₁ φ₁ φ₂ = simplify-∨ (assoc-∨ (nnf₀ ⊖ φ₁ ∨ nnf₀ ⊖ φ₂))
nnf₀ ⊖ .(φ₁ ∨ φ₂) | case₂ φ₁ φ₂ = simplify-∧ (assoc-∧ (nnf₀ ⊖ φ₁ ∧ nnf₀ ⊖ φ₂))
nnf₀ ⊖ .(φ₁ ⊃ φ₂) | case₃ φ₁ φ₂ = simplify-∧ (assoc-∧ (nnf₀ ⊖ φ₂ ∧ nnf₀ ⊕ φ₁))
nnf₀ ⊖ .(¬ φ)     | case₄ φ     = nnf₀ ⊕ φ
nnf₀ ⊖ .(⊥)       | case₅ φ     = ⊤
nnf₀ ⊖ .(⊤)       | case₆ φ     = ⊥
nnf₀ ⊖ φ          | other .φ    = ¬ φ

-- Lemma.
postulate
  nnf₀-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → (pol : Polarity)
    → Γ ⊢ nnf₀ pol φ

postulate
  from-nnf₀-lem
    : ∀ {Γ} {φ}
    → (pol : Polarity)
    → Γ ⊢ nnf₀ pol φ
    → Γ ⊢ φ

-- Def.
nnf : PropFormula → PropFormula
nnf φ = nnf₀ ⊕ φ

postulate
  nnf-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ nnf φ

postulate
  from-nnf-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ nnf φ
    → Γ ⊢ φ
-}





