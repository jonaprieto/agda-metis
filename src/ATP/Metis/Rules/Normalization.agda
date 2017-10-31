------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Normal Forms.
------------------------------------------------------------------------------

open import Data.Nat using (ℕ; suc; zero; _+_;_*_) renaming (_⊔_ to max )

module ATP.Metis.Rules.Normalization (n : ℕ) where

------------------------------------------------------------------------------

open import ATP.Metis.Rules.Conjunct n
open import ATP.Metis.Rules.Checking n
open import ATP.Metis.Rules.Reordering n
  using ( disj; disj-lem; reorder-∨; reorder-∨-lem; assoc-∧; assoc-∨)

open import Data.Bool.Base
  using ( Bool; true; false)

open import Data.PropFormula.Dec n
open import Data.PropFormula.Properties n
open import Data.PropFormula.Syntax n
open import Data.PropFormula.Views  n
  renaming ( disj to disjshape )

open import Relation.Binary.PropositionalEquality using (_≡_; sym)

------------------------------------------------------------------------------

data simplify-∨-Cases : PropFormula  → Set where

  sdisj₁ : (φ : PropFormula)     → simplify-∨-Cases (⊥ ∨ φ)
  sdisj₂ : (φ : PropFormula)     → simplify-∨-Cases (φ ∨ ⊥)
  sdisj₃ : (φ : PropFormula)     → simplify-∨-Cases (⊤ ∨ φ)
  sdisj₄ : (φ : PropFormula)     → simplify-∨-Cases (φ ∨ ⊤)
  sdisj₅ : (φ₁ φ₂ : PropFormula) → simplify-∨-Cases (φ₁ ∨ φ₂)
  other  : (φ : PropFormula)     → simplify-∨-Cases φ

simplify-∨-cases : (φ : PropFormula) → simplify-∨-Cases φ
simplify-∨-cases (⊥ ∨ φ)   = sdisj₁ _
simplify-∨-cases (φ ∨ ⊥)   = sdisj₂ _
simplify-∨-cases (⊤ ∨ φ)   = sdisj₃ _
simplify-∨-cases (φ ∨ ⊤)   = sdisj₄ _
simplify-∨-cases (φ₁ ∨ φ₂) = sdisj₅ _ _
simplify-∨-cases  φ        = other _

-- Def.
_∈∨_ : (φ ψ : PropFormula) → Dec (ψ ≡ reorder-∨ φ ψ)
φ ∈∨ ψ = eq ψ (reorder-∨ φ ψ)

-- Def.
simplify-∨ : PropFormula → PropFormula
simplify-∨ φ
  with simplify-∨-cases φ
simplify-∨ .(⊥ ∨ φ) | sdisj₁ φ = simplify-∨ φ
simplify-∨ .(φ ∨ ⊥) | sdisj₂ φ = simplify-∨ φ
simplify-∨ .(⊤ ∨ φ) | sdisj₃ φ = ⊤
simplify-∨ .(φ ∨ ⊤) | sdisj₄ φ = ⊤
simplify-∨ φ        | other .φ  = φ
simplify-∨ .(φ₁ ∨ φ₂)  | sdisj₅ φ₁ φ₂
  with neg-view  φ₁
simplify-∨ .(¬ ψ ∨ φ₂) | sdisj₅ .(¬ ψ) φ₂ | neg ψ
  with ⌊ ψ ∈∨ φ₂ ⌋
... | true  = ⊤
... | false
    with ⌊ (¬ ψ) ∈∨ φ₂ ⌋
... | true  = simplify-∨ φ₂
... | false
    with ⌊ eq (simplify-∨ φ₂) ⊤ ⌋
...     | true  = ⊤
...     | false
        with ⌊ eq (simplify-∨ φ₂) ⊥ ⌋
...     | true  = ¬ ψ
...     | false = ¬ ψ ∨ simplify-∨ φ₂
simplify-∨ .(φ₁ ∨ φ₂) | sdisj₅ φ₁ φ₂ | pos .φ₁
  with ⌊ (¬ φ₁) ∈∨ φ₂ ⌋
... | true  = ⊤
... | false
    with ⌊ φ₁ ∈∨ φ₂ ⌋
... | true  = simplify-∨ φ₂
... | false
    with ⌊ eq (simplify-∨ φ₂) ⊤ ⌋
...     | true  = ⊤
...     | false
        with ⌊ eq (simplify-∨ φ₂) ⊥ ⌋
...     | true  = φ₁
...     | false = φ₁ ∨ simplify-∨ φ₂


-- Lemma.
postulate
  simplify-∨-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ simplify-∨ φ


data simplify-∧-Cases : PropFormula  → Set where

  sconj₁ : (φ : PropFormula)     → simplify-∧-Cases (⊥ ∧ φ)
  sconj₂ : (φ : PropFormula)     → simplify-∧-Cases (φ ∧ ⊥)
  sconj₃ : (φ : PropFormula)     → simplify-∧-Cases (⊤ ∧ φ)
  sconj₄ : (φ : PropFormula)     → simplify-∧-Cases (φ ∧ ⊤)
  sconj₅ : (φ₁ φ₂ : PropFormula) → simplify-∧-Cases (φ₁ ∧ φ₂)
  other  : (φ : PropFormula)     → simplify-∧-Cases φ

simplify-∧-cases : (φ : PropFormula) → simplify-∧-Cases φ
simplify-∧-cases (⊥ ∧ φ)   = sconj₁ _
simplify-∧-cases (φ ∧ ⊥)   = sconj₂ _
simplify-∧-cases (⊤ ∧ φ)   = sconj₃ _
simplify-∧-cases (φ ∧ ⊤)   = sconj₄ _
simplify-∧-cases (φ₁ ∧ φ₂) = sconj₅ _ _
simplify-∧-cases  φ        = other _

-- Def.
_∈∧_ : (ψ φ : PropFormula) → Dec (ψ ≡ (disj φ ψ))
ψ ∈∧ φ = eq ψ (disj φ ψ)

-- Def.
simplify-∧ : PropFormula → PropFormula
simplify-∧ φ
  with simplify-∧-cases φ
simplify-∧ .(⊥ ∧ φ) | sconj₁ φ = ⊥
simplify-∧ .(φ ∧ ⊥) | sconj₂ φ = ⊥
simplify-∧ .(⊤ ∧ φ) | sconj₃ φ = simplify-∧ φ
simplify-∧ .(φ ∧ ⊤) | sconj₄ φ = simplify-∧ φ
simplify-∧ φ        | other .φ  = φ
simplify-∧ .(φ₁ ∧ φ₂)  | sconj₅ φ₁ φ₂
  with neg-view  φ₁
simplify-∧ .(¬ ψ ∧ φ₂) | sconj₅ .(¬ ψ) φ₂ | neg ψ
  with ⌊ ψ ∈∧ φ₂ ⌋
... | true  = ⊥
... | false
    with ⌊ (¬ ψ) ∈∧ φ₂ ⌋
... | true  = simplify-∧ φ₂
... | false
    with ⌊ eq (simplify-∧ φ₂) ⊥ ⌋
...     | true  = ⊥
...     | false
        with ⌊ eq (simplify-∧ φ₂) ⊤ ⌋
...     | true  = ¬ ψ
...     | false = ¬ ψ ∧ simplify-∧ φ₂
simplify-∧ .(φ₁ ∧ φ₂) | sconj₅ φ₁ φ₂ | pos .φ₁
  with ⌊ (¬ φ₁) ∈∧ φ₂ ⌋
... | true  = ⊥
... | false
    with ⌊ φ₁ ∈∧ φ₂ ⌋
... | true  = simplify-∧ φ₂
... | false
    with ⌊ eq (simplify-∧ φ₂) ⊥ ⌋
...     | true  = ⊥
...     | false
        with ⌊ eq (simplify-∧ φ₂) ⊤ ⌋
...     | true  = φ₁
...     | false = φ₁ ∧ simplify-∧ φ₂


-- Lemma.
postulate
  simplify-∧-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ simplify-∧ φ

----------------------------------------------------------------------

data Polarity : Set where
  ⊕ : Polarity
  ⊖ : Polarity


data nnf-Cases : PropFormula  → Set where

  case₁ : (φ₁ φ₂ : PropFormula) → nnf-Cases (φ₁ ∧ φ₂)
  case₂ : (φ₁ φ₂ : PropFormula) → nnf-Cases (φ₁ ∨ φ₂)
  case₃ : (φ₁ φ₂ : PropFormula) → nnf-Cases (φ₁ ⇒ φ₂)
  case₄ : (φ : PropFormula)     → nnf-Cases (¬ φ)
  case₅ : (φ : PropFormula)     → nnf-Cases ⊥
  case₆ : (φ : PropFormula)     → nnf-Cases ⊤
  other : (φ : PropFormula)     → nnf-Cases φ

nnf-cases : (φ : PropFormula) → nnf-Cases φ
nnf-cases (φ₁ ∧ φ₂) = case₁ _ _
nnf-cases (φ₁ ∨ φ₂) = case₂ _ _
nnf-cases (φ₁ ⇒ φ₂) = case₃ _ _
nnf-cases (¬ φ)     = case₄ _
nnf-cases ⊥         = case₅ ⊥
nnf-cases ⊤         = case₆ ⊤
nnf-cases φ         = other _

nnf₀ : Polarity → PropFormula → PropFormula
nnf₀ ⊕ φ
  with nnf-cases φ
nnf₀ ⊕ .(φ₁ ∧ φ₂) | case₁ φ₁ φ₂ = simplify-∧ (assoc-∧ (nnf₀ ⊕ φ₁ ∧ nnf₀ ⊕ φ₂))
nnf₀ ⊕ .(φ₁ ∨ φ₂) | case₂ φ₁ φ₂ = simplify-∨ (assoc-∨ (nnf₀ ⊕ φ₁ ∨ nnf₀ ⊕ φ₂))
nnf₀ ⊕ .(φ₁ ⇒ φ₂) | case₃ φ₁ φ₂ = simplify-∨ (assoc-∨ (nnf₀ ⊖ φ₁ ∨ nnf₀ ⊕ φ₂))
nnf₀ ⊕ .(¬ φ)     | case₄ φ     = nnf₀ ⊖ φ
nnf₀ ⊕ .(⊥)       | case₅ φ     = ⊥
nnf₀ ⊕ .(⊤)       | case₆ φ     = ⊤
nnf₀ ⊕ φ          | other .φ    = φ
nnf₀ ⊖ φ
  with nnf-cases φ
nnf₀ ⊖ .(φ₁ ∧ φ₂) | case₁ φ₁ φ₂ = simplify-∨ (assoc-∨ (nnf₀ ⊖ φ₁ ∨ nnf₀ ⊖ φ₂))
nnf₀ ⊖ .(φ₁ ∨ φ₂) | case₂ φ₁ φ₂ = simplify-∧ (assoc-∧ (nnf₀ ⊖ φ₁ ∧ nnf₀ ⊖ φ₂))
nnf₀ ⊖ .(φ₁ ⇒ φ₂) | case₃ φ₁ φ₂ = simplify-∧ (assoc-∧ (nnf₀ ⊖ φ₂ ∧ nnf₀ ⊕ φ₁))
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

------------------------------------------------------------------------------
-- Conjunctive Normal Forms (CNF)
------------------------------------------------------------------------------

-- Def.
dist-∨ : PropFormula → PropFormula
dist-∨ φ with c-view-aux φ
dist-∨ .((φ₁ ∧ φ₂) ∨ φ₃) | case₁ φ₁ φ₂ φ₃ = dist-∨ (φ₁ ∨ φ₃) ∧ dist-∨ (φ₂ ∨ φ₃)
dist-∨ .(φ₁ ∨ (φ₂ ∧ φ₃)) | case₂ φ₁ φ₂ φ₃ = dist-∨ (φ₁ ∨ φ₂) ∧ dist-∨ (φ₁ ∨ φ₃)
dist-∨ φ                 | other .φ       = φ

postulate
  -- Lemma.
  dist-∨-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ dist-∨ φ

postulate
  -- Lemma.
  from-dist-∨-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ dist-∨ φ
    → Γ ⊢ φ

-- Def.
dist : PropFormula → PropFormula
dist φ with d-view φ
dist .(φ ∧ ψ) | conj φ ψ      = dist φ ∧ dist ψ
dist .(φ ∨ ψ) | disjshape φ ψ = dist-∨ ((dist φ) ∨ (dist ψ))
dist φ        | other .φ      = φ

postulate
  -- Lemma.
  dist-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ dist φ

postulate
  -- Lemma.
  from-dist-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ dist φ
    → Γ ⊢ φ

-- Def.
cnf : PropFormula → PropFormula
cnf φ = dist (nnf φ)

-- Lemma.
cnf-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ cnf φ

-- Proof.
cnf-lem Γ⊢φ = dist-lem (nnf-lem Γ⊢φ)  -- ▩

postulate
  from-cnf-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ cnf φ
    → Γ ⊢ φ
