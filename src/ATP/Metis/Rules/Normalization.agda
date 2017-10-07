------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Normal Forms.
------------------------------------------------------------------------------

open import Data.Nat using (ℕ; suc; zero; _+_;_*_) renaming (_⊔_ to max )

module ATP.Metis.Rules.Normalization (n : ℕ) where

------------------------------------------------------------------------------

open import ATP.Metis.Rules.Checking n
open import ATP.Metis.Rules.Reordering n

open import Data.Bool.Base
  using ( Bool; true; false; if_then_else_; not)
  renaming (_∧_ to _and_; _∨_ to _or_)

open import Data.Fin  using ( Fin; #_ )
open import Data.List using ( List; [_]; [];  _++_; _∷_ ; concatMap; map )

open import Data.PropFormula.Properties n using ( subst )
open import Data.PropFormula.Syntax n
open import Data.PropFormula.SyntaxExperiment n
open import Data.PropFormula.Views  n
open import Data.PropFormula.NormalForms n
  using ( dnf-dist; thm-dnf-dist; cnf-dist; thm-cnf-dist )

open import Relation.Nullary using (yes; no)
open import Data.PropFormula.Theorems n

open import Function using ( _∘_; _$_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; sym )

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- A modified version of the negative normal form of the Agda-Prop module.
-- * We do not convert any biimplication.
------------------------------------------------------------------------------

data Polarity : Set where
  ⊕ : Polarity
  ⊝ : Polarity

data nnfView : PropFormula  → Set where
  conj   : (φ₁ φ₂ : PropFormula) → nnfView (φ₁ ∧ φ₂)
  disj   : (φ₁ φ₂ : PropFormula) → nnfView (φ₁ ∨ φ₂)
  impl   : (φ₁ φ₂ : PropFormula) → nnfView (φ₁ ⇒ φ₂)
  nneg   : (φ₁ : PropFormula)    → nnfView (¬ φ₁)
  other  : (φ₁ : PropFormula)    → nnfView φ₁

nnf-view : (φ : PropFormula) → nnfView φ
nnf-view (φ₁ ∧ φ₂) = conj _ _
nnf-view (φ₁ ∨ φ₂) = disj _ _
nnf-view (φ₁ ⇒ φ₂) = impl _ _
nnf-view (¬ φ)     = nneg _
nnf-view φ         = other _

nnf₀ : Polarity → PropFormula → PropFormula
nnf₀ ⊕ φ
  with nnf-view φ
nnf₀ ⊕ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = (nnf₀ ⊕ φ₁) ∧ (nnf₀ ⊕ φ₂)
nnf₀ ⊕ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ = (nnf₀ ⊕ φ₁) ∨ (nnf₀ ⊕ φ₂)
nnf₀ ⊕ .(φ₁ ⇒ φ₂) | impl φ₁ φ₂ = (nnf₀ ⊝ φ₁) ∨ (nnf₀ ⊕ φ₂)
nnf₀ ⊕ .(¬ φ)     | nneg φ     = nnf₀ ⊝ φ
nnf₀ ⊕ φ          | other .φ   = φ
nnf₀ ⊝ φ
  with nnf-view φ
nnf₀ ⊝ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = (nnf₀ ⊝ φ₁) ∨ (nnf₀ ⊝ φ₂)
nnf₀ ⊝ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ = (nnf₀ ⊝ φ₁) ∧ (nnf₀ ⊝ φ₂)
nnf₀ ⊝ .(φ₁ ⇒ φ₂) | impl φ₁ φ₂ = (nnf₀ ⊝ φ₂) ∧ (nnf₀ ⊕ φ₁)
nnf₀ ⊝ .(¬ φ)     | nneg φ     = nnf₀ ⊕ φ
nnf₀ ⊝ φ          | other .φ   = ¬ φ

polarity : PropFormula → Polarity
polarity φ
  with neg-view φ
polarity .(¬ φ) | neg φ  = ⊝
polarity φ      | pos .φ = ⊕

postulate
  thm-nnf₀
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ nnf₀ ⊕ φ

postulate
  thm-from-nnf₀
    : ∀ {Γ} {φ}
    → Γ ⊢ nnf₀ ⊕ φ
    → Γ ⊢ ¬ φ

nnf : PropFormula → PropFormula
nnf φ = nnf₀ ⊕ φ

postulate
  thm-from-nnf
    : ∀ {Γ} {φ}
    → Γ ⊢ nnf φ
    → Γ ⊢ φ

------------------------------------------------------------------------------

const : PropFormula → (PropFormula → PropFormula)
const φ = λ x → φ

nform : PropFormula → PropFormula → PropFormula
nform φ =
  (
   (dnf-nnf) ●
   (cnf-nnf) ●
   (↑f (const mem-nnf))
  ) φ
  where
    mem-nnf : PropFormula
    mem-nnf = nnf φ

    cnf-nnf : PropFormula → PropFormula → PropFormula
    cnf-nnf φ ψ = reorder-∧∨ (right-assoc-∧ (cnf-dist (mem-nnf))) ψ

    dnf-nnf : PropFormula → PropFormula → PropFormula
    dnf-nnf φ ψ = reorder-∨ (dnf-dist mem-nnf) ψ

------------------------------------------------------------------------------

-- cnf : PropFormula → PropFormula
-- cnf φ ψ = reorder-∧∨ {!!} {!!}

