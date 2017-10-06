------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Normal Forms.
------------------------------------------------------------------------------

open import Data.Nat using (ℕ; suc; zero; _+_;_*_) renaming (_⊔_ to max )

module ATP.Metis.Rules.Normalization (n : ℕ) where

------------------------------------------------------------------------------

open import ATP.Metis.Rules.Checking n

open import Data.Bool.Base
  using ( Bool; true; false; if_then_else_; not)
  renaming (_∧_ to _and_; _∨_ to _or_)

open import Data.Fin  using ( Fin; #_ )
open import Data.List using ( List; [_]; [];  _++_; _∷_ ; concatMap; map )

open import Data.PropFormula.Properties n using ( subst )
open import Data.PropFormula.Syntax n
open import Data.PropFormula.Views  n
open import Data.PropFormula.NormalForms n
  using (dnf-dist; thm-dnf-dist; cnf-dist; thm-cnf-dist)

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

nnf : Polarity → PropFormula → PropFormula
nnf ⊕ φ
  with nnf-view φ
nnf ⊕ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = (nnf ⊕ φ₁) ∧ (nnf ⊕ φ₂)
nnf ⊕ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ = (nnf ⊕ φ₁) ∨ (nnf ⊕ φ₂)
nnf ⊕ .(φ₁ ⇒ φ₂) | impl φ₁ φ₂ = (nnf ⊝ φ₁) ∨ (nnf ⊕ φ₂)
nnf ⊕ .(¬ φ)     | nneg φ     = nnf ⊝ φ
nnf ⊕ φ          | other .φ   = φ
nnf ⊝ φ
  with nnf-view φ
nnf ⊝ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = (nnf ⊝ φ₁) ∨ (nnf ⊝ φ₂)
nnf ⊝ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ = (nnf ⊝ φ₁) ∧ (nnf ⊝ φ₂)
nnf ⊝ .(φ₁ ⇒ φ₂) | impl φ₁ φ₂ = (nnf ⊝ φ₂) ∧ (nnf ⊕ φ₁)
nnf ⊝ .(¬ φ)     | nneg φ     = nnf ⊕ φ
nnf ⊝ φ          | other .φ   = φ

polarity : PropFormula → Polarity
polarity φ
  with neg-view φ
polarity .(¬ φ) | neg φ  = ⊝
polarity φ      | pos .φ = ⊕

postulate
  thm-nnf
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ nnf (polarity φ) φ

postulate
  thm-from-nnf-⊕
    : ∀ {Γ} {φ}
    → Γ ⊢ nnf ⊕ φ
    → Γ ⊢ φ

postulate
  thm-from-nnf-⊝
    : ∀ {Γ} {φ}
    → Γ ⊢ nnf ⊝ φ
    → Γ ⊢ ¬ φ

nnf-φ : PropFormula → PropFormula
nnf-φ φ = nnf (polarity φ) φ


----------------------------------------------------------------------------
-- Testing for a normal form.

is∨ : PropFormula → Bool
is∨ φ
  with d-view φ
is∨ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = false
is∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ = is∨ φ₁ and is∨ φ₂
is∨ φ          | other .φ   = true

is∧∨ : PropFormula → Bool
is∧∨ φ
  with d-view φ
is∧∨ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = is∧∨ φ₁ and is∧∨ φ₂
is∧∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ = is∨ φ₁ and is∨ φ₂
is∧∨ φ          | other .φ   = true

is∧ : PropFormula → Bool
is∧ φ
  with d-view φ
is∧ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = is∧ φ₁ and is∧ φ₂
is∧ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ = false
is∧ φ          | other .φ   = true

is∨∧ : PropFormula → Bool
is∨∧ φ
  with d-view φ
is∨∧ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = is∧ φ₁ and is∧ φ₂
is∨∧ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ = is∨∧ φ₁ and is∨∧ φ₂
is∨∧ φ          | other .φ   = true


isNNF : PropFormula → Bool
isNNF φ
  with push-neg-view φ
isNNF φ          | yes .φ     = false
isNNF .(φ₁ ∧ φ₂) | no-∧ φ₁ φ₂ = isNNF φ₁ and isNNF φ₂
isNNF .(φ₁ ∨ φ₂) | no-∨ φ₁ φ₂ = isNNF φ₁ and isNNF φ₂
isNNF φ          | no .φ      = true

isCNF : PropFormula → Bool
isCNF φ = isNNF φ and is∧∨ φ

isDNF : PropFormula → Bool
isDNF φ = isNNF φ and is∨∧ φ

------------------------------------------------------------------------------


