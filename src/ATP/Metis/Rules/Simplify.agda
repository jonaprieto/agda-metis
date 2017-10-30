------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Simplify inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Simplify ( n : ℕ ) where

------------------------------------------------------------------------------

open import ATP.Metis.Synonyms n
open import ATP.Metis.Rules.Normalization n
open import ATP.Metis.Rules.Conjunct n
open import ATP.Metis.Rules.Canonicalize n

open import Data.Bool.Base
  using    ( Bool; true; false )
  renaming ( _∨_ to _or_; _∧_ to _and_ )

open import Data.PropFormula.Dec n        using ( ⌊_⌋; yes; no )
open import Data.PropFormula.Properties n using ( eq ; subst )
open import Data.PropFormula.Syntax n
open import Data.PropFormula.Theorems n

open import Function using ( id ; _∘_ ; _$_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym )

------------------------------------------------------------------------------

data simplifyCases : PropFormula → Set where
  case₁ : (γ₁ γ₂ : PropFormula) → simplifyCases (γ₁ ⇒ γ₂)
  case₂ : (γ₁ γ₂ : PropFormula) → simplifyCases (γ₁ ∨ γ₂)
  other : (φ : PropFormula)     → simplifyCases φ

simplify-cases : (φ : PropFormula) → simplifyCases φ
simplify-cases (γ₁ ⇒ γ₂) = case₁ _ _
simplify-cases (γ₁ ∨ γ₂) = case₂ _ _
simplify-cases φ         = other _

simplify₀ : Premise → Premise → Conclusion → PropFormula
simplify₀ ⊥ φ₂ ψ  = ⊥
simplify₀ φ₁ ⊥ ψ  = ⊥
simplify₀ φ₁ φ₂ ⊤ = ⊤
simplify₀ φ₁ φ₂ ψ
  with ⌊ eq φ₁ ψ ⌋
...   | true = ψ
...   | false
  with ⌊ eq φ₂ ψ ⌋
...   | true = ψ
...   | false
  with simplify-cases φ₁
simplify₀ .(γ₁ ⇒ γ₂) φ₂ ψ | false | false | case₁ γ₁ γ₂
  with ⌊ eq γ₁ φ₂ ⌋
...   | true = γ₂
...   | false
  with ⌊ eq γ₂ (nnf (¬ φ₂)) ⌋
...   | true = γ₁
...   | false
  with ⌊ eq (nnf (¬ (γ₁ ⇒ γ₂))) (conjunct φ₂ (nnf (¬ (γ₁ ⇒ γ₂)))) ⌋
... | true  = ⊥
... | false
  with ⌊ eq (¬ (γ₁ ⇒ γ₂)) (canonicalize φ₂ (¬ (γ₁ ⇒ γ₂))) ⌋
... | true  = ⊥
... | false = γ₁ ⇒ γ₂
simplify₀ .(γ₁ ∨ γ₂) φ₂ ψ | false | false | case₂ γ₁ γ₂
  with ⌊ eq γ₁ (nnf (¬ φ₂)) ⌋
...   | true = γ₂
...   | false
  with ⌊ eq γ₂ (nnf (¬ φ₂)) ⌋
...   | true = γ₁
...   | false
  with ⌊ eq (nnf (¬ (γ₁ ∨ γ₂))) (conjunct φ₂ (nnf (¬ (γ₁ ∨ γ₂)))) ⌋
... | true  = ⊥
... | false
  with ⌊ eq (¬ (γ₁ ∨ γ₂)) (canonicalize φ₂ (¬ (γ₁ ∨ γ₂))) ⌋
... | true  = ⊥
... | false = γ₁ ∨ γ₂

simplify₀ φ₁ φ₂ ψ | false | false | other .φ₁
  with ⌊ eq (nnf (¬ φ₁)) (conjunct φ₂ (nnf (¬ φ₁))) ⌋
... | true  = ⊥
... | false
  with ⌊ eq (¬ φ₁) (canonicalize φ₂ (¬ φ₁)) ⌋
... | true  = ⊥
... | false = φ₁


postulate
  simplify₀-lem
    : ∀ {Γ} {φ₁ φ₂ : Premise}
      → Γ ⊢ φ₁
      → Γ ⊢ φ₂
      → (ψ : Conclusion)
      → Γ ⊢ simplify₀ φ₁ φ₂ ψ

data S-View : Premise → Premise → Conclusion → Set where
  normal : (φ₁ φ₂ ψ : PropFormula) → S-View φ₁ φ₂ ψ
  swap   : (φ₁ φ₂ ψ : PropFormula) → S-View φ₁ φ₂ ψ

s-view : (φ₁ φ₂ ψ : PropFormula) → S-View φ₁ φ₂ ψ
s-view φ₁ φ₂ ψ with simplify₀ φ₁ φ₂ ψ
... | ⊥ = normal φ₁ φ₂ ψ
... | z with simplify₀ φ₂ φ₁ ψ
...        | ⊥ = swap   φ₁ φ₂ ψ
...        | w = normal φ₁ φ₂ ψ

-- Def.
simplify : Premise → Premise → Conclusion → PropFormula
simplify φ₁ φ₂ ψ with s-view φ₁ φ₂ ψ
simplify φ₁ φ₂ ψ | normal .φ₁ .φ₂ .ψ = simplify₀ φ₁ φ₂ ψ
simplify φ₁ φ₂ ψ | swap   .φ₁ .φ₂ .ψ = simplify₀ φ₂ φ₁ ψ

postulate
  -- Theorem.
  simplify-thm
    : ∀ {Γ} {φ₁ φ₂ : Premise}
    → (ψ : Conclusion)
    → Γ ⊢ φ₁
    → Γ ⊢ φ₂
    → Γ ⊢ simplify φ₁ φ₂ ψ
