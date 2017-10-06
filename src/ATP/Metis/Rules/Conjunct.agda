------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Conjunct inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Conjunct ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool.Base         using ( Bool; false; true )
open import Data.List.Base         using (_∷_; []; [_]; List; _∷ʳ_; _++_)

open import Data.PropFormula.Dec n        using ( yes; no; ⌊_⌋ )
open import Data.PropFormula.Properties n using ( eq; subst )
open import Data.PropFormula.Syntax n
open import Data.PropFormula.Views n

open import Function using ( _$_; id )

open import Relation.Binary.PropositionalEquality using ( refl )

------------------------------------------------------------------------------

conjunct : PropFormula → PropFormula → PropFormula
conjunct φ ψ
  with ⌊ eq φ ψ ⌋
... | true  = ψ
... | false
    with conj-view φ
... | other _  =  φ
... | conj φ₁ φ₂
    with ⌊ eq (conjunct φ₁ ψ) ψ ⌋
...    | true  = ψ
...    | false
       with ⌊ eq (conjunct φ₂ ψ) ψ ⌋
...       | true   = ψ
...       | false  = φ

thm-conjunct
  : ∀ {Γ} {φ}
  → (ψ : PropFormula)
  → Γ ⊢ φ
  → Γ ⊢ conjunct φ ψ

thm-conjunct {Γ} {φ} ψ Γ⊢φ
  with eq φ ψ
... | yes p₁  = subst p₁ Γ⊢φ
... | no _
    with conj-view φ
...    | other _  = Γ⊢φ
...    | conj φ₁ φ₂
       with eq (conjunct φ₁ ψ) ψ
...       | yes p₂  = subst p₂ (thm-conjunct ψ (∧-proj₁ Γ⊢φ))
...       | no _
          with eq (conjunct φ₂ ψ) ψ
...          | yes p₃ = subst p₃ (thm-conjunct ψ (∧-proj₂ Γ⊢φ))
...          | no _   = Γ⊢φ

