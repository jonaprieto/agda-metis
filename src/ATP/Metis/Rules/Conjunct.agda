------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Conjunct inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Conjunct ( n : ℕ ) where

------------------------------------------------------------------------------

open import  ATP.Metis.Synonyms n

open import Data.Bool.Base using ( false; true )

open import Data.PropFormula.Dec n        using ( yes; no; ⌊_⌋ )
open import Data.PropFormula.Properties n using ( eq; subst )
open import Data.PropFormula.Syntax n
open import Data.PropFormula.Views  n using ( conj-view; other; conj )

open import Relation.Binary.PropositionalEquality using ( sym )

------------------------------------------------------------------------------

conjunct : PropFormula → PropFormula → PropFormula
conjunct φ ψ
  with ⌊ eq φ ψ ⌋
... | true  = ψ
... | false
    with conj-view φ
... | other _  =  φ
... | conj φ₁ φ₂
    with ⌊ eq ψ (conjunct φ₁ ψ) ⌋
...    | true  = ψ
...    | false
       with ⌊ eq ψ (conjunct φ₂ ψ)⌋
...       | true   = ψ
...       | false  = φ

conjunct-thm
  : ∀ {Γ} {φ}
  → (ψ : Conclusion)
  → Γ ⊢ φ
  → Γ ⊢ conjunct φ ψ

conjunct-thm {Γ} {φ} ψ Γ⊢φ
  with eq φ ψ
... | yes φ≡ψ = subst φ≡ψ Γ⊢φ
... | no _
    with conj-view φ
...    | other _  = Γ⊢φ
...    | conj φ₁ φ₂
       with eq ψ (conjunct φ₁ ψ)
...       | yes p₂  = subst (sym p₂) (conjunct-thm ψ (∧-proj₁ Γ⊢φ))
...       | no _
          with eq ψ (conjunct φ₂ ψ)
...          | yes p₃ = subst (sym p₃) (conjunct-thm ψ (∧-proj₂ Γ⊢φ))
...          | no _   = Γ⊢φ
