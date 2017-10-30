------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Canonicalize inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ; suc; zero )

module ATP.Metis.Rules.Canonicalize ( n : ℕ ) where

------------------------------------------------------------------------------

open import ATP.Metis.Synonyms n
open import ATP.Metis.Rules.Normalization n

open import ATP.Metis.Rules.Checking n using (_●_; _●⊢_; ↑f_; ↑t; id; thm-id)

open import ATP.Metis.Rules.Reordering n
open import ATP.Metis.Rules.Resolve n

open import Data.Bool.Base
  using    ( true; false )
  renaming ( _∨_ to _or_ )

open import Data.PropFormula.Dec n using ( ⌊_⌋ ; yes ; no )
open import Data.PropFormula.Properties n using ( eq ; subst )
open import Data.PropFormula.Syntax n

open import Data.Bool using (Bool; true; false)

open import Function  using ( _$_; _∘_ ; flip )
open import Relation.Binary.PropositionalEquality using ( _≡_; sym )

------------------------------------------------------------------------------

-- Def.
canonicalize₀ : Premise → Conclusion → PropFormula
canonicalize₀ φ ψ
  with ⌊ eq φ ψ ⌋
... | true  = ψ
... | false
    with ⌊ eq (cnf ψ) (reorder-∧∨ (cnf φ) (cnf ψ)) ⌋
...    | true  = ψ
...    | false = φ

postulate
  -- Lemma.
  canonicalize₀-lem
    : ∀ {Γ} {φ}
      → Γ ⊢ φ
      → (ψ : Conclusion)
      → Γ ⊢ canonicalize₀ φ ψ

-- Aux Def.
const : PropFormula → (PropFormula → PropFormula)
const φ = λ x → φ

-- Def.
canonicalize : Premise → Conclusion → PropFormula
canonicalize φ =
  ( canonicalize₀
  ● (↑f nnf)
  ● (↑f id)
  ) φ

postulate
  -- Theorem.
  canonicalize-thm
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → (ψ : PropFormula)
    → Γ ⊢ canonicalize φ ψ
