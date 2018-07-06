------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Canonicalize inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ; suc; zero )

module ATP.Metis.Rules.Canonicalize { n : ℕ } where

------------------------------------------------------------------------------

open import ATP.Metis.Synonyms
open import ATP.Metis.Rules.Normalization

open import ATP.Metis.Rules.Checking using (_●_; _●⊢_; ↑f_; ↑t; id; id-lem)

open import ATP.Metis.Rules.Reordering
open import ATP.Metis.Rules.Resolve

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

-- Lemma.
canonicalize₀-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : Conclusion)
  → Γ ⊢ canonicalize₀ φ ψ

-- Proof.
canonicalize₀-lem {φ = φ} Γ⊢φ ψ
  with eq φ ψ
...  | yes p₁ = subst p₁ Γ⊢φ
...  | no _
  with eq (cnf ψ) (reorder-∧∨ (cnf φ) (cnf ψ))
...  | yes p₂ =
       from-cnf-lem
         (subst (sym p₂)
         (reorder-∧∨-lem
           (cnf-lem Γ⊢φ)
           (cnf ψ)))
...  | no _   = Γ⊢φ
--------------------------------------------------------------------------- ∎

-- Def.
canonicalize : Premise → Conclusion → PropFormula
canonicalize φ =
  ( canonicalize₀  -- 3. Case cnf ψ ≡ reorder∧∨ (cnf φ) (cnf ψ)
  ● (↑f nnf)       -- 2. Case ψ ≡ nnf φ
  ● (↑f id)        -- 1. Case φ ≡ ψ
  ) φ

-- Theorem.
canonicalize-thm
  : ∀ {Γ} {φ : Premise}
  → (ψ : Conclusion)
  → Γ ⊢ φ
  → Γ ⊢ canonicalize φ ψ

-- Proof.
canonicalize-thm ψ Γ⊢φ =
   (  canonicalize₀-lem
   ●⊢ (↑t nnf-lem)
   ●⊢ ↑t id-lem
   ) Γ⊢φ ψ
--------------------------------------------------------------------------- ∎
