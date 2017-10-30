------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Clausify inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Clausify ( n : ℕ ) where

------------------------------------------------------------------------------

open import ATP.Metis.Rules.Normalization n
open import ATP.Metis.Rules.Reordering n using ( reorder-∧∨; reorder-∧∨-lem )
open import ATP.Metis.Synonyms n

open import Data.PropFormula.Dec n
open import Data.PropFormula.Properties n
open import Data.PropFormula.Syntax n

open import Data.Bool using ( true; false )

------------------------------------------------------------------------------

clausify : Premise → Conclusion → PropFormula
clausify φ ψ
   with ⌊ eq φ ψ ⌋
... | true  = ψ
... | false = reorder-∧∨ (cnf φ) ψ

clausify-thm
    : ∀ {Γ} {φ}
    → (ψ : Conclusion)
    → Γ ⊢ φ
    → Γ ⊢ clausify φ ψ

clausify-thm {_} {φ} ψ Γ⊢φ
   with eq φ ψ
... | yes φ≡ψ = subst φ≡ψ Γ⊢φ
... | no _    = reorder-∧∨-lem (cnf-lem Γ⊢φ) ψ
