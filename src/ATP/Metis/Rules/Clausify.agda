------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Clausify inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Clausify ( n : ℕ ) where

------------------------------------------------------------------------------

open import ATP.Metis.Rules.Checking n
open import ATP.Metis.Rules.Normalization n
open import ATP.Metis.Rules.Reordering n
  using ( reorder-∧∨; thm-reorder-∧∨ )

open import Data.PropFormula.Dec n
open import Data.PropFormula.Properties n
open import Data.PropFormula.Syntax n

open import Data.Bool               using ( true; false )

open import Function using ( _$_; id )

------------------------------------------------------------------------------

clausify : PropFormula → PropFormula → PropFormula
clausify φ ψ = nform φ ψ
--   with ⌊ eq φ ψ ⌋
-- ... | true  = ψ
-- ... | false = reorder-∧∨ (cnf-nnf (nnf φ)) ψ

thm-clausify
    : ∀ {Γ} {φ}
    → (ψ : PropFormula)
    → Γ ⊢ φ
    → Γ ⊢ clausify φ ψ

thm-clausify {Γ} {φ} ψ Γ⊢φ = thm-nform Γ⊢φ ψ
--   with eq φ ψ
-- ... | yes p = subst p Γ⊢φ
-- ... | no _  = thm-reorder-∧∨ (thm-cnf-nnf (thm-nnf Γ⊢φ)) ψ
