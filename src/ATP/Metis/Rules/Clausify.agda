------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Clausify inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Clausify ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Dec n
open import Data.PropFormula.Properties n
open import Data.PropFormula.Syntax n
open import Data.PropFormula.NormalForms n using ( cnf; thm-cnf )
open import Data.Bool               using ( true; false )

open import ATP.Metis.Rules.Reordering n
  using ( reorder-∧∨; thm-reorder-∧∨ )
open import Function using ( _$_; id )

------------------------------------------------------------------------------

clausify : PropFormula → PropFormula → PropFormula
clausify φ ψ
  with ⌊ eq φ ψ ⌋
...  | true  = ψ
...  | false = reorder-∧∨ (cnf φ) ψ

thm-clausify
    : ∀ {Γ} {φ}
    → (ψ : PropFormula)
    → Γ ⊢ φ
    → Γ ⊢ clausify φ ψ
atp-clausify = thm-clausify

thm-clausify {Γ} {φ} ψ Γ⊢φ
  with eq φ ψ
...  | yes φ≡ψ = subst φ≡ψ Γ⊢φ
...  | no  _   = thm-reorder-∧∨ (thm-cnf Γ⊢φ) ψ

