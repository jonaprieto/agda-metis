------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Clausify inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Clausify ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Dec n
open import Data.Prop.Properties n
open import Data.Prop.Syntax n
open import Data.Prop.NormalForms n using ( cnf; thm-cnf )
open import Data.Bool                        using ( true; false )

open import ATP.Metis.Rules.Reordering n using ( reorder-∧∨; thm-reorder-∧∨ )
open import Function using ( _$_; id )

------------------------------------------------------------------------------

clausify : Prop → Prop → Prop
clausify φ ψ
  with ⌊ eq φ ψ ⌋
...  | true  = ψ
...  | false = reorder-∧∨ (cnf φ) ψ

atp-clausify
    : ∀ {Γ} {φ}
    → (ψ : Prop)
    → Γ ⊢ φ
    → Γ ⊢ clausify φ ψ

atp-clausify {Γ} {φ} ψ Γ⊢φ
  with eq φ ψ
...  | yes φ≡ψ = subst φ≡ψ Γ⊢φ
...  | no  _   = thm-reorder-∧∨ (thm-cnf Γ⊢φ) ψ
