------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Clausify inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Clausify ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Function using ( _$_; id )

------------------------------------------------------------------------------

clausify : Prop → Prop → Prop
clausify φ φ′ = φ′

postulate
  atp-clausify
    : ∀ {Γ} {φ}
    → (φ′ : Prop)
    → Γ ⊢ φ
    → Γ ⊢ clausify φ φ′
