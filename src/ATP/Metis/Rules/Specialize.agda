------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Specialize inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Specialize ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Function using ( _$_; id )

------------------------------------------------------------------------------

specialize : Prop → Prop
specialize = id

atp-specialize : ∀ {Γ} {φ}
               → Γ ⊢ φ
               → Γ ⊢ specialize φ

atp-specialize = id
