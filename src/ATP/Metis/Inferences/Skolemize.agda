------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Skolemize inference rule.
------------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module ATP.Metis.Inferences.Skolemize (n : ℕ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Function using (_$_ ; id)

------------------------------------------------------------------------------

skolemize : Prop → Prop
skolemize = id

atp-skolemize : ∀ {Γ} {φ}
              → Γ ⊢ φ
              → Γ ⊢ skolemize φ

atp-skolemize = id
