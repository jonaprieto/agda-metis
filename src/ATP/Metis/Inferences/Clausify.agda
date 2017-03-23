------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Clausify inference rule.
------------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module ATP.Metis.Inferences.Clausify (n : ℕ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Function using (_$_ ; id)

------------------------------------------------------------------------------

clausify : Prop → Prop
clausify = id

atp-clausify : ∀ {Γ} {φ} → Γ ⊢ φ → Γ ⊢ clausify φ
atp-clausify = id
