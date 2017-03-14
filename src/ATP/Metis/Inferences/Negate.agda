------------------------------------------------------------------------
-- Agda-Metis Library.
-- Negate inference rule.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module ATP.Metis.Inferences.Negate (n : ℕ) where

open import Data.Prop.Syntax n

-- Negate inference.

atp-neg : Prop → Prop
atp-neg φ = ¬ φ
