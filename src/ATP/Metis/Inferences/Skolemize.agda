------------------------------------------------------------------------
-- Agda-Metis Library.
-- Skolemize inference rule.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module ATP.Metis.Inferences.Skolemize (n : ℕ) where

open import Data.Prop.Syntax n
open import Function using (_$_)
