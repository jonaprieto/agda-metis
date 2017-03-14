------------------------------------------------------------------------
-- Agda-Metis Library.
-- Specialize inference rule.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module ATP.Metis.Inferences.Specialize (n : ℕ) where

open import Data.Prop.Syntax n
open import Function using (_$_)