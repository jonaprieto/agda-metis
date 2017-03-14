------------------------------------------------------------------------
-- Agda-Metis Library.
--
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module ATP.Metis (n : ℕ) where

open import Data.Prop.Syntax n

open import ATP.Metis.Inferences n public

$false : Prop
$false = ⊥
