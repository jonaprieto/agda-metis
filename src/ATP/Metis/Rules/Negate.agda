------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Negate inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Negate ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n

------------------------------------------------------------------------------

atp-negate : Prop → Prop
atp-negate φ = ¬ φ
