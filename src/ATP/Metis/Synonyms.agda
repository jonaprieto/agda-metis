------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Type synonyms.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Synonyms (n : ℕ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Syntax n

------------------------------------------------------------------------------

Premise : Set
Premise = PropFormula

Conclusion : Set
Conclusion = PropFormula
