------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Type synonyms.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Synonyms (n : ℕ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Syntax n

------------------------------------------------------------------------------

Conclusion : Set
Conclusion = PropFormula

Lit : Set
Lit = PropFormula

Premise : Set
Premise = PropFormula
