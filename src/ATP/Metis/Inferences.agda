------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Rules of inference.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Inferences ( n : ℕ ) where

------------------------------------------------------------------------------

open import ATP.Metis.Inferences.Canonicalize n public
open import ATP.Metis.Inferences.Clausify n     public
open import ATP.Metis.Inferences.Conjunct n     public
open import ATP.Metis.Inferences.Negate n       public
open import ATP.Metis.Inferences.Resolve n      public
open import ATP.Metis.Inferences.Simplify n     public
open import ATP.Metis.Inferences.Skolemize n    public
open import ATP.Metis.Inferences.Specialize n   public
open import ATP.Metis.Inferences.Strip n        public

------------------------------------------------------------------------------
