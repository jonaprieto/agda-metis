------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Rules of inference.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules ( n : ℕ ) where

------------------------------------------------------------------------------

open import ATP.Metis.Rules.Canonicalize n public
open import ATP.Metis.Rules.Clausify n     public
open import ATP.Metis.Rules.Conjunct n     public
open import ATP.Metis.Rules.Negate n       public
open import ATP.Metis.Rules.Resolve n      public
open import ATP.Metis.Rules.Simplify n     public
open import ATP.Metis.Rules.Skolemize n    public
open import ATP.Metis.Rules.Specialize n   public
open import ATP.Metis.Rules.Strip n        public

------------------------------------------------------------------------------
