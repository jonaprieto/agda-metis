------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Rules of inference.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules ( n : ℕ ) where

------------------------------------------------------------------------------

open import ATP.Metis.Rules.Canonicalize  public
open import ATP.Metis.Rules.Clausify      public
open import ATP.Metis.Rules.Conjunct      public
open import ATP.Metis.Rules.Resolve       public
open import ATP.Metis.Rules.Simplify      public
open import ATP.Metis.Rules.Strip         public

------------------------------------------------------------------------------
