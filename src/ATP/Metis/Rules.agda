------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Rules of inference.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules ( n : ℕ ) where

------------------------------------------------------------------------------

open import ATP.Metis.Rules.Canonicalize n
  using ( atp-canonicalize ) public
open import ATP.Metis.Rules.Clausify n
  using ( clausify; atp-clausify ) public
open import ATP.Metis.Rules.Conjunct n
  using ( conjunct; atp-conjunct ) public
open import ATP.Metis.Rules.Resolve n
  using ( resolve; atp-resolve ) public
open import ATP.Metis.Rules.Simplify n
  using ( simplify; atp-simplify ) public
open import ATP.Metis.Rules.Strip n
  using ( split; atp-split; strip_to_ ) public

------------------------------------------------------------------------------
