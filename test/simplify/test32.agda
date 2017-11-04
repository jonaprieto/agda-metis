---------------------------------------------------------------------
-- To test `simplify` inference rule.
---------------------------------------------------------------------

open import Data.PropFormula 20 public
open import ATP.Metis.Rules.Simplify 20  public
open import Relation.Binary.PropositionalEquality

-- Note: When the symbol `?` appears, it means
--       we can not proved yet.

-- Variables.

p = Var (# 0)
q = Var (# 1)
r = Var (# 2)

p1     = Var (# 3)
q1     = Var (# 4)
a      = Var (# 5)
s      = Var (# 6)
g      = Var (# 7)
k      = Var (# 8)
lit    = Var (# 9)
clause = Var (# 10)

----------------------------------------------------------------------
-- Test Problem : 32
----------------------------------------------------------------------

module Test32 where

  private n0-0 : PropFormula
          n0-0 =  ¬ r ∧ (¬ q ∨ r)

  private n0-1 : PropFormula
          n0-1 =  q

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = refl
