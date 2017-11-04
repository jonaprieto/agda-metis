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
-- Test Problem : 34
----------------------------------------------------------------------

module Test34 where

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ ¬ q ∨ r

  private n0-2 : PropFormula
          n0-2 =  p

  private n0-4 : PropFormula
          n0-4 =  q

  private n0-5 : PropFormula
          n0-5 =  ¬ r

  private n0-6 : PropFormula
          n0-6 =  ⊥

  private out : PropFormula
          out =
            simplify
              (simplify
                (simplify n0-1 n0-2 n0-6) n0-4 n0-6)
              n0-5 n0-6

  private test : ⌊ eq out n0-6 ⌋ ≡ true
          test = refl 
