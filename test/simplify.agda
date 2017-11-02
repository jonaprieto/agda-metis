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

p1 = Var (# 3)
q1 = Var (# 4)
a = Var (# 5)
s = Var (# 6)
g = Var (# 7)
k = Var (# 8)
lit = Var (# 9)
clause = Var (# 10)
----------------------------------------------------------------------
-- Test Problem : 1
----------------------------------------------------------------------

module Test1 where

  private n0-0 : PropFormula
          n0-0 =  ¬ p

  private n0-1 : PropFormula
          n0-1 =  p

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = refl

----------------------------------------------------------------------
-- Test Problem : 3
----------------------------------------------------------------------

module Test3 where

  private n1-0 : PropFormula
          n1-0 =  ¬ q ∧ p

  private n1-1 : PropFormula
          n1-1 =  q

  private n1-2 : PropFormula
          n1-2 =  p

  private n1-3 : PropFormula
          n1-3 =  ⊥

  private out : PropFormula
          out = simplify (simplify n1-0 n1-1 n1-3) n1-2 n1-3

  private test : ⌊ eq out n1-3 ⌋ ≡ true
          test = refl

----------------------------------------------------------------------
-- Test Problem : 8
----------------------------------------------------------------------

module Test8 where

  private n1-0 : PropFormula
          n1-0 =  ¬ r ∧ p

  private n1-1 : PropFormula
          n1-1 =  r

  private n1-3 : PropFormula
          n1-3 =  p

  private n1-4 : PropFormula
          n1-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n1-0 n1-1 n1-4) n1-3 n1-4

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = refl


----------------------------------------------------------------------
-- Test Problem : 9
----------------------------------------------------------------------

module Test9 where

  private n2-0 : PropFormula
          n2-0 = ¬ q ∧ p ∧ r

  private n2-2 : PropFormula
          n2-2 = q

  private n2-3 : PropFormula
          n2-3 = p

  private n2-4 : PropFormula
          n2-4 = r

  private n2-5 : PropFormula
          n2-5 = ⊥

  private out : PropFormula
          out =
            (simplify
              (simplify (simplify n2-0 n2-2 n2-5) n2-3 n2-5)
                n2-4 n2-5)

  private test : ⌊ eq out n2-5 ⌋ ≡ true
          test = refl

----------------------------------------------------------------------
-- Test Problem : 11
----------------------------------------------------------------------

module Test11 where

  private n1-0 : PropFormula
          n1-0 =  ¬ q ∧ p

  private n1-2 : PropFormula
          n1-2 =  q

  private n1-4 : PropFormula
          n1-4 =  p

  private n1-5 : PropFormula
          n1-5 =  ⊥

  private out : PropFormula
          out = simplify (simplify n1-0 n1-2 n1-5) n1-4 n1-5

  private test : ⌊ eq out n1-5 ⌋ ≡ true
          test = refl

----------------------------------------------------------------------
-- Test Problem : 12
----------------------------------------------------------------------

module Test12 where

  private n2-0 : PropFormula
          n2-0 = ¬ r ∧ p ∧ q

  private n2-2 : PropFormula
          n2-2 = r

  private n2-4 : PropFormula
          n2-4 = p

  private n2-5 : PropFormula
          n2-5 = q

  private n2-6 : PropFormula
          n2-6 = ⊥

  private out : PropFormula
          out =
            simplify
              (simplify
                  (simplify n2-0 n2-2 n2-6)
                   n2-4 n2-6)
                n2-5 n2-6

  private test : ⌊ eq out n2-6 ⌋ ≡ true
          test = refl

----------------------------------------------------------------------
-- Test Problem : 13
----------------------------------------------------------------------

module Test13 where

  private n0-0 : PropFormula
          n0-0 =  ¬ r

  private n0-2 : PropFormula
          n0-2 =  r

  private n0-3 : PropFormula
          n0-3 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-2 n0-3

  private test : ⌊ eq out n0-3 ⌋ ≡ true
          test = refl

----------------------------------------------------------------------
-- Test Problem : 14
----------------------------------------------------------------------

module Test14 where

  private n1-0 : PropFormula
          n1-0 =  ¬ p ∧ r

  private n1-2 : PropFormula
          n1-2 =  p

  private n1-3 : PropFormula
          n1-3 =  r

  private n1-4 : PropFormula
          n1-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n1-0 n1-2 n1-4) n1-3 n1-4

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = refl

----------------------------------------------------------------------
-- Test Problem : 15
----------------------------------------------------------------------

module Test15 where

  private n2-0 : PropFormula
          n2-0 = ¬ q ∧ p ∧ r

  private n2-2 : PropFormula
          n2-2 = q

  private n2-3 : PropFormula
          n2-3 = p

  private n2-4 : PropFormula
          n2-4 = r

  private n2-5 : PropFormula
          n2-5 = ⊥

  private out : PropFormula
          out =
            simplify
              (simplify (simplify n2-0 n2-2 n2-5) n2-3 n2-5)
              n2-4 n2-5

  private test : ⌊ eq out n2-5 ⌋ ≡ true
          test = refl

----------------------------------------------------------------------
-- Test Problem : 16
----------------------------------------------------------------------

module Test16 where

  private n0-0 : PropFormula
          n0-0 =  ¬ p ∧ ¬ q

  private n0-1 : PropFormula
          n0-1 =  p ∨ q

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = refl

----------------------------------------------------------------------
-- Test Problem : 17
----------------------------------------------------------------------

module Test17 where

  private n0-0 : PropFormula
          n0-0 =  ¬ p ∧ ¬ q ∧ ¬ r

  private n0-1 : PropFormula
          n0-1 =  p ∨ q

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = refl

----------------------------------------------------------------------
-- Test Problem : 18
----------------------------------------------------------------------

module Test18 where

  private n0-0 : PropFormula
          n0-0 =  ¬ p ∧ ¬ q ∧ ¬ r

  private n0-1 : PropFormula
          n0-1 =  p ∨ q ∨ r

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = refl

----------------------------------------------------------------------
-- Test Problem : 19
----------------------------------------------------------------------

module Test19 where

  private n0-0 : PropFormula
          n0-0 =  ¬ p ∧ ¬ p1 ∧ ¬ q ∧ ¬ r

  private n0-1 : PropFormula
          n0-1 =  p ∨ p1 ∨ q ∨ r

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = refl

----------------------------------------------------------------------
-- Test Problem : 20
----------------------------------------------------------------------

module Test20 where

  private n0-0 : PropFormula
          n0-0 =  ¬ p ∧ (¬ p ∨ ¬ q)

  private n0-2 : PropFormula
          n0-2 =  p

  private n0-3 : PropFormula
          n0-3 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-2 n0-3

  private test : ⌊ eq out n0-3 ⌋ ≡ true
          test = refl

----------------------------------------------------------------------
-- Test Problem : 21
----------------------------------------------------------------------

module Test21 where

  private n1-0 : PropFormula
          n1-0 =  ¬ r ∧ p ∧ (¬ p ∨ ¬ q)

  private n1-2 : PropFormula
          n1-2 =  q ∨ r

  private n1-3 : PropFormula
          n1-3 =  p

  private n1-4 : PropFormula
          n1-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n1-0 n1-2 n1-4) n1-3 n1-4

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 22
----------------------------------------------------------------------

module Test22 where

  private n0-0 : PropFormula
          n0-0 =  ¬ p ∧ ¬ q

  private n0-2 : PropFormula
          n0-2 =  p ∨ q

  private n0-3 : PropFormula
          n0-3 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-2 n0-3

  private test : ⌊ eq out n0-3 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 23
----------------------------------------------------------------------

module Test23 where

  private n1-0 : PropFormula
          n1-0 =  ¬ p ∧ ¬ r ∧ q

  private n1-2 : PropFormula
          n1-2 =  p ∨ r

  private n1-3 : PropFormula
          n1-3 =  ⊥

  private out : PropFormula
          out = simplify n1-0 n1-2 n1-3

  private test : ⌊ eq out n1-3 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 24
----------------------------------------------------------------------

module Test24 where

  private n0-0 : PropFormula
          n0-0 =  ¬ q ∧ p

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ q

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 25
----------------------------------------------------------------------

module Test25 where

  private n0-2 : PropFormula
          n0-2 =  ¬ p ∨ q

  private n0-3 : PropFormula
          n0-3 =  ¬ q

  private n0-4 : PropFormula
          n0-4 =  ¬ p

  private out : PropFormula
          out = simplify n0-2 n0-3 n0-4

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 26
----------------------------------------------------------------------

module Test26 where

  private n0-3 : PropFormula
          n0-3 =  p ∨ r

  private n0-4 : PropFormula
          n0-4 =  ¬ r

  private n0-5 : PropFormula
          n0-5 =  p

  private out : PropFormula
          out = simplify n0-3 n0-4 n0-5

  private test : ⌊ eq out n0-5 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 27
----------------------------------------------------------------------

module Test27 where

  private n0-0 : PropFormula
          n0-0 =  ¬ q ∧ ¬ r ∧ p

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ q ∨ r

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 28
----------------------------------------------------------------------

module Test28 where

  private n0-3 : PropFormula
          n0-3 =  p ∨ q

  private n0-4 : PropFormula
          n0-4 =  ¬ p

  private n0-5 : PropFormula
          n0-5 =  q

  private out : PropFormula
          out = simplify n0-3 n0-4 n0-5

  private test : ⌊ eq out n0-5 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 29
----------------------------------------------------------------------

module Test29 where

  private n1-0 : PropFormula
          n1-0 =  ¬ q ∧ p ∧ (p ∨ q)

  private n1-2 : PropFormula
          n1-2 =  ¬ p ∨ q

  private n1-3 : PropFormula
          n1-3 =  ⊥

  private out : PropFormula
          out = simplify n1-0 n1-2 n1-3

  private test : ⌊ eq out n1-3 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 30
----------------------------------------------------------------------

module Test30 where

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ q

  private n0-2 : PropFormula
          n0-2 =  p

  private n0-3 : PropFormula
          n0-3 =  ¬ q

  private n0-4 : PropFormula
          n0-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n0-1 n0-2 n0-4) n0-3 n0-4

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 31
----------------------------------------------------------------------

module Test31 where

  private n0-0 : PropFormula
          n0-0 =  ¬ r ∧ p ∧ q

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ ¬ q ∨ r

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

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
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 33
----------------------------------------------------------------------

module Test33 where

  private n0-3 : PropFormula
          n0-3 =  ¬ p ∨ q

  private n0-2 : PropFormula
          n0-2 =  p

  private n0-4 : PropFormula
          n0-4 =  q

  private out : PropFormula
          out = simplify n0-3 n0-2 n0-4

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = {!!}

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
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 35
----------------------------------------------------------------------

module Test35 where

  private n0-0 : PropFormula
          n0-0 =  ¬ q ∧ p

  private n0-2 : PropFormula
          n0-2 =  q

  private n0-3 : PropFormula
          n0-3 =  p

  private n0-4 : PropFormula
          n0-4 =  ⊥

  private out : PropFormula
          out =
            simplify
              (simplify
                (simplify n0-0 n0-2 n0-4) n0-3 n0-4)
              n0-3 n0-4

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 36
----------------------------------------------------------------------

module Test36 where

  private n0-0 : PropFormula
          n0-0 =  ¬ p ∧ q

  private n0-1 : PropFormula
          n0-1 =  ¬ q ∨ p

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 37
----------------------------------------------------------------------

module Test37 where

  private n0-0 : PropFormula
          n0-0 =  ¬ r ∧ p ∧ q

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ ¬ q ∨ r

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 38
----------------------------------------------------------------------

module Test38 where

  private n0-0 : PropFormula
          n0-0 =  ¬ q ∧ p

  private n0-2 : PropFormula
          n0-2 =  ¬ p ∨ q

  private n0-3 : PropFormula
          n0-3 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-2 n0-3

  private test : ⌊ eq out n0-3 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 39
----------------------------------------------------------------------

module Test39 where

  private n1-0 : PropFormula
          n1-0 =  ¬ r ∧ p ∧ q

  private n1-2 : PropFormula
          n1-2 =  ¬ p ∨ r

  private n1-3 : PropFormula
          n1-3 =  ⊥

  private out : PropFormula
          out = simplify n1-0 n1-2 n1-3

  private test : ⌊ eq out n1-3 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 40
----------------------------------------------------------------------

module Test40 where

  private n0-0 : PropFormula
          n0-0 =  ¬ p1

  private n0-2 : PropFormula
          n0-2 =  p1

  private n0-3 : PropFormula
          n0-3 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-2 n0-3

  private test : ⌊ eq out n0-3 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 41
----------------------------------------------------------------------

module Test41 where

  private n0-0 : PropFormula
          n0-0 =  ¬ p

  private n0-1 : PropFormula
          n0-1 =  p

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 42
----------------------------------------------------------------------

module Test42 where

  private n0-0 : PropFormula
          n0-0 =  p ∧ q

  private n0-1 : PropFormula
          n0-1 =  ¬ p

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 43
----------------------------------------------------------------------

module Test43 where

  private n0-0 : PropFormula
          n0-0 =  p

  private n0-1 : PropFormula
          n0-1 =  ¬ p

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 44
----------------------------------------------------------------------

module Test44 where

  private n0-0 : PropFormula
          n0-0 =  q

  private n0-2 : PropFormula
          n0-2 =  ¬ q

  private n0-3 : PropFormula
          n0-3 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-2 n0-3

  private test : ⌊ eq out n0-3 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 45
----------------------------------------------------------------------

module Test45 where

  private n0-0 : PropFormula
          n0-0 =  p ∧ q

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ ¬ q

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 46
----------------------------------------------------------------------

module Test46 where

  private n0-0 : PropFormula
          n0-0 =  ¬ q ∧ p

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ q

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 48
----------------------------------------------------------------------

module Test48 where

  private n1-0 : PropFormula
          n1-0 =  ¬ p ∧ q

  private n1-2 : PropFormula
          n1-2 =  ¬ p

  private n1-3 : PropFormula
          n1-3 =  ¬ q

  private n1-4 : PropFormula
          n1-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n1-0 n1-2 n1-4) n1-3 n1-4

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 49
----------------------------------------------------------------------

module Test49 where

  private n0-0 : PropFormula
          n0-0 =  p ∧ q

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ ¬ q

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 50
----------------------------------------------------------------------

module Test50 where

  private n0-0 : PropFormula
          n0-0 =  ¬ q ∧ p

  private n0-1 : PropFormula
          n0-1 =  ¬ p

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 51
----------------------------------------------------------------------

module Test51 where

  private n0-0 : PropFormula
          n0-0 =  ¬ p ∧ ¬ q

  private n0-1 : PropFormula
          n0-1 =  p ∨ q

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 52
----------------------------------------------------------------------

module Test52 where

  private n0-0 : PropFormula
          n0-0 =  ¬ q ∧ p

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ q

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 54
----------------------------------------------------------------------

module Test54 where

  private n0-0 : PropFormula
          n0-0 =  ¬ p ∧ ¬ q

  private n0-1 : PropFormula
          n0-1 =  p ∨ q

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 55
----------------------------------------------------------------------

module Test55 where

  private n0-0 : PropFormula
          n0-0 =  ¬ p

  private n0-2 : PropFormula
          n0-2 =  p

  private n0-3 : PropFormula
          n0-3 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-2 n0-3

  private test : ⌊ eq out n0-3 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 56
----------------------------------------------------------------------

module Test56 where

  private n1-0 : PropFormula
          n1-0 =  ¬ q ∧ p

  private n1-2 : PropFormula
          n1-2 =  q

  private n1-3 : PropFormula
          n1-3 =  p

  private n1-4 : PropFormula
          n1-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n1-0 n1-2 n1-4) n1-3 n1-4

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 57
----------------------------------------------------------------------

module Test57 where

  private n0-0 : PropFormula
          n0-0 =  p ∧ q

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ ¬ q

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 58
----------------------------------------------------------------------

module Test58 where

  private n0-0 : PropFormula
          n0-0 =  ¬ p

  private n0-2 : PropFormula
          n0-2 =  p

  private n0-3 : PropFormula
          n0-3 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-2 n0-3

  private test : ⌊ eq out n0-3 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 60
----------------------------------------------------------------------

module Test60 where

  private n1-0 : PropFormula
          n1-0 =  ¬ p ∧ q

  private n1-2 : PropFormula
          n1-2 =  ¬ p

  private n1-3 : PropFormula
          n1-3 =  ¬ q

  private n1-4 : PropFormula
          n1-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n1-0 n1-2 n1-4) n1-3 n1-4

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 61
----------------------------------------------------------------------

module Test61 where

  private n0-0 : PropFormula
          n0-0 =  ¬ q ∧ ¬ r ∧ p

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ q ∨ r

  private n0-2 : PropFormula
          n0-2 =  ⊥

  private out : PropFormula
          out = simplify n0-0 n0-1 n0-2

  private test : ⌊ eq out n0-2 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 62
----------------------------------------------------------------------

module Test62 where

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ ¬ q

  private n0-2 : PropFormula
          n0-2 =  p

  private n0-3 : PropFormula
          n0-3 =  q

  private n0-4 : PropFormula
          n0-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n0-1 n0-2 n0-4) n0-3 n0-4

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 63
----------------------------------------------------------------------

module Test63 where

  private n1-1 : PropFormula
          n1-1 =  ¬ p ∨ ¬ q

  private n1-2 : PropFormula
          n1-2 =  p

  private n1-3 : PropFormula
          n1-3 =  q

  private n1-4 : PropFormula
          n1-4 =  ⊥

  private out : PropFormula
          out = simplify n1-1 n1-2 n1-3

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 67
----------------------------------------------------------------------

module Test67 where

  private n1-0 : PropFormula
          n1-0 =  ¬ q ∧ p

  private n1-2 : PropFormula
          n1-2 =  q

  private n1-3 : PropFormula
          n1-3 =  p

  private n1-4 : PropFormula
          n1-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n1-0 n1-2 n1-4) n1-3 n1-4

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 68
----------------------------------------------------------------------

module Test68 where

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ q

  private n0-2 : PropFormula
          n0-2 =  p

  private n0-3 : PropFormula
          n0-3 =  ¬ q

  private n0-4 : PropFormula
          n0-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n0-1 n0-2 n0-4) n0-3 n0-4

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 69
----------------------------------------------------------------------

module Test69 where

  private n1-1 : PropFormula
          n1-1 =  ¬ p ∨ q

  private n1-2 : PropFormula
          n1-2 =  p

  private n1-3 : PropFormula
          n1-3 =  ¬ q

  private n1-4 : PropFormula
          n1-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n1-1 n1-2 n1-4) n1-3 n1-4

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 70
----------------------------------------------------------------------

module Test70 where

  private n0-1 : PropFormula
          n0-1 =  p ∨ q

  private n0-2 : PropFormula
          n0-2 =  ¬ p

  private n0-3 : PropFormula
          n0-3 =  ¬ q

  private n0-4 : PropFormula
          n0-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n0-1 n0-2 n0-4) n0-3 n0-4

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 71
----------------------------------------------------------------------

module Test71 where

  private n1-1 : PropFormula
          n1-1 =  p ∨ q

  private n1-2 : PropFormula
          n1-2 =  ¬ p

  private n1-3 : PropFormula
          n1-3 =  ¬ q

  private n1-4 : PropFormula
          n1-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n1-1 n1-2 n1-4) n1-3 n1-4

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 72
----------------------------------------------------------------------

module Test72 where

  private n0-1 : PropFormula
          n0-1 =  p ∨ r ∨ (¬ p ∧ ¬ q)

  private n0-2 : PropFormula
          n0-2 =  ¬ p

  private n0-3 : PropFormula
          n0-3 =  ¬ r

  private n0-4 : PropFormula
          n0-4 =  q

  private n0-5 : PropFormula
          n0-5 =  ⊥

  private out : PropFormula
          out =
            simplify
              (simplify
                (simplify
                  (simplify n0-1 n0-2 n0-5)
                  n0-3 n0-5)
                n0-2 n0-5)
              n0-4 n0-5

  private test : ⌊ eq out n0-5 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 73
----------------------------------------------------------------------

module Test73 where

  private n0-1 : PropFormula
          n0-1 =  p ∨ (¬ q ∧ p)

  private n0-2 : PropFormula
          n0-2 =  ¬ p

  private n0-3 : PropFormula
          n0-3 =  ⊥

  private out : PropFormula
          out = simplify (simplify n0-1 n0-2 n0-3) n0-2 n0-3

  private test : ⌊ eq out n0-3 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 74
----------------------------------------------------------------------

module Test74 where

  private n0-2 : PropFormula
          n0-2 =  ¬ p ∨ q

  private n0-3 : PropFormula
          n0-3 =  ¬ q

  private n0-4 : PropFormula
          n0-4 =  ¬ p

  private out : PropFormula
          out = simplify n0-2 n0-3 n0-4

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 75
----------------------------------------------------------------------

module Test75 where

  private n0-1 : PropFormula
          n0-1 =  p ∨ q

  private n0-4 : PropFormula
          n0-4 =  ¬ p

  private n0-3 : PropFormula
          n0-3 =  ¬ q

  private n0-5 : PropFormula
          n0-5 =  ⊥

  private out : PropFormula
          out = simplify (simplify n0-1 n0-4 n0-5) n0-3 n0-5

  private test : ⌊ eq out n0-5 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 76
----------------------------------------------------------------------

module Test76 where

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ (q ∧ r)

  private n0-2 : PropFormula
          n0-2 =  p

  private n0-3 : PropFormula
          n0-3 =  ¬ q

  private n0-4 : PropFormula
          n0-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n0-1 n0-2 n0-4) n0-3 n0-4

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 77
----------------------------------------------------------------------

module Test77 where

  private n1-2 : PropFormula
          n1-2 =  ¬ q ∨ r

  private n1-3 : PropFormula
          n1-3 =  q

  private n1-4 : PropFormula
          n1-4 =  r

  private out : PropFormula
          out = simplify n1-2 n1-3 n1-4

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 78
----------------------------------------------------------------------
module Test78 where

  private n1-1 : PropFormula
          n1-1 =  ¬ r ∨ (p ∧ q)

  private n1-4 : PropFormula
          n1-4 =  r

  private n1-5 : PropFormula
          n1-5 =  ¬ p

  private n1-3 : PropFormula
          n1-3 =  q

  private n1-6 : PropFormula
          n1-6 =  ⊥

  private out : PropFormula
          out =
            simplify
              (simplify
                (simplify n1-1 n1-4 n1-6)
                n1-5 n1-6)
              n1-3 n1-6

  private test : ⌊ eq out n1-6 ⌋ ≡ true
          test = {!!}

{- -- Biconditional related problems.

----------------------------------------------------------------------
-- Test Problem : 79
----------------------------------------------------------------------

module Test79 where

  private n0-1 : PropFormula
          n0-1 =  ¬ p ⇔ (¬ q ⇔ r)

  private n0-2 : PropFormula
          n0-2 =  p

  private n0-3 : PropFormula
          n0-3 =  q

  private n0-4 : PropFormula
          n0-4 =  ¬ r

  private n0-5 : PropFormula
          n0-5 =  ⊥

  private out : PropFormula
          out = simplify n0-1 n0-2 n0-3 n0-4

  private test : ⌊ eq out n0-5 ⌋ ≡ true
          test = ?

----------------------------------------------------------------------
-- Test Problem : 80
----------------------------------------------------------------------

module Test80 where

  private n1-1 : PropFormula
          n1-1 =  ¬ p ⇔ (¬ q ⇔ r)

  private n1-2 : PropFormula
          n1-2 =  p

  private n1-3 : PropFormula
          n1-3 =  ¬ q

  private n1-4 : PropFormula
          n1-4 =  r

  private n1-5 : PropFormula
          n1-5 =  ⊥

  private out : PropFormula
          out = simplify n1-1 n1-2 n1-3 n1-4

  private test : ⌊ eq out n1-5 ⌋ ≡ true
          test = ?

----------------------------------------------------------------------
-- Test Problem : 81
----------------------------------------------------------------------

module Test81 where

  private n2-1 : PropFormula
          n2-1 = ¬ p ⇔ (¬ q ⇔ r)

  private n2-2 : PropFormula
          n2-2 = ¬ q ⇔ ¬ r

  private n2-3 : PropFormula
          n2-3 = ¬ p

  private n2-4 : PropFormula
          n2-4 = ⊥

  private out : PropFormula
          out = simplify n2-1 n2-2 n2-3

  private test : ⌊ eq out n2-4 ⌋ ≡ true
          test = ?

----------------------------------------------------------------------
-- Test Problem : 82
----------------------------------------------------------------------

module Test82 where

  private n3-1 : PropFormula
          n3-1 = ¬ p ⇔ (¬ q ⇔ r)

  private n3-2 : PropFormula
          n3-2 = ¬ p ⇔ ¬ q

  private n3-3 : PropFormula
          n3-3 = ¬ r

  private n3-4 : PropFormula
          n3-4 = ⊥

  private out : PropFormula
          out = simplify n3-1 n3-2 n3-3

  private test : ⌊ eq out n3-4 ⌋ ≡ true
          test = ?

----------------------------------------------------------------------
-- Test Problem : 83
----------------------------------------------------------------------

module Test83 where

  private n4-1 : PropFormula
          n4-1 = ¬ p ⇔ (¬ q ⇔ r)

  private n4-2 : PropFormula
          n4-2 = p

  private n4-3 : PropFormula
          n4-3 = ¬ q

  private n4-4 : PropFormula
          n4-4 = r

  private n4-5 : PropFormula
          n4-5 = ⊥

  private out : PropFormula
          out = simplify n4-1 n4-2 n4-3 n4-4

  private test : ⌊ eq out n4-5 ⌋ ≡ true
          test = ?

----------------------------------------------------------------------
-- Test Problem : 84
----------------------------------------------------------------------

module Test84 where

  private n5-1 : PropFormula
          n5-1 = ¬ p ⇔ (¬ q ⇔ r)

  private n5-2 : PropFormula
          n5-2 = ¬ p

  private n5-3 : PropFormula
          n5-3 = q

  private n5-4 : PropFormula
          n5-4 = r

  private n5-5 : PropFormula
          n5-5 = ⊥

  private out : PropFormula
          out = simplify n5-1 n5-2 n5-3 n5-4

  private test : ⌊ eq out n5-5 ⌋ ≡ true
          test = ?

-}

----------------------------------------------------------------------
-- Test Problem : 85
----------------------------------------------------------------------

module Test85 where

  private n0-1 : PropFormula
          n0-1 =  p ∨ (q ∧ r)

  private n0-2 : PropFormula
          n0-2 =  ¬ p

  private n0-3 : PropFormula
          n0-3 =  ¬ q

  private n0-4 : PropFormula
          n0-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n0-1 n0-2 n0-4) n0-3 n0-4

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 86
----------------------------------------------------------------------

module Test86 where

  private n1-3 : PropFormula
          n1-3 =  p ∨ q

  private n1-2 : PropFormula
          n1-2 =  ¬ p

  private n1-4 : PropFormula
          n1-4 =  q

  private out : PropFormula
          out = simplify n1-3 n1-2 n1-4

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 87
----------------------------------------------------------------------

module Test87 where

  private n1-1 : PropFormula
          n1-1 =  p ∨ (q ∧ r)

  private n1-2 : PropFormula
          n1-2 =  ¬ p

  private n1-4 : PropFormula
          n1-4 =  q

  private n1-5 : PropFormula
          n1-5 =  ¬ r

  private n1-6 : PropFormula
          n1-6 =  ⊥

  private out : PropFormula
          out =
            simplify
              (simplify
                (simplify  n1-1 n1-2 n1-6)
                n1-4 n1-6)
               n1-5 n1-6

  private test : ⌊ eq out n1-6 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 88
----------------------------------------------------------------------

module Test88 where

  private n2-1 : PropFormula
          n2-1 = p ∨ q

  private n2-2 : PropFormula
          n2-2 = ¬ p

  private n2-3 : PropFormula
          n2-3 = ¬ q

  private n2-4 : PropFormula
          n2-4 = ⊥

  private out : PropFormula
          out = simplify (simplify n2-1 n2-2 n2-4) n2-3 n2-4

  private test : ⌊ eq out n2-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 89
----------------------------------------------------------------------

module Test89 where

  private n3-1 : PropFormula
          n3-1 = p ∨ r

  private n3-2 : PropFormula
          n3-2 = ¬ p

  private n3-3 : PropFormula
          n3-3 = ¬ r

  private n3-4 : PropFormula
          n3-4 = ⊥

  private out : PropFormula
          out = simplify (simplify n3-1 n3-2 n3-4) n3-3 n3-4

  private test : ⌊ eq out n3-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 90
----------------------------------------------------------------------

module Test90 where

  private n0-1 : PropFormula
          n0-1 =  ¬ p ⇔ ¬ q

  private n0-2 : PropFormula
          n0-2 =  p

  private n0-3 : PropFormula
          n0-3 =  ¬ q

  private n0-4 : PropFormula
          n0-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n0-1 n0-2 n0-4) n0-3 n0-4

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 91
----------------------------------------------------------------------

module Test91 where

  private n1-1 : PropFormula
          n1-1 =  ¬ p ⇔ ¬ q

  private n1-2 : PropFormula
          n1-2 =  ¬ p

  private n1-3 : PropFormula
          n1-3 =  q

  private n1-4 : PropFormula
          n1-4 =  ⊥

  private out : PropFormula
          out = simplify n1-1 n1-2 n1-3

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 92
----------------------------------------------------------------------

module Test92 where

  private n2-1 : PropFormula
          n2-1 = ¬ p ∨ q

  private n2-2 : PropFormula
          n2-2 = p

  private n2-3 : PropFormula
          n2-3 = ¬ q

  private n2-4 : PropFormula
          n2-4 = ⊥

  private out : PropFormula
          out = simplify (simplify n2-1 n2-2 n2-4) n2-3 n2-4

  private test : ⌊ eq out n2-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 93
----------------------------------------------------------------------

module Test93 where

  private n3-1 : PropFormula
          n3-1 = ¬ q ∨ p

  private n3-2 : PropFormula
          n3-2 = q

  private n3-3 : PropFormula
          n3-3 = ¬ p

  private n3-4 : PropFormula
          n3-4 = ⊥

  private out : PropFormula
          out = simplify (simplify n3-1 n3-2 n3-4) n3-3 n3-4

  private test : ⌊ eq out n3-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 94
----------------------------------------------------------------------

module Test94 where

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ q

  private n0-2 : PropFormula
          n0-2 =  p

  private n0-3 : PropFormula
          n0-3 =  ¬ q

  private n0-4 : PropFormula
          n0-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n0-1 n0-2 n0-4) n0-3 n0-4

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 95
----------------------------------------------------------------------

module Test95 where

  private n1-1 : PropFormula
          n1-1 =  ¬ p ∨ q

  private n1-2 : PropFormula
          n1-2 =  p

  private n1-3 : PropFormula
          n1-3 =  ¬ q

  private n1-4 : PropFormula
          n1-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n1-1 n1-2 n1-4) n1-3 n1-4

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 96
----------------------------------------------------------------------

module Test96 where

  private n0-1 : PropFormula
          n0-1 =  ¬ p ∨ s ∨ (¬ r ∧ q)

  private n0-2 : PropFormula
          n0-2 =  p

  private n0-3 : PropFormula
          n0-3 =  ¬ s

  private n0-4 : PropFormula
          n0-4 =  ¬ q

  private n0-5 : PropFormula
          n0-5 =  ⊥

  private out : PropFormula
          out =
            simplify
              (simplify
                (simplify n0-1 n0-2 n0-5)
                n0-3 n0-5)
              n0-4 n0-5

  private test : ⌊ eq out n0-5 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 97
----------------------------------------------------------------------

module Test97 where

  private n1-5 : PropFormula
          n1-5 =  ¬ p ∨ q ∨ s

  private n1-2 : PropFormula
          n1-2 =  p

  private n1-3 : PropFormula
          n1-3 =  ¬ s

  private n1-6 : PropFormula
          n1-6 =  q

  private out : PropFormula
          out = simplify (simplify n1-5 n1-2 n1-6) n1-3 n1-6

  private test : ⌊ eq out n1-6 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 98
----------------------------------------------------------------------

module Test98 where

  private n1-1 : PropFormula
          n1-1 =  ¬ p ∨ s ∨ (¬ r ∧ q)

  private n1-2 : PropFormula
          n1-2 =  p

  private n1-3 : PropFormula
          n1-3 =  ¬ s

  private n1-4 : PropFormula
          n1-4 =  r

  private n1-6 : PropFormula
          n1-6 =  q

  private n1-7 : PropFormula
          n1-7 =  ⊥

  private out : PropFormula
          out =
            simplify
              (simplify
                (simplify
                    (simplify n1-1 n1-2 n1-7)
                    n1-3 n1-7)
                n1-4 n1-7)
              n1-6 n1-7

  private test : ⌊ eq out n1-7 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 99
----------------------------------------------------------------------

module Test99 where

  private n2-2 : PropFormula
          n2-2 = ¬ p ∨ q ∨ s

  private n2-3 : PropFormula
          n2-3 = p

  private n2-4 : PropFormula
          n2-4 = ¬ s

  private n2-5 : PropFormula
          n2-5 = q

  private out : PropFormula
          out = simplify (simplify n2-2 n2-3 n2-5) n2-4 n2-5

  private test : ⌊ eq out n2-5 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 100
----------------------------------------------------------------------

module Test100 where

  private n2-6 : PropFormula
          n2-6 = ¬ p ∨ ¬ r ∨ s

  private n2-3 : PropFormula
          n2-3 = p

  private n2-4 : PropFormula
          n2-4 = ¬ s

  private n2-7 : PropFormula
          n2-7 = ¬ r

  private out : PropFormula
          out = simplify (simplify n2-6 n2-3 n2-7) n2-4 n2-7

  private test : ⌊ eq out n2-7 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 101
----------------------------------------------------------------------

module Test101 where

  private n0-2 : PropFormula
          n0-2 =  ¬ g ∨ q

  private n0-3 : PropFormula
          n0-3 =  ¬ q

  private n0-4 : PropFormula
          n0-4 =  ¬ g

  private out : PropFormula
          out = simplify n0-2 n0-3 n0-4

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 102
----------------------------------------------------------------------

module Test102 where

  private n0-1 : PropFormula
          n0-1 =  g ∨ (¬ a ∧ k)

  private n0-4 : PropFormula
          n0-4 =  ¬ g

  private n0-5 : PropFormula
          n0-5 =  ¬ k

  private n0-6 : PropFormula
          n0-6 =  ⊥

  private out : PropFormula
          out = simplify (simplify n0-1 n0-4 n0-6) n0-5 n0-6

  private test : ⌊ eq out n0-6 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 103
----------------------------------------------------------------------

module Test103 where

  private n0-3 : PropFormula
          n0-3 =  ¬ q ∨ p

  private n0-2 : PropFormula
          n0-2 =  ¬ p

  private n0-4 : PropFormula
          n0-4 =  ¬ q

  private out : PropFormula
          out = simplify n0-3 n0-2 n0-4

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 104
----------------------------------------------------------------------
module Test104 where

  private n0-1 : PropFormula
          n0-1 =  p ∨ q

  private n0-2 : PropFormula
          n0-2 =  ¬ p

  private n0-4 : PropFormula
          n0-4 =  ¬ q

  private n0-5 : PropFormula
          n0-5 =  ⊥

  private out : PropFormula
          out = simplify (simplify n0-1 n0-2 n0-5) n0-4 n0-5

  private test : ⌊ eq out n0-5 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 105
----------------------------------------------------------------------

module Test105 where

  private n1-1 : PropFormula
          n1-1 =  ¬ p ∨ r

  private n1-2 : PropFormula
          n1-2 =  p

  private n1-3 : PropFormula
          n1-3 =  ¬ r

  private n1-4 : PropFormula
          n1-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n1-1 n1-2 n1-4) n1-3 n1-4

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = {!!}

{-
----------------------------------------------------------------------
-- Test Problem : 106
----------------------------------------------------------------------

module Test106 where

  private n0-1 : PropFormula
          n0-1 =  ¬ p ⇔ (¬ q ⇔ r)

  private n0-2 : PropFormula
          n0-2 =  p

  private n0-3 : PropFormula
          n0-3 =  q

  private n0-4 : PropFormula
          n0-4 =  ¬ r

  private n0-5 : PropFormula
          n0-5 =  ⊥

  private out : PropFormula
          out = simplify n0-1 n0-2 n0-3 n0-4

  private test : ⌊ eq out n0-5 ⌋ ≡ true
          test = ?

----------------------------------------------------------------------
-- Test Problem : 107
----------------------------------------------------------------------

module Test107 where

  private n1-1 : PropFormula
          n1-1 =  ¬ p ⇔ (¬ q ⇔ r)

  private n1-2 : PropFormula
          n1-2 =  p

  private n1-3 : PropFormula
          n1-3 =  ¬ q

  private n1-4 : PropFormula
          n1-4 =  r

  private n1-5 : PropFormula
          n1-5 =  ⊥

  private out : PropFormula
          out = simplify n1-1 n1-2 n1-3 n1-4

  private test : ⌊ eq out n1-5 ⌋ ≡ true
          test = ?

----------------------------------------------------------------------
-- Test Problem : 108
----------------------------------------------------------------------

module Test108 where

  private n2-1 : PropFormula
          n2-1 = ¬ p ⇔ (¬ q ⇔ r)

  private n2-2 : PropFormula
          n2-2 = ¬ q ⇔ ¬ r

  private n2-3 : PropFormula
          n2-3 = ¬ p

  private n2-4 : PropFormula
          n2-4 = ⊥

  private out : PropFormula
          out = simplify n2-1 n2-2 n2-3

  private test : ⌊ eq out n2-4 ⌋ ≡ true
          test = ?

----------------------------------------------------------------------
-- Test Problem : 109
----------------------------------------------------------------------

module Test109 where

  private n3-2 : PropFormula
          n3-2 = ¬ p ⇔ (¬ q ⇔ r)

  private n3-3 : PropFormula
          n3-3 = r

  private n3-4 : PropFormula
          n3-4 = ¬ p ⇔ ¬ q

  private out : PropFormula
          out = simplify n3-2 n3-3

  private test : ⌊ eq out n3-4 ⌋ ≡ true
          test = ?

----------------------------------------------------------------------
-- Test Problem : 110
----------------------------------------------------------------------

module Test110 where

  private n3-1 : PropFormula
          n3-1 = ¬ p ⇔ q

  private n3-4 : PropFormula
          n3-4 = ¬ p ⇔ ¬ q

  private n3-5 : PropFormula
          n3-5 = ⊥

  private out : PropFormula
          out = simplify n3-1 n3-4

  private test : ⌊ eq out n3-5 ⌋ ≡ true
          test = ?

----------------------------------------------------------------------
-- Test Problem : 111
----------------------------------------------------------------------

module Test111 where

  private n4-1 : PropFormula
          n4-1 = ¬ p ⇔ (¬ q ⇔ r)

  private n4-2 : PropFormula
          n4-2 = p

  private n4-3 : PropFormula
          n4-3 = q

  private n4-4 : PropFormula
          n4-4 = ¬ r

  private n4-5 : PropFormula
          n4-5 = ⊥

  private out : PropFormula
          out = simplify n4-1 n4-2 n4-3 n4-4

  private test : ⌊ eq out n4-5 ⌋ ≡ true
          test = ?

----------------------------------------------------------------------
-- Test Problem : 112
----------------------------------------------------------------------

module Test112 where

  private n5-1 : PropFormula
          n5-1 = ¬ p ⇔ (¬ q ⇔ r)

  private n5-2 : PropFormula
          n5-2 = ¬ p

  private n5-3 : PropFormula
          n5-3 = ¬ q

  private n5-4 : PropFormula
          n5-4 = ¬ r

  private n5-5 : PropFormula
          n5-5 = ⊥

  private out : PropFormula
          out = simplify n5-1 n5-2 n5-3 n5-4

  private test : ⌊ eq out n5-5 ⌋ ≡ true
          test = ?

-}

----------------------------------------------------------------------
-- Test Problem : 113
----------------------------------------------------------------------

module Test113 where

  private n0-3 : PropFormula
          n0-3 =  ¬ lit ∨ clause

  private n0-2 : PropFormula
          n0-2 =  ¬ clause

  private n0-4 : PropFormula
          n0-4 =  ¬ lit

  private out : PropFormula
          out = simplify n0-3 n0-2 n0-4

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = {!!}

----------------------------------------------------------------------
-- Test Problem : 114
----------------------------------------------------------------------

module Test114 where

  private n0-1 : PropFormula
          n0-1 =  clause ∨ lit

  private n0-2 : PropFormula
          n0-2 =  ¬ clause

  private n0-4 : PropFormula
          n0-4 =  ¬ lit

  private n0-5 : PropFormula
          n0-5 =  ⊥

  private out : PropFormula
          out = simplify (simplify n0-1 n0-2 n0-5) n0-4 n0-5

  private test : ⌊ eq out n0-5 ⌋ ≡ true
          test = {!!}

{-
----------------------------------------------------------------------
-- Test Problem : 115
----------------------------------------------------------------------

module Test115 where

  private n0-1 : PropFormula
          n0-1 =  ¬ p ⇔ q

  private n0-2 : PropFormula
          n0-2 =  p

  private n0-3 : PropFormula
          n0-3 =  q

  private n0-4 : PropFormula
          n0-4 =  ⊥

  private out : PropFormula
          out = simplify n0-1 n0-2 n0-3

  private test : ⌊ eq out n0-4 ⌋ ≡ true
          test = ?

-}

----------------------------------------------------------------------
-- Test Problem : 116
----------------------------------------------------------------------

module Test116 where

  private n1-1 : PropFormula
          n1-1 =  ¬ p ∨ ¬ q

  private n1-2 : PropFormula
          n1-2 =  p

  private n1-3 : PropFormula
          n1-3 =  q

  private n1-4 : PropFormula
          n1-4 =  ⊥

  private out : PropFormula
          out = simplify (simplify n1-1 n1-2 n1-4) n1-3 n1-4

  private test : ⌊ eq out n1-4 ⌋ ≡ true
          test = {!!}

