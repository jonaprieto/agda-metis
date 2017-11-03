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
-- Test Problem : 21
--------------------------------------------------------------------

n1-0 : PropFormula
n1-0 =  ¬ r ∧ p ∧ (¬ p ∨ ¬ q)

n1-2 : PropFormula
n1-2 =  q ∨ r -- ¬r ∧ ¬ q

n1-4 : PropFormula
n1-4 =  ⊥

out : PropFormula
out = simplify n1-0 n1-2 n1-4

test : ⌊ eq out n1-4 ⌋ ≡ true
test = refl

