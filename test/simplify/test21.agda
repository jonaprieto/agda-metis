---------------------------------------------------------------------
-- To test `simplify` inference rule.
---------------------------------------------------------------------

open import ATP.Metis.Synonyms 20
open import Data.PropFormula 20 public
open import Data.PropFormula.Views 20 public
open import Data.PropFormula.NormalForms 20
  using (isCNF; isDNF; isNNF )
  renaming (nnf to justNNF )

open import ATP.Metis.Rules 20  public
open import ATP.Metis.Rules.Normalization 20 public
open import ATP.Metis.Rules.Reordering 20 public
  hiding ( disj )

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


f1 = p ∧ q ∧ s

f2 = ¬ p ∨ ¬ q

out : PropFormula
out = simplify f1 f2 ⊥

test : ⌊ eq out ⊥ ⌋ ≡ true
test = {!!} -- refl
