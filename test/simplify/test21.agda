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

{-
with ⌊ eq (nnf (¬ φ₁)) (conjunct φ₂ (nnf (¬ φ₁))) ⌋
... | true  = ⊥
... | false
with ⌊ eq (¬ φ₁) (canonicalize φ₂ (¬ φ₁)) ⌋
... | true  = ⊥
... | false = φ₁
-}


f1 = dnf (¬ r ∧ p ∧ (¬ q ∨ ¬ s))
dnff1 =  (¬ r ∧ (p ∧ ¬ q)) ∨ (¬ r ∧ (p ∧ ¬ s))

f2 = q ∧ s

out : PropFormula
out = sdisj f1 f2

test : ⌊ eq out ⊥ ⌋ ≡ true
test = {!!} -- refl
