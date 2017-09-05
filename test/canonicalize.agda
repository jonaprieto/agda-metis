open import Data.PropFormula  9 public

-- Variables.

p : PropFormula
p = Var (# 0)

q : PropFormula
q = Var (# 1)

r : PropFormula
r = Var (# 2)

s : PropFormula
s = Var (# 3)

t : PropFormula
t = Var (# 4)

a : PropFormula
a = Var (# 5)

b : PropFormula
b = Var (# 6)

c : PropFormula
c = Var (# 7)

d : PropFormula
d = Var (# 8)


open import Data.PropFormula.SyntaxExperiment 9 using ( right-assoc-∧ )
open import ATP.Metis.Rules.Canonicalize 9
  using (rmDuplicates-∧; rmDuplicates-∧∨; rmDuplicates-∨; rmDuplicatesCNF; rmPairs-∨ )
open import ATP.Metis.Rules.Reordering 9
  using (right-assoc-∨)
open import Relation.Binary.PropositionalEquality

from7 = (q ∨ q ∨ r ∨ p ∨ q ∨ p)
rafrom7 = (q ∨ (q ∨ (r ∨ (p ∨ (q ∨ p)))))

ar7  = right-assoc-∨ from7

rtest7 : ⌊ eq (right-assoc-∨ from7) rafrom7 ⌋ ≡ true
rtest7 = refl

to7 = (r ∨ (q ∨ p))

test7 : ⌊ eq (rmDuplicates-∨ (right-assoc-∨ from7)) to7 ⌋ ≡ true
test7 = refl

test71 : ⌊ eq (rmDuplicatesCNF from7) to7 ⌋ ≡ true
test71 = refl

lazy : ∀ {Γ}{φ} → Γ , φ ⊢ ⊤
lazy = ⊤-intro

from8 = (q ∨ (q ∨ (r ∨ (p ∨ (q ∨ ¬ q)))))
to8 = ⊤

rtest8 : ⌊ eq (rmPairs-∨ from8) to8 ⌋ ≡ true
rtest8 = refl -- refl
