open import Data.Prop 9 public

-- Variables.

p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

r : Prop
r = Var (# 2)

s : Prop
s = Var (# 3)

t : Prop
t = Var (# 4)

a : Prop
a = Var (# 5)

b : Prop
b = Var (# 6)

c : Prop
c = Var (# 7)

d : Prop
d = Var (# 8)


open import Data.Prop.SyntaxExperiment 9 using ( right-assoc-∧ )
open import ATP.Metis.Rules.Canonicalize 9
  using (removeDuplicates-∧; removeDuplicates-∧∨; removeDuplicates-∨; removeDuplicatesCNF )
open import ATP.Metis.Rules.Reordering 9
  using (right-assoc-∨)
open import Relation.Binary.PropositionalEquality

from7 = (q ∨ q ∨ r ∨ p ∨ q ∨ p)
rafrom7 = (q ∨ (q ∨ (r ∨ (p ∨ (q ∨ p)))))

ar7  = right-assoc-∨ from7

rtest7 : ⌊ eq (right-assoc-∨ from7) rafrom7 ⌋ ≡ true
rtest7 = refl

to7 = (r ∨ (q ∨ p))

test7 : ⌊ eq (removeDuplicates-∨ (right-assoc-∨ from7)) to7 ⌋ ≡ true
test7 = refl

test71 : ⌊ eq (removeDuplicatesCNF from7) to7 ⌋ ≡ true
test71 = refl
