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
open import ATP.Metis.Rules.Reordering 9

open import Relation.Binary.PropositionalEquality

open import ATP.Metis.Rules.Resolve 9


r1 = resolve q (¬ q) q ⊥

tr1 : ⌊ eq r1 ⊥ ⌋ ≡ true
tr1 = refl

r2 = resolve p ((¬ p) ∨ q) p q
tr2 : ⌊ eq r2 q ⌋ ≡ true
tr2 = refl

q2 = rsol ((p ∨ q) ∧ (¬ p ∨ q))

r3 = resolve p ((¬ p) ∨ ((¬ q) ∨ r)) p ((¬ q) ∨ r)
tr3 : ⌊ eq r3 (¬ q ∨ r) ⌋ ≡ true
tr3 = refl

r4 = resolve p ((¬ p) ∨ ((¬ r) ∨ q)) p ((¬ r) ∨ q)
tr4 : ⌊ eq r4 (¬ r ∨ q) ⌋ ≡ true
tr4 = refl


r5 = resolve (p ∨ (q ∨ r)) ((¬ r) ∨ (p ∨ q)) r (p ∨ q)
tr5 : ⌊ eq r5 (p ∨ q) ⌋ ≡ true
tr5 = refl

r6 = resolve (p ∨ (q ∨ r)) ((¬ r) ∨ (p ∨ q)) r (p ∨ q)
tr6 : ⌊ eq r6 (p ∨ q) ⌋ ≡ true
tr6 = refl
