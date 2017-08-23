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
  using (right-assoc-∨; reorder-∨ )
open import Relation.Binary.PropositionalEquality

open import ATP.Metis.Rules.Resolve 9
  using ( resolve; helper-resolve )

r1 = resolve ⊥ q q (¬ q)

tr1 : ⌊ eq r1 ⊥ ⌋ ≡ true
tr1 = refl

r2 = resolve q p p ((¬ p) ∨ q)
tr2 : ⌊ eq r2 q ⌋ ≡ true
tr2 = refl

q2 = helper-resolve ((p ∨ q) ∧ (¬ p ∨ q))

r3 = resolve ((¬ q) ∨ r) p p ((¬ p) ∨ ((¬ q) ∨ r))
tr3 : ⌊ eq r3 (¬ q ∨ r) ⌋ ≡ true
tr3 = refl

r4 = resolve ((¬ r) ∨ q) p p ((¬ p) ∨ ((¬ r) ∨ q))
tr4 : ⌊ eq r4 (¬ r ∨ q) ⌋ ≡ true
tr4 = refl


r5 = resolve (p ∨ q) r (p ∨ (q ∨ r)) ((¬ r) ∨ (p ∨ q))
tr5 : ⌊ eq r5 (p ∨ q) ⌋ ≡ true
tr5 = refl

r6 = resolve (p ∨ q) r (p ∨ (q ∨ r)) ((¬ r) ∨ (p ∨ q))
tr6 : ⌊ eq r6 (p ∨ q) ⌋ ≡ true
tr6 = refl
