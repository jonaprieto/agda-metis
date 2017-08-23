open import ATP.Metis 9 public
open import Data.Prop 9 public

open import ATP.Metis.Rules.Reordering 9

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

-- Premise.

Γ : Ctxt
Γ = ∅

-- Conjecture.

goal : Prop
goal = (p ⇒ ((p ⇒ q) ⇒ q))

-- Subgoal.

subgoal₀ : Prop
subgoal₀ = ((p ∧ (p ⇒ q)) ⇒ q)

tt : Γ , ¬ subgoal₀ ⊢ ¬ q ∧ (p ∧ ((¬ p) ∨ q))
tt = thm-cnf (assume {Γ = Γ} (¬ (strip goal to (subgoal₀))))

c1 : Γ , ¬ subgoal₀ ⊢ ¬ q
c1 = atp-conjunct (¬ q) tt

c2 : Γ , ¬ subgoal₀ ⊢ (¬ p) ∨ q
c2 = atp-conjunct (¬ p ∨ q) tt

-- testing reorder-∨
original : Prop
original = a ∨ (b ∨ c)

norder : Prop
norder = (c ∨ b) ∨ a

fm1 = ((a ∨ b) ∨ c) ∨ d

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

test1 : ⌊ eq (reorder-∨ (a ∨ b) (b ∨ a)) (b ∨ a) ⌋ ≡ true
test1 = refl

test2 : ⌊ eq (reorder-∨ (a ∨ b ∨ a) (b ∨ a)) (b ∨ a) ⌋ ≡ true
test2 = refl



fa = (a ∨ b) ∨ (c ∨ d)
fgoal = ((a ∨ d) ∨ (b ∨ c))
-- eq (build-∨ a fgoal) fgoal
-- helper-build (right-assoc-∨ fa) fgoal

test3 : ⌊ eq (reorder-∨ ((a ∨ b) ∨ (c ∨ d)) ((a ∨ d) ∨ (b ∨ c)) ) ((a ∨ d) ∨ (b ∨ c)) ⌋ ≡ true
test3 = refl

-- test4 : ⌊ eq (reorder-∨ (a ∨ (b ∨ (c ∨ d))) (((a ∨ b) ∨ c) ∨ d) ) (((a ∨ b) ∨ c) ∨ d) ⌋ ≡ true
-- test4 = refl

-- phi : Prop
-- phi = p ∨ ((q ∧ r) ∨ s)

-- psi : Prop
-- psi = (s ∨ p) ∨ (r ∧ q)

-- test-41 : ⌊ eq (reorder-∨ phi psi) psi ⌋ ≡ true
-- test-41 = refl

------------------------------------------------------------------------------
-- resolve.
------------------------------------------------------------------------------

test-resolve1 : ⌊ eq (resolve a b (b ∨ a) (¬ b)) (a) ⌋ ≡ true
test-resolve1 = refl

------------------------------------------------------------------------------
-- clausify
------------------------------------------------------------------------------

fmc1 = (((¬ p) ∨ q) ∧ ((¬ q) ∨ p))
fmc2 = ((¬ p) ⇔ (¬ q))

cnffmc2 = (p ∨ ¬ q) ∧ (q ∨ ¬ p)

ctest0 : ⌊ eq (cnf fmc2) cnffmc2 ⌋ ≡ true
ctest0 = refl


from1 = p ∨ (q ∨ r)
to1   = (r ∨ q) ∨ p

ctest1 : ⌊ eq (reorder-∧∨ from1 to1) to1 ⌋ ≡ true
ctest1 = refl

ctest2 : ⌊ eq (reorder-∧∨ (cnf fmc2) fmc1) fmc1 ⌋ ≡ true
ctest2 = refl

to5   = (¬ p) ∨ ((¬ q) ∨ r)
from5 = (¬ p) ∨ (r ∨ ((¬ q) ∧ p))

ctest3 : ⌊ eq (reorder-∧∨ (cnf from5) to5) to5 ⌋ ≡ true
ctest3 = refl


cl1  = (¬ p ⇔ ¬ q ⇔ ¬ p ∧ ¬ q)
acl1 = (¬ p ∨ q ∧ (¬ q ∨ p ∧ (p ∨ q)))
cla1 = (clausify cl1 acl1)

-- clausify :
-- p ∨ (q ∨ ¬ p) ∧
-- (p ∨ (q ∨ ¬ q))
-- ∧ (p ∨ (p ∨ q ∨ ¬ q))
-- ∧
-- (p ∨ q ∨ q ∨ ¬ p ∧
-- (p ∨ q ∨ ¬ p ∨ ¬ p ∧
-- (p ∨ q ∨ ¬ q ∨ ¬ p))
-- ∧
-- (¬ q ∨ q ∨ ¬ p ∧
-- (¬ q ∨ ¬ p ∨ ¬ p ∧
-- (¬ q ∨ ¬ q ∨ ¬ p))))

tcl1 : ⌊ eq (clausify cl1 acl1) acl1 ⌋ ≡ true
tcl1 = {!!} -- refl

-- ctest6 : ⌊ eq (right-assoc-∧ (cnf from6)) (right-assoc-∧ cnf6) ⌋ ≡ true
-- ctest6 = refl
