-- Test for many examples

open import Data.PropFormula 9 public
open import Data.PropFormula.NormalForms 9
  renaming (cnf to justCNF; cnf-lem to thm-justCNF )

open import ATP.Metis.Rules.Normalization
open import ATP.Metis.Rules.Reordering
open import ATP.Metis.Rules.Strip
open import ATP.Metis.Rules.Conjunct
open import ATP.Metis.Rules.Clausify
open import ATP.Metis.Rules.Simplify
open import ATP.Metis.Rules.Resolve
  hiding (resolve)
  renaming (original-resolve to resolve)

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

-- Premise.

Γ : Ctxt
Γ = ∅

-- Conjecture.

goal : PropFormula
goal = (p ⊃ ((p ⊃ q) ⊃ q))

-- Subgoal.

subgoal₀ : PropFormula
subgoal₀ = ((p ∧ (p ⊃ q)) ⊃ q)

tt : Γ , ¬ subgoal₀ ⊢ ¬ q ∧ (p ∧ ((¬ p) ∨ q))
tt = thm-justCNF (assume {Γ = Γ} (¬ (strip goal to (subgoal₀))))

c1 : Γ , ¬ subgoal₀ ⊢ ¬ q
c1 = conjunct-thm (¬ q) tt

c2 : Γ , ¬ subgoal₀ ⊢ (¬ p) ∨ q
c2 = conjunct-thm (¬ p ∨ q) tt

-- testing reorder-∨
original : PropFormula
original = a ∨ (b ∨ c)

norder : PropFormula
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

-- phi : PropFormula
-- phi = p ∨ ((q ∧ r) ∨ s)

-- psi : PropFormula
-- psi = (s ∨ p) ∨ (r ∧ q)

-- test-41 : ⌊ eq (reorder-∨ phi psi) psi ⌋ ≡ true
-- test-41 = refl

------------------------------------------------------------------------------
-- resolve.
------------------------------------------------------------------------------

test-resolve1 : ⌊ eq (resolve (b ∨ a) (¬ b) b a) a ⌋ ≡ true
test-resolve1 = refl

------------------------------------------------------------------------------
-- clausify
------------------------------------------------------------------------------

fmc1 = (((¬ p) ∨ q) ∧ ((¬ q) ∨ p))
fmc2 = ((¬ p) ⇔ (¬ q))

cnffmc2 = (p ∨ ¬ q) ∧ (q ∨ ¬ p)

ctest0 : ⌊ eq (justCNF fmc2) cnffmc2 ⌋ ≡ true
ctest0 = refl


from1 = p ∨ (q ∨ r)
to1   = (r ∨ q) ∨ p

ctest1 : ⌊ eq (reorder-∧∨ from1 to1) to1 ⌋ ≡ true
ctest1 = refl

ctest2 : ⌊ eq (reorder-∧∨ (justCNF fmc2) fmc1) fmc1 ⌋ ≡ true
ctest2 = refl

to5   = (¬ p) ∨ ((¬ q) ∨ r)
from5 = (¬ p) ∨ (r ∨ ((¬ q) ∧ p))

ctest3 : ⌊ eq (reorder-∧∨ (justCNF from5) to5) to5 ⌋ ≡ true
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

-- tcl1 : ⌊ eq (clausify cl1 acl1) acl1 ⌋ ≡ true
-- tcl1 = {!!} -- refl

-- ctest6 : ⌊ eq (right-assoc-∧ (cnf from6)) (right-assoc-∧ cnf6) ⌋ ≡ true
-- ctest6 = refl
