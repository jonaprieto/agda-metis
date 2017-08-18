open import ATP.Metis 6 public
open import Data.Prop 6 public


-- Variables.

p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

a : Prop
a = Var (# 2)

b : Prop
b = Var (# 3)

c : Prop
c = Var (# 4)

d : Prop
d = Var (# 5)

-- Premise.

Γ : Ctxt
Γ = ∅

-- Conjecture.

goal : Prop
goal = (p ⇒ ((p ⇒ q) ⇒ q))

-- Subgoal.

subgoal₀ : Prop
subgoal₀ = ((p ∧ (p ⇒ q)) ⇒ q)

t : Γ , ¬ subgoal₀ ⊢ ¬ q ∧ (p ∧ ((¬ p) ∨ q))
t = thm-cnf (assume {Γ = Γ} (¬ (strip goal to (subgoal₀))))

c1 : Γ , ¬ subgoal₀ ⊢ ¬ q
c1 = atp-conjunct (¬ q) t

c2 : Γ , ¬ subgoal₀ ⊢ (¬ p) ∨ q
c2 = atp-conjunct (¬ p ∨ q) t

-- testing reorder-∨
original : Prop
original = a ∨ (b ∨ c)

norder : Prop
norder = (c ∨ b) ∨ a

fm1 = ((a ∨ b) ∨ c) ∨ d

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

test1 : ⌊ eq (reorder-∨ (a ∨ b) (b ∨ a)) (b ∨ a) ⌋ ≡ true
test1 = refl

test2 : ⌊ eq (reorder-∨ (a ∨ b) (b ∨ a ∨ a)) (a ∨ b) ⌋ ≡ false
test2 = refl


fa = (a ∨ b) ∨ (c ∨ d)
fgoal = ((a ∨ d) ∨ (b ∨ c))
-- eq (build-∨ a fgoal) fgoal
-- helper-build (right-assoc-∨ fa) fgoal

test3 : ⌊ eq (reorder-∨ ((a ∨ b) ∨ (c ∨ d)) ((a ∨ d) ∨ (b ∨ c)) ) ((a ∨ d) ∨ (b ∨ c)) ⌋ ≡ true
test3 = refl

-- test4 : ⌊ eq (reorder-∨ (a ∨ (b ∨ (c ∨ d))) (((a ∨ b) ∨ c) ∨ d) ) (((a ∨ b) ∨ c) ∨ d) ⌋ ≡ true
-- test4 = refl
