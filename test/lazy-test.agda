open import ATP.Metis 5 public
open import Data.Prop 5 public


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


postulate
  thm-orginal : ∅ ⊢ original
