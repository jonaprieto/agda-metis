------------------------------------------------------------------------------
-- Athena version 0.1-084ac4f.
-- TSTP file: test/prop-pack/problems/implication/impl-4.tstp.
------------------------------------------------------------------------------

module impl-4 where

------------------------------------------------------------------------------

open import ATP.Metis 2 public
open import Data.Prop 2 public

------------------------------------------------------------------------------

-- Variables.

p : Prop
p = Var (# 0)

q : Prop
q = Var (# 1)

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
t = thm-cnf (atp-strip (assume {Γ = Γ} (atp-negate subgoal₀)))

c1 : Γ , ¬ subgoal₀ ⊢ ¬ q
c1 = atp-conjunct (¬ q) t

c2 : Γ , ¬ subgoal₀ ⊢ (¬ p) ∨ q
c2 = atp-conjunct (¬ p ∨ q) t
