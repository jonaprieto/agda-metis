---------------------------------------------------------------------
-- To test `canonicalize` inference rule.
---------------------------------------------------------------------

open import Data.PropFormula 9 public

open import ATP.Metis.Rules.Canonicalize 9 public
open import ATP.Metis.Rules.Reordering 9 public
open import ATP.Metis.Rules.Resolve 9 public

open import Relation.Binary.PropositionalEquality

-- Note: When the symbol `?` appears, it means
--       we can not proved yet.
-- The problem names refer to problems in
-- Prop-Pack: jonaprieto/prop-pack in github.

-- Variables.

p = Var (# 0)
q = Var (# 1)
r = Var (# 2)

---------------------------------------------------------------------
-- Test Problem: 1
---------------------------------------------------------------------

caseNo1 : PropFormula
caseNo1 = ¬ ((p ∧ q) ⇒ r)

ansNo1 : PropFormula
ansNo1 = ((¬ r) ∧ (p ∧ q))

outCaseNo1 : PropFormula
outCaseNo1 = canonicalize caseNo1 ansNo1

testNo1 : ⌊ eq outCaseNo1 ansNo1 ⌋ ≡ true
testNo1 = refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 2
-- Description : impl-02.agda
---------------------------------------------------------------------

caseNo2 : PropFormula
caseNo2 = ¬ ((p ∧ q) ⇒ p)

ansNo2 : PropFormula
ansNo2 = ⊥

outCaseNo2 : PropFormula
outCaseNo2 = canonicalize caseNo2 ansNo2

testNo2 : ⌊ eq outCaseNo2 ansNo2 ⌋ ≡ true
testNo2 = refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 3
-- Description : bicond-09.agda
---------------------------------------------------------------------

caseNo3 : PropFormula
caseNo3 = ¬ ((((p ∧ q) ∧ (p ⇒ q)) ⇒ p))

ansNo3 : PropFormula
ansNo3 = ⊥

outCaseNo3 : PropFormula
outCaseNo3 = canonicalize caseNo3 ansNo3
-- Var zero ∧ (¬ Var zero ∨ Var (suc zero)

testNo3 : ⌊ eq outCaseNo3 ansNo3 ⌋ ≡ true
testNo3 = {!refl!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 4
-- Description : bicond-11.agda
---------------------------------------------------------------------

caseNo4 : PropFormula
caseNo4 = ¬ (p ⇒ q)

ansNo4 : PropFormula
ansNo4 = ((¬ q) ∧ p)

outCaseNo4 : PropFormula
outCaseNo4 = canonicalize caseNo4 ansNo4

testNo4 : ⌊ eq outCaseNo4 ansNo4 ⌋ ≡ true
testNo4 = refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 5
-- Description : bicond-11.agda
---------------------------------------------------------------------

caseNo5 : PropFormula
caseNo5 = ((p ∨ q) ⇔ q) ⇔ p

ansNo5 : PropFormula
ansNo5 = ((¬ p) ⇔ ((¬ q) ⇔ (p ∨ q)))

outCaseNo5 : PropFormula
outCaseNo5 = canonicalize caseNo5 ansNo5

testNo5 : ⌊ eq outCaseNo5 ansNo5 ⌋ ≡ true
testNo5 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 6
-- Description : disj-07.agda
---------------------------------------------------------------------

caseNo6 : PropFormula
caseNo6 = ((p ∧ q) ∨ (p ∧ r))

ansNo6 : PropFormula
ansNo6 = ((p ∧ q) ∨ (p ∧ r))

outCaseNo6 : PropFormula
outCaseNo6 = canonicalize caseNo6 ansNo6

testNo6 : ⌊ eq outCaseNo6 ansNo6 ⌋ ≡ true
testNo6 = refl -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 7
-- Description : disj-14.agda
---------------------------------------------------------------------

caseNo7 : PropFormula
caseNo7 = ((p ∨ q) ⇒ (p ∧ q))

ansNo7 : PropFormula
ansNo7 = (((¬ p) ∧ (¬ q)) ∨ (p ∧ q))

outCaseNo7 : PropFormula
outCaseNo7 = canonicalize-axiom caseNo7 ansNo7
-- (¬ Var zero ∨ Var (suc zero)) ∧ (¬ Var (suc zero) ∨ Var zero)

testNo7 : ⌊ eq outCaseNo7 ansNo7 ⌋ ≡ true
testNo7 = refl -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 8
-- Description : disj-14.agda
---------------------------------------------------------------------

caseNo8 : PropFormula
caseNo8 = ¬ (((p ⇒ q) ∧ q) ⇒ p)

ansNo8 : PropFormula
ansNo8 = ((¬ p) ∧ (q ∧ ((¬ p) ∨ q)))

outCaseNo8 : PropFormula
outCaseNo8 = canonicalize caseNo8 ansNo8
-- (¬ Var zero ∨ Var (suc zero)) ∧ Var (suc zero)

testNo8 : ⌊ eq outCaseNo8 ansNo8 ⌋ ≡ true
testNo8 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 9
-- Description : disj-15.agda
---------------------------------------------------------------------

caseNo9 : PropFormula
caseNo9 = ((q ⇒ r) ∧ (q ∨ p))

ansNo9 : PropFormula
ansNo9 = (((¬ q) ∨ r) ∧ (p ∨ q))

outCaseNo9 : PropFormula
outCaseNo9 = canonicalize caseNo9 ansNo9
-- ¬ Var (suc zero) ∨ Var (suc (suc zero)) ∧ (Var (suc zero) ∨ Var zero)

testNo9 : ⌊ eq outCaseNo9 ansNo9 ⌋ ≡ true
testNo9 = {!refl!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 10
-- Description : disj-15.agda
---------------------------------------------------------------------

caseNo10 : PropFormula
caseNo10 = ¬ (((¬ q) ∨ r) ∧ (p ∨ q))

ansNo10 : PropFormula
ansNo10 = ⊥

outCaseNo10 : PropFormula
outCaseNo10 = canonicalize caseNo10 ansNo10

testNo10 : ⌊ eq outCaseNo10 ansNo10 ⌋ ≡ true
testNo10 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 11
-- Description : bicond-01.agda
--
--    (atp-clausify (((¬ p) ∨ q) ∧ ((¬ q) ∨ p))
--      (atp-canonicalize ((¬ p) ⇔ (¬ q))
--        (weaken (¬ subgoal₀)
--          (assume {Γ = ∅} a₁))))))
---------------------------------------------------------------------

caseNo11 : PropFormula
caseNo11 = (p ⇔ q)

ansNo11 : PropFormula
ansNo11 = ((¬ p) ⇔ (¬ q))

outCaseNo11 : PropFormula
outCaseNo11 = canonicalize caseNo11 ansNo11

testNo11 : ⌊ eq outCaseNo11 ansNo11 ⌋ ≡ true
testNo11 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 12
-- Description : bicond-02.agda
--
--    (atp-simplify ((¬ q) ⇔ (¬ r))
--      (atp-canonicalize ((¬ p) ⇔ ((¬ q) ⇔ r))
--        (weaken (¬ subgoal₀)
--          (assume {Γ = [ a₁ ]} a₂)))
--      (atp-canonicalize p
--        (weaken-Δ₁
--          (∅ , a₂ , ¬ subgoal₀)
--          (assume {Γ = ∅} a₁)))))))
---------------------------------------------------------------------

caseNo12 : PropFormula
caseNo12 = ((p ⇔ q) ⇔ r)

ansNo12 : PropFormula
ansNo12 = ((¬ p) ⇔ ((¬ q) ⇔ r))

outCaseNo12 : PropFormula
outCaseNo12 = canonicalize caseNo12 ansNo12

testNo12 : ⌊ eq outCaseNo12 ansNo12 ⌋ ≡ true
testNo12 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 13
-- Description : bicond-03.agda
-- subgoal₀
---------------------------------------------------------------------

caseNo13 : PropFormula
caseNo13 = ¬ (((p ⇔ q) ∧ q) ⇒ p)

ansNo13 : PropFormula
ansNo13 = (¬ p) ∧ (q ∧ ((¬ p) ⇔ (¬ q)))

outCaseNo13 : PropFormula
outCaseNo13 = canonicalize caseNo13 ansNo13

testNo13 : ⌊ eq outCaseNo13 ansNo13 ⌋ ≡ true
testNo13 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 14
-- Description : bicond-03.agda
--        (atp-canonicalize ((¬ q) ∧ (p ∧ ((¬ p) ⇔ (¬ q))))
--          (assume {Γ = Γ}
--            (¬ subgoal₁))))
---------------------------------------------------------------------

caseNo14 : PropFormula
caseNo14 = ¬ (((p ⇔ q) ∧ p) ⇒ q)

ansNo14 : PropFormula
ansNo14 = ((¬ q) ∧ (p ∧ ((¬ p) ⇔ (¬ q))))

outCaseNo14 : PropFormula
outCaseNo14 = canonicalize caseNo14 ansNo14

testNo14 : ⌊ eq outCaseNo14 ansNo14 ⌋ ≡ true
testNo14 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 15
-- Description : bicond-06.agda
--         (atp-clausify ((¬ p) ∨ q)
--          (atp-canonicalize ((¬ q) ⇔ ((¬ p) ∧ (¬ q)))
--            (weaken (¬ subgoal₀)
--              (assume {Γ = ∅} a₁)))))
---------------------------------------------------------------------

caseNo15 : PropFormula
caseNo15 = ((p ∨ q) ⇔ q)

ansNo15 : PropFormula
ansNo15 = ((¬ q) ⇔ ((¬ p) ∧ (¬ q)))

outCaseNo15 : PropFormula
outCaseNo15 = canonicalize caseNo15 ansNo15

testNo15 : ⌊ eq outCaseNo15 ansNo15 ⌋ ≡ true
testNo15 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 16
-- Description : bicond-07.agda
---------------------------------------------------------------------

caseNo16 : PropFormula
caseNo16 = ((p ∧ q) ⇔ p)

ansNo16 : PropFormula
ansNo16 = ((¬ p) ⇔ ((¬ p) ∨ (¬ q)))

outCaseNo16 : PropFormula
outCaseNo16 = canonicalize caseNo16 ansNo16

testNo16 : ⌊ eq outCaseNo16 ansNo16 ⌋ ≡ true
testNo16 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 17
-- Description : bicond-07.agda
---------------------------------------------------------------------

caseNo17 : PropFormula
caseNo17 = (p ⇒ q)

ansNo17 : PropFormula
ansNo17 = ((¬ p) ∨ q)

outCaseNo17 : PropFormula
outCaseNo17 = canonicalize caseNo17 ansNo17

testNo17 : ⌊ eq outCaseNo17 ansNo17 ⌋ ≡ true
testNo17 = refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 18
-- Description : bicond-07.agda
---------------------------------------------------------------------

caseNo18 : PropFormula
caseNo18 = ¬ ((p ∧ p) ⇒ q)

ansNo18 : PropFormula
ansNo18 = ((¬ q) ∧ p)

outCaseNo18 : PropFormula
outCaseNo18 = canonicalize caseNo18 ansNo18

testNo18 : ⌊ eq outCaseNo18 ansNo18 ⌋ ≡ true
testNo18 = refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 19
-- Description : bicond-08.agda
---------------------------------------------------------------------

caseNo19 : PropFormula
caseNo19 = ((p ⇒ q) ∧ (q ⇒ p))

ansNo19 : PropFormula
ansNo19 = (((¬ p) ∨ q) ∧ ((¬ q) ∨ p))

outCaseNo19 : PropFormula
outCaseNo19 = canonicalize caseNo19 ansNo19

testNo19 : ⌊ eq outCaseNo19 ansNo19 ⌋ ≡ true
testNo19 = refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 20
-- Description : bicond-10.agda
---------------------------------------------------------------------

caseNo20 : PropFormula
caseNo20 = ¬ ((((p ⇒ q) ⇔ p) ∧ p) ⇒ q)

ansNo20 : PropFormula
ansNo20 = ((¬ q) ∧ (p ∧ ((¬ p) ⇔ ((¬ q) ∧ p))))

outCaseNo20 : PropFormula
outCaseNo20 = canonicalize caseNo20 ansNo20

testNo20 : ⌊ eq outCaseNo20 ansNo20 ⌋ ≡ true
testNo20 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 21
-- Description : bicond-12.agda
---------------------------------------------------------------------

caseNo21 : PropFormula
caseNo21 = (p ⇒ (q ⇔ r))

ansNo21 : PropFormula
ansNo21 = ((¬ p) ∨ ((¬ q) ⇔ (¬ r)))

outCaseNo21 : PropFormula
outCaseNo21 = canonicalize caseNo21 ansNo21

testNo21 : ⌊ eq outCaseNo21 ansNo21 ⌋ ≡ true
testNo21 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 22
-- Description : bicond-12.agda
---------------------------------------------------------------------

caseNo22 : PropFormula
caseNo22 = ¬ (((p ∧ q) ∧ p) ⇒ r)

ansNo22 : PropFormula
ansNo22 = ((¬ r) ∧ (p ∧ q))

outCaseNo22 : PropFormula
outCaseNo22 = canonicalize caseNo22 ansNo22

testNo22 : ⌊ eq outCaseNo22 ansNo22 ⌋ ≡ true
testNo22 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 23
-- Description : bicond-13.agda
---------------------------------------------------------------------

caseNo23 : PropFormula
caseNo23 = ¬ (((p ∨ (q ∧ r)) ∧ (¬ p)) ⇒ q)

ansNo23 : PropFormula
ansNo23 = ((¬ p) ∧ ((¬ q) ∧ (p ∨ (q ∧ r))))

outCaseNo23 : PropFormula
outCaseNo23 = canonicalize caseNo23 ansNo23

testNo23 : ⌊ eq outCaseNo23 ansNo23 ⌋ ≡ true
testNo23 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 24
-- Description : bicond-13.agda
--    (atp-canonicalize ((¬ p) ∧ ((¬ r) ∧ ((p ∨ q) ∧ (p ∨ (q ∧ r)))))
--      (assume {Γ = Γ}
--        (¬ subgoal₁))))
---------------------------------------------------------------------

caseNo24 : PropFormula
caseNo24 = ¬ (((p ∨ (q ∧ r)) ∧ ((p ∨ q) ∧ (¬ p))) ⇒ r)

ansNo24 : PropFormula
ansNo24 = ((¬ p) ∧ ((¬ r) ∧ ((p ∨ q) ∧ (p ∨ (q ∧ r)))))

outCaseNo24 : PropFormula
outCaseNo24 = canonicalize caseNo24 ansNo24

testNo24 : ⌊ eq outCaseNo24 ansNo24 ⌋ ≡ true
testNo24 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 25
-- Description : bicond-13.agda
---------------------------------------------------------------------

caseNo25 : PropFormula
caseNo25 = ¬ ((((p ∨ q) ∧ (p ∨ r)) ∧ (¬ p)) ⇒ q)

ansNo25 : PropFormula
ansNo25 = ((¬ p) ∧ ((¬ q) ∧ ((p ∨ q) ∧ (p ∨ r))))

outCaseNo25 : PropFormula
outCaseNo25 = canonicalize caseNo25 ansNo25

testNo25 : ⌊ eq outCaseNo25 ansNo25 ⌋ ≡ true
testNo25 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 26
-- Description : disj-01.agda
---------------------------------------------------------------------

caseNo26 : PropFormula
caseNo26 = ¬ ((¬ q) ⇒ p)

ansNo26 : PropFormula
ansNo26 = ((¬ p) ∧ (¬ q))

outCaseNo26 : PropFormula
outCaseNo26 = canonicalize caseNo26 ansNo26

testNo26 : ⌊ eq outCaseNo26 ansNo26 ⌋ ≡ true
testNo26 = refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 27
-- Description : disj-11.agda
---------------------------------------------------------------------

caseNo27 : PropFormula
caseNo27 = ((p ⇒ q) ⇒ (p ⇒ r))

ansNo27 : PropFormula
ansNo27 = ((¬ p) ∨ (r ∨ ((¬ q) ∧ p)))

outCaseNo27 : PropFormula
outCaseNo27 = canonicalize caseNo27 ansNo27

testNo27 : ⌊ eq outCaseNo27 ansNo27 ⌋ ≡ true
testNo27 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 28
-- Description : prop-09.agda
---------------------------------------------------------------------

caseNo28 : PropFormula
caseNo28 = ¬ (((p ∨ q) ∧ (((¬ p) ∨ q) ∧ (p ∨ (¬ q)))) ⇒ q)

ansNo28 : PropFormula
ansNo28 = ((¬ q) ∧ (((¬ p) ∨ q) ∧ (((¬ q) ∨ p) ∧ (p ∨ q))))

outCaseNo28 : PropFormula
outCaseNo28 = canonicalize caseNo28 ansNo28

testNo28 : ⌊ eq outCaseNo28 ansNo28 ⌋ ≡ true
testNo28 = {!!} -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 29
-- Description : prop-09.agda
---------------------------------------------------------------------

caseNo29 : PropFormula
caseNo29 = ¬ ((((p ∨ q) ∧ (((¬ p) ∨ q) ∧ (p ∨ (¬ q)))) ∧ (¬ (¬ q))) ⇒ q)

ansNo29 : PropFormula
ansNo29 = ⊥

outCaseNo29 : PropFormula
outCaseNo29 = canonicalize caseNo29 ansNo29

testNo29 : ⌊ eq outCaseNo29 ansNo29 ⌋ ≡ true
testNo29 = {!!} -- refl

---------------------------------------------------------------------
