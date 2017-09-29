open import Data.PropFormula 9 public

open import ATP.Metis.Rules.Canonicalize 9
open import ATP.Metis.Rules.Reordering 9

open import Data.PropFormula.SyntaxExperiment 9
open import Relation.Binary.PropositionalEquality

-- Note: When the symbol `?` appears, it means
--       we can not proved yet.

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

testNo1 : ⌊ eq (canonicalize caseNo1) ansNo1 ⌋ ≡ true
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

testNo2 : ⌊ eq (canonicalize caseNo2) ansNo2 ⌋ ≡ true
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

testNo3 : ⌊ eq (canonicalize caseNo3) ansNo3 ⌋ ≡ true
testNo3 = ? -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 4
-- Description : bicond-11.agda
---------------------------------------------------------------------

caseNo4 : PropFormula
caseNo4 = ¬ (p ⇒ q)

ansNo4 : PropFormula
ansNo4 = ((¬ q) ∧ p)

testNo4 : ⌊ eq (canonicalize caseNo4) ansNo4 ⌋ ≡ true
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

testNo5 : ⌊ eq (canonicalize caseNo5) ansNo5 ⌋ ≡ true
testNo5 = ? -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 6
-- Description : disj-07.agda
---------------------------------------------------------------------

caseNo6 : PropFormula
caseNo6 = ((p ∧ q) ∨ (p ∧ r))

ansNo6 : PropFormula
ansNo6 = ((p ∧ q) ∨ (p ∧ r))

testNo6 : ⌊ eq (canonicalize caseNo6) ansNo6 ⌋ ≡ true
testNo6 = ? -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 7
-- Description : disj-14.agda
---------------------------------------------------------------------

caseNo7 : PropFormula
caseNo7 = ((p ∨ q) ⇒ (p ∧ q))

ansNo7 : PropFormula
ansNo7 = (((¬ p) ∧ (¬ q)) ∨ (p ∧ q))

testNo7 : ⌊ eq (canonicalize caseNo7) ansNo7 ⌋ ≡ true
testNo7 = ? -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 8
-- Description : disj-14.agda
---------------------------------------------------------------------

caseNo8 : PropFormula
caseNo8 = ¬ (((p ⇒ q) ∧ q) ⇒ p)

ansNo8 : PropFormula
ansNo8 = ((¬ p) ∧ (q ∧ ((¬ p) ∨ q)))

testNo8 : ⌊ eq (canonicalize caseNo8) ansNo8 ⌋ ≡ true
testNo8 = ? -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 9
-- Description : disj-15.agda
---------------------------------------------------------------------

caseNo9 : PropFormula
caseNo9 = ((q ⇒ r) ∧ (q ∨ p))

ansNo9 : PropFormula
ansNo9 = (((¬ q) ∨ r) ∧ (p ∨ q))

testNo9 : ⌊ eq (canonicalize caseNo9) ansNo9 ⌋ ≡ true
testNo9 = ? -- refl

---------------------------------------------------------------------

---------------------------------------------------------------------
-- Test Problem: 10
-- Description : disj-15.agda
---------------------------------------------------------------------

caseNo10 : PropFormula
caseNo10 = ¬ (((¬ q) ∨ r) ∧ (p ∨ q))

ansNo10 : PropFormula
ansNo10 = ⊥

testNo10 : ⌊ eq (canonicalize caseNo10) ansNo10 ⌋ ≡ true
testNo10 = ? -- refl

---------------------------------------------------------------------
