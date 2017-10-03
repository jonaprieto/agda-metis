------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Check module.
--
-- * Description:
--
-- Some inference rules are composition of other rules.
-- Many of them work as follows:
--  - rule₁,₂,₃ : from Γ⊢ϕ try to construct Γ⊢ψ, for some ϕ, ψ ∈ PropFormula.
-- Then, we want to build a strong rule that compose other rules, and all rules
-- including the new one follows the same principle described above.
--
-- To compose in an efficient way, we propose the following algorithm:
--
-- Step 0 : Sort the rules in a convenient order.
-- Step 1 : Apply the first rule with Γ⊢ϕ and ψ and go to Step 3.
-- Step 2 : Apply the next rule to Γ⊢ϕ, ψ ∈ PropFormula,
-- Step 3 : If last step produces Γ⊢ψ, stop, else,
--          go to Step 2 but instead of Γ⊢ϕ, we use Γ⊢last-rule(ϕ) and ψ.
-- Step 4 : If there is more rules for applying go to Step 2. Otherwise stop.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ; suc; zero )

module ATP.Metis.Rules.Checking ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool.Base using    ( true; false )

open import Data.PropFormula.Dec n        using ( ⌊_⌋  )
open import Data.PropFormula.Properties n using ( eq )
open import Data.PropFormula.Syntax n

------------------------------------------------------------------------------

BinaryFunc : Set
BinaryFunc = PropFormula → PropFormula → PropFormula

data Check : (f : BinaryFunc) (x y : PropFormula) → Set where
  Stop     : (f : BinaryFunc) → (x y : PropFormula) → Check f x y
  Continue : (f : BinaryFunc) → (x y : PropFormula) → Check f x y

toCheck
  : (f : BinaryFunc)
  → (x : PropFormula)
  → (y : PropFormula)
  → Check f x y

toCheck f x y
  with ⌊ eq (f x y) y ⌋
... | true  = Stop _ _ _
... | false = Continue _ _ _

fromCheck
  : ∀ {g} {x y}
  (f : BinaryFunc)
  → Check g x y
  → PropFormula

fromCheck f (Stop g x y)     = g x y
fromCheck f (Continue g x y) = f (g x y) y

infixr 9 _●_

_●_ : (f : BinaryFunc)
  → (g : BinaryFunc)
  → (BinaryFunc)
f ● g = λ x y → fromCheck f (toCheck g x y)

infixr 9 _●⊢_

_●⊢_ : ∀ {Γ} {ϕ} {f g}
    → (rule₁ : ∀ {Γ} {ϕ} → Γ ⊢ ϕ → (ψ : PropFormula) → Γ ⊢ f ϕ ψ)
    → (rule₂ : ∀ {Γ} {ϕ} → Γ ⊢ ϕ → (ψ : PropFormula) → Γ ⊢ g ϕ ψ)
    → Γ ⊢ ϕ → (ψ : PropFormula) → Γ ⊢ (f ● g) ϕ ψ

_●⊢_ {Γ}{ϕ}{f}{g} rule₁ rule₂ Γ⊢ϕ ψ
  with toCheck g ϕ ψ
... | Stop g₁ x .ψ     = rule₂ Γ⊢ϕ ψ
... | Continue g₁ x .ψ = rule₁ (rule₂ Γ⊢ϕ ψ) ψ

------------------------------------------------------------------------------
-- Example

{-
f : BinaryFunc
f x y = y

postulate
  thm-f : ∀ {Γ} {ϕ}
    → Γ ⊢ ϕ
    → (ψ : PropFormula)
    → Γ ⊢ f ϕ ψ

g : BinaryFunc
g x y = y

postulate
  thm-g : ∀ {Γ} {ϕ}
    → Γ ⊢ ϕ
    → (ψ : PropFormula)
    → Γ ⊢ g ϕ ψ

h = f ● g

thm-h
  : ∀ {Γ} {ϕ}
  → Γ ⊢ ϕ
  → (ψ : PropFormula)
  → Γ ⊢ h ϕ ψ
thm-h = thm-f ●⊢ thm-g

-}
