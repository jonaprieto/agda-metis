------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Conjunct inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Conjunct ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool.Base         using ( false; true )

open import Data.Prop.Syntax n
open import Data.Prop.Dec n        using ( yes; no; ⌊_⌋ )
open import Data.Prop.Properties n using ( eq; subst )

open import Relation.Binary.PropositionalEquality using ( refl )
open import Function               using ( _$_; id )

------------------------------------------------------------------------------

data C-View : Prop → Prop → Set where
  instance
    conj  : (φ ψ ω : Prop) → C-View (φ ∧ ψ) ω
    other : (φ ψ : Prop)   → C-View φ ψ

c-view : (x y : Prop) → C-View x y
c-view (φ ∧ ψ) ω  = conj φ ψ ω
c-view φ       ω  = other φ ω

conjunct : Prop → Prop → Prop
conjunct x ω with c-view x ω
conjunct .(φ ∧ ψ) ω | conj φ ψ .ω
  with ⌊ eq φ ω ⌋ | ⌊ eq ψ ω ⌋
...  | true  | _     = φ
...  | false | true  = ψ
...  | false | false = conjunct φ ω
conjunct x ω | other .x .ω = x

atp-conjunct
  : ∀ {Γ} {φ}
  → (ω : Prop)
  → Γ ⊢ φ
  → Γ ⊢ conjunct φ ω

atp-conjunct {Γ} {φ} ω Γ⊢φ with c-view φ ω
atp-conjunct {Γ} {.(φ ∧ ψ)} ω Γ⊢φ | conj φ ψ .ω
  with ⌊ eq φ ω ⌋ | ⌊ eq ψ ω ⌋
... | true  | _     = ∧-proj₁ Γ⊢φ
... | false | true  = ∧-proj₂ Γ⊢φ
... | false | false = atp-conjunct {Γ = Γ} {φ = φ} ω (∧-proj₁ Γ⊢φ)
atp-conjunct {Γ} {.φ} ω Γ⊢φ       | other φ .ω = Γ⊢φ


------------------------------------------------------------------------------
-- rearrange-∧ is a function that only works with conjunctions, it rearranges
-- the order of its inner formulas given a target based on an expected order.
------------------------------------------------------------------------------

r-view : (x y : Prop) → C-View y x
r-view x (y ∧ z) = conj y z x
r-view x y       = other _ _

rearrange-∧ : Prop → Prop → Prop
rearrange-∧ x y with r-view x y
rearrange-∧ x .(φ ∧ ψ) | conj φ ψ .x = conjunct x φ ∧ rearrange-∧ x ψ
rearrange-∧ x y        | other .y .x = x


atp-rearrange-∧
  : ∀ {Γ} {φ}
  → (φ′ : Prop)
  → Γ ⊢ φ
  → Γ ⊢ rearrange-∧ φ φ′

atp-rearrange-∧ {Γ} {φ} φ′ Γ⊢φ with r-view φ φ′
atp-rearrange-∧ {Γ} {.ω} .(φ ∧ ψ) Γ⊢φ | conj φ ψ ω  =
  ∧-intro (atp-conjunct φ Γ⊢φ) (atp-rearrange-∧ ψ Γ⊢φ)
atp-rearrange-∧ {Γ} {.ψ} φ′ Γ⊢φ       | other .φ′ ψ = Γ⊢φ
