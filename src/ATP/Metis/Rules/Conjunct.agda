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
open import Data.Prop.Properties n using ( eq )

open import Function               using ( _$_; id )

------------------------------------------------------------------------------

conjunct : Prop → Prop → Prop
conjunct (φ ∧ ψ) ω with ⌊ eq φ ω ⌋ | ⌊ eq ψ ω ⌋
... | true  | _     = φ
... | false | true  = ψ
... | false | false = conjunct φ ω
conjunct φ ω        = φ

atp-conjunct
  : ∀ {Γ} {φ}
  → (ω : Prop)
  → Γ ⊢ φ
  → Γ ⊢ conjunct φ ω

atp-conjunct {Γ} {φ ∧ ψ} ω Γ⊢φ with ⌊ eq φ ω ⌋ | ⌊ eq ψ ω ⌋
... | true  | _     = ∧-proj₁ Γ⊢φ
... | false | true  = ∧-proj₂ Γ⊢φ
... | false | false = atp-conjunct {Γ = Γ} {φ = φ} ω (∧-proj₁ Γ⊢φ)
atp-conjunct {_} {Var x} _  = id
atp-conjunct {_} {⊤} _      = id
atp-conjunct {_} {⊥} _      = id
atp-conjunct {_} {φ ∨ φ₁} _ = id
atp-conjunct {_} {φ ⇒ φ₁} _ = id
atp-conjunct {_} {φ ⇔ φ₁} _ = id
atp-conjunct {_} {¬ φ} _    = id

------------------------------------------------------------------------------
-- rearrange-∧ is a function that only works in conjunction, it rearranges
-- the order of its inner formulas given a target, the expected order.
------------------------------------------------------------------------------

rearrange-∧ : Prop → Prop → Prop
rearrange-∧ φ (ω₁ ∧ ω₂) = conjunct φ ω₁ ∧ rearrange-∧ φ ω₂
rearrange-∧ φ (Var x)   = φ
rearrange-∧ φ ⊤         = φ
rearrange-∧ φ ⊥         = φ
rearrange-∧ φ (ψ ∨ ψ₁)  = φ
rearrange-∧ φ (ψ ⇒ ψ₁)  = φ
rearrange-∧ φ (ψ ⇔ ψ₁)  = φ
rearrange-∧ φ (¬ ψ)     = φ

atp-rearrange-∧
  : ∀ {Γ} {φ}
  → (φ̂ : Prop)
  → Γ ⊢ φ
  → Γ ⊢ rearrange-∧ φ φ̂

atp-rearrange-∧ (ω₁ ∧ ω₂) Γ⊢φ =
  ∧-intro
    (atp-conjunct ω₁ Γ⊢φ)
    (atp-rearrange-∧ ω₂ Γ⊢φ)

atp-rearrange-∧ (Var x) = id
atp-rearrange-∧ ⊤ = id
atp-rearrange-∧ ⊥ = id
atp-rearrange-∧ (ψ ∨ ψ₁) = id
atp-rearrange-∧ (ψ ⇒ ψ₁) = id
atp-rearrange-∧ (ψ ⇔ ψ₁) = id
atp-rearrange-∧ (¬ ψ) = id
