------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Conjunct inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Conjunct ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool.Base         using ( Bool; false; true )

open import Data.Prop.Syntax n
open import Data.Prop.Dec n        using ( yes; no; ⌊_⌋ )
open import Data.Prop.Properties n using ( eq; subst )

open import Relation.Binary.PropositionalEquality using ( refl )
open import Function               using ( _$_; id )

------------------------------------------------------------------------------

data ConjView : Prop → Set where
  conj  : (φ₁ φ₂ : Prop) → ConjView (φ₁ ∧ φ₂)
  other : (φ : Prop)     → ConjView φ

conj-view : (φ : Prop) → ConjView φ
conj-view (φ ∧ ψ) = conj _ _
conj-view φ       = other _

data C-View : Prop  → Set where
  do-nothing : (φ : Prop) → C-View φ
  pick       : (φ : Prop) → C-View φ
  call       : (φ : Prop) → C-View φ
  proj₁      : (φ : Prop) → C-View φ
  proj₂      : (φ : Prop) → C-View φ

conjunct₀ : ∀ {φ} → C-View φ → (ω : Prop) → C-View φ
conjunct₀ (call φ) ω with ⌊ eq φ ω ⌋
conjunct₀ (call φ) ω | true  = pick φ
conjunct₀ (call φ) ω | false with conj-view φ
conjunct₀ (call .(φ₁ ∧ φ₂)) ω | false | conj φ₁ φ₂
  with conjunct₀ (call φ₁) ω
...  | (pick .φ₁) = proj₁ (φ₁ ∧ φ₂)
...  | _ with conjunct₀ (call φ₂) ω
...         | (pick .φ₂) = proj₂ (φ₁ ∧ φ₂)
...         | _          = do-nothing (φ₁ ∧ φ₂)
conjunct₀ (call φ)         ω  | false | other .φ = do-nothing φ

conjunct₀ (pick       φ)   _ = do-nothing φ
conjunct₀ (do-nothing φ)   _ = do-nothing φ
conjunct₀ (proj₁ φ)        _ = do-nothing φ
conjunct₀ (proj₂ φ)        _ = do-nothing φ


conjunct : Prop → Prop → Prop
conjunct  φ  ω with conjunct₀ (call φ) ω
conjunct φ ω | do-nothing .φ = φ
conjunct φ ω | pick .φ       = φ
conjunct φ ω | call .φ       = φ
conjunct φ ω | proj₁ .φ with conj-view φ
... | conj φ₁ φ₂ = conjunct φ₁ ω
... | other .φ   = φ
conjunct φ ω | proj₂ .φ with conj-view φ
... | conj φ₁ φ₂ = conjunct φ₂ ω
... | other .φ   = φ

atp-conjunct
  : ∀ {Γ} {φ}
  → (ω : Prop)
  → Γ ⊢ φ
  → Γ ⊢ conjunct φ ω

atp-conjunct {Γ} {φ} ω Γ⊢φ with conjunct₀ (call φ) ω
... | do-nothing .φ = Γ⊢φ
... | pick .φ = Γ⊢φ
... | call .φ = Γ⊢φ
... | proj₁ .φ with conj-view φ
...               | conj φ₁ φ₂ = atp-conjunct ω (∧-proj₁ Γ⊢φ)
...               | other _ = Γ⊢φ

atp-conjunct {Γ} {.φ} ω Γ⊢φ | proj₂ φ with conj-view φ
... | conj φ₁ φ₂ = atp-conjunct ω (∧-proj₂ Γ⊢φ)
... | other .φ   = Γ⊢φ


------------------------------------------------------------------------------
-- rearrange-∧ is a function that only works with conjunctions, it rearranges
-- the order of its inner formulas given a target based on an expected order.
-- Notice that the target is a conjunction (φ ∧ ψ).
------------------------------------------------------------------------------

data R-View : Prop → Prop → Set where
  conj  : (φ ψ ω : Prop) → R-View φ (ψ ∧ ω)
  other : (φ ψ : Prop)   → R-View φ ψ

rearrange-∧ : Prop → Prop → Prop
rearrange-∧ φ ω with conj-view ω
rearrange-∧ φ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ = conjunct φ φ₁ ∧ rearrange-∧ φ φ₂
rearrange-∧ φ ω          | other .ω   = φ


atp-rearrange-∧
  : ∀ {Γ} {φ}
  → (ω : Prop)
  → Γ ⊢ φ
  → Γ ⊢ rearrange-∧ φ ω

atp-rearrange-∧ {Γ} {φ} ω Γ⊢φ with conj-view ω
... | conj  φ₁ φ₂ = ∧-intro (atp-conjunct φ₁ Γ⊢φ) (atp-rearrange-∧ φ₂ Γ⊢φ)
... | other .ω   = Γ⊢φ
