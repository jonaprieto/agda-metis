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

open import Data.List.Base using (_∷_; []; [_]; List; _∷ʳ_; _++_)

open import Relation.Binary.PropositionalEquality using ( refl )
open import Function               using ( _$_; id )

------------------------------------------------------------------------------

data ConjView : Prop → Set where
  conj  : (φ₁ φ₂ : Prop) → ConjView (φ₁ ∧ φ₂)
  other : (φ : Prop)     → ConjView φ

conj-view : (φ : Prop) → ConjView φ
conj-view (φ ∧ ψ) = conj _ _
conj-view φ       = other _

data Step  : Set where
  pick  : Step
  proj₁ : Step
  proj₂ : Step

Path : Set
Path = List (Step)

conjunct-path : (φ : Prop) → (ω : Prop) → Path → Path
conjunct-path φ ω path with ⌊ eq φ ω ⌋
... | true  = path ∷ʳ pick
... | false
    with conj-view φ
...    | other _   = []
...    | conj φ₁ φ₂
       with conjunct-path φ₁ ω []
...       | subpath@(_ ∷ _) = (path ∷ʳ proj₁) ++ subpath
...       | [] with conjunct-path φ₂ ω []
...               | subpath@(_ ∷ _) = (path ∷ʳ proj₂) ++ subpath
...               | []              = []


conjunct : (φ : Prop) → (ω : Prop) → Prop
conjunct φ ω with conj-view φ | conjunct-path φ ω []
... | _          | []           = φ
... | conj φ₁ φ₂ | pick  ∷ path = φ
... | conj φ₁ φ₂ | proj₁ ∷ path = conjunct φ₁ ω
... | conj φ₁ φ₂ | proj₂ ∷ path = conjunct φ₂ ω
... | other .φ   | _            = φ

atp-conjunct
  : ∀ {Γ} {φ}
  → (ω : Prop)
  → Γ ⊢ φ
  → Γ ⊢ conjunct φ ω

atp-conjunct {Γ} {φ} ω Γ⊢φ with conj-view φ | conjunct-path φ ω []
... | _          | []           = Γ⊢φ
... | conj φ₁ φ₂ | pick  ∷ path = Γ⊢φ
... | conj φ₁ φ₂ | proj₁ ∷ path = atp-conjunct ω (∧-proj₁ Γ⊢φ)
... | conj φ₁ φ₂ | proj₂ ∷ path = atp-conjunct ω (∧-proj₂ Γ⊢φ)
... | other .φ   | (_ ∷ _)      = Γ⊢φ

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
