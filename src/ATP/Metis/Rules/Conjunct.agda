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

open import Data.List.Base         using (_∷_; []; [_]; List; _∷ʳ_; _++_)

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
Path = List Step

conjunct-path : Prop → Prop → Path → Path
conjunct-path φ ψ path
    with ⌊ eq φ ψ ⌋
... | true  = path ∷ʳ pick
... | false
    with conj-view φ
...    | other _ = []
...    | conj φ₁ φ₂
       with conjunct-path φ₁ ψ []
...       | subpath@(_ ∷ _) = (path ∷ʳ proj₁) ++ subpath
...       | [] with conjunct-path φ₂ ψ []
...               | subpath@(_ ∷ _) = (path ∷ʳ proj₂) ++ subpath
...               | []              = []


conjunct : Prop → Prop → Prop
conjunct φ ψ
  with conj-view φ | conjunct-path φ ψ []
...  | _           | []        = φ
...  | conj _ _    | pick  ∷ _ = φ
...  | conj φ₁ _   | proj₁ ∷ _ = conjunct φ₁ ψ
...  | conj _  φ₂  | proj₂ ∷ _ = conjunct φ₂ ψ
...  | other .φ    | _         = φ

atp-conjunct
  : ∀ {Γ} {φ}
  → (ψ : Prop)
  → Γ ⊢ φ
  → Γ ⊢ conjunct φ ψ
thm-conjunct = atp-conjunct

atp-conjunct {Γ} {φ} ψ Γ⊢φ
  with conj-view φ | conjunct-path φ ψ []
...  | _           | []        = Γ⊢φ
...  | conj φ₁ _   | pick  ∷ _ = Γ⊢φ
...  | conj _ φ₂   | proj₁ ∷ _ = atp-conjunct ψ (∧-proj₁ Γ⊢φ)
...  | conj _ _    | proj₂ ∷ _ = atp-conjunct ψ (∧-proj₂ Γ⊢φ)
...  | other .φ    | (_ ∷ _)   = Γ⊢φ
