------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Canonicalize inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ; suc; zero )

module ATP.Metis.Rules.Canonicalize ( n : ℕ ) where

------------------------------------------------------------------------------

open import ATP.Metis.Rules.Reordering n
  using ( right-assoc-∨; reorder-∧∨; thm-reorder-∧∨; reorder-∨ )

open import Data.Bool.Base
  using    ( true; false )
  renaming ( _∨_ to _or_ )

open import Data.Prop.Dec n                  using ( ⌊_⌋ ; yes ; no )
open import Data.Prop.Properties n           using ( eq ; subst )
open import Data.Prop.Syntax n
open import Data.Prop.Theorems n
open import Data.Prop.NormalForms n
open import Data.Prop.Views n

open import Data.Prop.SyntaxExperiment n    using ( right-assoc-∧ )

open import Data.Bool using (Bool; true; false) renaming (_∨_ to _or_ )

open import Function                         using ( _$_; id ; _∘_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym ; trans)

------------------------------------------------------------------------------


-- All formulas are in NNF.

_∈-∨_ : Prop → Prop → Bool
φ ∈-∨ ψ
  with ⌊ eq φ ψ ⌋
...  | true = true
...  | false
     with disj-view ψ
...     | other .ψ   = false
...     | disj ψ₁ ψ₂ = φ ∈-∨ ψ₁ or φ ∈-∨ ψ₂

-- We assumed here that the formula is a disjunction and its right-associated.
rmDuplicates-∨ : Prop → Prop
rmDuplicates-∨ φ
  with disj-view φ
... | other _  = φ
... | disj φ₁ φ₂
    with φ₁ ∈-∨ φ₂
...    | true  = rmDuplicates-∨ φ₂
...    | false = φ₁ ∨ rmDuplicates-∨ φ₂

_∈-∧_ : Prop → Prop → Bool
φ ∈-∧ ψ
  with ⌊ eq (reorder-∨ φ ψ) ψ ⌋
...  | true = true
...  | false
     with conj-view ψ
...     | other .ψ   = false
...     | conj ψ₁ ψ₂ = φ ∈-∧ ψ₁ or φ ∈-∧ ψ₂


-- We assumed here that the formula is a disjunction and its right-associated.
rmDuplicates-∧∨ : Prop → Prop
rmDuplicates-∧∨ φ
  with conj-view φ
...  | other _    = rmDuplicates-∨ (right-assoc-∨ φ)
...  | conj φ₁ φ₂ = rmDuplicates-∧∨ φ₁ ∧ rmDuplicates-∧∨ φ₂

rmDuplicates-∧ : Prop → Prop
rmDuplicates-∧ φ
  with conj-view φ
...  | other _  = φ
...  | conj φ₁ φ₂
     with φ₁ ∈-∧ φ₂
...     | true  = rmDuplicates-∧ φ₂
...     | false = φ₁ ∧ rmDuplicates-∧ φ₂

rmDuplicatesCNF : Prop → Prop
rmDuplicatesCNF φ =
  rmDuplicates-∧ (rmDuplicates-∧∨ (right-assoc-∧ (cnf φ)))

thm-rmDuplicatesCNF
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ reorder-∧∨ φ (rmDuplicatesCNF φ)
thm-rmDuplicatesCNF {Γ}{φ} Γ⊢φ =
  thm-reorder-∧∨ Γ⊢φ (rmDuplicatesCNF φ)

-- φ ∨ ¬ φ deletions in a right-associated formula.
rmPairs-∨ : Prop → Prop
rmPairs-∨ φ
  with disj-view φ
... | other .φ   = φ
... | disj φ₁ φ₂
    with neg-view φ₁
rmPairs-∨ .(¬ φ ∨ φ₂) | disj .(¬ φ) φ₂ | neg φ
    with φ ∈-∨ φ₂
rmPairs-∨ .(¬ φ ∨ φ₂) | disj .(¬ φ) φ₂ | neg φ | true  = ⊤
rmPairs-∨ .(¬ φ ∨ φ₂) | disj .(¬ φ) φ₂ | neg φ | false
   with ⌊ eq (rmPairs-∨ φ₂) ⊤ ⌋
rmPairs-∨ .(¬ φ ∨ φ₂) | disj .(¬ φ) φ₂ | neg φ | false | false = ¬ φ ∨ rmPairs-∨ φ₂
rmPairs-∨ .(¬ φ ∨ φ₂) | disj .(¬ φ) φ₂ | neg φ | false | true  = ⊤
rmPairs-∨ .(φ₁ ∨ φ₂)  | disj φ₁ φ₂     | pos .φ₁
    with (¬ φ₁) ∈-∨ φ₂
rmPairs-∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ | pos .φ₁ | true  = ⊤
rmPairs-∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ | pos .φ₁ | false
  with ⌊ eq (rmPairs-∨ φ₂) ⊤ ⌋
rmPairs-∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ | pos .φ₁ | false | false = φ₁ ∨ rmPairs-∨ φ₂
rmPairs-∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ | pos .φ₁ | false | true  = ⊤

-- apply rmParis-∨ in the conjunctions.
rmPairs-∧∨ : Prop → Prop
rmPairs-∧∨ φ
  with conj-view φ
...  | other _    = rmPairs-∨ φ
...  | conj φ₁ φ₂ = rmPairs-∨ φ₁ ∧ rmPairs-∨ φ₂

data canonView : Prop  → Set where

-- Conjunction simplification cases.
  sconj₁ : (φ₁ : Prop)    → canonView (φ₁ ∧ ⊤)     -- φ ∧ ⊤ ==> φ.
  sconj₂ : (φ₁ : Prop)    → canonView (⊤ ∧ φ₁)     -- ⊤ ∧ φ ==> φ.
  sconj₃ : (φ₁ : Prop)    → canonView (φ₁ ∧ ⊥)     -- φ ∧ ⊥ ==> ⊥.
  sconj₄ : (φ₁ : Prop)    → canonView (⊥ ∧ φ₁)     -- ⊥ ∧ φ ==> ⊥.
  sconj₅ : (φ₁ φ₂ : Prop) → canonView (φ₁ ∧ φ₂)

-- Disjunction simplification cases.
  sdisj₁ : (φ₁ : Prop)    → canonView (φ₁ ∨ ⊤)     -- φ ∨ ⊤ ==> ⊤.
  sdisj₂ : (φ₁ : Prop)    → canonView (⊤ ∨ φ₁)     -- ⊤ ∨ φ ==> ⊤.
  sdisj₃ : (φ₁ : Prop)    → canonView (φ₁ ∨ ⊥)     -- φ ∨ ⊥ ==> φ.
  sdisj₄ : (φ₁ : Prop)    → canonView (⊥ ∨ φ₁)     -- ⊥ ∨ φ ==> φ.
  sdisj₅ : (φ₁ φ₂ : Prop) → canonView (φ₁ ∨ φ₂)

  ntop   : canonView (¬ ⊤)                         -- ¬ ⊤ ==> ⊥
  nbot   : canonView (¬ ⊥)                         -- ¬ ⊥ ==> ⊤
  other  : (φ₁ : Prop)    → canonView φ₁


canon-view : (φ : Prop) → canonView φ
canon-view (φ ∧ ⊤)  = sconj₁ _
canon-view (⊤ ∧ φ)  = sconj₂ _
canon-view (φ ∧ ⊥)  = sconj₃ _
canon-view (⊥ ∧ φ)  = sconj₄ _
canon-view (φ ∧ ψ)  = sconj₅ _ _
canon-view (φ ∨ ⊤)  = sdisj₁ _
canon-view (⊤ ∨ φ)  = sdisj₂ _
canon-view (φ ∨ ⊥)  = sdisj₃ _
canon-view (⊥ ∨ φ)  = sdisj₄ _
canon-view (φ ∨ φ₁) = sdisj₅ _ _
canon-view (¬ ⊤)    = ntop
canon-view (¬ ⊥)    = nbot
canon-view  φ       = other _


-- We assumed here that the formula is a disjunction and its right-associated.
canonicalize : Prop → Prop
canonicalize φ
  with canon-view φ
canonicalize .(φ₁ ∧ ⊤)  | sconj₁ φ₁ = canonicalize φ₁
canonicalize .(⊤ ∧ φ₁)  | sconj₂ φ₁ = canonicalize φ₁
canonicalize .(φ₁ ∧ ⊥)  | sconj₃ φ₁ = ⊥
canonicalize .(⊥ ∧ φ₁)  | sconj₄ φ₁ = ⊥
canonicalize .(φ₁ ∧ φ₂) | sconj₅ φ₁ φ₂
  with ⌊ eq (canonicalize φ₁) ⊤ ⌋
...  | true = canonicalize φ₂
...  | false
     with ⌊ eq (canonicalize φ₁) ⊥ ⌋
...     |  true = ⊥
...     |  false
        with ⌊ eq (canonicalize φ₂) ⊤ ⌋
...        | true = canonicalize φ₁
...        | false
           with  ⌊ eq (canonicalize φ₂) ⊥ ⌋
...           |  true  = ⊥
...           |  false
              with ⌊ eq φ₁ (¬ φ₂) ⌋
...              | true = ⊥
...              | false
                 with ⌊ eq (¬ φ₁) φ₂ ⌋
...                 | true  = ⊥
...                 | false = (canonicalize φ₁) ∧ (canonicalize φ₂)

canonicalize .(φ₁ ∨ ⊤)  | sdisj₁ φ₁ = ⊤
canonicalize .(⊤ ∨ φ₁)  | sdisj₂ φ₁ = ⊤
canonicalize .(φ₁ ∨ ⊥)  | sdisj₃ φ₁ = canonicalize φ₁
canonicalize .(⊥ ∨ φ₁)  | sdisj₄ φ₁ = canonicalize φ₁
canonicalize .(φ₁ ∨ φ₂) | sdisj₅ φ₁ φ₂
  with ⌊ eq (canonicalize φ₁) ⊤ ⌋
...  | true = ⊤
...  | false
     with ⌊ eq (canonicalize φ₁) ⊥ ⌋
...     | true = canonicalize φ₂
...     | false
        with ⌊ eq (canonicalize φ₂) ⊤ ⌋
...        | true = ⊤
...        | false
           with  ⌊ eq (canonicalize φ₂) ⊥ ⌋
...           | true  = canonicalize φ₁
...           | false = (canonicalize φ₁) ∨ (canonicalize φ₂)
canonicalize .(¬ ⊤)     | ntop = ⊥
canonicalize .(¬ ⊥)     | nbot = ⊤
canonicalize φ          | other .φ = φ


------------------------------------------------------------------------------
-- atp-canonicalize.
------------------------------------------------------------------------------

postulate
  atp-canonicalize
    : ∀ {Γ} {φ}
    → (φ′ : Prop)
    → Γ ⊢ φ
    → Γ ⊢ φ′
