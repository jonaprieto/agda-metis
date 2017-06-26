------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Canonicalize inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ; suc; zero )

module ATP.Metis.Rules.Canonicalize ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool.Base
  using    ( true; false )
  renaming ( _∨_ to _or_ )

open import Data.Prop.Dec n                  using ( ⌊_⌋ ; yes ; no )
open import Data.Prop.Properties n           using ( eq ; subst )
open import Data.Prop.Syntax n
open import Data.Prop.Theorems n
open import Data.Prop.NormalForms n

open import Function                         using ( _$_; id ; _∘_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym ; trans)

------------------------------------------------------------------------------


data canonView : Prop  → Set where

-- Conjunction simplification cases.
  sconj₁ : (φ₁ : Prop)    → canonView (φ₁ ∧ ⊤)     -- φ ∧ ⊤ ==> φ.
  sconj₂ : (φ₁ : Prop)    → canonView (⊤ ∧ φ₁)     -- ⊤ ∧ φ ==> φ.
  sconj₃ : (φ₁ : Prop)    → canonView (φ₁ ∧ ⊥)     -- φ ∧ ⊥ ==> ⊥.
  sconj₄ : (φ₁ : Prop)    → canonView (⊥ ∧ φ₁)     -- ⊥ ∧ φ ==> ⊥.
  sconj₅ : (φ₁ φ₂ : Prop) → canonView (φ₁ ∧ φ₂)    -- φ ∧ φ ==> φ.
  sconj₆ : (φ₁ φ₂ : Prop) → canonView (φ₁ ∧ φ₂)    -- φ ∧ ¬ φ ==> ⊥.
  sconj₇ : (φ₁ φ₂ : Prop) → canonView (φ₁ ∧ φ₂)    -- ¬ φ ∧ φ ==> ⊥.
  sconj₈ : (φ₁ φ₂ : Prop) → canonView (φ₁ ∧ φ₂)

-- Disjunction simplification cases.
  sdisj₁ : (φ₁ : Prop)    → canonView (φ₁ ∨ ⊤)     -- φ ∨ ⊤ ==> φ.
  sdisj₂ : (φ₁ : Prop)    → canonView (⊤ ∨ φ₁)     -- ⊤ ∨ φ ==> φ.
  sdisj₃ : (φ₁ : Prop)    → canonView (φ₁ ∨ ⊥)     -- φ ∨ ⊥ ==> φ.
  sdisj₄ : (φ₁ : Prop)    → canonView (⊥ ∨ φ₁)     -- ⊥ ∨ φ ==> φ.
  sdisj₅ : (φ₁ φ₂ : Prop) → canonView (φ₁ ∨ φ₂)    -- φ ∨ φ ==> φ.
  sdisj₆ : (φ₁ φ₂ : Prop) → canonView (φ₁ ∨ φ₂)    -- φ ∨ ¬ φ ==> ⊤.
  sdisj₇ : (φ₁ φ₂ : Prop) → canonView (φ₁ ∨ φ₂)    -- ¬ φ ∨ φ ==> ⊤.
  sdisj₈ : (φ₁ φ₂ : Prop) → canonView (φ₁ ∨ φ₂)

  nconj  : (φ₁ φ₂ : Prop) → canonView (¬ (φ₁ ∧ φ₂))
  ndisj  : (φ₁ φ₂ : Prop) → canonView (¬ (φ₁ ∨ φ₂))
  nneg   : (φ₁ : Prop)    → canonView (¬ ¬ φ₁)
  ntop   : canonView (¬ ⊤)
  nbot   : canonView (¬ ⊥)
  other  : (φ₁ : Prop)    → canonView φ₁


canon-view : (φ : Prop) → canonView φ

canon-view (φ ∧ ⊤) = sconj₁ _
canon-view (⊤ ∧ φ) = sconj₂ _
canon-view (φ ∧ ⊥) = sconj₃ _
canon-view (⊥ ∧ φ) = sconj₄ _
canon-view (φ ∧ φ₁)
  with ⌊ eq φ φ₁ ⌋ | ⌊ eq φ (¬ φ₁) ⌋ | ⌊ eq (¬ φ) φ₁ ⌋
...  | true  | _     | _    = sconj₅ _ _
...  | _     | true  | _    = sconj₆ _ _
...  | _     | _     | true = sconj₇ _ _
...  | _     | _     | _    = sconj₈ _ _

canon-view (φ ∨ ⊤) = sdisj₁ _
canon-view (⊤ ∨ φ) = sdisj₂ _
canon-view (φ ∨ ⊥) = sdisj₃ _
canon-view (⊥ ∨ φ) = sdisj₄ _
canon-view (φ ∨ φ₁)
  with ⌊ eq φ φ₁ ⌋ | ⌊ eq φ (¬ φ₁) ⌋ | ⌊ eq (¬ φ) φ₁ ⌋
...  | true  | _     | _    = sdisj₅ _ _
...  | _     | true  | _    = sdisj₆ _ _
...  | _     | _     | true = sdisj₇ _ _
...  | _     | _     | _    = sdisj₈ _ _

canon-view (¬ ⊤)        = ntop
canon-view (¬ ⊥)        = nbot
canon-view (¬ (φ ∧ φ₁)) = nconj φ φ₁
canon-view (¬ (φ ∨ φ₁)) = ndisj φ φ₁
canon-view (¬ (¬ φ))    = nneg φ
canon-view  φ           = other _

canon : ℕ → Prop → Prop
canon zero φ    = φ
canon (suc n) φ with canon-view φ
... | sconj₁ φ₁    = canon n φ₁
... | sconj₂ φ₁    = canon n φ₁
... | sconj₃ _     = ⊥
... | sconj₄ _     = ⊥
... | sconj₅ φ₁ _  = canon n φ₁
... | sconj₆ φ₁ φ₂ = ⊥
... | sconj₇ φ₁ φ₂ = ⊥
... | sconj₈ φ₁ φ₂ = canon n (canon n φ₁ ∧ canon n φ₂)

... | sdisj₁ φ₁    = canon n φ₁
... | sdisj₂ φ₁    = canon n φ₁
... | sdisj₃ φ₁    = canon n φ₁
... | sdisj₄ φ₁    = canon n φ₁
... | sdisj₅ φ₁ φ₂ = canon n φ₁
... | sdisj₆ φ₁ φ₂ = ⊤
... | sdisj₇ φ₁ φ₂ = ⊤
... | sdisj₈ φ₁ φ₂ = canon n (canon n φ₁ ∨ canon n φ₂)

... | nconj φ₁ φ₂  = φ₂
... | ndisj φ₁ φ₂  = φ₂
... | nneg φ₁      = canon n φ₁
... | ntop         = ⊤
... | nbot         = ⊤
... | other .φ     = φ

snnf : Prop → Prop
snnf φ = (canon (ubsizetree (nnf φ)) (nnf φ))

canonicalize_to_ : Prop → Prop →  Prop
canonicalize φ to φ₁
  with ⌊ eq φ₁ (snnf φ) ⌋
...  | true  = snnf φ
...  | false with ⌊ eq φ₁ (dist′ (snnf φ)) ⌋
...          | true = dist′ (snnf φ)
...          | false  with ⌊ eq φ₁ (dist (snnf φ)) ⌋
...                      | true = dnf (dist φ)
...                      | false = φ₁


-- ... | z = ?
--      where
--        φnnf   = canon (ubsizetree φnnf) φnnf
--        φdnf   = dist φnnf
--        φcnf   = dist′ φnnf


------------------------------------------------------------------------------
-- atp-canonicalize.
------------------------------------------------------------------------------

postulate
  atp-canonicalize
    : ∀ {Γ} {φ}
    → (φ′ : Prop)
    → Γ ⊢ φ
    → Γ ⊢ canonicalize φ to φ′
