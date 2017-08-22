------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Resolve inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ; suc; zero; _+_ )

module ATP.Metis.Rules.Resolve ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Data.Prop.Dec n                  using ( yes; no; ⌊_⌋ )
open import Data.Prop.Properties n           using ( eq; subst )
open import Data.Prop.Views n
  using ( DisjView; disj-view; disj; other)

open import Data.Prop.Theorems.Conjunction n using ( ∧-dmorgan₁ )
open import Data.Prop.Theorems.Disjunction n
  using ( ∨-comm; lem1; lem2; ∨-assoc₂; subst⊢∨₂; resolve₇)

open import Data.Bool                        using ( true; false )
open import Function                         using ( _$_; id; _∘_ )
open import Relation.Binary.PropositionalEquality using ( sym )

open import ATP.Metis.Rules.Reordering n
  using ( reorder-∨; thm-reorder-∨; tdisj-view; TDisjView; case₁; case₂; other)

------------------------------------------------------------------------------

-- Resolution using reorder-∨.

helper-resolve : Prop → Prop
helper-resolve φ
  with tdisj-view φ
helper-resolve .((φ₁ ∨ φ₂) ∨ φ₃) | case₁ φ₁ φ₂ φ₃
  with ⌊ eq φ₂ (¬ φ₁) ⌋
...    | true  = φ₃
...    | false = (φ₁ ∨ φ₂) ∨ φ₃
helper-resolve .(φ₁ ∨ φ₂)      | case₂ φ₁ φ₂ = φ₁ ∨ φ₂
helper-resolve φ               | other .φ    = φ

postulate
  thm-helper-resolve
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ helper-resolve φ

-- thm-helper-resolve {Γ} {φ} Γ⊢φ
--   with tdisj-view φ
-- thm-helper-resolve {Γ} {.((φ₁ ∨ φ₂) ∨ φ₃)} Γ⊢φ | case₁ φ₁ φ₂ φ₃
--   with eq φ₂ (¬ φ₁)
-- ...    | yes φ₂≡¬φ₁ = {!!}
-- ...    | no _       = Γ⊢φ
-- thm-helper-resolve {Γ} {.(φ₁ ∨ φ₂)} Γ⊢φ        | case₂ φ₁ φ₂ = Γ⊢φ
-- thm-helper-resolve {Γ} {_} Γ⊢φ                 | other _     = Γ⊢φ



resolve : Prop → Prop → Prop → Prop → Prop
resolve goal l φ₁ φ₂ = helper-resolve (reorder-∨ (φ₁ ∨ φ₂) ((l ∨ (¬ l)) ∨ goal))

atp-resolve
  : ∀ {Γ} {φ₁ φ₂}
  → (ψ : Prop)  -- goal
  → (l : Prop)   -- literal
  → Γ ⊢ φ₁       -- left side
  → Γ ⊢ φ₂       -- right side
  → Γ ⊢ resolve ψ l φ₁ φ₂       -- goal theorem

atp-resolve {_} {_}{φ₂} ψ l Γ⊢φ₁ Γ⊢φ₂ =
  thm-helper-resolve (thm-reorder-∨ (∨-intro₁ φ₂ Γ⊢φ₁) (l ∨ ¬ l ∨ ψ))
