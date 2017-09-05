------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Resolve inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ; suc; zero; _+_ )

module ATP.Metis.Rules.Resolve ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Syntax n
open import Data.PropFormula.Dec n                  using ( yes; no; ⌊_⌋ )
open import Data.PropFormula.Properties n           using ( eq; subst )
open import Data.PropFormula.NormalForms n          using ( cnf; thm-cnf )
open import Data.PropFormula.Views n
  using ( DisjView; disj-view; disj; other)

open import Data.PropFormula.Theorems.Conjunction n using ( ∧-dmorgan₁ )
open import Data.PropFormula.Theorems.Disjunction n
  using ( ∨-comm; lem1; lem2; ∨-assoc₂; subst⊢∨₁; resolve₀)

open import Data.Bool                        using ( true; false )
open import Function                         using ( _$_; id; _∘_ )
open import Relation.Binary.PropositionalEquality using ( sym )

open import ATP.Metis.Rules.Reordering n
  using ( reorder-∨; thm-reorder-∨; reorder-∧∨; thm-reorder-∧∨)

------------------------------------------------------------------------------

-- Resolution using reorder-∨.
data ResView : PropFormula → Set where
  case₁ : (φ₁ φ₂ φ₃ φ₄ : PropFormula) → ResView ((φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄))
  other : (φ : PropFormula)           → ResView φ

res-view : (φ : PropFormula) → ResView φ
res-view ((φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄)) = case₁ _ _ _ _
res-view φ                       = other _


helper-resolve : PropFormula → PropFormula
helper-resolve φ
  with res-view φ
helper-resolve φ                        | other .φ    = φ
helper-resolve .((φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄)) | case₁ φ₁ φ₂ φ₃ φ₄
  with ⌊ eq φ₃ (¬ φ₁) ⌋
...    | false = (φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄)
...    | true
       with ⌊ eq φ₄ φ₂ ⌋
...       | true  = φ₂
...       | false = φ₂ ∨ φ₄


thm-helper-resolve
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ helper-resolve φ

thm-helper-resolve {Γ} {φ} Γ⊢φ
  with res-view φ
thm-helper-resolve {Γ} {_} Γ⊢φ                        | other _     = Γ⊢φ
thm-helper-resolve {Γ} {.((φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄))} Γ⊢φ | case₁ φ₁ φ₂ φ₃ φ₄
  with eq φ₃ (¬ φ₁)
...    | no  _ = Γ⊢φ
...    | yes p₁
       with eq φ₄ φ₂
...       | yes p₂ =
            ⇒-elim
              (⇒-intro
                (∨-elim {Γ = Γ}
                  (assume {Γ = Γ} φ₂)
                  (subst p₂ (assume {Γ = Γ} φ₄))))
              (resolve₀
                (∧-proj₁ Γ⊢φ)
                (subst⊢∨₁
                  (⇒-intro (subst p₁ (assume {Γ = Γ} φ₃)))
                  (∧-proj₂ Γ⊢φ)))
...       | no _   = helper -- TODO: this is above (repeated)
          where
            helper : Γ ⊢ φ₂ ∨ φ₄
            helper = resolve₀
              (∧-proj₁ Γ⊢φ)
              (subst⊢∨₁
                (⇒-intro (subst p₁ (assume {Γ = Γ} φ₃)))
                (∧-proj₂ Γ⊢φ))


resolve : PropFormula → PropFormula → PropFormula → PropFormula → PropFormula
resolve goal l φ₁ φ₂ =
  helper-resolve $
     (reorder-∨ φ₁ $ l ∨ goal)
   ∧ (reorder-∨ φ₂ $ ¬ l ∨ goal)

atp-resolve
  : ∀ {Γ} {φ₁ φ₂}
  → (ψ : PropFormula)   -- goal
  → (l : PropFormula)   -- literal
  → Γ ⊢ φ₁       -- left side
  → Γ ⊢ φ₂       -- right side
  → Γ ⊢ resolve ψ l φ₁ φ₂

atp-resolve {Γ} {φ₁}{φ₂} ψ l Γ⊢φ₁ Γ⊢φ₂ =
  thm-helper-resolve
    (∧-intro
      (thm-reorder-∨ Γ⊢φ₁ (l ∨ ψ))
      (thm-reorder-∨ Γ⊢φ₂ (¬ l ∨ ψ)))
