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

open import Data.Bool                             using ( true; false )
open import Function                              using ( _$_; id; _∘_ )
open import Relation.Binary.PropositionalEquality using ( sym )

open import ATP.Metis.Rules.Reordering n

------------------------------------------------------------------------------

-- Resolution using reorder-∨.
data ResView : PropFormula → Set where
  case₁ : (φ₁ φ₂ φ₃ φ₄ : PropFormula) → ResView ((φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄))
  other : (φ : PropFormula)           → ResView φ

res-view : (φ : PropFormula) → ResView φ
res-view ((φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄)) = case₁ _ _ _ _
res-view φ                       = other _

rsol : PropFormula → PropFormula
rsol φ
  with res-view φ
rsol φ                        | other .φ    = φ
rsol .((φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄)) | case₁ φ₁ φ₂ φ₃ φ₄
  with ⌊ eq φ₃ (¬ φ₁) ⌋
...    | false = (φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄)
...    | true
       with ⌊ eq φ₄ φ₂ ⌋
...       | true  = φ₂
...       | false = φ₂ ∨ φ₄

lem-rsol
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ rsol φ

lem-rsol {Γ} {φ} Γ⊢φ
  with res-view φ
lem-rsol {Γ} {_} Γ⊢φ                        | other _     = Γ⊢φ
lem-rsol {Γ} {.((φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄))} Γ⊢φ | case₁ φ₁ φ₂ φ₃ φ₄
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
...       | no _   = helper
          where
            helper : Γ ⊢ φ₂ ∨ φ₄
            helper = resolve₀
              (∧-proj₁ Γ⊢φ)
              (subst⊢∨₁
                (⇒-intro (subst p₁ (assume {Γ = Γ} φ₃)))
                (∧-proj₂ Γ⊢φ))

{-
  The best scenario for resolve rule:

           φ₁                      ϕ₂
       ──────── reorder-∨     ────────── reorder-∨
        l ∨ goal               ¬ l ∨ goal
   ──────────────────────────────────────────  resolve φ₁ φ₂ l goal
                        goal

-}

resolve : PropFormula → PropFormula → PropFormula → PropFormula → PropFormula
resolve φ₁ φ₂ l goal =
  rsol $ (reorder-∨ φ₁ $ l ∨ goal) ∧ (reorder-∨ φ₂ $ ¬ l ∨ goal)
thm-resolve
  : ∀ {Γ} {φ₁ φ₂}
  → (ψ : PropFormula)   -- goal
  → (l : PropFormula)   -- literal
  → Γ ⊢ φ₁              -- left side
  → Γ ⊢ φ₂              -- right side
  → Γ ⊢ resolve φ₁ φ₂ l ψ

thm-resolve {Γ} {φ₁}{φ₂} ψ l Γ⊢φ₁ Γ⊢φ₂ =
  lem-rsol
    (∧-intro
      (thm-reorder-∨ Γ⊢φ₁ (l ∨ ψ))
      (thm-reorder-∨ Γ⊢φ₂ (¬ l ∨ ψ)))
