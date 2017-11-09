------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Resolve inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ; suc; zero; _+_ )

module ATP.Metis.Rules.Resolve ( n : ℕ ) where

------------------------------------------------------------------------------

open import ATP.Metis.Synonyms n
open import ATP.Metis.Rules.Reordering n

open import Data.PropFormula.Syntax n
open import Data.PropFormula.Dec n                  using ( yes; no; ⌊_⌋ )
open import Data.PropFormula.Properties n           using ( eq; subst )

open import Data.PropFormula.Theorems.Disjunction n
   using ( subst⊢∨₁; resolve₀ )

open import Data.Bool                             using ( true; false )
open import Relation.Binary.PropositionalEquality using ( sym )

------------------------------------------------------------------------------

-- Resolution using reorder-∨.
data resCases : PropFormula → Set where
  case₁ : (φ₁ φ₂ φ₃ φ₄ : PropFormula) → resCases ((φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄))
--  case₂ : (φ₁ φ₂ φ₃ : PropFormula)    → resCases ((φ₁ ∨ φ₂) ∧ φ₃)
  other : (φ : PropFormula)           → resCases φ

rsol-cases : (φ : PropFormula) → resCases φ
rsol-cases ((φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄)) = case₁ _ _ _ _
-- rsol-cases ((φ₁ ∨ φ₂) ∧ φ₃)        = case₂ _ _ _
rsol-cases φ                       = other _

-- Def.
rsol : PropFormula → PropFormula
rsol φ
  with rsol-cases φ
rsol φ                        | other .φ    = φ
rsol .((φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄)) | case₁ φ₁ φ₂ φ₃ φ₄
  with ⌊ eq φ₃ (¬ φ₁) ⌋
...    | false = (φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄)
...    | true
       with ⌊ eq φ₄ φ₂ ⌋
...       | true  = φ₂
...       | false = φ₂ ∨ φ₄
-- rsol .((φ₁ ∨ φ₂) ∧ φ₃) | case₂ φ₁ φ₂ φ₃
--  with ⌊ eq φ₃ (¬ φ₁) ⌋
-- ... | x = {!!}

postulate
  -- Lemma.
  rsol-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ rsol φ

{-
-- Proof.
rsol-lem {Γ} {φ} Γ⊢φ
  with rsol-cases φ
rsol-lem {Γ} {_} Γ⊢φ                        | other _     = Γ⊢φ
rsol-lem {Γ} {.((φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄))} Γ⊢φ | case₁ φ₁ φ₂ φ₃ φ₄
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
--------------------------------------------------------------------------- ■
-}

{-
           φ₁                      ϕ₂
       ──────── reorder-∨     ────────── reorder-∨
        ℓ ∨ goal               ¬ ℓ ∨ goal
   ──────────────────────────────────────────  resolve φ₁ φ₂ ℓ goal
                        goal
-}

-- Def.
resolve : Premise → Premise → Lit → Conclusion → PropFormula
resolve φ₁ φ₂ ℓ ψ =
  rsol ((reorder-∨ φ₁ (ℓ ∨ ψ)) ∧ (reorder-∨ φ₂ (¬ ℓ ∨ ψ)))

-- Theorem.
resolve-thm
  : ∀ {Γ} {φ₁ φ₂ : Premise}
  → (ψ : Conclusion)
  → (ℓ : Lit)
  → Γ ⊢ φ₁
  → Γ ⊢ φ₂
  → Γ ⊢ resolve φ₁ φ₂ ℓ ψ

-- Proof.
resolve-thm ψ ℓ Γ⊢φ₁ Γ⊢φ₂ =
  rsol-lem
    (∧-intro
      (reorder-∨-lem Γ⊢φ₁ (ℓ ∨ ψ))
      (reorder-∨-lem Γ⊢φ₂ (¬ ℓ ∨ ψ)))
--------------------------------------------------------------------------- ■
