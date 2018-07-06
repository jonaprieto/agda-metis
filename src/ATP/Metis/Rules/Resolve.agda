------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Resolve inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ; suc; zero; _+_ )

module ATP.Metis.Rules.Resolve { n : ℕ } where

------------------------------------------------------------------------------

open import ATP.Metis.Synonyms
open import ATP.Metis.Rules.Reordering
open import ATP.Metis.Rules.Simplify

open import Data.PropFormula.Syntax n
open import Data.PropFormula.Dec n         using ( yes; no; ⌊_⌋ )
open import Data.PropFormula.Properties n         using ( eq; subst )

open import Data.PropFormula.Theorems.Classical n
open import Data.PropFormula.Theorems.Disjunction n
   using ( subst⊢∨₁; resolve₀; ∨-comm )

open import Data.Bool                             using ( true; false )
open import Relation.Binary.PropositionalEquality using ( sym )

------------------------------------------------------------------------------

{-
  The spirit of the resolve rule is to perform resolution
  in propositional logic:

        ℓ ∨ goal               ¬ ℓ ∨ goal
   ──────────────────────────────────────────  resolve φ₁ φ₂ ℓ goal
                     goal*

  The resulting formula, goal*, is a simplification
  (See the simplify rule section in the documentation).
-}



{- The version of resolve presented in the following is based on the
   simplify rule, which it means the `original-resolve` function
   (original resolve) presented later are completely different
   functions.  Nevertheless, for the reconstruction, both serve the
   same purpose*, that is, to simplify while applying resolution.  -}

-- Def.
resolve :  Premise → Premise → Lit → Conclusion → PropFormula
resolve φ₁ φ₂ ℓ ψ = simplify (φ₁ ∧ φ₂) (¬ ℓ ∨ ℓ) ψ

-- Theorem.
resolve-thm
  : ∀ {Γ} {φ₁ φ₂ : Premise}
  → (ψ : Conclusion)
  → (ℓ : Lit)
  → Γ ⊢ φ₁
  → Γ ⊢ φ₂
  → Γ ⊢ resolve φ₁ φ₂ ℓ ψ

-- Proof.
resolve-thm ψ ℓ Γ⊢φ₁ Γ⊢φ₂ = simplify-thm ψ (∧-intro Γ⊢φ₁ Γ⊢φ₂) (∨-comm PEM)
--------------------------------------------------------------------------- ∎

---------------------------------------------------------------------------
-- Alternative definition.
---------------------------------------------------------------------------

{- To maintain consistency with the master thesis that first presents
  the reconstruction, we keep maintaining the following version.
  However, we are not using the following version. It's computational
  more expensive that the one presented above with the `resolve`
  function. -}

-- [ DEPRECATED]
-- Resolution using reorder-∨.
data resCases : PropFormula → Set where
  case₁ : (φ₁ φ₂ φ₃ φ₄ : PropFormula) → resCases ((φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄))
  other : (φ : PropFormula)           → resCases φ

rsol-cases : (φ : PropFormula) → resCases φ
rsol-cases ((φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄)) = case₁ _ _ _ _
rsol-cases φ                       = other _

-- [ DEPRECATED]
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

-- [ DEPRECATED]
-- Lemma.
rsol-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ rsol φ

-- [ DEPRECATED]
-- Proof.
rsol-lem {φ = φ} Γ⊢φ
  with rsol-cases φ
rsol-lem                               Γ⊢φ | other _ = Γ⊢φ
rsol-lem {Γ}{.((φ₁ ∨ φ₂) ∧ (φ₃ ∨ φ₄))} Γ⊢φ | case₁ φ₁ φ₂ φ₃ φ₄
  with eq φ₃ (¬ φ₁)
...    | no  _ = Γ⊢φ
...    | yes p₁
       with eq φ₄ φ₂
...       | yes p₂ =
            ⊃-elim
              (⊃-intro
                (∨-elim
                  (assume φ₂)
                  (subst p₂ (assume φ₄))))
              (resolve₀
                (∧-proj₁ Γ⊢φ)
                (subst⊢∨₁
                  (⊃-intro (subst p₁ (assume φ₃)))
                  (∧-proj₂ Γ⊢φ)))
...       | no _   = helper
          where
            helper : Γ ⊢ φ₂ ∨ φ₄
            helper = resolve₀
              (∧-proj₁ Γ⊢φ)
              (subst⊢∨₁
                (⊃-intro (subst p₁ (assume φ₃)))
                (∧-proj₂ Γ⊢φ))
--------------------------------------------------------------------------- ∎

-- [ DEPRECATED]
{-
           φ₁                      ϕ₂
       ──────── reorder-∨     ────────── reorder-∨
        ℓ ∨ goal               ¬ ℓ ∨ goal
   ──────────────────────────────────────────  resolve φ₁ φ₂ ℓ goal
                        goal
-}


-- [ DEPRECATED]
-- Def.
original-resolve : Premise → Premise → Lit → Conclusion → PropFormula
original-resolve φ₁ φ₂ ℓ ψ =
  rsol ((reorder-∨ φ₁ (ℓ ∨ ψ)) ∧ (reorder-∨ φ₂ (¬ ℓ ∨ ψ)))

-- [ DEPRECATED]
-- Theorem.
original-resolve-thm
  : ∀ {Γ} {φ₁ φ₂ : Premise}
  → (ψ : Conclusion)
  → (ℓ : Lit)
  → Γ ⊢ φ₁
  → Γ ⊢ φ₂
  → Γ ⊢ original-resolve φ₁ φ₂ ℓ ψ

-- Proof.
original-resolve-thm ψ ℓ Γ⊢φ₁ Γ⊢φ₂ =
  rsol-lem
    (∧-intro
      (reorder-∨-lem Γ⊢φ₁ (ℓ ∨ ψ))
      (reorder-∨-lem Γ⊢φ₂ (¬ ℓ ∨ ψ)))
--------------------------------------------------------------------------- ∎
