------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Simplify inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Simplify ( n : ℕ ) where

------------------------------------------------------------------------------

open import ATP.Metis.Synonyms n
open import ATP.Metis.Rules.Normalization n public

open import Data.Bool.Base
  using    ( Bool; true; false )
  renaming ( _∨_ to _or_; _∧_ to _and_ )

open import Data.PropFormula.Dec n        using ( ⌊_⌋; yes; no )
open import Data.PropFormula.Properties n using ( eq ; subst )
open import Data.PropFormula.Syntax n

open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym )

------------------------------------------------------------------------------

data reduceCases : PropFormula → Set where
  case-conj : (φ₁ φ₂ : PropFormula) → reduceCases (φ₁ ∧ φ₂)
  case-disj : (φ₁ φ₂ : PropFormula) → reduceCases (φ₁ ∨ φ₂)
  case-lit  : (φ : PropFormula)     → reduceCases φ
  other     : (φ : PropFormula)     → reduceCases φ

reduce-cases : (φ : PropFormula) → reduceCases φ
reduce-cases (Var _)   = case-lit _
reduce-cases ⊤         = case-lit _
reduce-cases ⊥         = case-lit _
reduce-cases (¬ Var _) = case-lit _
reduce-cases (¬ ⊤)     = case-lit _
reduce-cases (¬ ⊥)     = case-lit _
reduce-cases (x ∧ x₁)  = case-conj _ _
reduce-cases (x ∨ x₁)  = case-disj _ _
reduce-cases φ         = other _

-- Def.
reduce-ℓ : PropFormula → Lit → PropFormula
reduce-ℓ φ ℓ
  with reduce-cases φ
...  | case-conj φ₁ φ₂ = simplify-∧ (reduce-ℓ φ₁ ℓ ∧ reduce-ℓ φ₂ ℓ)
...  | case-disj φ₁ φ₂ = simplify-∨ (reduce-ℓ φ₁ ℓ ∨ reduce-ℓ φ₂ ℓ)
...  | case-lit .φ
     with eq ℓ (nnf (¬ φ))
...     | yes _ = ⊥
...     | no  _ = φ
reduce-ℓ φ ℓ | other .φ = φ

-- Lemma.
reduce-ℓ-lem
  : ∀ {Γ} {φ ℓ}
  → Γ ⊢ φ
  → Γ ⊢ ℓ
  → Γ ⊢ reduce-ℓ φ ℓ

-- Proof.
reduce-ℓ-lem {Γ}{φ}{ℓ} Γ⊢φ Γ⊢ℓ
  with reduce-cases φ
...  | case-conj φ₁ φ₂ =
  simplify-∧-lem
    (∧-intro
      (reduce-ℓ-lem (∧-proj₁ Γ⊢φ) Γ⊢ℓ)
      (reduce-ℓ-lem (∧-proj₂ Γ⊢φ) Γ⊢ℓ))
...  | case-disj φ₁ φ₂ =
  simplify-∨-lem
    (⊃-elim
      (⊃-intro
        (∨-elim {Γ = Γ}
          (∨-intro₁ (reduce-ℓ φ₂ ℓ)
            (reduce-ℓ-lem (assume {Γ = Γ} φ₁) (weaken φ₁ Γ⊢ℓ)))
          (∨-intro₂ (reduce-ℓ φ₁ ℓ)
            (reduce-ℓ-lem (assume {Γ = Γ} φ₂) (weaken φ₂ Γ⊢ℓ)))))
      Γ⊢φ)
...  | case-lit .φ
     with eq ℓ (nnf (¬ φ))
...     | yes p₁ = ¬-elim (from-nnf-lem (subst p₁ Γ⊢ℓ)) Γ⊢φ
...     | no  _  = Γ⊢φ
reduce-ℓ-lem Γ⊢φ _ | other _ = Γ⊢φ
---------------------------------------------------------------------------- ∎


-- Def.
simplify : Premise → Premise → Conclusion → PropFormula
simplify φ₁ φ₂ ψ
  with eq φ₁ ψ
... | yes _ = ψ
... | no  _
  with eq φ₁ ⊥
... | yes _ = ψ
... | no  _
  with eq φ₂ ψ
... | yes _ = ψ
... | no _
  with eq φ₂ ⊥
... | yes _ = ψ
simplify φ₁ φ₂ ψ | no _ | no _ | no _ | no _
 with reduce-cases φ₂
... | case-conj φ₂₁ φ₂₂ = simplify (simplify φ₁ φ₂₁ ψ) φ₂₂ ψ
... | case-disj φ₂₁ φ₂₂ = simplify-∨ (simplify φ₁ φ₂₁ ψ ∨ simplify φ₁ φ₂₂ ψ)
... | case-lit ℓ        = reduce-ℓ φ₁ ℓ
... | other _           = φ₁

-- Theorem.
simplify-thm
  : ∀ {Γ} {φ₁ φ₂ : Premise}
  → (ψ : Conclusion)
  → Γ ⊢ φ₁
  → Γ ⊢ φ₂
  → Γ ⊢ simplify φ₁ φ₂ ψ

-- Proof.
simplify-thm {Γ}{φ₁}{φ₂} ψ Γ⊢φ₁ Γ⊢φ₂
  with eq φ₁ ψ
...  | yes φ₁≡ψ = subst φ₁≡ψ Γ⊢φ₁
...  | no  _
  with eq φ₁ ⊥
... | yes φ₁≡⊥ = ⊥-elim ψ (subst φ₁≡⊥ Γ⊢φ₁)
... | no  _
  with eq φ₂ ψ
...  | yes φ₂≡ψ = subst φ₂≡ψ Γ⊢φ₂
...  | no _
  with eq φ₂ ⊥
...  | yes φ₂≡⊥ = ⊥-elim ψ (subst φ₂≡⊥ Γ⊢φ₂)
simplify-thm {Γ}{φ₁}{φ₂} ψ Γ⊢φ₁ Γ⊢φ₂ | no _ | no _ | no _ | no _
  with reduce-cases φ₂
... | case-conj φ₂₁ φ₂₂ =
        simplify-thm ψ
          (simplify-thm  ψ Γ⊢φ₁ (∧-proj₁ Γ⊢φ₂)) (∧-proj₂ Γ⊢φ₂)
... | case-disj φ₂₁ φ₂₂ =
        simplify-∨-lem
          (⊃-elim
            (⊃-intro
              (∨-elim {Γ = Γ}
                (∨-intro₁ (simplify φ₁ φ₂₂ ψ )
                  (simplify-thm ψ (weaken φ₂₁ Γ⊢φ₁) (assume {Γ = Γ} φ₂₁)))
                (∨-intro₂ (simplify φ₁ φ₂₁ ψ)
                  (simplify-thm ψ (weaken φ₂₂ Γ⊢φ₁) (assume {Γ = Γ} φ₂₂)))))
            Γ⊢φ₂)
... | case-lit ℓ        = reduce-ℓ-lem Γ⊢φ₁ Γ⊢φ₂
... | other _           = Γ⊢φ₁
---------------------------------------------------------------------------- ∎
