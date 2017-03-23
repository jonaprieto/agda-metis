------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Resolve inference rule.
------------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module ATP.Metis.Inferences.Resolve (n : ℕ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Data.Prop.Dec n        using (yes ; no ; ⌊_⌋)
open import Data.Prop.Properties n using (eq)

open import Data.Prop.Theorems.Conjunction n using (∧-morgan₁)
open import Data.Prop.Theorems.Disjunction n using (∨-comm ; lem1 ; lem2)

open import Data.Bool using (true ; false)
open import Function  using (_$_ ; id ; _∘_ )

------------------------------------------------------------------------------

atp-resolve₀ : ∀ {Γ} {L C D}
             → Γ ⊢ L ∨ C → Γ ⊢ ¬ L ∨ D
             → Γ ⊢ C ∨ D

atp-resolve₀ {Γ} {L}{C}{D} seq₁ seq₂ =
  lem1 $
    ∧-morgan₁ $
      ¬-intro $
        ¬-elim
          (lem2 {Γ = Γ , ¬ C ∧ ¬ D} $
            ∧-intro
              (weaken (¬ C ∧ ¬ D) seq₂)
              (∧-proj₂ $ assume {Γ = Γ} $ ¬ C ∧ ¬ D))
          (lem2 $
            ∧-intro
              (weaken (¬ C ∧ ¬ D) seq₁)
              (∧-proj₁ $ assume {Γ = Γ} $ ¬ C ∧ ¬ D))


atp-resolve₁ : ∀ {Γ} {L C D }
             → Γ ⊢ C ∨ L → Γ ⊢ ¬ L ∨ D
             → Γ ⊢ C ∨ D

atp-resolve₁ = atp-resolve₀ ∘ ∨-comm


atp-resolve₂ : ∀ {Γ} {L C D }
             → Γ ⊢ L ∨ C → Γ ⊢ D ∨ ¬ L
             → Γ ⊢ C ∨ D

atp-resolve₂ seq₁ seq₂ = atp-resolve₀ seq₁ (∨-comm seq₂)


atp-resolve₃ : ∀ {Γ} {L C D }
             → Γ ⊢ C ∨ L → Γ ⊢ D ∨ ¬ L
             → Γ ⊢ C ∨ D

atp-resolve₃ {Γ} {L}{C}{D} seq₁ seq₂ =  atp-resolve₀ (∨-comm seq₁) (∨-comm seq₂)


atp-resolve₄ : ∀ {Γ} {L C}
             → Γ ⊢ ¬ L ∨ C → Γ ⊢ L
             → Γ ⊢ C

atp-resolve₄ {Γ} {L} {C} seq₁ seq₂ =
  ⇒-elim
    (⇒-intro $
      ∨-elim {Γ = Γ}
        (assume {Γ = Γ} C)
        (assume {Γ = Γ} C))
    (atp-resolve₀ {Γ = Γ} {L = L} {C = C} {D = C}
      (∨-intro₁ C seq₂)
      seq₁)

atp-resolve₅ : ∀ {Γ} {L C}
             → Γ ⊢ C ∨ ¬ L
             → Γ ⊢ L
             → Γ ⊢ C

atp-resolve₅ = atp-resolve₄ ∘ ∨-comm


atp-resolve₆ : ∀ {Γ} {L C}
             → Γ ⊢ C ∨ L → Γ ⊢ ¬ L
             → Γ ⊢ C

atp-resolve₆ {Γ} {L} {C} seq₁ seq₂ =
  ⇒-elim
    (⇒-intro $
      ∨-elim {Γ = Γ}
        (assume {Γ = Γ}  C)
        (assume {Γ = Γ} C))
    (atp-resolve₀ (∨-comm seq₁) (∨-intro₁ C seq₂))


atp-resolve₇ : ∀ {Γ} {L C}
             → Γ ⊢ L ∨ C → Γ ⊢ ¬ L
             → Γ ⊢ C

atp-resolve₇ {Γ} {L} {C} seq₁ seq₂ = atp-resolve₆ (∨-comm seq₁) seq₂


atp-resolve₈ : ∀ {Γ} {φ}
             → Γ ⊢ φ → Γ ⊢ ¬ φ
             → Γ ⊢ ⊥

atp-resolve₈ seq₁ seq₂ = ¬-elim seq₂ seq₁

atp-resolve₉ : ∀ {Γ} {φ}
             → Γ ⊢ ¬ φ → Γ ⊢ φ
             → Γ ⊢ ⊥

atp-resolve₉ = ¬-elim
