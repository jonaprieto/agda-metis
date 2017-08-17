------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Resolve inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Resolve ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Data.Prop.Dec n                  using ( yes; no; ⌊_⌋ )
open import Data.Prop.Properties n           using ( eq )
open import Data.Prop.Views n
  using ( DisjView; disj-view; disj; other)

open import Data.Prop.Theorems.Conjunction n using ( ∧-dmorgan₁ )
open import Data.Prop.Theorems.Disjunction n using ( ∨-comm; lem1; lem2 )

open import Data.Bool                        using ( true; false )
open import Function                         using ( _$_; id; _∘_  )

------------------------------------------------------------------------------

atp-resolve₀ : ∀ {Γ} {L C D}
             → Γ ⊢ L ∨ C → Γ ⊢ ¬ L ∨ D
             → Γ ⊢ C ∨ D

atp-resolve₀ {Γ} {L}{C}{D} seq₁ seq₂ =
  lem1 $
    ∧-dmorgan₁ $
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


resolve : Prop → Prop → Prop → Prop → Prop
resolve φ′ l φ₁ φ₂ = φ′

postulate
  atp-resolve
    : ∀ {Γ} {φ₁ φ₂}
    → (φ′ : Prop)
    → (l : Prop)
    → Γ ⊢ φ₁
    → Γ ⊢ φ₂
    → Γ ⊢ φ′

------------------------------------------------------------------------------
-- Reordering of a disjunction.
------------------------------------------------------------------------------

reorder-∨ : Prop → Prop → Prop
reorder-∨ φ ψ
  with disj-view φ
...  | other _  = φ
...  | disj φ₁ φ₂
     with disj-view ψ
...     | other _    = φ
...     | disj ψ₁ ψ₂
        with ⌊ eq φ₁ ψ₁ ⌋ | ⌊ eq φ₁ ψ₂ ⌋ | ⌊ eq φ₂ ψ₁ ⌋ | ⌊ eq φ₂ ψ₂ ⌋
...        | true | _    | _    | _    = φ₁ ∨ (reorder-∨ φ₂ ψ₂)
...        | _    | true | _    | _    = φ₁ ∨ (reorder-∨ φ₂ ψ₁)
...        | _    | _    | true | _    = φ₂ ∨ (reorder-∨ φ₁ ψ₂)
...        | _    | _    | _    | true = φ₂ ∨ (reorder-∨ φ₁ ψ₁)
...        | _    | _    | _    | _    = (reorder-∨ φ ψ₁) ∨ (reorder-∨ φ ψ₂)

thm-s₁ : ∀ {Γ} {φ₁ φ₂} → Γ ⊢ φ₁ ∨ φ₂ → (ψ : Prop) → Γ , φ₁ ⊢ reorder-∨ (φ₁ ∨ φ₂) ψ
thm-s₁ {Γ} {φ₁}{φ₂} Γ⊢φ ψ
  with disj-view ψ
...     | other _    = weaken φ₁ Γ⊢φ
...     | disj ψ₁ ψ₂
  with ⌊ eq φ₁ ψ₁ ⌋ | ⌊ eq φ₁ ψ₂ ⌋ | ⌊ eq φ₂ ψ₁ ⌋ | ⌊ eq φ₂ ψ₂ ⌋
...        | true | _    | _    | _    = {!!} -- ∨-intro₁ (reorder-∨ φ₂ ψ₂) (assume {Γ = Γ} φ₁)
...        | _    | true | _    | _    = {!!}
...        | _    | _    | true | _    = {!!}
...        | _    | _    | _    | true = {!!}
...        | _    | _    | _    | _    = {!!}

thm-s₂ : ∀ {Γ} {p q} → Γ ⊢ p ∨ q → (ψ : Prop) → Γ , q ⊢ reorder-∨ (p ∨ q) ψ
thm-s₂ = {!!}


thm-reorder-∨
  : ∀ {Γ} {p q}
  → (ψ : Prop)
  → Γ ⊢ p ∨ q
  → Γ ⊢ reorder-∨ (p ∨ q) ψ

thm-reorder-∨ {Γ} {φ} ψ Γ⊢φ  =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (thm-s₁ Γ⊢φ ψ)
        (thm-s₂ Γ⊢φ ψ)))
    Γ⊢φ




