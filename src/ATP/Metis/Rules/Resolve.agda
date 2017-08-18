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
open import Data.Prop.Theorems.Disjunction n using ( ∨-comm; lem1; lem2; ∨-assoc₂ )

open import Data.Bool                        using ( true; false )
open import Function                         using ( _$_; id; _∘_ )
open import Relation.Binary.PropositionalEquality using ( sym )

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

-- If ψ is a disjunction and φ is in ψ as a disjunct, we build from φ
-- the disjunction ψ.
build-∨ : Prop → Prop → Prop
build-∨ φ ψ
  with ⌊ eq φ ψ ⌋
... | true  = φ
... | false
    with disj-view ψ
...    | other _    = φ
...    | disj ψ₁ ψ₂
       with ⌊ eq (build-∨ φ ψ₁) ψ₁ ⌋
...       | true =(build-∨ φ ψ₁) ∨ ψ₂
...       | false
          with ⌊ eq (build-∨ φ ψ₂) ψ₂ ⌋
...          | true  = ψ₁ ∨ (build-∨ φ ψ₂)
...          | false = φ

thm-build-∨
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : Prop)
  → Γ ⊢ build-∨ φ ψ

thm-build-∨ {Γ} {φ} Γ⊢φ ψ
  with ⌊ eq φ ψ ⌋
... | true  = Γ⊢φ
... | false
    with disj-view ψ
...    | other _    = Γ⊢φ
...    | disj ψ₁ ψ₂
       with ⌊ eq (build-∨ φ ψ₁) ψ₁ ⌋
...       | true = ∨-intro₁ ψ₂ (thm-build-∨ Γ⊢φ ψ₁)
...       | false
          with ⌊ eq (build-∨ φ ψ₂) ψ₂ ⌋
...          | true  = ∨-intro₂ ψ₁ (thm-build-∨ Γ⊢φ ψ₂)
...          | false = Γ⊢φ


factor : Prop → Prop
factor φ
  with disj-view φ
... | other _ = φ
... | disj φ₁ φ₂
    with eq φ₁ (factor φ₂)
...    | yes _ = φ₁
...    | no _  = φ

thm-factor
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ factor φ
thm-factor {Γ}{φ} Γ⊢φ
  with disj-view φ
... | other _ = Γ⊢φ
... | disj φ₁ φ₂
  with eq φ₁ (factor φ₂)
...    | yes φ₁≡factorφ₂ =
         ⇒-elim
           (⇒-intro
             (∨-elim {Γ = Γ}
               (assume {Γ = Γ} φ₁)
               (subst
                 (sym φ₁≡factorφ₂)
                 (thm-factor $ assume {Γ = Γ} φ₂))))
           Γ⊢φ
...    | no _            = Γ⊢φ

helper-build : Prop → Prop → Prop
helper-build φ ψ
  with disj-view φ
... | other _    = build-∨ φ ψ
... | disj φ₁ φ₂ = factor (build-∨ φ₁ ψ ∨ helper-build φ₂ ψ)

thm-helper-build
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : Prop)
  → Γ ⊢ helper-build φ ψ

thm-helper-build {Γ} {φ} Γ⊢φ ψ
  with disj-view φ
... | other _    = thm-build-∨ Γ⊢φ ψ
... | disj φ₁ φ₂ =
        thm-factor
         (⇒-elim
            (⇒-intro
              (∨-elim {Γ = Γ}
                (∨-intro₁ (helper-build φ₂ ψ) (thm-build-∨ (assume {Γ = Γ} φ₁) ψ))
                (∨-intro₂ (build-∨ φ₁ ψ) (thm-helper-build (assume {Γ = Γ} φ₂) ψ))))
            Γ⊢φ)

data TDisjView : Prop → Set where
  case₁ : (φ₁ φ₂ φ₃ : Prop) → TDisjView ((φ₁ ∨ φ₂) ∨ φ₃)
  case₂ : (φ₁ φ₂ : Prop) → TDisjView (φ₁ ∨ φ₂)
  other : (φ : Prop) → TDisjView φ

tdisj-view : (φ : Prop) → TDisjView φ
tdisj-view ((φ₁ ∨ φ₂) ∨ φ₃) = case₁ _ _ _
tdisj-view (φ ∨ ψ)          = case₂ _ _
tdisj-view φ                = other _

right-assoc-∨ₙ : ℕ → Prop → Prop
right-assoc-∨ₙ zero φ  = φ
right-assoc-∨ₙ (suc n) φ
  with tdisj-view φ
right-assoc-∨ₙ (suc n₁) .(φ₁ ∨ φ₂ ∨ φ₃) | case₁ φ₁ φ₂ φ₃ = right-assoc-∨ₙ n₁ (φ₁ ∨ (φ₂ ∨ φ₃))
right-assoc-∨ₙ (suc n₁) .(φ ∨ ψ)        | case₂ φ ψ      = φ ∨ right-assoc-∨ₙ n₁ ψ
right-assoc-∨ₙ (suc n₁) φ               | other .φ       = φ

thm-right-assoc-∨ₙ
  : ∀ {Γ} {φ}
  → (n : ℕ)
  → Γ ⊢ φ
  → Γ ⊢ right-assoc-∨ₙ n φ

thm-right-assoc-∨ₙ {Γ} {φ} zero Γ⊢φ = Γ⊢φ
thm-right-assoc-∨ₙ {Γ} {φ} (suc n) Γ⊢φ
  with tdisj-view φ
thm-right-assoc-∨ₙ {Γ} {_} (suc n₁) Γ⊢φ | case₁ φ₁ φ₂ φ₃ = thm-right-assoc-∨ₙ n₁ (∨-assoc₂ Γ⊢φ)
thm-right-assoc-∨ₙ {Γ} {_} (suc n₁) Γ⊢φ | case₂ φ ψ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (right-assoc-∨ₙ n₁ ψ) (assume {Γ = Γ} φ))
        (∨-intro₂ φ (thm-right-assoc-∨ₙ n₁ (assume {Γ = Γ} ψ)))))
    Γ⊢φ
thm-right-assoc-∨ₙ {Γ} {_} (suc n₁) Γ⊢φ | other φ = Γ⊢φ

iter-right-assoc-∨ : Prop → ℕ
iter-right-assoc-∨ φ
  with tdisj-view φ
... | case₁ φ₁ φ₂ φ₃ = 1 + iter-right-assoc-∨ φ₂ + iter-right-assoc-∨ φ₃
... | case₂ φ₁ φ₂ = 1 + iter-right-assoc-∨ φ₂
... | other .φ = 1

right-assoc-∨ : Prop → Prop
right-assoc-∨ φ = right-assoc-∨ₙ (iter-right-assoc-∨ φ) φ

thm-right-assoc-∨
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ right-assoc-∨ φ
thm-right-assoc-∨ {Γ}{φ} Γ⊢φ = thm-right-assoc-∨ₙ (iter-right-assoc-∨ φ) Γ⊢φ

reorder-∨ : Prop → Prop → Prop
reorder-∨ φ ψ = helper-build (right-assoc-∨ φ) ψ

thm-reorder-∨
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : Prop)
  → Γ ⊢ reorder-∨ φ ψ
thm-reorder-∨ {Γ} {φ} Γ⊢φ ψ = thm-helper-build (thm-right-assoc-∨ Γ⊢φ) ψ
