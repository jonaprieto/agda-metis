------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Reordering module.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ; suc; zero; _+_ )

module ATP.Metis.Rules.Reordering ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Data.Prop.Dec n                  using ( yes; no; ⌊_⌋ )
open import Data.Prop.Properties n           using ( eq; subst )
open import Data.Prop.Views n
  using ( DisjView; disj-view; disj; other; conj-view; conj)

open import Data.Prop.Theorems.Conjunction n using ( ∧-dmorgan₁ )
open import Data.Prop.Theorems.Disjunction n
  using ( ∨-comm; lem1; lem2; ∨-assoc₂; subst⊢∨₂; resolve₇)

open import Data.Bool                        using ( true; false )
open import Function                         using ( _$_; id; _∘_ )
open import Relation.Binary.PropositionalEquality using ( sym )

open import ATP.Metis.Rules.Conjunct n
  using ( conjunct; atp-conjunct; Path; pick; proj₁; proj₂; ConjView )

open import Data.List.Base         using (_∷_; []; [_]; List; _∷ʳ_; _++_)

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Reordering of a disjunction.
------------------------------------------------------------------------------

build-∨ : Prop → Prop → Prop
build-∨ φ ψ
  with ⌊ eq φ ψ ⌋
... | true  = ψ
... | false
    with disj-view ψ
...    | other _    = φ
...    | disj ψ₁ ψ₂
       with ⌊ eq (build-∨ φ ψ₁) ψ₁ ⌋
...       | true = (build-∨ φ ψ₁) ∨ ψ₂ -- TODO : return ψ₁ and use subst theorem.
...       | false
          with ⌊ eq (build-∨ φ ψ₂) ψ₂ ⌋
...          | true  = ψ₁ ∨ (build-∨ φ ψ₂)  -- TODO: return ψ₂ and use subst theorem.
...          | false = φ

postulate
  thm-build-∨
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → (ψ : Prop)
    → Γ ⊢ build-∨ φ ψ

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
                (∨-intro₁ (helper-build φ₂ ψ)
                  (thm-build-∨ (assume {Γ = Γ} φ₁) ψ))
                (∨-intro₂ (build-∨ φ₁ ψ)
                  (thm-helper-build (assume {Γ = Γ} φ₂) ψ))))
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
right-assoc-∨ₙ (suc n₁) .((φ₁ ∨ φ₂) ∨ φ₃) | case₁ φ₁ φ₂ φ₃ =
  right-assoc-∨ₙ n₁ (φ₁ ∨ (φ₂ ∨ φ₃))
right-assoc-∨ₙ (suc n₁) .(φ ∨ ψ)        | case₂ φ ψ      =
  φ ∨ right-assoc-∨ₙ n₁ ψ
right-assoc-∨ₙ (suc n₁) φ               | other .φ       = φ

thm-right-assoc-∨ₙ
  : ∀ {Γ} {φ}
  → (n : ℕ)
  → Γ ⊢ φ
  → Γ ⊢ right-assoc-∨ₙ n φ

thm-right-assoc-∨ₙ {Γ} {φ} zero Γ⊢φ = Γ⊢φ
thm-right-assoc-∨ₙ {Γ} {φ} (suc n) Γ⊢φ
  with tdisj-view φ
thm-right-assoc-∨ₙ {Γ} {_} (suc n₁) Γ⊢φ | case₁ φ₁ φ₂ φ₃ =
  thm-right-assoc-∨ₙ n₁ (∨-assoc₂ Γ⊢φ)
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
... | case₁ φ₁ φ₂ φ₃ = 2 + iter-right-assoc-∨ φ₂ + iter-right-assoc-∨ φ₃
... | case₂ φ₁ φ₂ = 2 + iter-right-assoc-∨ φ₂
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

------------------------------------------------------------------------------
-- Reordering a conjunction.
------------------------------------------------------------------------------

reorder-∧ : Prop → Prop → Prop
reorder-∧ φ ψ
  with ⌊ eq φ ψ ⌋
...  | true = φ
...  | false
     with conj-view ψ
...     | other _  = conjunct φ ψ
...     | conj ψ₁ ψ₂
        with ⌊ eq (reorder-∧ φ ψ₁) ψ₁ ⌋
...        | false = φ
...        | true
           with ⌊ eq (reorder-∧ φ ψ₂) ψ₂ ⌋
...           | true  = ψ₁ ∧ ψ₂
...           | false = φ

thm-reorder-∧
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : Prop)
  → Γ ⊢ reorder-∧ φ ψ

thm-reorder-∧ {Γ} {φ} Γ⊢φ ψ
  with ⌊ eq φ ψ ⌋
... | true = Γ⊢φ
... | false
    with conj-view ψ
...    | other _  = atp-conjunct ψ Γ⊢φ
...    | conj ψ₁ ψ₂
       with eq (reorder-∧ φ ψ₁) ψ₁
...       | no  _  = Γ⊢φ
...       | yes p₁
          with eq (reorder-∧ φ ψ₂) ψ₂
...          | no  _  = Γ⊢φ
...          | yes p₂ =
                   ∧-intro
                   (subst p₁ (thm-reorder-∧ Γ⊢φ ψ₁))
                   (subst p₂ (thm-reorder-∧ Γ⊢φ ψ₂))


-- Reordering a conjunction of disjunctions.
-- Conversion from a CNF formula φ to another CNF formula ψ.

conjuct-∨ : Prop → Prop → Prop
conjuct-∨ φ ψ
  with ⌊ eq (reorder-∨ φ ψ) ψ ⌋
... | true  = ψ
... | false
    with conj-view ψ
conjuct-∨ φ .(ψ₁ ∧ ψ₂) | false | conj ψ₁ ψ₂
  with  ⌊ eq (conjuct-∨ φ ψ₁) ψ₁ ⌋
... | false = φ
... | true
  with  ⌊ eq (reorder-∨ φ ψ₂) ψ₂ ⌋
... | false = φ
... | true  = ψ₁ ∧ ψ₂
conjuct-∨ φ ψ          | false | other .ψ
  with conj-view φ
conjuct-∨ φ ψ          | false | other .ψ | (other .φ)  = φ
conjuct-∨ .(φ₁ ∧ φ₂) ψ | false | other .ψ | (conj φ₁ φ₂)
  with ⌊ eq (conjuct-∨ φ₁ ψ) ψ ⌋
... | true = ψ
... | false
    with  ⌊ eq (conjuct-∨ φ₂ ψ) ψ ⌋
... | true = ψ
... | false = φ₁ ∧ φ₂


thm-conjunct-∨
  : ∀ {Γ} {φ}
  → (ψ : Prop)
  → Γ ⊢ φ
  → Γ ⊢ conjuct-∨ φ ψ

thm-conjunct-∨ {Γ}{φ} ψ Γ⊢φ
  with eq (reorder-∨ φ ψ) ψ
... | yes p₁ = subst p₁ (thm-reorder-∨ Γ⊢φ ψ)
... | no _
    with conj-view ψ
thm-conjunct-∨ {Γ}{φ} .(ψ₁ ∧ ψ₂) Γ⊢φ | no _ | conj ψ₁ ψ₂
  with  eq (conjuct-∨ φ ψ₁) ψ₁
... | no _ = Γ⊢φ
... | yes p₂
  with  eq (reorder-∨ φ ψ₂) ψ₂
... | no _   = Γ⊢φ
... | yes p₃ =
          ∧-intro
            (subst p₂ (thm-conjunct-∨ ψ₁ Γ⊢φ))
            (subst p₃ (thm-reorder-∨ Γ⊢φ ψ₂))
thm-conjunct-∨ {Γ}{φ} ψ Γ⊢φ          | no _ | other .ψ
  with conj-view φ
thm-conjunct-∨ {Γ}{φ} ψ Γ⊢φ          | no _ | other .ψ | (other .φ)
  = Γ⊢φ
thm-conjunct-∨ {Γ}{.(φ₁ ∧ φ₂)} ψ Γ⊢φ | no _ | other .ψ | (conj φ₁ φ₂)
  with eq (conjuct-∨ φ₁ ψ) ψ
... | yes p₄ = subst p₄ (thm-conjunct-∨ ψ (∧-proj₁ Γ⊢φ))
... | no _
  with  eq (conjuct-∨ φ₂ ψ) ψ
... | yes p₅ = subst p₅ (thm-conjunct-∨ ψ (∧-proj₂ Γ⊢φ))
... | no  _ = Γ⊢φ


reorder-∧∨ : Prop → Prop → Prop
reorder-∧∨ φ ψ
  with ⌊ eq (reorder-∨ φ ψ) ψ ⌋
...  | true = ψ
...  | false
     with conj-view ψ
...     | other _  = conjuct-∨ φ ψ
...     | conj ψ₁ ψ₂
        with ⌊ eq (reorder-∧∨ φ ψ₁) ψ₁ ⌋
...        | false = φ
...        | true
           with ⌊ eq (reorder-∧∨ φ ψ₂) ψ₂ ⌋
...           | true  = ψ₁ ∧ ψ₂
...           | false = φ


thm-reorder-∧∨
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : Prop)
  → Γ ⊢ reorder-∧∨ φ ψ

thm-reorder-∧∨ {Γ} {φ} Γ⊢φ ψ
  with eq (reorder-∨ φ ψ) ψ
...  | yes p₀ = subst p₀ (thm-reorder-∨ Γ⊢φ ψ)
...  | no  _
     with conj-view ψ
...     | other _  = thm-conjunct-∨ ψ Γ⊢φ
...     | conj ψ₁ ψ₂
        with eq (reorder-∧∨ φ ψ₁) ψ₁
...        | no  _  = Γ⊢φ
...        | yes p₁
           with eq (reorder-∧∨ φ ψ₂) ψ₂
...           | yes p₂ =
                    ∧-intro
                      (subst p₁ (thm-reorder-∧∨ Γ⊢φ ψ₁))
                      (subst p₂ (thm-reorder-∧∨ Γ⊢φ ψ₂))
...          | no  _  = Γ⊢φ
