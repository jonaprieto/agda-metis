------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Reordering module.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ; suc; zero; _+_ )

module ATP.Metis.Rules.Reordering ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Syntax n
open import Data.PropFormula.Dec n                  using ( yes; no; ⌊_⌋ )
open import Data.PropFormula.Properties n           using ( eq; subst )
open import Data.PropFormula.Views n
  using ( DisjView; disj-view; disj; other; conj-view; conj)

open import Data.PropFormula.Theorems.Conjunction n using ( ∧-dmorgan₁ )
open import Data.PropFormula.Theorems.Disjunction n
  using ( ∨-comm; lem1; lem2; ∨-assoc₂; subst⊢∨₂; resolve₇)

open import Data.Bool                        using ( true; false )
open import Function                         using ( _$_; id; _∘_ )
open import Relation.Binary.PropositionalEquality using ( sym )

open import ATP.Metis.Rules.Conjunct n
  using ( conjunct; thm-conjunct )

open import Data.List.Base  using (_∷_; []; [_]; List; _∷ʳ_; _++_)

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Reordering of a disjunction.
------------------------------------------------------------------------------

build-∨ : PropFormula → PropFormula → PropFormula
build-∨ φ ψ
  with ⌊ eq φ ψ ⌋
... | true  = ψ
... | false
    with disj-view ψ
...    | other _    = φ
...    | disj ψ₁ ψ₂
       with ⌊ eq (build-∨ φ ψ₁) ψ₁ ⌋
...       | true = ψ₁ ∨ ψ₂
...       | false
          with ⌊ eq (build-∨ φ ψ₂) ψ₂ ⌋
...          | true  = ψ₁ ∨ ψ₂
...          | false = φ


lem-build-∨
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : PropFormula)
  → Γ ⊢ build-∨ φ ψ

lem-build-∨ {Γ}{φ} Γ⊢φ ψ
  with eq φ ψ
... | yes φ≡ψ  = subst φ≡ψ Γ⊢φ
... | no  _
    with disj-view ψ
...    | other _    = Γ⊢φ
...    | disj ψ₁ ψ₂
       with eq (build-∨ φ ψ₁) ψ₁
...       | yes p₁ = ∨-intro₁ ψ₂ (subst p₁ (lem-build-∨ Γ⊢φ ψ₁))
...       | no  _
          with eq (build-∨ φ ψ₂) ψ₂
...          | yes p₂  = ∨-intro₂ ψ₁ (subst p₂ (lem-build-∨ Γ⊢φ ψ₂))
...          | no  _   = Γ⊢φ

factor : PropFormula → PropFormula
factor φ
  with disj-view φ
... | other _ = φ
... | disj φ₁ φ₂
    with eq φ₁ (factor φ₂)
...    | yes _ = φ₁
...    | no _  = φ

lem-factor
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ factor φ
lem-factor {Γ}{φ} Γ⊢φ
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
                 (lem-factor $ assume {Γ = Γ} φ₂))))
           Γ⊢φ
...    | no _            = Γ⊢φ

sbuild-∨ : PropFormula → PropFormula → PropFormula
sbuild-∨ φ ψ
  with disj-view φ
... | other _    = build-∨ φ ψ
... | disj φ₁ φ₂ = factor (build-∨ φ₁ ψ ∨ sbuild-∨ φ₂ ψ)

lem-sbuild-∨
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : PropFormula)
  → Γ ⊢ sbuild-∨ φ ψ

lem-sbuild-∨ {Γ} {φ} Γ⊢φ ψ
  with disj-view φ
... | other _    = lem-build-∨ Γ⊢φ ψ
... | disj φ₁ φ₂ =
        lem-factor
         (⇒-elim
            (⇒-intro
              (∨-elim {Γ = Γ}
                (∨-intro₁ (sbuild-∨ φ₂ ψ)
                  (lem-build-∨ (assume {Γ = Γ} φ₁) ψ))
                (∨-intro₂ (build-∨ φ₁ ψ)
                  (lem-sbuild-∨ (assume {Γ = Γ} φ₂) ψ))))
            Γ⊢φ)

data TDisjView : PropFormula → Set where
  case₁ : (φ₁ φ₂ φ₃ : PropFormula) → TDisjView ((φ₁ ∨ φ₂) ∨ φ₃)
  case₂ : (φ₁ φ₂ : PropFormula)    → TDisjView (φ₁ ∨ φ₂)
  other : (φ : PropFormula)        → TDisjView φ

tdisj-view : (φ : PropFormula) → TDisjView φ
tdisj-view ((φ₁ ∨ φ₂) ∨ φ₃) = case₁ _ _ _
tdisj-view (φ ∨ ψ)          = case₂ _ _
tdisj-view φ                = other _

rdisjₙ : ℕ → PropFormula → PropFormula
rdisjₙ zero φ  = φ
rdisjₙ (suc n) φ
  with tdisj-view φ
rdisjₙ (suc n₁) .((φ₁ ∨ φ₂) ∨ φ₃) | case₁ φ₁ φ₂ φ₃ =
  rdisjₙ n₁ (φ₁ ∨ (φ₂ ∨ φ₃))
rdisjₙ (suc n₁) .(φ ∨ ψ)          | case₂ φ ψ      =
  φ ∨ rdisjₙ n₁ ψ
rdisjₙ (suc n₁) φ                 | other .φ       = φ

lem-rdisjₙ
  : ∀ {Γ} {φ}
  → (n : ℕ)
  → Γ ⊢ φ
  → Γ ⊢ rdisjₙ n φ

lem-rdisjₙ {Γ} {φ} zero Γ⊢φ = Γ⊢φ
lem-rdisjₙ {Γ} {φ} (suc n) Γ⊢φ
  with tdisj-view φ
lem-rdisjₙ {Γ} {_} (suc n₁) Γ⊢φ | case₁ φ₁ φ₂ φ₃ =
  lem-rdisjₙ n₁ (∨-assoc₂ Γ⊢φ)
lem-rdisjₙ {Γ} {_} (suc n₁) Γ⊢φ | case₂ φ ψ      =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (rdisjₙ n₁ ψ)
          (assume {Γ = Γ} φ))
        (∨-intro₂ φ (lem-rdisjₙ n₁
          (assume {Γ = Γ} ψ)))))
    Γ⊢φ
lem-rdisjₙ {Γ} {_} (suc n₁) Γ⊢φ | other φ = Γ⊢φ

rdisj-complexity : PropFormula → ℕ
rdisj-complexity φ
  with tdisj-view φ
... | case₁ φ₁ φ₂ φ₃ = 2 + rdisj-complexity φ₂ + rdisj-complexity φ₃
... | case₂ φ₁ φ₂    = 2 + rdisj-complexity φ₂
... | other .φ       = 1

rdisj : PropFormula → PropFormula
rdisj φ = rdisjₙ (rdisj-complexity φ) φ

lem-rdisj
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ rdisj φ
lem-rdisj {Γ}{φ} Γ⊢φ = lem-rdisjₙ (rdisj-complexity φ) Γ⊢φ

reorder-∨ : PropFormula → PropFormula → PropFormula
reorder-∨ φ ψ = sbuild-∨ (rdisj φ) ψ

thm-reorder-∨
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : PropFormula)
  → Γ ⊢ reorder-∨ φ ψ
thm-reorder-∨ {Γ} {φ} Γ⊢φ ψ = lem-sbuild-∨ (lem-rdisj Γ⊢φ) ψ

------------------------------------------------------------------------------
-- Reordering a conjunction.
------------------------------------------------------------------------------

reorder-∧ : PropFormula → PropFormula → PropFormula
reorder-∧ φ ψ
  with ⌊ eq φ ψ ⌋
...  | true = φ
...  | false
     with conj-view ψ
...     | other _ = conjunct φ ψ
...     | conj ψ₁ ψ₂
        with ⌊ eq (reorder-∧ φ ψ₁) ψ₁ ⌋
...        | false = φ
...        | true
           with ⌊ eq (reorder-∧ φ ψ₂) ψ₂ ⌋
...           | true  = ψ₁ ∧ ψ₂
...           | false = φ

lem-reorder-∧
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : PropFormula)
  → Γ ⊢ reorder-∧ φ ψ

lem-reorder-∧ {Γ} {φ} Γ⊢φ ψ
  with ⌊ eq φ ψ ⌋
... | true = Γ⊢φ
... | false
    with conj-view ψ
...    | other _  = thm-conjunct ψ Γ⊢φ
...    | conj ψ₁ ψ₂
       with eq (reorder-∧ φ ψ₁) ψ₁
...       | no  _ = Γ⊢φ
...       | yes p₁
          with eq (reorder-∧ φ ψ₂) ψ₂
...          | no  _  = Γ⊢φ
...          | yes p₂ =
                   ∧-intro
                   (subst p₁ (lem-reorder-∧ Γ⊢φ ψ₁))
                   (subst p₂ (lem-reorder-∧ Γ⊢φ ψ₂))


-------------------------------------------------------------------------------
-- Reordering a conjunction of disjunctions.
-- Conversion from a CNF formula φ to another CNF formula ψ.
------------------------------------------------------------------------------

conjunct-∨ : PropFormula → PropFormula → PropFormula
conjunct-∨ φ ψ
  with ⌊ eq (reorder-∨ φ ψ) ψ ⌋
... | true  = ψ
... | false
    with conj-view ψ
conjunct-∨ φ .(ψ₁ ∧ ψ₂) | false | conj ψ₁ ψ₂
  with  ⌊ eq (conjunct-∨ φ ψ₁) ψ₁ ⌋
... | false = φ
... | true
  with  ⌊ eq (reorder-∨ φ ψ₂) ψ₂ ⌋
... | false = φ
... | true  = ψ₁ ∧ ψ₂
conjunct-∨ φ ψ          | false | other .ψ
  with conj-view φ
conjunct-∨ φ ψ          | false | other .ψ | (other .φ)  = φ
conjunct-∨ .(φ₁ ∧ φ₂) ψ | false | other .ψ | (conj φ₁ φ₂)
  with ⌊ eq (conjunct-∨ φ₁ ψ) ψ ⌋
... | true = ψ
... | false
    with  ⌊ eq (conjunct-∨ φ₂ ψ) ψ ⌋
... | true = ψ
... | false = φ₁ ∧ φ₂

lem-conjunct-∨
  : ∀ {Γ} {φ}
  → (ψ : PropFormula)
  → Γ ⊢ φ
  → Γ ⊢ conjunct-∨ φ ψ

lem-conjunct-∨ {Γ}{φ} ψ Γ⊢φ
  with eq (reorder-∨ φ ψ) ψ
... | yes p₁ = subst p₁ (thm-reorder-∨ Γ⊢φ ψ)
... | no _
    with conj-view ψ
lem-conjunct-∨ {Γ}{φ} .(ψ₁ ∧ ψ₂) Γ⊢φ | no _ | conj ψ₁ ψ₂
  with  eq (conjunct-∨ φ ψ₁) ψ₁
... | no _ = Γ⊢φ
... | yes p₂
  with  eq (reorder-∨ φ ψ₂) ψ₂
... | no _   = Γ⊢φ
... | yes p₃ =
          ∧-intro
            (subst p₂ (lem-conjunct-∨ ψ₁ Γ⊢φ))
            (subst p₃ (thm-reorder-∨ Γ⊢φ ψ₂))
lem-conjunct-∨ {Γ}{φ} ψ Γ⊢φ          | no _ | other .ψ
  with conj-view φ
lem-conjunct-∨ {Γ}{φ} ψ Γ⊢φ          | no _ | other .ψ | (other .φ)
  = Γ⊢φ
lem-conjunct-∨ {Γ}{.(φ₁ ∧ φ₂)} ψ Γ⊢φ | no _ | other .ψ | (conj φ₁ φ₂)
  with eq (conjunct-∨ φ₁ ψ) ψ
... | yes p₄ = subst p₄ (lem-conjunct-∨ ψ (∧-proj₁ Γ⊢φ))
... | no _
  with  eq (conjunct-∨ φ₂ ψ) ψ
... | yes p₅ = subst p₅ (lem-conjunct-∨ ψ (∧-proj₂ Γ⊢φ))
... | no  _ = Γ⊢φ


reorder-∧∨ : PropFormula → PropFormula → PropFormula
reorder-∧∨ φ ψ
  with ⌊ eq (reorder-∨ φ ψ) ψ ⌋
...  | true  = ψ
...  | false
     with conj-view ψ
...     | other _  = conjunct-∨ φ ψ
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
  → (ψ : PropFormula)
  → Γ ⊢ reorder-∧∨ φ ψ

thm-reorder-∧∨ {Γ} {φ} Γ⊢φ ψ
  with eq (reorder-∨ φ ψ) ψ
...  | yes p₀ = subst p₀ (thm-reorder-∨ Γ⊢φ ψ)
...  | no  _
     with conj-view ψ
...     | other _  = lem-conjunct-∨ ψ Γ⊢φ
...     | conj ψ₁ ψ₂
        with eq (reorder-∧∨ φ ψ₁) ψ₁
...        | no  _  = Γ⊢φ
...        | yes p₁
           with eq (reorder-∧∨ φ ψ₂) ψ₂
...           | yes p₂ =
                    ∧-intro
                      (subst p₁ (thm-reorder-∧∨ Γ⊢φ ψ₁))
                      (subst p₂ (thm-reorder-∧∨ Γ⊢φ ψ₂))
...           | no  _  = Γ⊢φ
