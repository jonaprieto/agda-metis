------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Canonicalize inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ; suc; zero )

module ATP.Metis.Rules.Canonicalize ( n : ℕ ) where

------------------------------------------------------------------------------

open import ATP.Metis.Rules.Conjunct n using ( conjunct; thm-conjunct )
open import ATP.Metis.Rules.Reordering n

open import Data.Bool.Base
  using    ( true; false )
  renaming ( _∨_ to _or_ )

open import Data.PropFormula.Dec n        using ( ⌊_⌋ ; yes ; no )
open import Data.PropFormula.NormalForms n
open import Data.PropFormula.Properties n using ( eq ; subst )
open import Data.PropFormula.Syntax n
open import Data.PropFormula.SyntaxExperiment n
  using ( right-assoc-∧; thm-right-assoc-∧ )
open import Data.PropFormula.Theorems n
open import Data.PropFormula.Views n

open import Data.Bool using (Bool; true; false) renaming (_∨_ to _or_ )

open import Function  using ( _$_; id ; _∘_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym ; trans)

------------------------------------------------------------------------------

_∈-∨_ : PropFormula → PropFormula → Bool
φ ∈-∨ ψ
  with ⌊ eq φ ψ ⌋
...  | true = true
...  | false
     with disj-view ψ
...     | other .ψ   = false
...     | disj ψ₁ ψ₂ = φ ∈-∨ ψ₁ or φ ∈-∨ ψ₂

-- We assumed here that the formula is a disjunction and its right-associated.
rm-∨ : PropFormula → PropFormula
rm-∨ φ
  with disj-view φ
... | other _  = φ
... | disj φ₁ φ₂
    with φ₁ ∈-∨ φ₂
...    | true  = rm-∨ φ₂
...    | false = φ₁ ∨ rm-∨ φ₂

-- We assumed here that the formula is a disjunction and its right-associated.
rm-∧∨ : PropFormula → PropFormula
rm-∧∨ φ
  with conj-view φ
...  | other _    = rm-∨ (rdisj φ)
...  | conj φ₁ φ₂ = rm-∧∨ φ₁ ∧ rm-∧∨ φ₂

_∈-∧_ : PropFormula → PropFormula → Bool
φ ∈-∧ ψ
  with ⌊ eq (reorder-∨ φ ψ) ψ ⌋
...  | true = true
...  | false
     with conj-view ψ
...     | other .ψ   = false
...     | conj ψ₁ ψ₂ = φ ∈-∧ ψ₁ or φ ∈-∧ ψ₂

rm-∧ : PropFormula → PropFormula
rm-∧ φ
  with conj-view φ
...  | other _  = φ
...  | conj φ₁ φ₂
     with φ₁ ∈-∧ φ₂
...     | true  = rm-∧ φ₂
...     | false = φ₁ ∧ rm-∧ φ₂

redun₀ : PropFormula → PropFormula
redun₀ = rm-∧ ∘ rm-∧∨

-- With the following theorem, we aim to remove from the proposition
-- redundancies of the following two kinds:
--       φ ∨ φ             φ ∧ φ
--      --------   and    --------.
--         φ                 φ

redun : PropFormula → PropFormula
redun φ = reorder-∧∨ φ (redun₀ φ)

thm-redun
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ redun φ
thm-redun {Γ}{φ} Γ⊢φ = thm-reorder-∧∨ Γ⊢φ (redun₀ φ)

-----------------------------------------------------------------------------

-- φ ∨ ¬ φ deletions in a right-associated formula.
rmPEM-∨ : PropFormula → PropFormula
rmPEM-∨ φ
  with disj-view φ
... | other .φ   = φ
... | disj φ₁ φ₂
    with neg-view φ₁
rmPEM-∨ .(¬ φ ∨ φ₂) | disj .(¬ φ) φ₂ | neg φ
    with φ ∈-∨ φ₂
rmPEM-∨ .(¬ φ ∨ φ₂) | disj .(¬ φ) φ₂ | neg φ | true  = ⊤
rmPEM-∨ .(¬ φ ∨ φ₂) | disj .(¬ φ) φ₂ | neg φ | false
   with ⌊ eq (rmPEM-∨ φ₂) ⊤ ⌋
rmPEM-∨ .(¬ φ ∨ φ₂) | disj .(¬ φ) φ₂ | neg φ | false | false = ¬ φ ∨ rmPEM-∨ φ₂
rmPEM-∨ .(¬ φ ∨ φ₂) | disj .(¬ φ) φ₂ | neg φ | false | true  = ⊤
rmPEM-∨ .(φ₁ ∨ φ₂)  | disj φ₁ φ₂     | pos .φ₁
    with (¬ φ₁) ∈-∨ φ₂
rmPEM-∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ | pos .φ₁ | true  = ⊤
rmPEM-∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ | pos .φ₁ | false
  with ⌊ eq (rmPEM-∨ φ₂) ⊤ ⌋
rmPEM-∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ | pos .φ₁ | false | false = φ₁ ∨ rmPEM-∨ φ₂
rmPEM-∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ | pos .φ₁ | false | true  = ⊤

thm-rmPEM-∨
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ rmPEM-∨ φ

thm-rmPEM-∨ {Γ} {φ} Γ⊢φ
  with disj-view φ
... | other .φ   = Γ⊢φ
... | disj φ₁ φ₂
  with neg-view φ₁
thm-rmPEM-∨ {Γ} {.(¬ φ ∨ φ₂)} Γ⊢φ | disj .(¬ φ) φ₂ | neg φ
  with φ ∈-∨ φ₂
thm-rmPEM-∨ {Γ} {.(¬ φ ∨ φ₂)} Γ⊢φ | disj .(¬ φ) φ₂ | neg φ | true  = ⊤-intro
thm-rmPEM-∨ {Γ} {.(¬ φ ∨ φ₂)} Γ⊢φ | disj .(¬ φ) φ₂ | neg φ | false
  with ⌊ eq (rmPEM-∨ φ₂) ⊤ ⌋
thm-rmPEM-∨ {Γ} {.(¬ φ ∨ φ₂)} Γ⊢φ | disj .(¬ φ) φ₂ | neg φ | false | false =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (rmPEM-∨ φ₂) (assume {Γ = Γ} (¬ φ)))
        (∨-intro₂ (¬ φ) (thm-rmPEM-∨ (assume {Γ = Γ} φ₂)))))
    Γ⊢φ
thm-rmPEM-∨ {Γ} {.(¬ φ ∨ φ₂)} Γ⊢φ | disj .(¬ φ) φ₂ | neg φ | false | true  = ⊤-intro
thm-rmPEM-∨ {Γ} {.(φ₁ ∨ φ₂) } Γ⊢φ | disj φ₁ φ₂     | pos .φ₁
  with (¬ φ₁) ∈-∨ φ₂
thm-rmPEM-∨ {Γ} {.(φ₁ ∨ φ₂) } Γ⊢φ | disj φ₁ φ₂ | pos .φ₁ | true  = ⊤-intro
thm-rmPEM-∨ {Γ} {.(φ₁ ∨ φ₂) } Γ⊢φ | disj φ₁ φ₂ | pos .φ₁ | false
  with ⌊ eq (rmPEM-∨ φ₂) ⊤ ⌋
thm-rmPEM-∨ {Γ} {.(φ₁ ∨ φ₂) } Γ⊢φ | disj φ₁ φ₂ | pos .φ₁ | false | false =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (rmPEM-∨ φ₂) (assume {Γ = Γ} (φ₁)))
        (∨-intro₂ (φ₁) (thm-rmPEM-∨ (assume {Γ = Γ} φ₂)))))
    Γ⊢φ
thm-rmPEM-∨ {Γ} {.(φ₁ ∨ φ₂) } Γ⊢φ | disj φ₁ φ₂ | pos .φ₁ | false | true  = ⊤-intro


-- apply rmPEM-∨ in a CNF
-- The conjunction, again, have to be a right-associative conjunction.
rmPEM-∧∨ : PropFormula → PropFormula
rmPEM-∧∨ φ
  with conj-view φ
...  | other _    = rmPEM-∨ φ
...  | conj φ₁ φ₂ = rmPEM-∨ φ₁ ∧ rmPEM-∧∨ φ₂

thm-rmPEM-∧∨
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ rmPEM-∧∨ φ

thm-rmPEM-∧∨ {Γ} {φ} Γ⊢φ
  with conj-view φ
...  | other _    = thm-rmPEM-∨ Γ⊢φ
...  | conj φ₁ φ₂ =
            ∧-intro
              (thm-rmPEM-∨ (∧-proj₁ Γ⊢φ))
              (thm-rmPEM-∧∨ (∧-proj₂ Γ⊢φ))


rmBot-∧ : PropFormula → PropFormula
rmBot-∧ φ
  with conj-view φ
... | other .φ   = φ
... | conj φ₁ φ₂
    with neg-view φ₁
rmBot-∧ .(¬ φ ∧ φ₂) | conj .(¬ φ) φ₂ | neg φ
    with ⌊ eq (conjunct φ₂ φ) φ ⌋
rmBot-∧ .(¬ φ ∧ φ₂) | conj .(¬ φ) φ₂ | neg φ | true  = ⊥
rmBot-∧ .(¬ φ ∧ φ₂) | conj .(¬ φ) φ₂ | neg φ | false
  with ⌊ eq (rmBot-∧ φ₂) ⊥ ⌋
rmBot-∧ .(¬ φ ∧ φ₂) | conj .(¬ φ) φ₂ | neg φ | false | false = ¬ φ ∧ rmBot-∧ φ₂
rmBot-∧ .(¬ φ ∧ φ₂) | conj .(¬ φ) φ₂ | neg φ | false | true  = ⊥
rmBot-∧ .(φ₁ ∧ φ₂)  | conj φ₁ φ₂     | pos .φ₁
  with ⌊ eq (conjunct φ₂ (¬ φ₁)) (¬ φ₁) ⌋
rmBot-∧ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ | pos .φ₁ | true  = ⊥
rmBot-∧ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ | pos .φ₁ | false
  with ⌊ eq (rmBot-∧ φ₂) ⊥ ⌋
rmBot-∧ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ | pos .φ₁ | false | true  = ⊥
rmBot-∧ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ | pos .φ₁ | false | false = φ₁ ∧ rmBot-∧ φ₂

thm-rmBot-∧
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ rmBot-∧ φ

thm-rmBot-∧ {Γ} {φ} Γ⊢φ
  with conj-view φ
...  | other .φ   = Γ⊢φ
...  | conj φ₁ φ₂
  with neg-view φ₁
thm-rmBot-∧ {Γ} {.(¬ φ ∧ φ₂)} Γ⊢φ | conj .(¬ φ) φ₂ | neg φ
  with eq (conjunct φ₂ φ) φ
thm-rmBot-∧ {Γ} {.(¬ φ ∧ φ₂)} Γ⊢φ | conj .(¬ φ) φ₂ | neg φ | yes p₁  =
  ¬∧-to-⊥
    (∧-intro
      (∧-proj₁ Γ⊢φ)
      (subst p₁ (thm-conjunct φ (∧-proj₂ Γ⊢φ))))
thm-rmBot-∧ {Γ} {.(¬ φ ∧ φ₂)} Γ⊢φ | conj .(¬ φ) φ₂ | neg φ | no _
  with eq (rmBot-∧ φ₂) ⊥
thm-rmBot-∧ {Γ} {.(¬ φ ∧ φ₂)} Γ⊢φ | conj .(¬ φ) φ₂ | neg φ | no _ | no _ =
  ∧-intro (∧-proj₁ Γ⊢φ) (thm-rmBot-∧ (∧-proj₂ Γ⊢φ))
thm-rmBot-∧ {Γ} {.(¬ φ ∧ φ₂)} Γ⊢φ | conj .(¬ φ) φ₂ | neg φ | no _ | yes p₂ =
  subst p₂ (thm-rmBot-∧ (∧-proj₂ Γ⊢φ))
thm-rmBot-∧ {Γ} {.(φ₁ ∧ φ₂) } Γ⊢φ | conj φ₁ φ₂     | pos .φ₁
  with eq (conjunct φ₂ (¬ φ₁)) (¬ φ₁)
thm-rmBot-∧ {Γ} {.(φ₁ ∧ φ₂) } Γ⊢φ | conj φ₁ φ₂ | pos .φ₁ | yes p₃  =
  ¬∧-to-⊥
    (∧-comm
      (∧-intro
        (∧-proj₁ Γ⊢φ)
        (subst p₃ (thm-conjunct (¬ φ₁) (∧-proj₂ Γ⊢φ)))))
thm-rmBot-∧ {Γ} {.(φ₁ ∧ φ₂) } Γ⊢φ | conj φ₁ φ₂ | pos .φ₁ | no _
  with eq (rmBot-∧ φ₂) ⊥
thm-rmBot-∧ {Γ} {.(φ₁ ∧ φ₂) } Γ⊢φ | conj φ₁ φ₂ | pos .φ₁ | no _ | no _ =
  ∧-intro (∧-proj₁ Γ⊢φ) (thm-rmBot-∧ (∧-proj₂ Γ⊢φ))
thm-rmBot-∧ {Γ} {.(φ₁ ∧ φ₂) } Γ⊢φ | conj φ₁ φ₂ | pos .φ₁ | no _ | yes p₄  =
  subst p₄ (thm-rmBot-∧ (∧-proj₂ Γ⊢φ))


data canonView : PropFormula  → Set where

-- Conjunction simplification cases.
  sconj₁ : (φ₁ : PropFormula)    → canonView (φ₁ ∧ ⊤)     -- φ ∧ ⊤ ==> φ.
  sconj₂ : (φ₁ : PropFormula)    → canonView (⊤ ∧ φ₁)     -- ⊤ ∧ φ ==> φ.
  sconj₃ : (φ₁ : PropFormula)    → canonView (φ₁ ∧ ⊥)     -- φ ∧ ⊥ ==> ⊥.
  sconj₄ : (φ₁ : PropFormula)    → canonView (⊥ ∧ φ₁)     -- ⊥ ∧ φ ==> ⊥.
  sconj₅ : (φ₁ φ₂ : PropFormula) → canonView (φ₁ ∧ φ₂)

-- Disjunction simplification cases.
  sdisj₁ : (φ₁ : PropFormula)    → canonView (φ₁ ∨ ⊤)     -- φ ∨ ⊤ ==> ⊤.
  sdisj₂ : (φ₁ : PropFormula)    → canonView (⊤ ∨ φ₁)     -- ⊤ ∨ φ ==> ⊤.
  sdisj₃ : (φ₁ : PropFormula)    → canonView (φ₁ ∨ ⊥)     -- φ ∨ ⊥ ==> φ.
  sdisj₄ : (φ₁ : PropFormula)    → canonView (⊥ ∨ φ₁)     -- ⊥ ∨ φ ==> φ.
  sdisj₅ : (φ₁ φ₂ : PropFormula) → canonView (φ₁ ∨ φ₂)
  other  : (φ₁ : PropFormula)    → canonView φ₁


canon-view : (φ : PropFormula) → canonView φ
canon-view (φ ∧ ⊤)  = sconj₁ _
canon-view (⊤ ∧ φ)  = sconj₂ _
canon-view (φ ∧ ⊥)  = sconj₃ _
canon-view (⊥ ∧ φ)  = sconj₄ _
canon-view (φ ∧ ψ)  = sconj₅ _ _
canon-view (φ ∨ ⊤)  = sdisj₁ _
canon-view (⊤ ∨ φ)  = sdisj₂ _
canon-view (φ ∨ ⊥)  = sdisj₃ _
canon-view (⊥ ∨ φ)  = sdisj₄ _
canon-view (φ ∨ φ₁) = sdisj₅ _ _
canon-view  φ       = other _


-- We assumed here that the formula is a disjunction and its right-associated.
canon : PropFormula → PropFormula
canon φ
  with canon-view φ
canon .(φ₁ ∧ ⊤)  | sconj₁ φ₁ = canon φ₁
canon .(⊤ ∧ φ₁)  | sconj₂ φ₁ = canon φ₁
canon .(φ₁ ∧ ⊥)  | sconj₃ φ₁ = ⊥
canon .(⊥ ∧ φ₁)  | sconj₄ φ₁ = ⊥
canon .(φ₁ ∧ φ₂) | sconj₅ φ₁ φ₂
  with ⌊ eq (canon φ₁) ⊤ ⌋
...  | true = canon φ₂
...  | false
     with ⌊ eq (canon φ₁) ⊥ ⌋
...     | true = ⊥
...     | false
        with ⌊ eq (canon φ₂) ⊤ ⌋
...        | true = canon φ₁
...        | false
           with  ⌊ eq (canon φ₂) ⊥ ⌋
...           |  true  = ⊥
...           |  false = canon φ₁ ∧ canon φ₂

canon .(φ₁ ∨ ⊤)  | sdisj₁ φ₁ = ⊤
canon .(⊤ ∨ φ₁)  | sdisj₂ φ₁ = ⊤
canon .(φ₁ ∨ ⊥)  | sdisj₃ φ₁ = canon φ₁
canon .(⊥ ∨ φ₁)  | sdisj₄ φ₁ = canon φ₁
canon .(φ₁ ∨ φ₂) | sdisj₅ φ₁ φ₂
  with ⌊ eq (canon φ₁) ⊤ ⌋
...  | true = ⊤
...  | false
     with ⌊ eq (canon φ₁) ⊥ ⌋
...     | true = canon φ₂
...     | false
        with ⌊ eq (canon φ₂) ⊤ ⌋
...        | true = ⊤
...        | false
           with  ⌊ eq (canon φ₂) ⊥ ⌋
...           | true  = canon φ₁
...           | false = canon φ₁ ∨ canon φ₂
canon φ          | other .φ = φ

thm-canon
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ canon φ

thm-canon {Γ} {φ} Γ⊢φ
  with canon-view φ
thm-canon {Γ} {.(φ₁ ∧ ⊤) } Γ⊢φ | sconj₁ φ₁ = thm-canon (∧-proj₁ Γ⊢φ)
thm-canon {Γ} {.(⊤ ∧ φ₁) } Γ⊢φ | sconj₂ φ₁ = thm-canon (∧-proj₂ Γ⊢φ)
thm-canon {Γ} {.(φ₁ ∧ ⊥) } Γ⊢φ | sconj₃ φ₁ = ∧-proj₂ Γ⊢φ
thm-canon {Γ} {.(⊥ ∧ φ₁) } Γ⊢φ | sconj₄ φ₁ = ∧-proj₁ Γ⊢φ
thm-canon {Γ} {.(φ₁ ∧ φ₂)} Γ⊢φ | sconj₅ φ₁ φ₂
  with eq (canon φ₁) ⊤
...  | yes p = thm-canon (∧-proj₂ Γ⊢φ)
...  | no _
     with eq (canon φ₁) ⊥
...     | yes p = subst p (thm-canon (∧-proj₁ Γ⊢φ))
...     | no _
        with eq (canon φ₂) ⊤
...        | yes p = thm-canon (∧-proj₁ Γ⊢φ)
...        | no _
           with  eq (canon φ₂) ⊥
...           |  yes p  = subst p (thm-canon (∧-proj₂ Γ⊢φ))
...           |  no _ = ∧-intro (thm-canon (∧-proj₁ Γ⊢φ)) (thm-canon (∧-proj₂ Γ⊢φ))

thm-canon {Γ} {.(φ₁ ∨ ⊤) } Γ⊢φ | sdisj₁ φ₁ = ⊤-intro
thm-canon {Γ} {.(⊤ ∨ φ₁) } Γ⊢φ | sdisj₂ φ₁ = ⊤-intro
thm-canon {Γ} {.(φ₁ ∨ ⊥) } Γ⊢φ | sdisj₃ φ₁ = thm-canon (φ∨⊥-to-φ Γ⊢φ)
thm-canon {Γ} {.(⊥ ∨ φ₁) } Γ⊢φ | sdisj₄ φ₁ = thm-canon (φ∨⊥-to-φ (∨-comm Γ⊢φ))
thm-canon {Γ} {.(φ₁ ∨ φ₂)} Γ⊢φ | sdisj₅ φ₁ φ₂
  with eq (canon φ₁) ⊤
...  | yes p = ⊤-intro
...  | no _
     with eq (canon φ₁) ⊥
...     | yes p =
            ⇒-elim
              (⇒-intro
                (∨-elim {Γ = Γ}
                  (⊥-elim (canon φ₂) (subst p (thm-canon (assume {Γ = Γ} φ₁))))
                  (thm-canon (assume {Γ = Γ} φ₂))))
             Γ⊢φ
...     | no _
        with eq (canon φ₂) ⊤
...        | yes _ = ⊤-intro
...        | no _
           with  eq (canon φ₂) ⊥
...           | yes p₂  =
                    ⇒-elim
                      (⇒-intro
                        (∨-elim {Γ = Γ}
                        (thm-canon (assume {Γ = Γ} φ₁))
                        (⊥-elim (canon φ₁)
                          (subst p₂
                            (thm-canon (assume {Γ = Γ} φ₂))))))
                    Γ⊢φ
...           | no _ =
                   ⇒-elim
                     (⇒-intro
                       (∨-elim {Γ = Γ}
                         (∨-intro₁ (canon φ₂)
                           (thm-canon (assume {Γ = Γ} φ₁)))
                         (∨-intro₂ (canon φ₁)
                           (thm-canon (assume {Γ = Γ} φ₂)))))
                     Γ⊢φ
thm-canon {Γ} {φ} Γ⊢φ | other .φ = Γ⊢φ


canonicalize₀ : PropFormula → PropFormula
canonicalize₀ =  canon ∘ rmBot-∧ ∘ rmPEM-∧∨ ∘ redun ∘ right-assoc-∧ ∘ cnf

thm-canonicalize₀
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ canonicalize₀ φ

thm-canonicalize₀ =
  thm-canon ∘ thm-rmBot-∧ ∘ thm-rmPEM-∧∨ ∘ thm-redun ∘ thm-right-assoc-∧ ∘ thm-cnf

------------------------------------------------------------------------------
-- atp-canonicalize.
------------------------------------------------------------------------------

postulate
  thm-canonicalize
    : ∀ {Γ} {φ}
    → (ψ : PropFormula)
    → Γ ⊢ φ
    → Γ ⊢ canonicalize₀ φ

atp-canonicalize = thm-canonicalize

postulate
  thm-canonicalize-axiom
    : ∀ {Γ} {φ}
    → (ψ : PropFormula)
    → Γ ⊢ φ
    → Γ ⊢ ψ
