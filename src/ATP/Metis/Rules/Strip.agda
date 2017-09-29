------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Strip inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ ; zero ; suc; _+_) renaming (_⊔_ to max )

module ATP.Metis.Rules.Strip ( n : ℕ ) where

------------------------------------------------------------------------------

open import ATP.Metis.Rules.Conjunct n using ( conjunct; atp-conjunct )

open import Data.Bool
  renaming ( _∧_ to _&&_; _∨_ to _||_ )
  using    ( Bool; true; false; if_then_else_ )

open import Data.List using ( List ; [] ; _∷_ ; _++_ ; [_] ; foldl )

open import Data.PropFormula.Syntax   n
open import Data.PropFormula.Theorems n
open import Data.PropFormula.Views    n

open import Function using ( _$_; id; _∘_ )

open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)
open import Relation.Nullary                      renaming (¬_ to ¬₂)

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Spliting the goal.
------------------------------------------------------------------------------

data ShuntView : PropFormula → Set where
  case₁ : (φ₁ φ₂ φ₃ : PropFormula) → ShuntView (φ₁ ⇒ (φ₂ ⇒ φ₃))
  case₂ : (φ₁ φ₂ φ₃ : PropFormula) → ShuntView (φ₁ ⇒ (φ₂ ∧ φ₃))
  other : (φ : PropFormula)        → ShuntView φ

unshunt-view : (φ : PropFormula) → ShuntView φ
unshunt-view (φ₁ ⇒ (φ₂ ⇒ φ₃)) = case₁ _ _ _
unshunt-view (φ₁ ⇒ (φ₂ ∧ φ₃)) = case₂ _ _ _
unshunt-view φ                = other _

unshuntₙ : ℕ → PropFormula → PropFormula
unshuntₙ zero φ  = φ
unshuntₙ (suc n) φ with unshunt-view φ
... | case₁ φ₁ φ₂ φ₃ = unshuntₙ n ((φ₁ ∧ φ₂) ⇒ φ₃)
... | case₂ φ₁ φ₂ φ₃ = (unshuntₙ n (φ₁ ⇒ φ₂)) ∧ (unshuntₙ n (φ₁ ⇒ φ₃))
... | other _        = φ

thm-inv-unshuntₙ
  : ∀ {Γ} {φ}
  → (n : ℕ)
  → Γ ⊢ unshuntₙ n φ
  → Γ ⊢ φ

thm-inv-unshuntₙ {_} {φ} zero    Γ⊢ushuntnφ  = Γ⊢ushuntnφ
thm-inv-unshuntₙ {_} {φ} (suc n) Γ⊢ushuntnφ with unshunt-view φ
... | case₁ φ₁ φ₂ φ₃ =
  ∧⇒-to-⇒⇒
    (thm-inv-unshuntₙ n
      Γ⊢ushuntnφ)
... | case₂ φ₁ φ₂ φ₃ =
  ⇒∧⇒-to-⇒∧
    (∧-intro
      (thm-inv-unshuntₙ n
        (∧-proj₁ Γ⊢ushuntnφ))
      (thm-inv-unshuntₙ n
        (∧-proj₂ Γ⊢ushuntnφ)))
... | other _ = Γ⊢ushuntnφ

-- Unshunt complexity measure.
unshunt-cmeasure : PropFormula → ℕ
unshunt-cmeasure φ with unshunt-view φ
... | case₁ _ _ φ₃  = unshunt-cmeasure φ₃ + 2
... | case₂ _ φ₂ φ₃ = max (unshunt-cmeasure φ₂) (unshunt-cmeasure φ₃) + 1
... | other .φ      = 1

unshunt : PropFormula → PropFormula
unshunt φ = unshuntₙ (unshunt-cmeasure φ + 1) φ

thm-inv-unshunt
  : ∀ {Γ} {φ}
  → Γ ⊢ unshunt φ
  → Γ ⊢ φ

thm-inv-unshunt {_} {φ} = thm-inv-unshuntₙ (unshunt-cmeasure φ + 1)

data StripView : PropFormula → Set where
  conj    : (φ₁ φ₂ : PropFormula) → StripView (φ₁ ∧ φ₂)
  disj    : (φ₁ φ₂ : PropFormula) → StripView (φ₁ ∨ φ₂)
  impl    : (φ₁ φ₂ : PropFormula) → StripView (φ₁ ⇒ φ₂)
  biimpl  : (φ₁ φ₂ : PropFormula) → StripView (φ₁ ⇔ φ₂)
  nconj   : (φ₁ φ₂ : PropFormula) → StripView (¬ (φ₁ ∧ φ₂))
  ndisj   : (φ₁ φ₂ : PropFormula) → StripView (¬ (φ₁ ∨ φ₂))
  nimpl   : (φ₁ φ₂ : PropFormula) → StripView (¬ (φ₁ ⇒ φ₂))
  nbiimpl : (φ₁ φ₂ : PropFormula) → StripView (¬ (φ₁ ⇔ φ₂))
  nneg    : (φ₁ : PropFormula)    → StripView (¬ ¬ φ₁)
  nbot    : StripView (¬ ⊥)
  ntop    : StripView (¬ ⊤)
  other   : (φ₁ : PropFormula)    → StripView φ₁

split-view : (φ : PropFormula) → StripView φ
split-view (φ₁ ∧ φ₂)     = conj _ _
split-view (φ₁ ∨ φ₂)     = disj _ _
split-view (φ₁ ⇒ φ₂)     = impl _ _
split-view (φ₁ ⇔ φ₂)     = biimpl _ _
split-view (¬ ⊤)         = ntop
split-view (¬ ⊥)         = nbot
split-view (¬ (φ₁ ∧ φ₂)) = nconj _ _
split-view (¬ (φ₁ ∨ φ₂)) = ndisj _ _
split-view (¬ (φ₁ ⇒ φ₂)) = nimpl _ _
split-view (¬ (φ₁ ⇔ φ₂)) = nbiimpl _ _
split-view (¬ (¬ φ₁))    = nneg _
split-view φ₁            = other _


splitₙ : ℕ → PropFormula → PropFormula
splitₙ zero φ = φ
splitₙ (suc n) φ
  with split-view φ
...  | conj φ₁ φ₂    = unshunt (splitₙ n φ₁) ∧
                       unshunt (φ₁ ⇒ splitₙ n φ₂)
...  | disj φ₁ φ₂    = unshunt (¬ φ₁ ⇒ (splitₙ n φ₂))
...  | impl φ₁ φ₂    = unshunt (φ₁ ⇒ (splitₙ n φ₂))
...  | biimpl φ₁ φ₂  = unshunt (φ₁ ⇒ (splitₙ n φ₂)) ∧
                       unshunt (φ₂ ⇒ (splitₙ n φ₁))
...  | nconj φ₁ φ₂   = unshunt (φ₁ ⇒ (splitₙ n (¬ φ₂)))
...  | ndisj φ₁ φ₂   = unshunt (splitₙ n (¬ φ₁)) ∧
                       unshunt (¬ φ₁ ⇒ splitₙ n (¬ φ₂))
...  | nimpl φ₁ φ₂   = unshunt (splitₙ n φ₁) ∧
                       unshunt (φ₁ ⇒ splitₙ n (¬ φ₂))
...  | nbiimpl φ₁ φ₂ = unshunt (φ₁ ⇒ splitₙ n (¬ φ₂)) ∧
                       unshunt ((¬ φ₂) ⇒ splitₙ n φ₁)
...  | nneg φ₁       = unshunt (splitₙ n φ₁)
...  | nbot          = ⊤
...  | ntop          = ⊥
...  | other .φ      = φ

-- * SplitₙGoal theorem.
thm-splitₙ
  : ∀ {Γ} {φ}
  → (n : ℕ)
  → Γ ⊢ splitₙ n φ
  → Γ ⊢ φ

thm-splitₙ {_} {_} zero Γ⊢splitₙ = Γ⊢splitₙ
thm-splitₙ {Γ} {φ} (suc n) Γ⊢splitₙ with split-view φ
... | conj φ₁ φ₂ =
  ∧-intro
    helper
    (thm-splitₙ n
      (⇒-elim
        (thm-inv-unshunt (∧-proj₂ Γ⊢splitₙ))
        helper ))
  where
    helper : Γ ⊢ φ₁
    helper = thm-splitₙ n (thm-inv-unshunt (∧-proj₁ Γ⊢splitₙ))

... | disj φ₁ φ₂ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ φ₂ (assume {Γ = Γ} φ₁))
        (∨-intro₂ φ₁
          (thm-splitₙ n
            (⇒-elim
              (thm-inv-unshunt
                (weaken (¬ φ₁) Γ⊢splitₙ))
              (assume {Γ = Γ} (¬ φ₁)))))))
    (PEM {Γ = Γ} {φ = φ₁})

... | impl φ₁ φ₂ =
 ⇒-intro
   (thm-splitₙ n
     (⇒-elim
       (weaken φ₁
         (thm-inv-unshunt Γ⊢splitₙ))
         (assume {Γ = Γ} φ₁)))

... | biimpl φ₁ φ₂ =
  ⇔-equiv₂ (∧-intro helper₁ helper₂)
  where
    helper₁ : Γ ⊢ φ₁ ⇒ φ₂
    helper₁ = ⇒-intro
         (thm-splitₙ n
           (⇒-elim
             (weaken φ₁
               (thm-inv-unshunt (∧-proj₁ Γ⊢splitₙ)))
             (assume {Γ = Γ} φ₁)))

    helper₂ : Γ ⊢ φ₂ ⇒ φ₁
    helper₂ = ⇒-intro
          (thm-splitₙ n
            (⇒-elim
              (weaken φ₂
                (thm-inv-unshunt (∧-proj₂ Γ⊢splitₙ)))
             (assume {Γ = Γ} φ₂)))

... |  nconj φ₁ φ₂ =
  ¬∨¬-to-¬∧ (⇒-to-¬∨ helper)
  where
    helper : Γ ⊢ φ₁ ⇒ ¬ φ₂
    helper =
      (⇒-intro
        (thm-splitₙ n
          (⇒-elim
            (weaken φ₁
              (thm-inv-unshunt Γ⊢splitₙ))
          (assume {Γ = Γ} φ₁))))

... | ndisj φ₁ φ₂ =
  ¬∧¬-to-¬∨
    (∧-intro
      helper
      (thm-splitₙ n
        (⇒-elim
          (thm-inv-unshunt (∧-proj₂ Γ⊢splitₙ))
          helper)))
  where
    helper : Γ ⊢ ¬ φ₁
    helper = thm-splitₙ n (thm-inv-unshunt (∧-proj₁ Γ⊢splitₙ))

... | nimpl φ₁ φ₂ =
  ¬-intro
    (¬-elim
      (weaken (φ₁ ⇒ φ₂)
        (⇒-elim
          helper
          Γ⊢φ₁))
      (⇒-elim
        (assume {Γ = Γ} (φ₁ ⇒ φ₂))
        (weaken (φ₁ ⇒ φ₂) Γ⊢φ₁)))
  where
    Γ⊢φ₁ : Γ ⊢ φ₁
    Γ⊢φ₁ = thm-splitₙ n (thm-inv-unshunt (∧-proj₁ Γ⊢splitₙ))

    helper : Γ ⊢ φ₁ ⇒ ¬ φ₂
    helper =
      ⇒-intro
        (thm-splitₙ n
          (⇒-elim
            (thm-inv-unshunt (weaken φ₁ (∧-proj₂ Γ⊢splitₙ)))
            (assume {Γ = Γ} φ₁)))

... | nbiimpl φ₁ φ₂ = ⇒¬∧¬⇒-to-¬⇔ (∧-intro helper₁ helper₂)
  where
    helper₁ : Γ ⊢ φ₁ ⇒ ¬ φ₂
    helper₁ =
      ⇒-intro
        (thm-splitₙ n
          (⇒-elim
            (thm-inv-unshunt (weaken φ₁ (∧-proj₁ Γ⊢splitₙ)))
            (assume {Γ = Γ} φ₁)))

    helper₂ : Γ ⊢ ¬ φ₂ ⇒ φ₁
    helper₂ =
      ⇒-intro
        (thm-splitₙ n
          (⇒-elim
            (thm-inv-unshunt (weaken (¬ φ₂) (∧-proj₂ Γ⊢splitₙ)))
            (assume {Γ = Γ} (¬ φ₂))))

... | nneg φ₁  = ¬¬-equiv₂ (thm-splitₙ n (thm-inv-unshunt Γ⊢splitₙ))
... | nbot     = ¬-intro (assume {Γ = Γ} ⊥)
... | ntop     = ⊥-elim (¬ ⊤) Γ⊢splitₙ
... | other φ₁ = Γ⊢splitₙ

-- Split complexity measure.
split-complexity : PropFormula → ℕ
split-complexity φ with split-view φ
... | conj φ₁ φ₂    = max (split-complexity φ₁) (split-complexity φ₂) + 1
... | disj φ₁ φ₂    = split-complexity φ₂ + 1
... | impl φ₁ φ₂    = split-complexity φ₂ + 1
... | biimpl φ₁ φ₂  = max (split-complexity φ₁) (split-complexity φ₂) + 1
... | nconj φ₁ φ₂   = split-complexity (¬ φ₂) + 1
... | ndisj φ₁ φ₂   = max (split-complexity (¬ φ₁)) (split-complexity (¬ φ₂)) + 1
... | nimpl φ₁ φ₂   = max (split-complexity φ₁) (split-complexity (¬ φ₂)) + 1
... | nbiimpl φ₁ φ₂ = max (split-complexity (¬ φ₁)) (split-complexity (¬ φ₂)) + 1
... | nneg φ₁       = split-complexity φ₁ + 1
... | nbot          = 1
... | ntop          = 1
... | other .φ      = 1

split : PropFormula → PropFormula
split φ = splitₙ (split-complexity φ) φ

thm-split
  : ∀ {Γ} {φ}
  → Γ ⊢ split φ
  → Γ ⊢ φ
thm-split {_} {φ} = thm-splitₙ (split-complexity φ)

atp-split
  : ∀ {Γ} {φ}
  → Γ ⊢ split φ ⇒ φ
atp-split {Γ} {φ} = ⇒-intro (thm-split (assume {Γ = Γ} (split φ)))

strip_to_ : PropFormula → PropFormula → PropFormula
strip φ to ψ = conjunct (split φ) ψ
