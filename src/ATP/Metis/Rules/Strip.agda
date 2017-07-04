------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Strip inference rule.
------------------------------------------------------------------------------

-- {-# OPTIONS --exact-split #-}
{-# OPTIONS --allow-unsolved-metas #-}


open import Data.Nat using ( ℕ ; zero ; suc; _+_ )

module ATP.Metis.Rules.Strip ( n : ℕ ) where

------------------------------------------------------------------------------

open import ATP.Metis.Rules.Conjunct n using ( conjunct; atp-conjunct )

open import Data.Bool
  renaming ( _∧_ to _&&_; _∨_ to _||_ )
  using    ( Bool; true; false; if_then_else_ )

open import Data.List using ( List ; [] ; _∷_ ; _++_ ; [_] ; foldl )
open import Data.Prop.Syntax n
open import Data.Prop.Theorems n
open import Data.Prop.Views n
open import Data.Prop.SyntaxExperiment n

open import Function                      using ( _$_; id; _∘_ )
open import Relation.Nullary renaming (¬_ to ¬₂)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Spliting the goal.
------------------------------------------------------------------------------

data ShuntView : Prop → Set where
  case₁ : (φ₁ φ₂ φ₃ : Prop) → ShuntView (φ₁ ⇒ (φ₂ ⇒ φ₃))
  case₂ : (φ₁ φ₂ φ₃ : Prop) → ShuntView (φ₁ ⇒ (φ₂ ∧ φ₃))
  other : (φ : Prop)        → ShuntView φ

unshunt-view : (φ : Prop) → ShuntView φ
unshunt-view (φ₁ ⇒ (φ₂ ⇒ φ₃)) = case₁ _ _ _
unshunt-view (φ₁ ⇒ (φ₂ ∧ φ₃)) = case₂ _ _ _
unshunt-view φ                 = other _

unshunt′ : ℕ → Prop → Prop
unshunt′ zero φ  = φ
unshunt′ (suc n) φ with unshunt-view φ
... | case₁ φ₁ φ₂ φ₃ = unshunt′ n ((φ₁ ∧ φ₂) ⇒ φ₃)
... | case₂ φ₁ φ₂ φ₃ = (unshunt′ n (φ₁ ⇒ φ₂)) ∧ (unshunt′ n (φ₁ ⇒ φ₃))
... | other _        = φ

thm-inv-unshunt′
  : ∀ {Γ} {φ}
  → (n : ℕ)
  → Γ ⊢ unshunt′ n φ
  → Γ ⊢ φ

thm-inv-unshunt′ {_} {φ} zero    Γ⊢ushuntnφ  = Γ⊢ushuntnφ
thm-inv-unshunt′ {_} {φ} (suc n) Γ⊢ushuntnφ with unshunt-view φ
... | case₁ φ₁ φ₂ φ₃ =
  ∧⇒-to-⇒⇒
    (thm-inv-unshunt′ n
      Γ⊢ushuntnφ)
... | case₂ φ₁ φ₂ φ₃ =
  ⇒∧⇒-to-⇒∧
    (∧-intro
      (thm-inv-unshunt′ n
        (∧-proj₁ Γ⊢ushuntnφ))
      (thm-inv-unshunt′ n
        (∧-proj₂ Γ⊢ushuntnφ)))
... | other _ = Γ⊢ushuntnφ

calls-unshunt : Prop → ℕ
calls-unshunt φ with unshunt-view φ
... | case₁ _ _ φ₃  = 2 + calls-unshunt φ₃
... | case₂ _ φ₂ φ₃ = 1 + calls-unshunt φ₂ + calls-unshunt φ₃
... | other .φ      = 1


postulate
  thm-unshunt′
    : ∀ {Γ} {φ}
    → (n : ℕ)
    → Γ ⊢ φ
    → Γ ⊢ unshunt′ n φ

unshunt : Prop → Prop
unshunt φ = unshunt′ (calls-unshunt φ + 1) φ

postulate
  thm-unshunt
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ unshunt φ

thm-inv-unshunt
  : ∀ {Γ} {φ}
  → Γ ⊢ unshunt φ
  → Γ ⊢ φ

thm-inv-unshunt {_} {φ} = thm-inv-unshunt′ (calls-unshunt φ + 1)

data StripView : Prop → Set where
  conj     : (φ₁ φ₂ : Prop) → StripView (φ₁ ∧ φ₂)
  disj     : (φ₁ φ₂ : Prop) → StripView (φ₁ ∨ φ₂)
  impl     : (φ₁ φ₂ : Prop) → StripView (φ₁ ⇒ φ₂)
  biimpl   : (φ₁ φ₂ : Prop) → StripView (φ₁ ⇔ φ₂)
  nconj    : (φ₁ φ₂ : Prop) → StripView (¬ (φ₁ ∧ φ₂))
  ndisj    : (φ₁ φ₂ : Prop) → StripView (¬ (φ₁ ∨ φ₂))
  nimpl    : (φ₁ φ₂ : Prop) → StripView (¬ (φ₁ ⇒ φ₂))
  nbiimpl  : (φ₁ φ₂ : Prop) → StripView (¬ (φ₁ ⇔ φ₂))
  nneg     : (φ₁ : Prop)    → StripView (¬ ¬ φ₁)
  nbot     : StripView (¬ ⊥)
  ntop     : StripView (¬ ⊤)
  other    : (φ₁ : Prop)    → StripView φ₁

strip-view : (φ : Prop) → StripView φ
strip-view (φ₁ ∧ φ₂)     = conj _ _
strip-view (φ₁ ∨ φ₂)     = disj _ _
strip-view (φ₁ ⇒ φ₂)     = impl _ _
strip-view (φ₁ ⇔ φ₂)     = biimpl _ _
strip-view (¬ ⊤)         = ntop
strip-view (¬ ⊥)         = nbot
strip-view (¬ (φ₁ ∧ φ₂)) = nconj _ _
strip-view (¬ (φ₁ ∨ φ₂)) = ndisj _ _
strip-view (¬ (φ₁ ⇒ φ₂)) = nimpl _ _
strip-view (¬ (φ₁ ⇔ φ₂)) = nbiimpl _ _
strip-view (¬ (¬ φ₁))    = nneg _
strip-view φ₁            = other _


split-goal₀ : Prop → Prop
split-goal₀ φ
  with strip-view φ
...  | conj φ₁ φ₂    = unshunt (split-goal₀ φ₁) ∧ unshunt (φ₁ ⇒ split-goal₀ φ₂)
...  | disj φ₁ φ₂    = unshunt (¬ φ₁ ⇒ (split-goal₀ φ₂))
...  | impl φ₁ φ₂    = unshunt (φ₁ ⇒ (split-goal₀ φ₂))
...  | biimpl φ₁ φ₂  = unshunt (φ₁ ⇒ (split-goal₀ φ₂)) ∧ unshunt (φ₂ ⇒ (split-goal₀ φ₁))
...  | nconj φ₁ φ₂   = unshunt (φ₁ ⇒ (split-goal₀ (¬ φ₂)))
...  | ndisj φ₁ φ₂   = unshunt (split-goal₀ (¬ φ₁)) ∧ unshunt (¬ φ₁ ⇒ split-goal₀ (¬ φ₂))
...  | nimpl φ₁ φ₂   = unshunt (split-goal₀ φ₁) ∧ unshunt ( ¬ φ₁ ⇒ split-goal₀ (¬ φ₂))
...  | nbiimpl φ₁ φ₂ =
  unshunt (split-goal₀ φ₁) ∧ unshunt ( ¬ φ₁ ⇒ split-goal₀ (¬ φ₂))
  ∧ unshunt (split-goal₀ φ₂) ∧ unshunt ( ¬ φ₂ ⇒ split-goal₀ (¬ φ₁))
...  | nneg φ₁       = unshunt (split-goal₀ φ₁)
...  | nbot          = ⊤
...  | ntop          = ⊥
...  | other .φ      = φ

-- * SplitGoal theorem.
thm
  : ∀ {Γ} {φ}
  → Γ ⊢ split-goal₀ φ
  → Γ ⊢ φ

thm {Γ} {φ} split with strip-view φ
thm {Γ} {.(φ₁ ∧ φ₂)} split | conj φ₁ φ₂ =
  ∧-intro p (thm (⇒-elim (thm-inv-unshunt (∧-proj₂ split)) p ))
  where
    p : Γ ⊢ φ₁
    p = thm (thm-inv-unshunt (∧-proj₁ split))

thm {Γ} {.(φ₁ ∨ φ₂)} split | disj φ₁ φ₂ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ φ₂ (assume {Γ = Γ} φ₁))
        (∨-intro₂ φ₁
          (thm
            (⇒-elim
              (thm-inv-unshunt
                (weaken (¬ φ₁) split))
              (assume {Γ = Γ} (¬ φ₁)))))))
    (PEM {Γ = Γ} {φ = φ₁})

thm {Γ} {.(φ₁ ⇒ φ₂)} split | impl φ₁ φ₂ =
 ⇒-intro
   (thm
     (⇒-elim
       (weaken φ₁
         (thm-inv-unshunt split))
         (assume {Γ = Γ} φ₁)))

thm {Γ} {.(φ₁ ⇔ φ₂)} split    | biimpl φ₁ φ₂ =
  ⇔-equiv₂ (∧-intro p1 p2)
  where
    p1 : Γ ⊢ φ₁ ⇒ φ₂
    p1 = ⇒-intro
         (thm
           (⇒-elim
             (weaken φ₁
               (thm-inv-unshunt (∧-proj₁ split)))
             (assume {Γ = Γ} φ₁)))

    p2 : Γ ⊢ φ₂ ⇒ φ₁
    p2 = ⇒-intro
          (thm
            (⇒-elim
              (weaken φ₂
                (thm-inv-unshunt (∧-proj₂ split)))
             (assume {Γ = Γ} φ₂)))

thm {Γ} {.(¬ (φ₁ ∧ φ₂))} split | nconj φ₁ φ₂ =
  {!!} --  ¬∨¬-to-¬∧ (⇒-to-¬∨ {!!})
  where
    p1 : Γ ⊢ φ₁ ⇒ ¬ φ₂
    p1 =
      (⇒-intro
        (thm {!!}))
          -- (⇒-elim
          --   (weaken φ₁
          --     (thm-inv-unshunt split))
          -- (assume {Γ = Γ} φ₁))))

thm {Γ} {.(¬ (φ₁ ∨ φ₂))} split | ndisj φ₁ φ₂ = {!!}
thm {Γ} {.(¬ (φ₁ ⇒ φ₂))} split | nimpl φ₁ φ₂ = {!!}
thm {Γ} {.(¬ (φ₁ ⇔ φ₂))} split | nbiimpl φ₁ φ₂ = {!!}
thm {Γ} {.(¬ (¬ φ₁))} split | nneg φ₁ = ¬¬-equiv₂ (thm (thm-inv-unshunt split))
thm {Γ} {.(¬ ⊥)} split | nbot = ¬-intro (assume {Γ = Γ} ⊥)
thm {Γ} {.(¬ ⊤)} split | ntop = ⊥-elim (¬ ⊤) split
thm {Γ} {.φ₁} split | other φ₁ = split

postulate
  thm-split-goal₀
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ split-goal₀ φ

-- thm-split-goal₀
--   : ∀ {Γ} {φ}
--   → (n : ℕ)
--   → Γ ⊢ φ
--   → Γ ⊢ split-goal₀ φ

-- thm-split-goal₀ {Γ} {φ} n Γ⊢φ = ?

split-goal : Prop → Prop
split-goal = unshunt ∘ split-goal₀

thm-split-goal
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ split-goal φ

thm-split-goal = thm-unshunt ∘ thm-split-goal₀

strip_to_ : Prop → Prop → Prop
strip φ to ψ = conjunct (split-goal φ) ψ

postulate
  atp-strip-to
    : ∀ {Γ} {φ}
    → (ψ : Prop)
    → Γ ⊢ φ
    → Γ ⊢ strip φ to ψ

postulate
  atp-splitGoal
    : ∀ {Γ} {φ}
    → Γ ⊢ split-goal φ ⇒ φ
