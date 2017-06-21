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

open import Function                      using ( _$_; id; _∘_ )
open import Relation.Nullary renaming (¬_ to ¬₂)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≢_)

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Spliting the goal.
------------------------------------------------------------------------------

listMkConj : List Prop → Prop
listMkConj []         = ⊤
listMkConj (fm ∷ fms) = foldl (_∧_) fm fms

splitGoal₀ : Prop → List Prop
splitGoal₀ fm = split [] true fm
  where
    split : List Prop → Bool → Prop → List Prop
    split asms pol fm = case-split pol fm
      where
        case-split : Bool → Prop → List Prop
        -- positive splittables
        case-split true ⊤     = []
        case-split true (¬ f) = split asms false f
        case-split true (f₁ ∧ f₂) =
          (split asms true f₁) ++ (split (asms ++ [ f₁ ]) true f₂)
        case-split true (f₁ ∨ f₂) = split (asms ++ [ (¬ f₁) ]) true f₂
        case-split true (f₁ ⇒ f₂) = split (asms ++ [ f₁ ]) true f₂

        -- negative splittables
        case-split false ⊥ = []
        case-split false (¬ f) = split asms true f
        case-split false (f₁ ∧ f₂) = split (asms ++ [ f₁ ]) false f₂
        case-split false (f₁ ∨ f₂) =
          (split asms false f₁) ++ (split (asms ++ [ (¬ f₁) ]) false f₂)
        case-split false (f₁ ⇒ f₂) =
          (split asms true f₁) ++ (split (asms ++ [ (¬ f₁) ]) false f₂)
        case-split pol fm = [ addAsms asms (if pol then fm else (¬ fm)) ]
          where
            addAsms : List Prop → Prop → Prop
            addAsms [] goal   = goal
            addAsms asms goal = (listMkConj asms) ⇒ goal

splitGoal : Prop → Prop
splitGoal fm = flat $ splitGoal₀ fm
  where
    flat : List Prop → Prop
    flat []         = ⊤
    flat (φ ∷ [])   = φ
    flat (fm ∷ fms) = foldl (_∧_) fm fms

postulate atp-splitGoal : ∀ {Γ} {φ}
                        → Γ ⊢ splitGoal φ ⇒ φ

------------------------------------------------------------------------------
-- Strip rule.
------------------------------------------------------------------------------

strip : Prop → Prop

strip fm@(Var x)  = fm
strip ⊤           = ⊤
strip ⊥           = ⊥
strip fm@(φ ∧ φ₁) = fm

strip fm@(φ ∨ Var x)     = fm
strip fm@(φ ∨ ⊤)         = ⊤
strip fm@(φ ∨ ⊥)         = ¬ φ ⇒ ⊥
strip fm@(φ ∨ (φ₁ ∧ φ₂)) = fm
strip fm@(φ ∨ (φ₁ ∨ φ₂)) = (¬ φ ∧ ¬ φ₁) ⇒ φ₂
strip fm@(φ ∨ (φ₁ ⇒ φ₂)) = (¬ φ ∧ φ₁) ⇒ φ₂
strip fm@(φ ∨ (φ₁ ⇔ φ₂)) = fm
strip fm@(φ ∨ ¬ φ₁)      = ¬ φ ⇒ ¬ φ₁

-- split over the second term
-- strip fm@(φ ∨ ψ)         = ¬ φ ⇒ ψ


strip fm@(φ ⇒ Var x) = fm
strip fm@(φ ⇒ ⊤) = ⊤
strip fm@(φ ⇒ ⊥) = fm
strip fm@(φ ⇒ φ₁ ∧ φ₂) = fm -- generate two subgoals φ⇒φ₁ and φ⇒φ₂
strip fm@(φ ⇒ φ₁ ∨ φ₂) = (φ ∧ ¬ φ₁) ⇒ φ₂
strip fm@(φ ⇒ φ₁ ⇒ φ₂) = (φ ∧ φ₁) ⇒ φ₂
strip fm@(φ ⇒ φ₁ ⇔ φ₂) = fm -- none
strip fm@(φ ⇒ ¬ φ₁) = fm

-- this strip doesn't apply
strip fm@(φ ⇔ Var x)   = fm
strip fm@(φ ⇔ ⊤)       = fm
strip fm@(φ ⇔ ⊥)       = fm
strip fm@(φ ⇔ φ₁ ∧ φ₂) = fm
strip fm@(φ ⇔ φ₁ ∨ φ₂) = fm
strip fm@(φ ⇔ φ₁ ⇒ φ₂) = fm
strip fm@(φ ⇔ φ₁ ⇔ φ₂) = fm
strip fm@(φ ⇔ ¬ φ₁)    = fm

strip fm@(¬ Var x)     = fm
strip fm@(¬ ⊤)         = ⊥
strip fm@(¬ ⊥)         = ⊤
strip fm@(¬ (φ ∧ φ₁))  = φ ⇒ ¬ φ₁
strip fm@(¬ (φ ∨ φ₁))  = fm
strip fm@(¬ (φ ⇒ φ₁))  = fm
strip fm@(¬ (φ ⇔ φ₁))  = fm
strip (¬ (¬ φ))         = strip φ

------------------------------------------------------------------------------
-- atp-strip.
------------------------------------------------------------------------------

atp-strip : ∀ {Γ} {φ}
          → Γ ⊢ φ
          → Γ ⊢ strip φ

atp-strip {Γ} {Var x}  = id
atp-strip {Γ} {⊤}      = id
atp-strip {Γ} {⊥}      = id
atp-strip {Γ} {φ ∧ φ₁} = id

atp-strip {Γ} {φ ∨ Var x}     = id
atp-strip {Γ} {φ ∨ ⊤}         = λ _ → ⊤-intro
atp-strip {Γ} {φ ∨ ⊥}         = ∨-to-¬⇒
atp-strip {Γ} {φ ∨ (φ₁ ∧ φ₂)} = id
atp-strip {Γ} {φ ∨ (φ₁ ∨ φ₂)} Γ⊢φ∨⟪φ₁∨φ₂⟫ =
  subst⊢⇒₁
    (⇒-intro
      (¬∧¬-to-¬∨ (assume {Γ = Γ} (¬ φ ∧ ¬ φ₁))))
    (∨-to-¬⇒
      (∨-assoc₁ Γ⊢φ∨⟪φ₁∨φ₂⟫))

atp-strip {Γ} {φ ∨ (φ₁ ⇒ φ₂)} Γ⊢φ∨⟪φ₁⇒φ₂⟫ =
  subst⊢⇒₁
    (⇒-trans thm1 thm2)
    (∨-to-¬⇒
      (∨-assoc₁
        (subst⊢∨₂
          (⇒-intro (⇒-to-¬∨ (assume {Γ = Γ} (φ₁ ⇒ φ₂))))
          Γ⊢φ∨⟪φ₁⇒φ₂⟫)))
  where
    ⇒-to-¬¬ : ∀ {Γ} → Γ ⊢ φ₁ ⇒ ¬ (¬ φ₁)
    ⇒-to-¬¬ {Γ} =
      ⇒-intro $
        ¬¬-equiv₂ (assume {Γ = Γ} φ₁)

    thm1 : Γ ⊢ (¬ φ ∧ φ₁) ⇒ (¬ φ ∧ ¬ (¬ φ₁))
    thm1 =
      ⇒-intro
      (subst⊢∧₂
        (⇒-to-¬¬ {Γ = Γ , ¬ φ ∧ φ₁})
        (assume {Γ = Γ} (¬ φ ∧ φ₁)))

    thm2 : Γ ⊢ (¬ φ ∧ ¬ (¬ φ₁)) ⇒ ¬ (φ ∨ ¬ φ₁)
    thm2 =
      ⇒-intro
        (∨-dmorgan₂
          (assume {Γ = Γ} (¬ φ ∧ ¬ (¬ φ₁))))

atp-strip {Γ} {φ ∨ (φ₁ ⇔ φ₂)} = id
atp-strip {Γ} {φ ∨ ¬ φ₁}      = ∨-to-¬⇒

atp-strip {Γ} {φ ⇒ Var x} = id
atp-strip {Γ} {φ ⇒ ⊤} = λ _ → ⊤-intro
atp-strip {Γ} {φ ⇒ ⊥} = id
atp-strip {Γ} {φ ⇒ φ₁ ∧ φ₂} = id

atp-strip {Γ} {φ ⇒ (φ₁ ∨ φ₂)} Γ⊢φ⇒⟪φ₁∨φ₂⟫ =
  ⇒-intro
    (⇒-elim
      (⇒-intro
        (∨-elim {Γ = Γ , φ ∧ ¬ φ₁}
          (⊥-elim φ₂
            (¬-elim
              (weaken φ₁
                (∧-proj₂
                  (assume {Γ = Γ} (φ ∧ ¬ φ₁))))
              (assume {Γ = Γ , φ ∧ ¬ φ₁} φ₁)))
          (assume {Γ = Γ , φ ∧ ¬ φ₁ } φ₂)))
      (⇒-elim
        (weaken (φ ∧ ¬ φ₁) Γ⊢φ⇒⟪φ₁∨φ₂⟫)
        (∧-proj₁
          (assume {Γ = Γ} (φ ∧ ¬ φ₁)))))

atp-strip {Γ} {φ ⇒ φ₁ ⇒ φ₂} = ⇒⇒-to-∧⇒
atp-strip {Γ} {φ ⇒ φ₁ ⇔ φ₂} = id
atp-strip {Γ} {φ ⇒ ¬ φ₁}    = id

atp-strip {Γ} {φ ⇔ Var x}   = id
atp-strip {Γ} {φ ⇔ ⊤}       = id
atp-strip {Γ} {φ ⇔ ⊥}       = id
atp-strip {Γ} {φ ⇔ φ₁ ∧ φ₂} = id
atp-strip {Γ} {φ ⇔ φ₁ ∨ φ₂} = id
atp-strip {Γ} {φ ⇔ φ₁ ⇒ φ₂} = id
atp-strip {Γ} {φ ⇔ φ₁ ⇔ φ₂} = id
atp-strip {Γ} {φ ⇔ ¬ φ₁}    = id

atp-strip {Γ} {¬ Var x}     = id
atp-strip {Γ} {¬ ⊤}         = ¬⊤-to-⊥
atp-strip {Γ} {¬ ⊥}         = ¬⊥-to-⊤
atp-strip {Γ} {¬ (φ ∧ φ₁)}  Γ⊢¬⟪φ∧φ₁⟫ = ¬∨-to-⇒ (∧-dmorgan₁ Γ⊢¬⟪φ∧φ₁⟫)
atp-strip {Γ} {¬ (φ ∨ φ₁)}  = id
atp-strip {Γ} {¬ (φ ⇒ φ₁)}  = id
atp-strip {Γ} {¬ (φ ⇔ φ₁)}  = id
atp-strip {Γ} {¬ (¬ φ)} Γ⊢¬¬φ = atp-strip (¬¬-equiv₁ Γ⊢¬¬φ)

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

♯calls-unshunt : Prop → ℕ
♯calls-unshunt φ with unshunt-view φ
... | case₁ _ _ φ₃  = 2 + ♯calls-unshunt φ₃
... | case₂ _ φ₂ φ₃ = 1 + ♯calls-unshunt φ₂ + ♯calls-unshunt φ₃
... | other .φ      = 1

postulate
  thm-unshunt′
    : ∀ {Γ} {φ}
    → (n : ℕ)
    → Γ ⊢ φ
    → Γ ⊢ unshunt′ n φ

unshunt : Prop → Prop
unshunt φ = unshunt′ (♯calls-unshunt φ + 15) φ

postulate
  thm-unshunt
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ unshunt φ

data StripView : Prop → Set where
  conj  : (φ₁ φ₂ : Prop) → StripView (φ₁ ∧ φ₂)
  disj  : (φ₁ φ₂ : Prop) → StripView (φ₁ ∨ φ₂)
  impl  : (φ₁ φ₂ : Prop) → StripView (φ₁ ⇒ φ₂)
  nconj : (φ₁ φ₂ : Prop) → StripView (¬ (φ₁ ∧ φ₂))
  ndisj : (φ₁ φ₂ : Prop) → StripView (¬ (φ₁ ∨ φ₂))
  nimpl : (φ₁ φ₂ : Prop) → StripView (¬ (φ₁ ⇒ φ₂))
  nneg  : (φ₁ : Prop)    → StripView (¬ ¬ φ₁)
  nbot  : StripView (¬ ⊥)
  ntop  : StripView (¬ ⊤)
  other : (φ₁ : Prop)    → StripView φ₁

strip-view : (φ : Prop) → StripView φ
strip-view (φ₁ ∧ φ₂)     = conj _ _
strip-view (φ₁ ∨ φ₂)     = disj _ _
strip-view (φ₁ ⇒ φ₂)     = impl _ _
strip-view (¬ ⊤)         = ntop
strip-view (¬ ⊥)         = nbot
strip-view (¬ (φ₁ ∧ φ₂)) = nconj _ _
strip-view (¬ (φ₁ ∨ φ₂)) = ndisj _ _
strip-view (¬ (φ₁ ⇒ φ₂)) = nimpl _ _
strip-view (¬ (¬ φ₁))    = nneg _
strip-view φ₁            = other _


strip₀ : Prop → Prop
strip₀ φ
  with strip-view φ
...  | conj φ₁ φ₂   = unshunt (strip₀ φ₁) ∧ unshunt (φ₁ ⇒ strip₀ φ₂)
...  | disj φ₁ φ₂   = unshunt (¬ φ₁ ⇒ (strip₀ φ₂))
...  | impl φ₁ φ₂   = unshunt (φ₁ ⇒ (strip₀ φ₂))
...  | nconj φ₁ φ₂  = unshunt (φ₁ ⇒ (strip₀ (¬ φ₂)))
...  | ndisj φ₁ φ₂  = unshunt (strip₀ (¬ φ₁)) ∧ unshunt (¬ φ₁ ⇒ strip₀ (¬ φ₂))
...  | nimpl φ₁ φ₂  = unshunt (strip₀ φ₁) ∧ unshunt ( ¬ φ₁ ⇒ strip₀ (¬ φ₂))
...  | nneg φ₁      = unshunt (strip₀ φ₁)
...  | nbot         = ⊤
...  | ntop         = ⊥
...  | other .φ     = φ


postulate
  thm-strip₀
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ strip₀ φ

-- thm-strip₀
--   : ∀ {Γ} {φ}
--   → (n : ℕ)
--   → Γ ⊢ φ
--   → Γ ⊢ strip₀ φ

-- thm-strip₀ {Γ} {φ} n Γ⊢φ = ?

strip′ : Prop → Prop
strip′ = unshunt ∘ strip₀

thm-strip′
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ strip′ φ

thm-strip′ = thm-unshunt ∘ thm-strip₀

strip_to_ : Prop → Prop → Prop
strip φ to ψ = conjunct (strip′ φ) ψ

postulate
  atp-strip-to
    : ∀ {Γ} {φ}
    → (ψ : Prop)
    → Γ ⊢ φ
    → Γ ⊢ strip φ to ψ
