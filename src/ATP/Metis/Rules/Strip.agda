------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Strip inference rule.
------------------------------------------------------------------------------

-- {-# OPTIONS --exact-split #-}
{-# OPTIONS --allow-unsolved-metas #-}


open import Data.Nat using ( ℕ ; zero ; suc; _+_ )

module ATP.Metis.Rules.Strip ( n : ℕ ) where

------------------------------------------------------------------------------

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


data _∙_⊢₂_ (Γ : Ctxt) : Ctxt → Prop → Set where
  none   : ∀ {φ}     → Γ ⊢ φ                   → Γ ∙ [] ⊢₂ φ
  weaken : ∀ {Δ} {φ} → (ψ : Prop) → Γ ∙ Δ ⊢₂ φ → Γ ∙ (ψ ∷ Δ) ⊢₂ φ

to⊢₂
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (Δ : Ctxt)
  → Γ ∙ Δ ⊢₂ φ

to⊢₂ {Γ}{φ} Γ⊢φ []      = none Γ⊢φ
to⊢₂ {Γ}{φ} Γ⊢φ (x ∷ Δ) = weaken x (to⊢₂ Γ⊢φ Δ)

data TView : Prop → Set where
  top   : TView ⊤
  other : (φ : Prop) → TView φ

t-view : (φ : Prop) → TView φ
t-view ⊤ = top
t-view φ = other _

flat-∧ : Ctxt → Prop
flat-∧ []      = ⊤
flat-∧ (φ ∷ Δ) = φ ∧ flat-∧ Δ

from-⊢₂
  : ∀ {Γ Δ} {φ}
  → Γ ∙ Δ ⊢₂ φ
  → Γ ⊢ flat-∧ Δ ⇒ φ

from-⊢₂ {Γ} {.[]}    {φ} (none x)             = ⇒-intro (weaken ⊤ x)
from-⊢₂ {Γ} {ψ ∷ []} {φ} (weaken .ψ (none x)) = ⇒-intro (weaken (ψ ∧ ⊤) x)
from-⊢₂ {Γ} {ψ ∷ Δ}  {φ} (weaken .ψ Γ∙Δ⊢₂φ)   =
  ⇒-intro
    (⇒-elim
      (weaken (flat-∧ (ψ ∷ Δ))
        (from-⊢₂ Γ∙Δ⊢₂φ))
      (∧-proj₂
        (assume {Γ = Γ} (flat-∧ (ψ ∷ Δ)))))


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


data StripAuxView : Prop → Set where
  case₁ : (φ₁ φ₂ φ₃ : Prop) → StripAuxView (φ₁ ⇒ (φ₂ ⇒ φ₃))
  case₂ : (φ₁ φ₂ φ₃ : Prop) → StripAuxView (φ₁ ⇒ (φ₂ ∧ φ₃))
  other : (φ : Prop)        → StripAuxView φ


strip-aux-view : (φ : Prop) → StripAuxView φ
strip-aux-view (φ₁ ⇒ (φ₂ ⇒ φ₃)) = case₁ _ _ _
strip-aux-view (φ₁ ⇒ (φ₂ ∧ φ₃)) = case₂ _ _ _
strip-aux-view φ                = other _

strip-aux : ℕ → Prop → Prop
strip-aux zero φ  = φ
strip-aux (suc n) φ with strip-aux-view φ
... | case₁ φ₁ φ₂ φ₃ = strip-aux n ((φ₁ ∧ φ₂) ⇒ φ₃)
... | case₂ φ₁ φ₂ φ₃ = (strip-aux n (φ₁ ⇒ φ₂)) ∧ (strip-aux n (φ₁ ⇒ φ₃))
... | other _       = φ

♯calls-strip-aux : Prop → ℕ
♯calls-strip-aux φ with strip-aux-view φ
... | case₁ _ _ φ₃  = 2 + ♯calls-strip-aux φ₃
... | case₂ _ φ₂ φ₃ = 1 + ♯calls-strip-aux φ₂ + ♯calls-strip-aux φ₃
... | other .φ      = 1

postulate
  thm-strip-aux
    : ∀ {Γ} {φ}
    → (n : ℕ)
    → Γ ⊢ φ
    → Γ ⊢ strip-aux n φ

unshunt : Prop → Prop
unshunt φ = strip-aux (♯calls-strip-aux φ) φ

postulate
  thm-unshunt
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ unshunt φ

strip₀ : ℕ → Prop → Prop
strip₀ zero φ        = φ
strip₀ (suc n) φ
  with n-view φ
...  | conj φ₁ φ₂   = strip₀ n φ₁ ∧ unshunt (φ₁ ⇒ strip₀ n φ₂)
...  | disj φ₁ φ₂   = unshunt (¬ φ₁ ⇒ (strip₀ n φ₂))
...  | impl φ₁ φ₂   = unshunt (φ₁ ⇒ (strip₀ n φ₂))
...  | biimpl _ _   = φ
...  | nconj φ₁ φ₂  = unshunt (¬ φ₁ ⇒ (strip₀ n (¬ φ₂)))
...  | ndisj φ₁ φ₂  = strip₀ n (¬ φ₁) ∧ unshunt (¬ φ₁ ⇒ strip₀ n (¬ φ₂))
...  | nneg φ₁      = strip₀ n φ₁
...  | ntop         = ⊥
...  | nbot         = ⊤
...  | nimpl φ₁ φ₂  = strip₀ n φ₁ ∧ unshunt (φ₁ ⇒ strip₀ n (¬ φ₂))
...  | nbiim _ _    = φ
...  | other .φ     = φ


postulate
  thm-strip₀
    : ∀ {Γ} {φ}
    → (n : ℕ)
    → Γ ⊢ φ
    → Γ ⊢ strip₀ n φ


-- thm-strip₀
--   : ∀ {Γ} {φ}
--   → (n : ℕ)
--   → Γ ⊢ φ
--   → Γ ⊢ strip₀ n φ

-- thm-strip₀ {Γ} {φ} zero Γ⊢φ = Γ⊢φ
-- thm-strip₀ {Γ} {φ} (suc n) Γ⊢φ
--   with n-view φ
-- ...  | conj φ₁ φ₂   =
--   ∧-intro
--     (thm-strip₀ n (∧-proj₁ Γ⊢φ))
--     (thm-strip₀ n (⇒-intro (weaken φ₁ (∧-proj₂ Γ⊢φ))))
-- ...  | disj φ₁ φ₂   = thm-strip₀ n (∨-to-¬⇒ Γ⊢φ)
-- ...  | impl φ₁ φ₂   = thm-strip₀ n (⇒-to-¬∨ Γ⊢φ)
-- ...  | biimpl φ₁ φ₂ = Γ⊢φ
-- ...  | nconj φ₁ φ₂  =
--   thm-strip₀ n
--     (⇒-intro
--       (⇒-elim
--         (⇒-intro
--           (∨-elim {Γ = Γ , φ₁}
--             (⊥-elim (¬ φ₂)
--               (¬-elim
--                 (assume {Γ = Γ , φ₁} (¬ φ₁))
--                 (weaken (¬ φ₁) (assume {Γ = Γ} φ₁))))
--             (assume {Γ = Γ , φ₁} (¬ φ₂))))
--         (weaken φ₁ (¬∧-to-¬∨¬ Γ⊢φ))))
-- ...  | ndisj φ₁ φ₂  =
--   ∧-intro
--     (thm-strip₀ n (∧-proj₁ (¬∨-to-¬∧¬ Γ⊢φ)))
--     (thm-strip₀ n
--       ((⇒-intro
--         (weaken (¬ φ₁)
--           ((∧-proj₂ (¬∨-to-¬∧¬ Γ⊢φ)))))))
-- ...  | nneg φ₁      = thm-strip₀ n (¬¬-equiv₁ Γ⊢φ)
-- ...  | ntop         = ¬-elim Γ⊢φ ⊤-intro
-- ...  | nbot         = ⊤-intro
-- ...  | nimpl φ₁ φ₂  =
--   ∧-intro
--     (thm-strip₀ n (∧-proj₁ (¬⇒-to-∧¬ Γ⊢φ)))
--     (thm-strip₀ n (⇒-intro (weaken φ₁ (∧-proj₂ (¬⇒-to-∧¬ Γ⊢φ)))))
-- ...  | nbiim φ₁ φ₂  = Γ⊢φ
-- ...  | other .φ     = Γ⊢φ


♯strip₀ : Prop → ℕ
♯strip₀ φ with n-view φ
...  | conj φ₁ φ₂   = 1 + ♯strip₀ φ₁ + ♯strip₀ φ₂
...  | disj φ₁ φ₂   = 1 + ♯strip₀ φ₂
...  | impl φ₁ φ₂   = 1 + ♯strip₀ φ₂
...  | biimpl _ _   = 0
...  | nconj φ₁ φ₂  = 1 + ♯strip₀ (¬ φ₂)
...  | ndisj φ₁ φ₂  = 1 + ♯strip₀ (¬ φ₁) + ♯strip₀ (¬ φ₂)
...  | nneg φ₁      = 1 + ♯strip₀ φ₁
...  | ntop         = 0
...  | nbot         = 0
...  | nimpl φ₁ φ₂  = 1 + ♯strip₀ φ₁ + ♯strip₀ (¬ φ₂)
...  | nbiim _ _    = 0
...  | other .φ     = 0


strip′ : Prop → Prop
strip′ φ = unshunt (strip₀ (♯strip₀ φ) φ)

postulate
  atp-strip′
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ strip′ φ

-- atp-strip′ {_} {φ} Γ⊢φ = thm-unshunt (thm-strip₀ (♯strip₀ φ) Γ⊢φ)
