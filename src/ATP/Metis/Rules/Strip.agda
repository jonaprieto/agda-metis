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
-- The following theorem about contraction intends to
-- simplify the expression providing a conjunction of the
-- assumptions whenever it's possible in just the following case:
--
--   Γ ⊢ φ₁ ⇒ (φ₂ ⇒ φ₃)
--   ────────────────────────────── (thm-contraction)
--   Γ ⊢ contraction (φ₁ ∧ φ₂ ⇒ φ₃)

data ContractionView : Prop → Set where
  impl  : (φ₁ φ₂ φ₃ : Prop) → ContractionView (φ₁ ⇒ (φ₂ ⇒ φ₃))
  other : (φ : Prop)        → ContractionView φ

contra-view : (φ : Prop) → ContractionView φ
contra-view (φ₁ ⇒ (φ₂ ⇒ φ₃)) = impl _ _ _
contra-view φ                = other _

contraction₀ : ℕ → Prop → Prop
contraction₀ (suc n) φ with contra-view φ
... | impl φ₁ φ₂ φ₃ = contraction₀ n ((φ₁ ∧ φ₂) ⇒ φ₃)
... | other _       = φ
contraction₀ zero φ = φ

steps-contraction : Prop → ℕ
steps-contraction φ with contra-view φ
... | impl _ _ φ₃ = 1 + steps-contraction φ₃
... | other _     = zero

thm-contraction′
  : ∀ {Γ} {φ}
  → (n : ℕ)
  → Γ ⊢ φ
  → Γ ⊢ contraction₀ n φ

thm-contraction′ {Γ} {φ} (suc n) Γ⊢φ
  with contra-view φ
...  | impl φ₁ φ₂ φ₃ =
  thm-contraction′ n
    (⇒-intro
      (⇒-elim
        (⇒-elim
          (weaken (φ₁ ∧ φ₂)
            Γ⊢φ)
          (∧-proj₁
            (assume {Γ = Γ} (φ₁ ∧ φ₂))))
      (∧-proj₂
        (assume {Γ = Γ} (φ₁ ∧ φ₂)))))
...  | other _       = Γ⊢φ
thm-contraction′ zero Γ⊢φ  = Γ⊢φ

contraction : Prop → Prop
contraction φ = contraction₀ (steps-contraction φ) φ

thm-contraction
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ contraction φ

thm-contraction {Γ} {φ} Γ⊢φ = thm-contraction′ (steps-contraction φ) Γ⊢φ
