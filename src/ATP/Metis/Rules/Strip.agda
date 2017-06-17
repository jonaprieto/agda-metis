------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Strip inference rule.
------------------------------------------------------------------------------

-- {-# OPTIONS --exact-split #-}
{-# OPTIONS --allow-unsolved-metas #-}


open import Data.Nat using ( ℕ ; zero ; suc )

module ATP.Metis.Rules.Strip ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool
  renaming ( _∧_ to _&&_; _∨_ to _||_ )
  using    ( Bool; true; false; if_then_else_ )

open import Data.List using ( List ; [] ; _∷_ ; _++_ ; [_] ; foldl )
open import Data.Prop.Syntax n
open import Data.Prop.Theorems n

open import Function                      using ( _$_; id; _∘_ )
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

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

postulate
  helper
    : ∀ {Γ} {φ₁ φ₂ ψ}
    → Γ ⊢ φ₁ ⇒ ψ
    → Γ ⊢ φ₂ ⇒ ψ
    → Γ ⊢ (φ₁ ∧ φ₂) ⇒ ψ

data View : Prop → Set where
  conj : (φ ψ : Prop) → View (φ ∧ ψ)
  other : (φ : Prop) → View φ

view : (φ : Prop) → View φ
view (φ ∧ ψ) = conj _ _
view φ       = other _

q : ∀ {Γ} → Γ ⨆ [] ≡ Γ
q {[]}    = refl
q {x ∷ Γ} rewrite q {Γ = Γ} = refl

p : ∀ {Γ Δ} {ψ} →  Γ ⨆ (ψ ∷ Δ) ≡ (Γ ⨆ Δ) , ψ
p {Γ} {[]} {ψ} rewrite q {Γ = Γ} = refl
p {Γ} {x ∷ Δ} {ψ} rewrite p {Γ = Γ} {Δ = Δ} {ψ = x} = {!!}
  where
  o : ((Γ ++ Δ) ++ x ∷ []) ++ ψ ∷ [] ≡ (Γ ++ x ∷ Δ) ++ ψ ∷ []
  o = {!!}


from⊢₂
  : ∀ {Γ Δ} {φ}
  → Γ ∙ Δ ⊢₂ φ
  → Γ ⨆ Δ ⊢ φ

from⊢₂ {Γ} {.[]} {φ} (none x)                  = weaken-Δ₁ [] x
from⊢₂ {Γ} {ψ ∷ []} {φ} (weaken .ψ (none Γ⊢φ)) = weaken ψ Γ⊢φ
from⊢₂ {Γ} {ψ ∷ Δ} {φ} (weaken .ψ teo)    rewrite p {Γ = Γ} {Δ = Δ} {ψ = ψ} =  weaken ψ help
  where
  help : Γ ⨆ Δ ⊢ φ
  help = from⊢₂ teo


-- from⊢₂ {Γ} {.[]}       {φ} (none x)             = ⇒-intro (weaken ⊤ x)
-- from⊢₂ {Γ} {.(ψ ∷ [])} {φ} (weaken ψ (none x)) = ⇒-intro (weaken ψ x)
-- from⊢₂ {Γ} {ψ ∷ Δ}         {φ} Γ∙Δ,ψ⊢₂φ = {!helper!}

stripConj : Prop → List Prop
stripConj ⊤  = []
stripConj fm = strip' [] fm
  where
    strip' : List Prop → Prop → List Prop
    strip' cs (p ∧ q) = strip' (cs ++ [ p ]) q
    strip' cs fm      = cs ++ [ fm ]

strip-∧ : Prop → Prop
strip-∧ fm = listMkConj $ stripConj fm

-- strip of disjunctions.

listMkDisj : List Prop → Prop
listMkDisj []         = ⊥
listMkDisj (fm ∷ fms) = foldl (_∨_) fm fms

stripDisj : Prop → List Prop
stripDisj ⊥  = []
stripDisj fm = strip' [] fm
  where
    strip' : List Prop → Prop → List Prop
    strip' cs (p ∨ q) = strip' (cs ++ [ p ]) q
    strip' cs fm      = cs ++ [ fm ]

strip-∨ : Prop → Prop
strip-∨ fm = listMkDisj $ stripDisj fm

-- strip of equivalences.

listMkEquiv : List Prop → Prop
listMkEquiv []         = ⊤
listMkEquiv (fm ∷ fms) = foldl (_⇔_) fm fms

stripEquiv : Prop → List Prop
stripEquiv ⊤  = []
stripEquiv fm = strip' [] fm
  where
    strip' : List Prop → Prop → List Prop
    strip' cs (p ⇔ q) = strip' ( cs ++ [ p ]) q
    strip' cs fm      = cs ++ [ fm ]

flatEquiv : Prop → List Prop
flatEquiv fm = flat [] [ fm ]
  where
    flat : List Prop → List Prop → List Prop
    flat acc []              = acc
    flat acc (p ⇔ q ∷ fms) = flat (p ∷ acc) (q ∷ fms)
    flat acc (⊤ ∷ fms)       = flat acc fms
    flat acc (fm ∷ fms)      = flat (fm ∷ acc) fms

strip-⇔ : Prop → Prop
strip-⇔ fm = listMkEquiv $ stripEquiv fm

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
