------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Strip inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Strip ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Prop.Syntax n
open import Data.Prop.Theorems.Negation n using ( ¬-⊤; ¬-⊥₁ )

open import Data.Bool
  renaming ( _∧_ to _&&_; _∨_ to _||_ )
  using    ( Bool; true; false; if_then_else_ )
open import Data.List using ( List ; [] ; _∷_ ; _++_ ; [_] ; foldl)

open import Function                      using ( _$_; id )

------------------------------------------------------------------------------

strip : Prop → Prop
strip (Var x) = (Var x)
strip (¬ ⊤)   = ⊥
strip (¬ ⊥)   = ⊤
strip (¬ φ)   = ¬ φ
strip (φ₁ ∨ φ₂ ∨ φ₃)   = (¬ φ₁) ∧ (¬ φ₂) ⇒ φ₃
strip (φ ∨ ψ)          = (¬ φ) ⇒ ψ
strip (φ₁ ⇒ (φ₂ ⇒ φ₃)) = φ₁ ∧ strip (φ₂ ⇒ φ₃)
strip φ = φ


postulate
  atp-step-strip : ∀ {Γ} {φ}
                 → Γ ⊢ φ
                 → Γ ⊢ strip φ

atp-strip : ∀ {Γ : Ctxt} {φ : Prop} → Γ ⊢ φ → Γ ⊢ strip φ
atp-strip {Γ} {Var x}          = id
atp-strip {Γ} {φ₁ ⇒ (φ₂ ⇒ φ₃)} = atp-step-strip
atp-strip {Γ} {¬ ⊤}            = ¬-⊤
atp-strip {Γ} {¬ ⊥}            = ¬-⊥₁
atp-strip {Γ} {φ}              = atp-step-strip


------------------------------------------------------------------------------
-- Spliting the goal.
------------------------------------------------------------------------------


listMkConj : List Prop → Prop
listMkConj []         = ⊤
listMkConj (fm ∷ fms) = foldl (_∧_) fm fms

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
    flat acc ((p ⇔ q) ∷ fms) = flat (p ∷ acc) (q ∷ fms)
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
                        → Γ ⊢ (splitGoal φ ⇒ φ)
