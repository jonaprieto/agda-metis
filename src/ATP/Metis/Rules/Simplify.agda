------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Simplify inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Simplify ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool.Base
  using    ( Bool; true; false )
  renaming ( _∨_ to _or_; _∧_ to _and_ )

open import Data.Prop.Syntax n
open import Data.Prop.Dec n        using ( ⌊_⌋ )
open import Data.Prop.Properties n using ( eq )

open import Function               using ( id )

------------------------------------------------------------------------------

isOpposite : Prop → Prop → Bool
isOpposite (¬ (¬ φ)) ψ = isOpposite φ ψ
isOpposite φ (¬ (¬ ψ)) = isOpposite φ ψ
isOpposite φ ψ = ⌊ eq φ (¬ ψ) ⌋ or ⌊ eq (¬ φ) ψ ⌋

simplify : Prop → Prop → Prop

simplify ⊥ φ      = ⊥
simplify φ ⊥      = ⊥

{-
simplify (φ ⇒ ψ) ω with ⌊ eq φ ω ⌋
... | true  = ψ
... | false = (φ ⇒ ψ) ∧ ω

simplify (φ ⇔ (ψ ⇔ ω)) ρ with ⌊ eq φ ρ ⌋ | ⌊ eq ψ ρ ⌋ | ⌊ eq ω ρ ⌋
... | true | _    | _     = (ψ ⇔ ω)
... | _    | true | _     = (φ ⇔ ω)
... | _    | _    | true  = (φ ⇔ ψ)
... | _    | _    | false with ⌊ eq (φ ⇔ ψ) ρ ⌋
...                       | true  = ω
...                       | false with ⌊ eq (φ ⇔ ω) ρ ⌋
...                               | true  = ψ
...                               | false with ⌊ eq (ψ ⇔ ω) ρ ⌋
...                                       | true = φ
...                                       | false = φ ⇔ (ψ ⇔ ω)
simplify (¬ ⊥)  φ = φ
simplify (¬ ⊤)  φ = ⊥
simplify ⊤ φ      = φ
simplify φ ⊤      = φ

simplify φ  (ψ ∨ ω) with isOpposite φ (¬ ψ)
... | true  = ω
... | false with isOpposite φ (¬ ω)
...         | true  = ψ
...         | false = φ ∧ (ψ ∨ ω)

simplify (φ ∨ ψ) (ω ∧ ρ) with isOpposite φ ω | isOpposite ψ ρ
... | true | _    = ψ ∧ ρ
... | _    | true = φ ∧ ρ
... | _    | _    = (φ ∨ ψ) ∧ ω ∧ ρ


simplify (φ ∨ ψ) ω with isOpposite ω (¬ φ)
... | true  = ψ
... | false with isOpposite ω (¬ ψ)
...         | true  = φ
...         | false = (φ ∨ ψ) ∧ ω


-}

simplify (φ ∧ ψ) ω with isOpposite φ ψ or isOpposite φ ω or isOpposite ψ ω
... | true   = ⊥
... | false = φ ∧ ψ ∧ ω

simplify ω (φ ∧ ψ) with isOpposite φ ψ or isOpposite φ ω or isOpposite ψ ω
... | true   = ⊥
... | false = φ ∧ ψ ∧ ω

simplify φ ψ with ⌊ eq φ ψ ⌋
simplify φ ψ | true  = φ
simplify φ ψ | false with ⌊ eq φ (¬ ψ) ⌋ | ⌊ eq (¬ φ) ψ ⌋
simplify φ ψ | false | false | false = φ ∧ ψ
simplify φ ψ | false | _     | _     = ⊥


postulate
  atp-simplify :
      ∀ {Γ} {φ ψ}
    → Γ ⊢ φ
    → Γ ⊢ ψ
    → Γ ⊢ simplify φ ψ


{-
atp-simplify : ∀ {Γ} {φ}
             → Γ ⊢ φ
             → Γ ⊢ simplify φ

atp-simplify {Γ} {Var x} = id
atp-simplify {Γ} {⊤}     = id
atp-simplify {Γ} {⊥}     = id
atp-simplify {Γ} {φ = φ₁ ∧ ¬ φ₂} = atp-step-simplify
atp-simplify {Γ} {¬ φ ∧ ψ}       = atp-step-simplify
atp-simplify {Γ} {φ}             = atp-step-simplify
-}

-- thm-simplify₀ : ∀ {Γ} {φ ψ}
--               → Γ ⊢ φ
--               → Γ ⊢ ¬ φ ⇔ ψ
--               → Γ ⊢ ¬ ψ
--
-- thm-simplify₀ {Γ}{φ}{ψ} =
--   {! ¬-intro  !}

-- open import Data.List using (List ; [] ; _∷_ ; _++_ ; [_])
--
-- toAnd : Prop → List Prop
-- toAnd (φ ∧ ψ) = toAnd φ ++ toAnd ψ
-- toAnd φ = [ φ ]
--
--
-- -- Plan:
-- simplify2 : List Prop → Prop
-- simplify2 []     = ⊤
-- simplify2 [ φ ]  = ?
-- simplify2 (φ ∷ ψ   φs) with ⌊ eq φ ψ ⌋
-- ... | true  = simplify2 (ψ ∷ φs)
-- ... | false = ?
