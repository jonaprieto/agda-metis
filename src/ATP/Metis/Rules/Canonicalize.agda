------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Canonicalize inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Canonicalize ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool.Base                   using ( true; false )

open import Data.Prop.Syntax n
open import Data.Prop.Dec n                  using ( ⌊_⌋ )
open import Data.Prop.Properties n           using ( eq )

open import Data.Prop.Theorems.Implication n using ( ⇒-equiv )
open import Data.Prop.Theorems.Negation n    using ( ¬-⊤; ¬-⊥₁ )

open import Function                         using ( _$_; id )

------------------------------------------------------------------------------

canonicalize : Prop → Prop
canonicalize (φ ⇒ ψ)     = ¬ φ ∨ ψ
canonicalize (¬ (φ ⇒ ψ)) with ⌊ eq φ ψ ⌋
... | true  = ⊥
... | false = canonicalize φ ∧ canonicalize (¬ ψ)
canonicalize (¬ ⊤)       = ⊥
canonicalize (¬ ⊥)       = ⊤
-- canonicalize (¬ (¬ φ))   = canonicalize φ
canonicalize φ           = φ



postulate
  atp-step-canonicalize :
      ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ canonicalize φ


atp-canonicalize : ∀ {Γ} {φ}
                 → Γ ⊢ φ
                 → Γ ⊢ canonicalize φ

atp-canonicalize {Γ} {Var x}      = id
atp-canonicalize {Γ} {⊤}          = id
atp-canonicalize {Γ} {⊥}          = id
atp-canonicalize {Γ} {φ ∧ φ₁}     = id
atp-canonicalize {Γ} {φ ∨ φ₁}     = id
atp-canonicalize {Γ} {φ ⇒ φ₁}     = ⇒-equiv
atp-canonicalize {Γ} {¬ (φ ⇒ φ₁)} = atp-step-canonicalize

atp-canonicalize {Γ} {¬ ⊤}        = ¬-⊤
atp-canonicalize {Γ} {¬ ⊥}        = ¬-⊥₁
atp-canonicalize {Γ} {φ}          = atp-step-canonicalize
