------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Canonicalize inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Canonicalize ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool.Base                   using ( true; false )

open import Data.Prop.Syntax n
open import Data.Prop.Dec n                  using ( ⌊_⌋ ; yes ; no )
open import Data.Prop.Properties n           using ( eq ; subst )

open import Data.Prop.Theorems.Implication n using ( ⇒-equiv ; th244e )
open import Data.Prop.Theorems.Negation n    using ( ¬-⊤; ¬-⊥₁ )
open import Data.Prop.Theorems.Mixies n      using ( neg-⇒ )

open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym ; trans)
open import Function                         using ( _$_; id ; _∘_ )

------------------------------------------------------------------------------

canonicalize : Prop → Prop
canonicalize (φ ⇒ ψ)     = ¬ φ ∨ ψ
canonicalize (¬ (φ ⇒ ψ)) with ⌊ eq φ ψ ⌋
... | true  = ⊥
... | false = canonicalize φ ∧ canonicalize (¬ ψ)
canonicalize (¬ ⊤)       = ⊥
canonicalize (¬ ⊥)       = ⊤
canonicalize (¬ (¬ φ))   = canonicalize φ
canonicalize φ           = φ



postulate
  atp-step-canonicalize :
      ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ canonicalize φ


atp-canonicalize : ∀ {Γ} {φ}
                 → Γ ⊢ φ
                 → Γ ⊢ canonicalize φ

atp-canonicalize {Γ} {Var x}       = id
atp-canonicalize {Γ} {⊤}           = id
atp-canonicalize {Γ} {⊥}           = id
atp-canonicalize {Γ} {φ ∧ φ₁}      = id
atp-canonicalize {Γ} {φ ∨ φ₁}      = id
atp-canonicalize {Γ} {φ ⇒ φ₁}      = ⇒-equiv
atp-canonicalize {Γ} {¬ (¬ φ)} seq = atp-canonicalize (⇒-elim th244e seq)
atp-canonicalize {Γ} {f@(¬ (φ ⇒ ψ))} seq with eq φ ψ
... | yes p1 = ¬-elim seq (⇒-intro (subst p1 (assume {Γ = Γ} φ)))
... | no  _  =
          ∧-intro
            (atp-canonicalize
              (∧-proj₁ (neg-⇒ seq)))
            (atp-canonicalize
              (∧-proj₂ (neg-⇒ seq)))

atp-canonicalize {Γ} {¬ ⊤}        = ¬-⊤
atp-canonicalize {Γ} {¬ ⊥}        = ¬-⊥₁
atp-canonicalize {Γ} {φ ⇔ φ₁}     = id
atp-canonicalize {Γ} {¬ Var x}    = id
atp-canonicalize {Γ} {¬ (φ ∧ φ₁)} = id
atp-canonicalize {Γ} {¬ (φ ∨ φ₁)} = id
atp-canonicalize {Γ} {¬ (φ ⇔ φ₁)} = id
