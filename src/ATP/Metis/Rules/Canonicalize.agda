------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Canonicalize inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Canonicalize ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool.Base                   using ( true; false )

open import Data.Prop.Dec n                  using ( ⌊_⌋ ; yes ; no )
open import Data.Prop.Properties n           using ( eq ; subst )
open import Data.Prop.Syntax n
open import Data.Prop.Theorems n

open import Function                         using ( _$_; id ; _∘_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym ; trans)

------------------------------------------------------------------------------

canonicalize : Prop → Prop
canonicalize (φ ⇒ ψ)     = ¬ φ ∨ ψ
canonicalize (¬ (φ ⇒ ψ)) with ⌊ eq φ ψ ⌋
... | false = canonicalize φ ∧ canonicalize (¬ ψ)
... | true  = ⊥
canonicalize (¬ (¬ φ))   = canonicalize φ
canonicalize (¬ ⊤)       = ⊥
canonicalize (¬ ⊥)       = ⊤
canonicalize φ           = φ

------------------------------------------------------------------------------
-- atp-canonicalize.
------------------------------------------------------------------------------

atp-canonicalize : ∀ {Γ} {φ}
                 → Γ ⊢ φ
                 → Γ ⊢ canonicalize φ

atp-canonicalize {Γ} {Var x}       = id
atp-canonicalize {Γ} {⊤}           = id
atp-canonicalize {Γ} {⊥}           = id
atp-canonicalize {Γ} {φ ∧ φ₁}      = id
atp-canonicalize {Γ} {φ ∨ φ₁}      = id
atp-canonicalize {Γ} {φ ⇒ φ₁}      = ⇒-to-¬∨
atp-canonicalize {Γ} {¬ (¬ φ)}     = atp-canonicalize ∘ ¬¬-equiv₁
atp-canonicalize {Γ} {¬ (φ ⇒ ψ)} Γ⊢¬⟪φ⇒ψ⟫ with eq φ ψ
... | yes φ≡ψ = ¬-elim Γ⊢¬⟪φ⇒ψ⟫ (⇒-intro (subst φ≡ψ (assume {Γ = Γ} φ)))
... | no  φ≢ψ  =
          ∧-intro
            (atp-canonicalize (∧-proj₁ (¬⇒-to-∧¬ Γ⊢¬⟪φ⇒ψ⟫)))
            (atp-canonicalize (∧-proj₂ (¬⇒-to-∧¬ Γ⊢¬⟪φ⇒ψ⟫)))

atp-canonicalize {Γ} {¬ ⊤}        = ¬⊤-to-⊥
atp-canonicalize {Γ} {¬ ⊥}        = ¬⊥-to-⊤
atp-canonicalize {Γ} {φ ⇔ φ₁}     = id
atp-canonicalize {Γ} {¬ Var x}    = id
atp-canonicalize {Γ} {¬ (φ ∧ φ₁)} = id
atp-canonicalize {Γ} {¬ (φ ∨ φ₁)} = id
atp-canonicalize {Γ} {¬ (φ ⇔ φ₁)} = id
