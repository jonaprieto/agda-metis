------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Canonicalize inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Canonicalize ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool.Base
  using    ( true; false )
  renaming ( _∨_ to _or_ )

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
... | false = canonicalize (¬ ψ) ∧ canonicalize φ
... | true  = ⊥
canonicalize (¬ (φ ∧ ψ)) with ⌊ eq φ (¬ ψ) ⌋ or ⌊ eq (¬ φ) ψ ⌋
... | false = canonicalize (¬ φ) ∨ canonicalize (¬ ψ)
... | true  = ⊤
canonicalize (φ ∧ ψ) with ⌊ eq φ (¬ ψ) ⌋ or ⌊ eq (¬ φ) ψ ⌋
... | false = canonicalize φ ∧ canonicalize ψ
... | true  = ⊥
canonicalize (¬ (¬ φ))   = canonicalize φ
canonicalize (¬ ⊤)       = ⊥
canonicalize (¬ ⊥)       = ⊤
canonicalize φ           = φ

------------------------------------------------------------------------------
-- atp-canonicalize.
------------------------------------------------------------------------------

atp-canonicalize
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ canonicalize φ

atp-canonicalize {Γ} {Var x}       = id
atp-canonicalize {Γ} {⊤}           = id
atp-canonicalize {Γ} {⊥}           = id

atp-canonicalize {Γ} {φ ∧ ψ} Γ⊢φ∧ψ with eq φ (¬ ψ) | eq (¬ φ) ψ
... | yes φ≡¬ψ | yes ¬φ≡ψ = ¬-elim (subst φ≡¬ψ (∧-proj₁ Γ⊢φ∧ψ)) (∧-proj₂ Γ⊢φ∧ψ)
... | yes φ≡¬ψ | no  ¬φ≢ψ = ¬-elim (subst φ≡¬ψ (∧-proj₁ Γ⊢φ∧ψ)) (∧-proj₂ Γ⊢φ∧ψ)
... | no  φ≢¬ψ | yes ¬φ≡ψ = ¬-elim (subst (sym ¬φ≡ψ) (∧-proj₂ Γ⊢φ∧ψ)) (∧-proj₁ Γ⊢φ∧ψ)
... | no  φ≢¬ψ | no  ¬φ≢ψ =
      ∧-intro
        (atp-canonicalize (∧-proj₁ Γ⊢φ∧ψ))
        (atp-canonicalize (∧-proj₂ Γ⊢φ∧ψ))

atp-canonicalize {Γ} {φ ∨ φ₁}      = id
atp-canonicalize {Γ} {φ ⇒ φ₁}      = ⇒-to-¬∨
atp-canonicalize {Γ} {¬ (¬ φ)}     = atp-canonicalize ∘ ¬¬-equiv₁
atp-canonicalize {Γ} {¬ (φ ⇒ ψ)} Γ⊢¬⟪φ⇒ψ⟫ with eq φ ψ
... | yes φ≡ψ = ¬-elim Γ⊢¬⟪φ⇒ψ⟫ (⇒-intro (subst φ≡ψ (assume {Γ = Γ} φ)))
... | no  φ≢ψ  =
          ∧-intro
            (atp-canonicalize (∧-proj₂ (¬⇒-to-∧¬ Γ⊢¬⟪φ⇒ψ⟫)))
            (atp-canonicalize (∧-proj₁ (¬⇒-to-∧¬ Γ⊢¬⟪φ⇒ψ⟫)))

atp-canonicalize {Γ} {¬ ⊤}        = ¬⊤-to-⊥
atp-canonicalize {Γ} {¬ ⊥}        = ¬⊥-to-⊤
atp-canonicalize {Γ} {φ ⇔ φ₁}     = id
atp-canonicalize {Γ} {¬ Var x}    = id

atp-canonicalize {Γ} {¬ (φ ∧ ψ)} Γ⊢¬⟪φ∧ψ⟫ with eq φ (¬ ψ) | eq (¬ φ) ψ
... | yes φ≡¬ψ | yes ¬φ≡ψ = ⊤-intro
... | yes φ≡¬ψ | no  ¬φ≢ψ = ⊤-intro
... | no  φ≢¬ψ | yes ¬φ≡ψ = ⊤-intro
... | no  φ≢¬ψ | no  ¬φ≢ψ =
    ⇒-elim
      (⇒-intro
        (∨-elim {Γ = Γ}
          (∨-intro₁ (canonicalize (¬ ψ)) (atp-canonicalize (assume {Γ = Γ} (¬ φ))))
          (∨-intro₂ (canonicalize (¬ φ)) (atp-canonicalize (assume {Γ = Γ} (¬ ψ))))))
      Γ⊢¬φ∨¬ψ
    where
      Γ⊢¬φ∨¬ψ : Γ ⊢ ¬ φ ∨ ¬ ψ
      Γ⊢¬φ∨¬ψ = ¬∧-to-¬∨¬ Γ⊢¬⟪φ∧ψ⟫

atp-canonicalize {Γ} {¬ (φ ∨ φ₁)} = id
atp-canonicalize {Γ} {¬ (φ ⇔ φ₁)} = id
