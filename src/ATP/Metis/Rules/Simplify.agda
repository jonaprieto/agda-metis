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
open import Data.Prop.Dec n        using ( ⌊_⌋ ; yes ; no )
open import Data.Prop.Properties n using ( eq ; subst )

open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym )
open import Function               using ( id )

------------------------------------------------------------------------------

isOpposite : Prop → Prop → Bool
isOpposite (¬ (¬ φ)) ψ = isOpposite φ ψ
isOpposite φ (¬ (¬ ψ)) = isOpposite φ ψ
isOpposite φ ψ = ⌊ eq φ (¬ ψ) ⌋ or ⌊ eq (¬ φ) ψ ⌋


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

simplify : Prop → Prop → Prop

simplify ⊥ φ      = ⊥
simplify φ ⊥      = ⊥

-- simplify (φ ∧ ψ) ω with isOpposite φ ψ or isOpposite φ ω or isOpposite ψ ω
-- ... | true   = ⊥
-- ... | false = φ ∧ ψ ∧ ω

-- simplify ω (φ ∧ ψ) with isOpposite φ ψ or isOpposite φ ω or isOpposite ψ ω
-- ... | true   = ⊥
-- ... | false = φ ∧ ψ ∧ ω

simplify φ ψ with ⌊ eq φ ψ ⌋
simplify φ ψ | true  = ψ
simplify φ ψ | false with ⌊ eq φ (¬ ψ) ⌋ | ⌊ eq (¬ φ) ψ ⌋
simplify φ ψ | false | false | false = φ ∧ ψ
simplify φ ψ | false | _     | _     = ⊥

postulate
  atp-simplify :
      ∀ {Γ} {φ ψ}
    → Γ ⊢ φ
    → Γ ⊢ ψ
    → Γ ⊢ simplify φ ψ

atp-simplify2 : ∀ {Γ} {φ ψ}
             → Γ ⊢ φ
             → Γ ⊢ ψ
             → Γ ⊢ simplify φ ψ

atp-simplify2 {Γ}{⊥}{_} seq₁ _    = seq₁
atp-simplify2 {Γ}{φ}{⊥} seq₁ seq₂ = ⊥-elim (simplify φ ⊥) seq₂
atp-simplify2 {Γ}{φ}{ψ} seq₁ seq₂ with eq (simplify φ ψ) ψ
... | yes p1 = subst (sym p1) seq₂
... | no ¬p1 with eq (simplify φ ψ) (φ ∧ ψ)
...   | yes p2 = subst {Γ = Γ} (sym p2) (∧-intro seq₁ seq₂)
...   | no ¬p2 with eq φ (¬ ψ) | eq (¬ φ) ψ | eq (φ ∧ ψ) (simplify φ ψ)
...     | yes φ≡¬ψ | _        | _ = ⊥-elim  (simplify φ ψ)
                                    (¬-elim (subst φ≡¬ψ seq₁) seq₂)
...     | no φ≢¬ψ  | yes ¬φ≡ψ | _ = ⊥-elim (simplify φ ψ)
                                    (¬-elim (subst (sym ¬φ≡ψ) seq₂) seq₁)
...     | no φ≢¬ψ  | no ¬φ≢ψ  | yes p3 = subst p3 (∧-intro seq₁ seq₂)
...     | no φ≢¬ψ  | no ¬φ≢ψ  | no ¬p3 = {!!}
