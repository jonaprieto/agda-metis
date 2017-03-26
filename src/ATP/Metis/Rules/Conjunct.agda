------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Conjunct inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Conjunct ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool.Base         using ( false; true )

open import Data.Prop.Syntax n
open import Data.Prop.Dec n        using ( yes; no; ⌊_⌋ )
open import Data.Prop.Properties n using ( eq )

open import Function               using ( _$_; id )

------------------------------------------------------------------------------

conjunct : Prop → Prop → Prop
conjunct (φ ∧ ψ) ω with ⌊ eq φ ω ⌋ | ⌊ eq ψ ω ⌋
... | true  | _     = φ
... | false | true  = ψ
... | false | false = conjunct φ ω
conjunct φ ω        = φ


atp-conjunct : ∀ {Γ} {φ}
             → (ω : Prop)
             → Γ ⊢ φ
             → Γ ⊢ conjunct φ ω

atp-conjunct {Γ} {φ ∧ ψ} ω seq with ⌊ eq φ ω ⌋ | ⌊ eq ψ ω ⌋
... | true  | _     = ∧-proj₁ seq
... | false | true  = ∧-proj₂ seq
... | false | false = atp-conjunct {Γ = Γ} {φ = φ} ω (∧-proj₁ seq)
atp-conjunct {_} {Var x} _  = id
atp-conjunct {_} {⊤} _      = id
atp-conjunct {_} {⊥} _      = id
atp-conjunct {_} {φ ∨ φ₁} _ = id
atp-conjunct {_} {φ ⇒ φ₁} _ = id
atp-conjunct {_} {φ ⇔ φ₁} _ = id
atp-conjunct {_} {¬ φ} _    = id
