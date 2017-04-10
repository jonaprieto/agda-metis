------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Simplify inference rule.
------------------------------------------------------------------------------

{-# OPTIONS --exact-split #-}

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Simplify ( n : ℕ ) where

------------------------------------------------------------------------------

open import Data.Bool.Base
  using    ( Bool; true; false )
  renaming ( _∨_ to _or_; _∧_ to _and_ )

open import Data.Prop.Syntax n
open import Data.Prop.Dec n        using ( ⌊_⌋; yes; no )
open import Data.Prop.Properties n using ( eq ; subst )
open import Data.Prop.Theorems n

open import Function               using ( id )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym )

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Simplify function takes the first formula of the input
-- and tries to simplify it based on the second one of the input.
------------------------------------------------------------------------------

simplify : Prop → Prop → Prop

simplify ⊤       φ = ⊤
simplify ⊥       φ = ⊥
simplify (Var x) ψ with ⌊ eq ⊥ ψ ⌋
... | true  = ⊥
... | false = Var x

simplify (¬ φ)  ψ with ⌊ eq φ ψ ⌋ |  ⌊ eq ⊥ φ ⌋ | ⌊ eq ⊤ φ ⌋
... | true  | true  | true  = ⊥
... | true  | true  | false = ⊥
... | true  | false | true  = ⊥
... | true  | false | false = ⊥
... | false | true  | true  = ⊥
... | false | true  | false = ψ
... | false | false | true  = ⊥
... | false | false | false = ¬ φ ∧ ψ

simplify (φ ⇔ ψ) ω with ⌊ eq φ ω ⌋ | ⌊ eq ψ ω ⌋
... | true  | false = ψ
... | true  | true  = ψ
... | false | true  = φ
... | false | false = (φ ⇔ ψ) ∧ ω


simplify (φ ⇒ ψ) ω with ⌊ eq φ ω ⌋
... | true  = ψ
... | false = (φ ⇒ ψ) ∧ ω

simplify (ψ ∨ ω) φ with ⌊ eq φ (¬ ψ) ⌋
... | true  = ω
... | false with ⌊ eq φ (¬ ω) ⌋
...         | true  = ψ
...         | false = (ψ ∨ ω) ∧ φ

simplify (φ ∧ ψ) ω with ⌊ eq φ (¬ ω) ⌋ or ⌊ eq ω (¬ φ) ⌋
... | true  = ⊥
... | false with  ⌊ eq ψ (¬ ω) ⌋ or ⌊ eq ω (¬ ψ) ⌋
...         | true  = ⊥
...         | false = (φ ∧ ψ) ∧ ω


------------------------------------------------------------------------------
-- Simplies preservs theorems, it just simplifies them.
------------------------------------------------------------------------------

atp-simplify : ∀ {Γ} {φ ψ}
             → Γ ⊢ φ
             → Γ ⊢ ψ
             → Γ ⊢ simplify φ ψ

------------------------------------------------------------------------------
atp-simplify {Γ} {Var x} {ψ}  Γ⊢Varx Γ⊢ψ with eq ⊥ ψ
... | yes ⊥≡ψ = subst (sym ⊥≡ψ) Γ⊢ψ
... | no  ⊥≢ψ = Γ⊢Varx
------------------------------------------------------------------------------

------------------------------------------------------------------------------
atp-simplify {Γ} {¬ φ} {ψ} Γ⊢¬φ Γ⊢ψ with eq φ ψ | eq ⊥ φ | eq ⊤ φ
... | yes φ≡ψ | yes ⊥≡φ | yes ⊤≡φ = ¬-elim Γ⊢¬φ (subst (sym φ≡ψ) Γ⊢ψ)
... | yes φ≡ψ | yes ⊥≡φ | no  ⊤≢φ = ¬-elim Γ⊢¬φ (subst (sym φ≡ψ) Γ⊢ψ)
... | yes φ≡ψ | no  ⊥≢φ | yes ⊤≡φ = ¬-elim Γ⊢¬φ (subst (sym φ≡ψ) Γ⊢ψ)
... | yes φ≡ψ | no  ⊥≢φ | no  ⊤≢φ = ¬-elim Γ⊢¬φ (subst (sym φ≡ψ) Γ⊢ψ)
... | no  φ≢ψ | yes ⊥≡φ | yes ⊤≡φ = ¬-⊤ (¬-inside (sym ⊤≡φ) Γ⊢¬φ)
... | no  φ≢ψ | yes ⊥≡φ | no  ⊤≢φ = Γ⊢ψ
... | no  φ≢ψ | no  ⊥≢φ | yes ⊤≡φ = ¬-⊤ (¬-inside (sym ⊤≡φ) Γ⊢¬φ)
... | no  φ≢ψ | no  ⊥≢φ | no  ⊤≢φ = ∧-intro Γ⊢¬φ Γ⊢ψ

------------------------------------------------------------------------------

------------------------------------------------------------------------------
atp-simplify {Γ} {φ ⇔ ψ} {ω} Γ⊢φ⇔ψ Γ⊢ω with eq φ ω | eq ψ ω
... | yes φ≡ω | yes ψ≡ω = subst (sym ψ≡ω) Γ⊢ω
... | yes φ≡ω | no  ψ≢ω = ⇔-elim₁ (subst (sym φ≡ω) Γ⊢ω) Γ⊢φ⇔ψ
... | no _    | yes ψ≡ω = ⇔-elim₂ (subst (sym ψ≡ω) Γ⊢ω) Γ⊢φ⇔ψ
... | no _    | no  ψ≢ω = ∧-intro Γ⊢φ⇔ψ Γ⊢ω
------------------------------------------------------------------------------

------------------------------------------------------------------------------
atp-simplify {Γ} {φ ⇒ ψ} {ω} Γ⊢φ⇒ψ Γ⊢ω with eq φ ω
... | yes φ≡ω = ⇒-elim Γ⊢φ⇒ψ (subst (sym φ≡ω) Γ⊢ω)
... | no  φ≢ω = ∧-intro Γ⊢φ⇒ψ Γ⊢ω
------------------------------------------------------------------------------

------------------------------------------------------------------------------
atp-simplify {Γ} {ψ ∨ ω} {φ} Γ⊢ψ∨ω Γ⊢φ with eq φ (¬ ψ)
... | yes φ≡¬ψ  = resolve₇ Γ⊢ψ∨ω Γ⊢¬ψ
    where
      Γ⊢¬ψ : Γ ⊢ ¬ ψ
      Γ⊢¬ψ = subst φ≡¬ψ Γ⊢φ

... | no  φ≢¬ψ  with eq φ (¬ ω)
...         | yes φ≡¬ω = resolve₆ Γ⊢ψ∨ω Γ⊢¬ω
            where
              Γ⊢¬ω : Γ ⊢ ¬ ω
              Γ⊢¬ω = subst φ≡¬ω Γ⊢φ

...         | no  φ≢¬ω = ∧-intro Γ⊢ψ∨ω Γ⊢φ
------------------------------------------------------------------------------

------------------------------------------------------------------------------
atp-simplify {Γ} {φ ∧ ψ} {ω} Γ⊢φ∧ψ Γ⊢ω with eq φ (¬ ω) | eq ω (¬ φ)
... | yes φ≡¬ω | _        = ¬-elim (subst φ≡¬ω (∧-proj₁ Γ⊢φ∧ψ)) Γ⊢ω
... | no  _    | yes ω≡¬φ = ¬-elim (subst ω≡¬φ Γ⊢ω) (∧-proj₁ Γ⊢φ∧ψ)

... | no  _    | no  ω≢¬φ with eq ψ (¬ ω) | eq ω (¬ ψ)
...    | yes ψ≡¬ω | _        = ¬-elim (subst ψ≡¬ω (∧-proj₂ Γ⊢φ∧ψ)) Γ⊢ω
...    | no   _   | yes ω≡¬ψ = ¬-elim (subst ω≡¬ψ Γ⊢ω) (∧-proj₂ Γ⊢φ∧ψ)
...    | no   _   | no  ω≢¬ψ = ∧-intro Γ⊢φ∧ψ Γ⊢ω
------------------------------------------------------------------------------

------------------------------------------------------------------------------
atp-simplify {Γ} {⊤} {φ} _    Γ⊢φ = ⊤-intro
atp-simplify {Γ} {⊥} {_} Γ⊢⊥  _   = Γ⊢⊥
------------------------------------------------------------------------------
