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

open import Data.Prop.Dec n        using ( ⌊_⌋; yes; no )
open import Data.Prop.Properties n using ( eq ; subst )
open import Data.Prop.Syntax n
open import Data.Prop.Theorems n

open import Function               using ( id ; _∘_ ; _$_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym )

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Simplify function takes the first formula of the input
-- and tries to simplify it based on the second one of the input.
------------------------------------------------------------------------------

simplify : Prop → Prop → Prop

simplify ⊤ φ = ⊤
simplify ⊥ φ = ⊥
simplify (Var x) ψ with ⌊ eq ⊥ ψ ⌋
... | false  = Var x
... | true   = ⊥

simplify (¬ φ)  ψ with ⌊ eq φ ψ ⌋ |  ⌊ eq ⊥ φ ⌋ | ⌊ eq ⊤ φ ⌋
... | false | false | false = ¬ φ ∧ ψ
... | false | false | true  = ⊥
... | false | true  | false = ψ
... | false | true  | true  = ⊥
... | true  | false | false = ⊥
... | true  | false | true  = ⊥
... | true  | true  | false = ⊥
... | true  | true  | true  = ⊥

simplify (φ ⇔ ψ) ω with ⌊ eq φ ω ⌋ | ⌊ eq ψ ω ⌋
... | false | false = (φ ⇔ ψ) ∧ ω
... | false | true  = φ
... | true  | false = ψ
... | true  | true  = ψ

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
... | false with ⌊ eq ψ (¬ ω) ⌋ or ⌊ eq ω (¬ ψ) ⌋
...         | false = (φ ∧ ψ) ∧ ω
...         | true  = ⊥

------------------------------------------------------------------------------
-- atp-simplify₀.
------------------------------------------------------------------------------

atp-simplify₀
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ
  → Γ ⊢ ψ
  → Γ ⊢ simplify φ ψ

atp-simplify₀ {Γ} {Var x} {ψ}  Γ⊢Varx Γ⊢ψ with eq ⊥ ψ
... | no  ⊥≢ψ = Γ⊢Varx
... | yes ⊥≡ψ = subst (sym ⊥≡ψ) Γ⊢ψ

atp-simplify₀ {Γ} {¬ φ} {ψ} Γ⊢¬φ Γ⊢ψ with eq φ ψ | eq ⊥ φ | eq ⊤ φ
... | no  φ≢ψ | no  ⊥≢φ | no  ⊤≢φ = ∧-intro Γ⊢¬φ Γ⊢ψ
... | no  φ≢ψ | no  ⊥≢φ | yes ⊤≡φ = ¬⊤-to-⊥ (¬-inside (sym ⊤≡φ) Γ⊢¬φ)
... | no  φ≢ψ | yes ⊥≡φ | no  ⊤≢φ = Γ⊢ψ
... | no  φ≢ψ | yes ⊥≡φ | yes ⊤≡φ = ¬⊤-to-⊥ (¬-inside (sym ⊤≡φ) Γ⊢¬φ)
... | yes φ≡ψ | no  ⊥≢φ | no  ⊤≢φ = ¬-elim Γ⊢¬φ (subst (sym φ≡ψ) Γ⊢ψ)
... | yes φ≡ψ | no  ⊥≢φ | yes ⊤≡φ = ¬-elim Γ⊢¬φ (subst (sym φ≡ψ) Γ⊢ψ)
... | yes φ≡ψ | yes ⊥≡φ | no  ⊤≢φ = ¬-elim Γ⊢¬φ (subst (sym φ≡ψ) Γ⊢ψ)
... | yes φ≡ψ | yes ⊥≡φ | yes ⊤≡φ = ¬-elim Γ⊢¬φ (subst (sym φ≡ψ) Γ⊢ψ)

atp-simplify₀ {Γ} {φ ⇔ ψ} {ω} Γ⊢φ⇔ψ Γ⊢ω with eq φ ω | eq ψ ω
... | no  φ≢ω | no  ψ≢ω = ∧-intro Γ⊢φ⇔ψ Γ⊢ω
... | no  φ≢ω | yes ψ≡ω = ⇔-elim₂ (subst (sym ψ≡ω) Γ⊢ω) Γ⊢φ⇔ψ
... | yes φ≡ω | no  ψ≢ω = ⇔-elim₁ (subst (sym φ≡ω) Γ⊢ω) Γ⊢φ⇔ψ
... | yes φ≡ω | yes ψ≡ω = subst (sym ψ≡ω) Γ⊢ω

atp-simplify₀ {Γ} {φ ⇒ ψ} {ω} Γ⊢φ⇒ψ Γ⊢ω with eq φ ω
... | no  φ≢ω = ∧-intro Γ⊢φ⇒ψ Γ⊢ω
... | yes φ≡ω = ⇒-elim Γ⊢φ⇒ψ (subst (sym φ≡ω) Γ⊢ω)

atp-simplify₀ {Γ} {ψ ∨ ω} {φ} Γ⊢ψ∨ω Γ⊢φ with eq φ (¬ ψ)
... | yes φ≡¬ψ = resolve₇ Γ⊢ψ∨ω Γ⊢¬ψ
    where
      Γ⊢¬ψ : Γ ⊢ ¬ ψ
      Γ⊢¬ψ = subst φ≡¬ψ Γ⊢φ

... | no  φ≢¬ψ  with eq φ (¬ ω)
...             | no  φ≢¬ω = ∧-intro Γ⊢ψ∨ω Γ⊢φ
...             | yes φ≡¬ω = resolve₆ Γ⊢ψ∨ω Γ⊢¬ω
                where
                  Γ⊢¬ω : Γ ⊢ ¬ ω
                  Γ⊢¬ω = subst φ≡¬ω Γ⊢φ

atp-simplify₀ {Γ} {φ ∧ ψ} {ω} Γ⊢φ∧ψ Γ⊢ω with eq φ (¬ ω) | eq ω (¬ φ)
... | yes φ≡¬ω | no  ω≡¬φ = ¬-elim (subst φ≡¬ω (∧-proj₁ Γ⊢φ∧ψ)) Γ⊢ω
... | yes φ≡¬ω | yes ω≡¬φ = ¬-elim (subst φ≡¬ω (∧-proj₁ Γ⊢φ∧ψ)) Γ⊢ω
... | no  φ≢¬ω | yes ω≡¬φ = ¬-elim (subst ω≡¬φ Γ⊢ω) (∧-proj₁ Γ⊢φ∧ψ)
... | no  φ≢¬ω | no  ω≢¬φ
    with eq ψ (¬ ω) | eq ω (¬ ψ)
...    | no   ψ≢¬ω  | no  ω≢¬ψ = ∧-intro Γ⊢φ∧ψ Γ⊢ω
...    | no   ψ≢¬ω  | yes ω≡¬ψ = ¬-elim (subst ω≡¬ψ Γ⊢ω) (∧-proj₂ Γ⊢φ∧ψ)
...    | yes ψ≡¬ω   | no  ω≡¬ψ = ¬-elim (subst ψ≡¬ω (∧-proj₂ Γ⊢φ∧ψ)) Γ⊢ω
...    | yes ψ≡¬ω   | yes ω≡¬ψ = ¬-elim (subst ψ≡¬ω (∧-proj₂ Γ⊢φ∧ψ)) Γ⊢ω

atp-simplify₀ {Γ} {⊤} {_} Γ⊢⊤ _ = Γ⊢⊤
atp-simplify₀ {Γ} {⊥} {_} Γ⊢⊥ _ = Γ⊢⊥

------------------------------------------------------------------------------
-- Hard-simplify function: applies simplify onto two formulas, if the results
-- is not bottom, it applies simplify flipping the formulas into the input.
------------------------------------------------------------------------------

hard-simplify : Prop → Prop → Prop
hard-simplify φ ψ
    with simplify φ ψ | simplify ψ φ
... | Var x  | Var x₁ = simplify φ ψ
... | Var x  | ¬ ρ    = simplify φ ψ
... | Var x  | ρ ⇒ ρ₁ = simplify φ ψ
... | Var x  | ρ ⇔ ρ₁ = simplify φ ψ
... | Var x  | ρ ∧ ρ₁ = simplify φ ψ
... | Var x  | ρ ∨ ρ₁ = simplify φ ψ
... | Var x  | ⊤      = simplify φ ψ
... | Var x  | ⊥      = simplify ψ φ
... | ¬ ω    | Var x  = simplify φ ψ
... | ¬ ω    | ¬ ρ    = simplify φ ψ
... | ¬ ω    | ρ ⇒ ρ₁ = simplify φ ψ
... | ¬ ω    | ρ ⇔ ρ₁ = simplify φ ψ
... | ¬ ω    | ρ ∧ ρ₁ = simplify φ ψ
... | ¬ ω    | ρ ∨ ρ₁ = simplify φ ψ
... | ¬ ω    | ⊤      = simplify φ ψ
... | ¬ ω    | ⊥      = simplify ψ φ
... | ω ⇒ ω₁ | Var x  = simplify φ ψ
... | ω ⇒ ω₁ | ¬ ρ    = simplify φ ψ
... | ω ⇒ ω₁ | ρ ⇒ ρ₁ = simplify φ ψ
... | ω ⇒ ω₁ | ρ ⇔ ρ₁ = simplify φ ψ
... | ω ⇒ ω₁ | ρ ∧ ρ₁ = simplify φ ψ
... | ω ⇒ ω₁ | ρ ∨ ρ₁ = simplify φ ψ
... | ω ⇒ ω₁ | ⊤      = simplify φ ψ
... | ω ⇒ ω₁ | ⊥      = simplify ψ φ
... | ω ⇔ ω₁ | Var x  = simplify φ ψ
... | ω ⇔ ω₁ | ¬ ρ    = simplify φ ψ
... | ω ⇔ ω₁ | ρ ⇒ ρ₁ = simplify φ ψ
... | ω ⇔ ω₁ | ρ ⇔ ρ₁ = simplify φ ψ
... | ω ⇔ ω₁ | ρ ∧ ρ₁ = simplify φ ψ
... | ω ⇔ ω₁ | ρ ∨ ρ₁ = simplify φ ψ
... | ω ⇔ ω₁ | ⊤      = simplify φ ψ
... | ω ⇔ ω₁ | ⊥      = simplify ψ φ
... | ω ∧ ω₁ | Var x  = simplify φ ψ
... | ω ∧ ω₁ | ¬ ρ    = simplify φ ψ
... | ω ∧ ω₁ | ρ ⇒ ρ₁ = simplify φ ψ
... | ω ∧ ω₁ | ρ ⇔ ρ₁ = simplify φ ψ
... | ω ∧ ω₁ | ρ ∧ ρ₁ = simplify φ ψ
... | ω ∧ ω₁ | ρ ∨ ρ₁ = simplify φ ψ
... | ω ∧ ω₁ | ⊤      = simplify φ ψ
... | ω ∧ ω₁ | ⊥      = simplify ψ φ
... | ω ∨ ω₁ | Var x  = simplify φ ψ
... | ω ∨ ω₁ | ¬ ρ    = simplify φ ψ
... | ω ∨ ω₁ | ρ ⇒ ρ₁ = simplify φ ψ
... | ω ∨ ω₁ | ρ ⇔ ρ₁ = simplify φ ψ
... | ω ∨ ω₁ | ρ ∧ ρ₁ = simplify φ ψ
... | ω ∨ ω₁ | ρ ∨ ρ₁ = simplify φ ψ
... | ω ∨ ω₁ | ⊤      = simplify φ ψ
... | ω ∨ ω₁ | ⊥      = simplify ψ φ
... | ⊤      | Var x  = simplify φ ψ
... | ⊤      | ¬ ρ    = simplify φ ψ
... | ⊤      | ρ ⇒ ρ₁ = simplify φ ψ
... | ⊤      | ρ ⇔ ρ₁ = simplify φ ψ
... | ⊤      | ρ ∧ ρ₁ = simplify φ ψ
... | ⊤      | ρ ∨ ρ₁ = simplify φ ψ
... | ⊤      | ⊤      = simplify φ ψ
... | ⊤      | ⊥      = simplify ψ φ
... | ⊥      | _      = simplify φ ψ

------------------------------------------------------------------------------
-- atp-simplify.
------------------------------------------------------------------------------

atp-simplify
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ
  → Γ ⊢ ψ
  → Γ ⊢ hard-simplify φ ψ

atp-simplify {Γ} {φ} {ψ} Γ⊢φ Γ⊢ψ
    with simplify φ ψ | simplify ψ φ
... | Var x  | Var x₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | Var x  | ¬ ρ    = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | Var x  | ρ ⇒ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | Var x  | ρ ⇔ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | Var x  | ρ ∧ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | Var x  | ρ ∨ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | Var x  | ⊤      = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | Var x  | ⊥      = atp-simplify₀ Γ⊢ψ Γ⊢φ
... | ¬ ω    | Var x  = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ¬ ω    | ¬ ρ    = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ¬ ω    | ρ ⇒ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ¬ ω    | ρ ⇔ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ¬ ω    | ρ ∧ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ¬ ω    | ρ ∨ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ¬ ω    | ⊤      = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ¬ ω    | ⊥      = atp-simplify₀ Γ⊢ψ Γ⊢φ
... | ω ⇒ ω₁ | Var x  = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ⇒ ω₁ | ¬ ρ    = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ⇒ ω₁ | ρ ⇒ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ⇒ ω₁ | ρ ⇔ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ⇒ ω₁ | ρ ∧ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ⇒ ω₁ | ρ ∨ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ⇒ ω₁ | ⊤      = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ⇒ ω₁ | ⊥      = atp-simplify₀ Γ⊢ψ Γ⊢φ
... | ω ⇔ ω₁ | Var x  = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ⇔ ω₁ | ¬ ρ    = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ⇔ ω₁ | ρ ⇒ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ⇔ ω₁ | ρ ⇔ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ⇔ ω₁ | ρ ∧ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ⇔ ω₁ | ρ ∨ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ⇔ ω₁ | ⊤      = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ⇔ ω₁ | ⊥      = atp-simplify₀ Γ⊢ψ Γ⊢φ
... | ω ∧ ω₁ | Var x  = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ∧ ω₁ | ¬ ρ    = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ∧ ω₁ | ρ ⇒ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ∧ ω₁ | ρ ⇔ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ∧ ω₁ | ρ ∧ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ∧ ω₁ | ρ ∨ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ∧ ω₁ | ⊤      = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ∧ ω₁ | ⊥      = atp-simplify₀ Γ⊢ψ Γ⊢φ
... | ω ∨ ω₁ | Var x  = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ∨ ω₁ | ¬ ρ    = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ∨ ω₁ | ρ ⇒ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ∨ ω₁ | ρ ⇔ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ∨ ω₁ | ρ ∧ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ∨ ω₁ | ρ ∨ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ∨ ω₁ | ⊤      = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ω ∨ ω₁ | ⊥      = atp-simplify₀ Γ⊢ψ Γ⊢φ
... | ⊤      | Var x  = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ⊤      | ¬ ρ    = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ⊤      | ρ ⇒ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ⊤      | ρ ⇔ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ⊤      | ρ ∧ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ⊤      | ρ ∨ ρ₁ = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ⊤      | ⊤      = atp-simplify₀ Γ⊢φ Γ⊢ψ
... | ⊤      | ⊥      = atp-simplify₀ Γ⊢ψ Γ⊢φ
... | ⊥      | _      = atp-simplify₀ Γ⊢φ Γ⊢ψ
