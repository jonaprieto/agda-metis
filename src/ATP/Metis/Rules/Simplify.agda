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

open import Data.PropFormula.Dec n        using ( ⌊_⌋; yes; no )
open import Data.PropFormula.Properties n using ( eq ; subst )
open import Data.PropFormula.Syntax n
open import Data.PropFormula.Theorems n

open import Function using ( id ; _∘_ ; _$_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym )

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Simplify function takes the first formula of the input
-- and tries to simplify it based on the second one of the input.
------------------------------------------------------------------------------

simplify : PropFormula → PropFormula → PropFormula

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
-- thm-simplify₀.
------------------------------------------------------------------------------

thm-simplify₀
  : ∀ {Γ} {φ ψ}
  → Γ ⊢ φ
  → Γ ⊢ ψ
  → Γ ⊢ simplify φ ψ

thm-simplify₀ {Γ} {Var x} {ψ}  Γ⊢Varx Γ⊢ψ with eq ⊥ ψ
... | no  ⊥≢ψ = Γ⊢Varx
... | yes ⊥≡ψ = subst (sym ⊥≡ψ) Γ⊢ψ

thm-simplify₀ {Γ} {¬ φ} {ψ} Γ⊢¬φ Γ⊢ψ with eq φ ψ | eq ⊥ φ | eq ⊤ φ
... | no  φ≢ψ | no  ⊥≢φ | no  ⊤≢φ = ∧-intro Γ⊢¬φ Γ⊢ψ
... | no  φ≢ψ | no  ⊥≢φ | yes ⊤≡φ = ¬⊤-to-⊥ (¬-inside (sym ⊤≡φ) Γ⊢¬φ)
... | no  φ≢ψ | yes ⊥≡φ | no  ⊤≢φ = Γ⊢ψ
... | no  φ≢ψ | yes ⊥≡φ | yes ⊤≡φ = ¬⊤-to-⊥ (¬-inside (sym ⊤≡φ) Γ⊢¬φ)
... | yes φ≡ψ | no  ⊥≢φ | no  ⊤≢φ = ¬-elim Γ⊢¬φ (subst (sym φ≡ψ) Γ⊢ψ)
... | yes φ≡ψ | no  ⊥≢φ | yes ⊤≡φ = ¬-elim Γ⊢¬φ (subst (sym φ≡ψ) Γ⊢ψ)
... | yes φ≡ψ | yes ⊥≡φ | no  ⊤≢φ = ¬-elim Γ⊢¬φ (subst (sym φ≡ψ) Γ⊢ψ)
... | yes φ≡ψ | yes ⊥≡φ | yes ⊤≡φ = ¬-elim Γ⊢¬φ (subst (sym φ≡ψ) Γ⊢ψ)

thm-simplify₀ {Γ} {φ ⇔ ψ} {ω} Γ⊢φ⇔ψ Γ⊢ω with eq φ ω | eq ψ ω
... | no  φ≢ω | no  ψ≢ω = ∧-intro Γ⊢φ⇔ψ Γ⊢ω
... | no  φ≢ω | yes ψ≡ω = ⇔-elim₂ (subst (sym ψ≡ω) Γ⊢ω) Γ⊢φ⇔ψ
... | yes φ≡ω | no  ψ≢ω = ⇔-elim₁ (subst (sym φ≡ω) Γ⊢ω) Γ⊢φ⇔ψ
... | yes φ≡ω | yes ψ≡ω = subst (sym ψ≡ω) Γ⊢ω

thm-simplify₀ {Γ} {φ ⇒ ψ} {ω} Γ⊢φ⇒ψ Γ⊢ω with eq φ ω
... | no  φ≢ω = ∧-intro Γ⊢φ⇒ψ Γ⊢ω
... | yes φ≡ω = ⇒-elim Γ⊢φ⇒ψ (subst (sym φ≡ω) Γ⊢ω)

thm-simplify₀ {Γ} {ψ ∨ ω} {φ} Γ⊢ψ∨ω Γ⊢φ with eq φ (¬ ψ)
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

thm-simplify₀ {Γ} {φ ∧ ψ} {ω} Γ⊢φ∧ψ Γ⊢ω with eq φ (¬ ω) | eq ω (¬ φ)
... | yes φ≡¬ω | no  ω≡¬φ = ¬-elim (subst φ≡¬ω (∧-proj₁ Γ⊢φ∧ψ)) Γ⊢ω
... | yes φ≡¬ω | yes ω≡¬φ = ¬-elim (subst φ≡¬ω (∧-proj₁ Γ⊢φ∧ψ)) Γ⊢ω
... | no  φ≢¬ω | yes ω≡¬φ = ¬-elim (subst ω≡¬φ Γ⊢ω) (∧-proj₁ Γ⊢φ∧ψ)
... | no  φ≢¬ω | no  ω≢¬φ
    with eq ψ (¬ ω) | eq ω (¬ ψ)
...    | no   ψ≢¬ω  | no  ω≢¬ψ = ∧-intro Γ⊢φ∧ψ Γ⊢ω
...    | no   ψ≢¬ω  | yes ω≡¬ψ = ¬-elim (subst ω≡¬ψ Γ⊢ω) (∧-proj₂ Γ⊢φ∧ψ)
...    | yes ψ≡¬ω   | no  ω≡¬ψ = ¬-elim (subst ψ≡¬ω (∧-proj₂ Γ⊢φ∧ψ)) Γ⊢ω
...    | yes ψ≡¬ω   | yes ω≡¬ψ = ¬-elim (subst ψ≡¬ω (∧-proj₂ Γ⊢φ∧ψ)) Γ⊢ω

thm-simplify₀ {Γ} {⊤} {_} Γ⊢⊤ _ = Γ⊢⊤
thm-simplify₀ {Γ} {⊥} {_} Γ⊢⊥ _  = Γ⊢⊥

------------------------------------------------------------------------------
-- Hard-simplify function: applies simplify onto two formulas, if the results
-- is not bottom, it applies simplify flipping the formulas into the input.
------------------------------------------------------------------------------

data S-View : PropFormula → PropFormula → Set where
  normal : (φ ψ : PropFormula) → S-View φ ψ
  swap   : (φ ψ : PropFormula) → S-View φ ψ

s-view : (x y : PropFormula) → S-View x y
s-view φ ψ with simplify φ ψ
... | ⊥ = normal φ ψ
... | z with simplify ψ φ
...        | ⊥ = swap φ ψ
...        | w = normal φ ψ

hard-simplify : PropFormula → PropFormula → PropFormula
hard-simplify x y with s-view x y
hard-simplify x y | normal .x .y = simplify x y
hard-simplify x y | swap .x .y   = simplify y x

------------------------------------------------------------------------------
-- thm-simplify.
------------------------------------------------------------------------------

postulate
  thm-simplify
    : ∀ {Γ} {φ ψ}
    → (γ : PropFormula)
    → Γ ⊢ φ
    → Γ ⊢ ψ
    → Γ ⊢ γ

-- thm-simplify {Γ} {φ} {ψ} Γ⊢φ Γ⊢ψ with s-view φ ψ
-- thm-simplify {Γ} {.φ} {.ψ} Γ⊢φ Γ⊢ψ | normal φ ψ = thm-simplify₀ Γ⊢φ Γ⊢ψ
-- thm-simplify {Γ} {.φ} {.ψ} Γ⊢φ Γ⊢ψ | swap φ ψ   = thm-simplify₀ Γ⊢ψ Γ⊢φ
