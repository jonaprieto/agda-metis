------------------------------------------------------------------------
-- Agda-Metis Library.
-- Simplify inference rule.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)

module ATP.Metis.Inferences.Simplify (n : ℕ) where

open import Data.Bool.Base
  using (Bool ; true ; false)
  renaming (_∨_ to _or_ ; _∧_ to _and_)

open import Data.Prop.Syntax n
open import Data.Prop.Dec n using (⌊_⌋)
open import Data.Prop.Properties n using (eq)

open import Function using (id)

-- Simplify inference.

isOpposite : Prop → Prop → Bool
isOpposite (¬ (¬ φ)) ψ = isOpposite φ ψ
isOpposite φ (¬ (¬ ψ)) = isOpposite φ ψ
isOpposite φ ψ = ⌊ eq φ (¬ ψ) ⌋ or ⌊ eq (¬ φ) ψ ⌋


simplify : Prop → Prop
simplify (Var x)  = Var x
simplify ⊤        = ⊤
simplify ⊥        = ⊥
simplify (φ ⇒ φ₁) = φ ⇒ φ₁
simplify ((φ ⇒ ψ) ∧ ω) with ⌊ eq φ ω ⌋
... | true  = simplify ψ
... | false = (φ ⇒ ψ) ∧ ω -- simplify ((¬ φ ∨ ψ) ∧ ω)

-- For now, it is off course ugly. :(

simplify ((φ ⇔ (ψ ⇔ ω)) ∧ ρ) with ⌊ eq φ ρ ⌋ | ⌊ eq ψ ρ ⌋ | ⌊ eq ω ρ ⌋
... | true | _    | _     = simplify (ψ ⇔ ω)
... | _    | true | _     = simplify (φ ⇔ ω)
... | _    | _    | true  = simplify (φ ⇔ ψ)
... | _    | _    | false with ⌊ eq (φ ⇔ ψ) ρ ⌋
...                       | true  = ω
...                       | false with ⌊ eq (φ ⇔ ω) ρ ⌋
...                               | true  = ψ
...                               | false with ⌊ eq (ψ ⇔ ω) ρ ⌋
...                                       | true = φ
...                                       | false = φ ⇔ (ψ ⇔ ω)

simplify (φ ⇔ φ₁) = φ ⇔ φ₁
simplify (¬ ⊥)    = ⊤
simplify (¬ ⊤)    = ⊥
simplify (⊥ ∧ φ)  = ⊥
simplify (φ ∧ ⊥)  = ⊥
simplify (⊥ ∨ φ)  = simplify φ
simplify (φ ∨ ⊥)  = simplify φ
simplify (⊤ ∧ φ)  = simplify φ
simplify (φ ∧ ⊤)  = simplify φ

simplify (φ ∧ (ψ ∨ ω)) with isOpposite φ (¬ ψ)
... | true  = simplify ω
... | false with isOpposite φ (¬ ω)
...         | true  = simplify ψ
...         | false = φ ∧ (ψ ∨ ω)

simplify ((φ ∨ ψ) ∧ ω) with isOpposite ω (¬ φ)
... | true  = simplify ψ
... | false with isOpposite ω (¬ ψ)
...         | true  = simplify φ
...         | false = (φ ∨ ψ) ∧ ω

simplify ((φ ∨ ψ) ∧ ω ∧ ρ) with isOpposite φ ω | isOpposite ψ ρ
... | true | _    = ψ ∧ ρ
... | _    | true = φ ∧ ρ
... | _    | _    = (φ ∨ ψ) ∧ ω ∧ ρ


simplify (φ ∧ ψ ∧ ω) with isOpposite φ ψ or isOpposite φ ω or isOpposite ψ ω
... | true   = ⊥
... | false = φ ∧ ψ ∧ ω


simplify (φ ∧ ψ) with ⌊ eq φ ψ ⌋
simplify (φ ∧ ψ) | true  = simplify φ
simplify (φ ∧ ψ) | false with ⌊ eq φ (¬ ψ) ⌋ | ⌊ eq (¬ φ) ψ ⌋
simplify (φ ∧ ψ) | false | false | false = φ ∧ ψ
simplify (φ ∧ ψ) | false | _     | _     = ⊥

simplify (φ ∨ ψ) with ⌊ eq φ ψ ⌋
simplify (φ ∨ ψ) | true = simplify φ
simplify (φ ∨ ψ) | false with  ⌊ eq φ (¬ ψ) ⌋ | ⌊ eq (¬ φ) ψ ⌋
simplify (φ ∨ ψ) | false | false | false = φ ∨ ψ
simplify (φ ∨ ψ) | false | _     | _     = ⊤

simplify φ = φ


-- ATP.

postulate
  atp-step : ∀ {Γ} {φ} → (f : Prop → Prop) → Γ ⊢ φ → Γ ⊢ f φ


atp-simplify : ∀ {Γ : Ctxt} {φ : Prop} → Γ ⊢ φ → Γ ⊢ simplify φ
atp-simplify {Γ} {Var x} = id --id
atp-simplify {Γ} {⊤}     = id -- id
atp-simplify {Γ} {⊥}     = id -- id
atp-simplify {Γ} {φ = φ₁ ∧ ¬ φ₂} seq =
  atp-step (λ _ → simplify (φ₁ ∧ ¬ φ₂)) seq
atp-simplify {Γ} {¬ φ ∧ ψ} =
  atp-step (λ _ → simplify (¬ φ ∧ ψ))
atp-simplify {Γ} {φ} seq = id (atp-step (λ _ → simplify φ) seq)

