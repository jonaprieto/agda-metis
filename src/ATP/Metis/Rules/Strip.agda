------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Strip inference rule.
------------------------------------------------------------------------------

open import Data.Nat
  using    (zero ; _+_)
  renaming ( ℕ to Nat; _⊔_ to max ; suc to suc )

module ATP.Metis.Rules.Strip ( n : Nat ) where

------------------------------------------------------------------------------

open import Data.PropFormula.Syntax   n
open import Data.PropFormula.Theorems n
open import Data.PropFormula.Views    n

------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- Stripping a goal.
------------------------------------------------------------------------------

data uhCases : PropFormula → Set where
  case₁ : (φ₁ φ₂ φ₃ : PropFormula) → uhCases (φ₁ ⇒ (φ₂ ⇒ φ₃))
  case₂ : (φ₁ φ₂ φ₃ : PropFormula) → uhCases (φ₁ ⇒ (φ₂ ∧ φ₃))
  other : (φ : PropFormula)        → uhCases φ

uh-cases : (φ : PropFormula) → uhCases φ
uh-cases (φ₁ ⇒ (φ₂ ⇒ φ₃)) = case₁ _ _ _
uh-cases (φ₁ ⇒ (φ₂ ∧ φ₃)) = case₂ _ _ _
uh-cases φ                = other _

-- Def.
uh₁ : PropFormula → Nat → PropFormula
uh₁ φ zero = φ
uh₁ φ (suc n)
  with uh-cases φ
...  | case₁ φ₁ φ₂ φ₃ = uh₁ ((φ₁ ∧ φ₂) ⇒ φ₃) n
...  | case₂ φ₁ φ₂ φ₃ = uh₁ (φ₁ ⇒ φ₂) n ∧ uh₁ (φ₁ ⇒ φ₃) n
...  | other _        = φ

-- Complexity measure of uh₁.
uh-cm : PropFormula → Nat
uh-cm φ
  with uh-cases φ
...  | case₁ _ _ φ₃  = uh-cm φ₃ + 3
...  | case₂ _ φ₂ φ₃ = max (uh-cm φ₂) (uh-cm φ₃) + 2
...  | other .φ      = 1

-- Lemma.
uh₁-lem
  : ∀ {Γ} {φ}
  → (n : Nat)
  → Γ ⊢ uh₁ φ n
  → Γ ⊢ φ

-- Proof.
uh₁-lem {_} {φ} zero    Γ⊢ushuntnφ  = Γ⊢ushuntnφ
uh₁-lem {_} {φ} (suc n) Γ⊢ushuntnφ
  with uh-cases φ
...  | case₁ φ₁ φ₂ φ₃ =
        ∧⇒-to-⇒⇒
          (uh₁-lem n
            Γ⊢ushuntnφ)
...  | case₂ φ₁ φ₂ φ₃ =
        ⇒∧⇒-to-⇒∧
          (∧-intro
            (uh₁-lem n
              (∧-proj₁ Γ⊢ushuntnφ))
            (uh₁-lem n
              (∧-proj₂ Γ⊢ushuntnφ)))
...  | other _ = Γ⊢ushuntnφ -- ▩

-- Def.
uh : PropFormula → PropFormula
uh φ = uh₁ φ (uh-cm φ)


-- Lemma.
uh-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ uh φ
  → Γ ⊢ φ

-- Proof.
uh-lem {_} {φ} = uh₁-lem (uh-cm φ) --  ▩


data stripCases : PropFormula → Set where
  conj    : (φ₁ φ₂ : PropFormula) → stripCases (φ₁ ∧ φ₂)
  disj    : (φ₁ φ₂ : PropFormula) → stripCases (φ₁ ∨ φ₂)
  impl    : (φ₁ φ₂ : PropFormula) → stripCases (φ₁ ⇒ φ₂)
  biimpl  : (φ₁ φ₂ : PropFormula) → stripCases (φ₁ ⇔ φ₂)
  nconj   : (φ₁ φ₂ : PropFormula) → stripCases (¬ (φ₁ ∧ φ₂))
  ndisj   : (φ₁ φ₂ : PropFormula) → stripCases (¬ (φ₁ ∨ φ₂))
  nimpl   : (φ₁ φ₂ : PropFormula) → stripCases (¬ (φ₁ ⇒ φ₂))
  nbiimpl : (φ₁ φ₂ : PropFormula) → stripCases (¬ (φ₁ ⇔ φ₂))
  nneg    : (φ : PropFormula)    → stripCases (¬ ¬ φ)
  nbot    : stripCases (¬ ⊥)
  ntop    : stripCases (¬ ⊤)
  other   : (φ : PropFormula)    → stripCases φ

strip-cases : (φ : PropFormula) → stripCases φ
strip-cases (φ₁ ∧ φ₂)     = conj _ _
strip-cases (φ₁ ∨ φ₂)     = disj _ _
strip-cases (φ₁ ⇒ φ₂)     = impl _ _
strip-cases (φ₁ ⇔ φ₂)     = biimpl _ _
strip-cases (¬ ⊤)         = ntop
strip-cases (¬ ⊥)         = nbot
strip-cases (¬ (φ₁ ∧ φ₂)) = nconj _ _
strip-cases (¬ (φ₁ ∨ φ₂)) = ndisj _ _
strip-cases (¬ (φ₁ ⇒ φ₂)) = nimpl _ _
strip-cases (¬ (φ₁ ⇔ φ₂)) = nbiimpl _ _
strip-cases (¬ (¬ φ))     = nneg _
strip-cases φ₁            = other _

-- Def.
strip₁ : PropFormula → Nat → PropFormula
strip₁ φ (suc n)
  with strip-cases φ
...  | conj φ₁ φ₂    = uh (strip₁ φ₁ n) ∧ uh (φ₁ ⇒ strip₁ φ₂ n)
...  | disj φ₁ φ₂    = uh (¬ φ₁ ⇒ strip₁ φ₂ n)
...  | impl φ₁ φ₂    = uh (φ₁ ⇒ strip₁ φ₂ n)
...  | biimpl φ₁ φ₂  = uh (φ₁ ⇒ strip₁ φ₂ n) ∧ uh (φ₂ ⇒ strip₁ φ₁ n)
...  | nconj φ₁ φ₂   = uh (φ₁ ⇒ strip₁ (¬ φ₂) n)
...  | ndisj φ₁ φ₂   = uh (strip₁ (¬ φ₁) n) ∧ uh (¬ φ₁ ⇒ strip₁ (¬ φ₂) n)
...  | nimpl φ₁ φ₂   = uh (strip₁ φ₁ n) ∧ uh (φ₁ ⇒ strip₁ (¬ φ₂) n)
...  | nbiimpl φ₁ φ₂ = uh (φ₁ ⇒ strip₁ (¬ φ₂) n) ∧ uh ((¬ φ₂) ⇒ strip₁ φ₁ n)
...  | nneg φ₁       = uh (strip₁ φ₁ n)
...  | nbot          = ⊤
...  | ntop          = ⊥
...  | other .φ      = φ
strip₁ φ _  = φ

-- Strip complexity measure.
strip-cm : PropFormula → Nat
strip-cm φ with strip-cases φ
... | conj φ₁ φ₂    = max (strip-cm φ₁) (strip-cm φ₂) + 1
... | disj φ₁ φ₂    = strip-cm φ₂ + 1
... | impl φ₁ φ₂    = strip-cm φ₂ + 1
... | biimpl φ₁ φ₂  = max (strip-cm φ₁) (strip-cm φ₂) + 1
... | nconj φ₁ φ₂   = strip-cm (¬ φ₂) + 1
... | ndisj φ₁ φ₂   = max (strip-cm (¬ φ₁)) (strip-cm (¬ φ₂)) + 1
... | nimpl φ₁ φ₂   = max (strip-cm φ₁) (strip-cm (¬ φ₂)) + 1
... | nbiimpl φ₁ φ₂ = max (strip-cm (¬ φ₁)) (strip-cm (¬ φ₂)) + 1
... | nneg φ₁       = strip-cm φ₁ + 1
... | nbot          = 1
... | ntop          = 1
... | other .φ      = 1

-- Lemma.
strip₁-lem
  : ∀ {Γ} {φ}
  → (n : Nat)
  → Γ ⊢ strip₁ φ n
  → Γ ⊢ φ

-- Proof.
strip₁-lem {_} {_} zero    Γ⊢strip₁ = Γ⊢strip₁
strip₁-lem {Γ} {φ} (suc n) Γ⊢strip₁
  with strip-cases φ
...  | conj φ₁ φ₂ =
        ∧-intro
          helper
          (strip₁-lem n
            (⇒-elim
              (uh-lem (∧-proj₂ Γ⊢strip₁))
              helper ))
        where
          helper : Γ ⊢ φ₁
          helper = strip₁-lem n (uh-lem (∧-proj₁ Γ⊢strip₁))

...  | disj φ₁ φ₂ =
        ⇒-elim
          (⇒-intro
            (∨-elim {Γ = Γ}
              (∨-intro₁ φ₂ (assume {Γ = Γ} φ₁))
              (∨-intro₂ φ₁
                (strip₁-lem n
                  (⇒-elim
                    (uh-lem
                      (weaken (¬ φ₁) Γ⊢strip₁))
                    (assume {Γ = Γ} (¬ φ₁)))))))
          (PEM {Γ = Γ} {φ = φ₁})

... | impl φ₁ φ₂ =
        ⇒-intro
          (strip₁-lem n
            (⇒-elim
              (weaken φ₁
                (uh-lem Γ⊢strip₁))
                (assume {Γ = Γ} φ₁)))

... | biimpl φ₁ φ₂ =
        ⇔-equiv₂ (∧-intro helper₁ helper₂)
        where
          helper₁ : Γ ⊢ φ₁ ⇒ φ₂
          helper₁ = ⇒-intro
               (strip₁-lem n
                 (⇒-elim
                   (weaken φ₁
                     (uh-lem (∧-proj₁ Γ⊢strip₁)))
                   (assume {Γ = Γ} φ₁)))

          helper₂ : Γ ⊢ φ₂ ⇒ φ₁
          helper₂ = ⇒-intro
                (strip₁-lem n
                  (⇒-elim
                    (weaken φ₂
                      (uh-lem (∧-proj₂ Γ⊢strip₁)))
                   (assume {Γ = Γ} φ₂)))

... |  nconj φ₁ φ₂ =
  ¬∨¬-to-¬∧ (⇒-to-¬∨ helper)
  where
    helper : Γ ⊢ φ₁ ⇒ ¬ φ₂
    helper =
      (⇒-intro
        (strip₁-lem n
          (⇒-elim
            (weaken φ₁
              (uh-lem Γ⊢strip₁))
          (assume {Γ = Γ} φ₁))))

... | ndisj φ₁ φ₂ =
  ¬∧¬-to-¬∨
    (∧-intro
      helper
      (strip₁-lem n
        (⇒-elim
          (uh-lem (∧-proj₂ Γ⊢strip₁))
          helper)))
  where
    helper : Γ ⊢ ¬ φ₁
    helper = strip₁-lem n (uh-lem (∧-proj₁ Γ⊢strip₁))

... | nimpl φ₁ φ₂ =
  ¬-intro
    (¬-elim
      (weaken (φ₁ ⇒ φ₂)
        (⇒-elim
          helper
          Γ⊢φ₁))
      (⇒-elim
        (assume {Γ = Γ} (φ₁ ⇒ φ₂))
        (weaken (φ₁ ⇒ φ₂) Γ⊢φ₁)))
  where
    Γ⊢φ₁ : Γ ⊢ φ₁
    Γ⊢φ₁ = strip₁-lem n (uh-lem (∧-proj₁ Γ⊢strip₁))

    helper : Γ ⊢ φ₁ ⇒ ¬ φ₂
    helper =
      ⇒-intro
        (strip₁-lem n
          (⇒-elim
            (uh-lem (weaken φ₁ (∧-proj₂ Γ⊢strip₁)))
            (assume {Γ = Γ} φ₁)))

... | nbiimpl φ₁ φ₂ = ⇒¬∧¬⇒-to-¬⇔ (∧-intro helper₁ helper₂)
  where
    helper₁ : Γ ⊢ φ₁ ⇒ ¬ φ₂
    helper₁ =
      ⇒-intro
        (strip₁-lem n
          (⇒-elim
            (uh-lem (weaken φ₁ (∧-proj₁ Γ⊢strip₁)))
            (assume {Γ = Γ} φ₁)))

    helper₂ : Γ ⊢ ¬ φ₂ ⇒ φ₁
    helper₂ =
      ⇒-intro
        (strip₁-lem n
          (⇒-elim
            (uh-lem (weaken (¬ φ₂) (∧-proj₂ Γ⊢strip₁)))
            (assume {Γ = Γ} (¬ φ₂))))

... | nneg φ₁  = ¬¬-equiv₂ (strip₁-lem n (uh-lem Γ⊢strip₁))
... | nbot     = ¬-intro (assume {Γ = Γ} ⊥)
... | ntop     = ⊥-elim (¬ ⊤) Γ⊢strip₁
... | other φ₁ = Γ⊢strip₁  -- ▩

-- Def.
strip : PropFormula → PropFormula
strip φ = strip₁ φ (strip-cm φ)

-- Lemma.
strip-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ strip φ
  → Γ ⊢ φ

-- Proof.
strip-lem {_} {φ} = strip₁-lem (strip-cm φ) -- ▩

-- Theorem.
strip-thm
  : ∀ {Γ} {φ}
  → Γ ⊢ strip φ ⇒ φ

-- Proof.
strip-thm {Γ} {φ} = ⇒-intro (strip-lem (assume {Γ = Γ} (strip φ))) -- ▩
