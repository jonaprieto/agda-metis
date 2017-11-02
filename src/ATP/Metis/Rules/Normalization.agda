------------------------------------------------------------------------------
-- Agda-Prop Library.
-- Normalization functions.
------------------------------------------------------------------------------

open import Data.Nat using (suc; zero; _+_;_*_)
  renaming (_⊔_ to max; ℕ to Nat)

module ATP.Metis.Rules.Normalization (n : Nat) where

------------------------------------------------------------------------------

open import ATP.Metis.Rules.Conjunct n
open import ATP.Metis.Rules.Checking n
open import ATP.Metis.Rules.Reordering n
  using ( disj; disj-lem; reorder-∨; reorder-∨-lem; assoc-∧; assoc-∨)
  using ( assoc-∧-lem; assoc-∨-lem)
  using ( from-assoc-∧-lem; from-assoc-∨-lem )

open import Data.Bool.Base
  using ( Bool; true; false)

open import Data.PropFormula.Dec n
open import Data.PropFormula.Properties n
open import Data.PropFormula.NormalForms n
  using (cnf-dist; cnf-dist-lem; from-cnf-dist-lem )
open import Data.PropFormula.Syntax n
open import Data.PropFormula.Theorems n
open import Data.PropFormula.Views  n
  renaming ( disj to disjshape )

open import Relation.Binary.PropositionalEquality using (_≡_; sym)

------------------------------------------------------------------------------

data simplify-∨-Cases : PropFormula  → Set where

  sdisj₁ : (φ : PropFormula)     → simplify-∨-Cases (⊥ ∨ φ)
  sdisj₂ : (φ : PropFormula)     → simplify-∨-Cases (φ ∨ ⊥)
  sdisj₃ : (φ : PropFormula)     → simplify-∨-Cases (⊤ ∨ φ)
  sdisj₄ : (φ : PropFormula)     → simplify-∨-Cases (φ ∨ ⊤)
  sdisj₅ : (φ₁ φ₂ : PropFormula) → simplify-∨-Cases (φ₁ ∨ φ₂)
  other  : (φ : PropFormula)     → simplify-∨-Cases φ

simplify-∨-cases : (φ : PropFormula) → simplify-∨-Cases φ
simplify-∨-cases (⊥ ∨ φ)   = sdisj₁ _
simplify-∨-cases (φ ∨ ⊥)   = sdisj₂ _
simplify-∨-cases (⊤ ∨ φ)   = sdisj₃ _
simplify-∨-cases (φ ∨ ⊤)   = sdisj₄ _
simplify-∨-cases (φ₁ ∨ φ₂) = sdisj₅ _ _
simplify-∨-cases  φ        = other _

-- Def.
_∈∨_ : (φ ψ : PropFormula) → Dec (ψ ≡ reorder-∨ φ ψ)
φ₁ ∈∨ φ = eq φ (reorder-∨ φ₁ φ)

-- Def.
simplify-∨ : PropFormula → PropFormula
simplify-∨ φ
  with simplify-∨-cases φ
simplify-∨ .(⊥ ∨ φ) | sdisj₁ φ = simplify-∨ φ
simplify-∨ .(φ ∨ ⊥) | sdisj₂ φ = simplify-∨ φ
simplify-∨ .(⊤ ∨ φ) | sdisj₃ φ = ⊤
simplify-∨ .(φ ∨ ⊤) | sdisj₄ φ = ⊤
simplify-∨ φ        | other .φ  = φ
simplify-∨ .(φ₁ ∨ φ₂)  | sdisj₅ φ₁ φ₂
  with neg-view  φ₁
simplify-∨ .(¬ ψ ∨ φ₂) | sdisj₅ .(¬ ψ) φ₂ | neg ψ
  with ⌊ ψ ∈∨ φ₂ ⌋
... | true  = ⊤
... | false
    with ⌊ (¬ ψ) ∈∨ φ₂ ⌋
... | true  = simplify-∨ φ₂
... | false
    with ⌊ eq (simplify-∨ φ₂) ⊤ ⌋
...     | true  = ⊤
...     | false
        with ⌊ eq (simplify-∨ φ₂) ⊥ ⌋
...     | true  = ¬ ψ
...     | false = ¬ ψ ∨ simplify-∨ φ₂
simplify-∨ .(φ₁ ∨ φ₂) | sdisj₅ φ₁ φ₂ | pos .φ₁
  with ⌊ (¬ φ₁) ∈∨ φ₂ ⌋
... | true  = ⊤
... | false
    with ⌊ φ₁ ∈∨ φ₂ ⌋
... | true  = simplify-∨ φ₂
... | false
    with ⌊ eq (simplify-∨ φ₂) ⊤ ⌋
...     | true  = ⊤
...     | false
        with ⌊ eq (simplify-∨ φ₂) ⊥ ⌋
...     | true  = φ₁
...     | false = φ₁ ∨ simplify-∨ φ₂


-- Lemma.
simplify-∨-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ simplify-∨ φ

-- Proof.
simplify-∨-lem {Γ} {φ} Γ⊢φ
  with simplify-∨-cases φ
simplify-∨-lem {Γ} {.(⊥ ∨ φ)} Γ⊢φ | sdisj₁ φ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (⊥-elim (simplify-∨ φ) (assume {Γ = Γ} ⊥))
        (simplify-∨-lem (assume {Γ = Γ} φ))))
  Γ⊢φ
simplify-∨-lem {Γ} {.(φ ∨ ⊥)} Γ⊢φ | sdisj₂ φ =
  ⇒-elim
    (⇒-intro
    (∨-elim {Γ = Γ}
      (simplify-∨-lem (assume {Γ = Γ} φ))
      (⊥-elim (simplify-∨ φ) (assume {Γ = Γ} ⊥))))
    Γ⊢φ
simplify-∨-lem {Γ} {.(⊤ ∨ φ)} Γ⊢φ | sdisj₃ φ = ⊤-intro
simplify-∨-lem {Γ} {.(φ ∨ ⊤)} Γ⊢φ | sdisj₄ φ = ⊤-intro
simplify-∨-lem {Γ} {.φ}       Γ⊢φ | other φ  = Γ⊢φ
simplify-∨-lem {Γ} {.(φ₁ ∨ φ₂)} Γ⊢φ | sdisj₅ φ₁ φ₂
  with neg-view  φ₁
simplify-∨-lem {Γ} {.(¬ ψ ∨ φ₂)} Γ⊢φ  | sdisj₅ .(¬ ψ) φ₂ | neg ψ
  with ψ ∈∨ φ₂
... | yes p₁ = ⊤-intro
... | no _
    with (¬ ψ) ∈∨ φ₂
... | yes p₂ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (simplify-∨-lem
          (subst (sym p₂) (reorder-∨-lem (assume {Γ = Γ} (¬ ψ)) φ₂)))
        (simplify-∨-lem (assume {Γ = Γ} φ₂))))
    Γ⊢φ
... | no _
    with eq (simplify-∨ φ₂) ⊤
...     | yes p₃ = ⊤-intro
...     | no _
        with eq (simplify-∨ φ₂) ⊥
...     | yes p₄ =
            ⇒-elim
                (⇒-intro
                  (∨-elim {Γ = Γ}
                    (assume {Γ = Γ} (¬ ψ))
                    (⊥-elim (¬ ψ)
                      (subst p₄ (simplify-∨-lem (assume {Γ = Γ} φ₂))))))
                Γ⊢φ
...     | no _ =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (simplify-∨ φ₂) (assume {Γ = Γ} (¬ ψ)))
        (∨-intro₂ (¬ ψ) (simplify-∨-lem (assume {Γ = Γ} φ₂)))))
    Γ⊢φ
simplify-∨-lem {Γ} {.(φ₁ ∨ φ₂)} Γ⊢φ  | sdisj₅ φ₁ φ₂ | pos .φ₁
  with (¬ φ₁) ∈∨ φ₂
... | yes p₅ = ⊤-intro
... | no _
    with φ₁ ∈∨ φ₂
... | yes p₆ =
          ⇒-elim
            (⇒-intro
              (∨-elim {Γ = Γ}
                (simplify-∨-lem
                  (subst (sym p₆) (reorder-∨-lem (assume {Γ = Γ} φ₁) φ₂)))
                (simplify-∨-lem (assume {Γ = Γ} φ₂))))
            Γ⊢φ
... | no _
    with eq (simplify-∨ φ₂) ⊤
...     | yes p₇ = ⊤-intro
...     | no _
        with eq (simplify-∨ φ₂) ⊥
...     | yes p₈ =
          ⇒-elim
            (⇒-intro
              (∨-elim {Γ = Γ}
                (assume {Γ = Γ} φ₁)
                (⊥-elim φ₁ (subst p₈ (simplify-∨-lem (assume {Γ = Γ} φ₂))))))
            Γ⊢φ
...     | no _ =
          ⇒-elim
            (⇒-intro
            (∨-elim {Γ = Γ}
               (∨-intro₁ (simplify-∨ φ₂) (assume {Γ = Γ} φ₁))
               (∨-intro₂ φ₁ (simplify-∨-lem (assume {Γ = Γ} φ₂)))))
            Γ⊢φ
--------------------------------------------------------------------------- ■

-- Lemma.
from-simplify-∨-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ simplify-∨ φ
  → Γ ⊢ φ

-- Proof.
from-simplify-∨-lem {Γ} {φ} Γ⊢simplifyφ
  with simplify-∨-cases φ
from-simplify-∨-lem {Γ} {.(⊥ ∨ φ)} Γ⊢simplifyφ | sdisj₁ φ =
  ∨-intro₂ ⊥ (from-simplify-∨-lem Γ⊢simplifyφ)
from-simplify-∨-lem {Γ} {.(φ ∨ ⊥)} Γ⊢simplifyφ | sdisj₂ φ =
  ∨-intro₁ ⊥ (from-simplify-∨-lem Γ⊢simplifyφ)
from-simplify-∨-lem {Γ} {.(⊤ ∨ φ)} Γ⊢simplifyφ | sdisj₃ φ =
  ∨-intro₁ φ Γ⊢simplifyφ
from-simplify-∨-lem {Γ} {.(φ ∨ ⊤)} Γ⊢simplifyφ | sdisj₄ φ =
  ∨-intro₂ φ Γ⊢simplifyφ
from-simplify-∨-lem {Γ} {.φ}       Γ⊢simplifyφ | other φ  = Γ⊢simplifyφ
from-simplify-∨-lem {Γ} {.(φ₁ ∨ φ₂)} Γ⊢simplifyφ | sdisj₅ φ₁ φ₂
  with neg-view  φ₁
from-simplify-∨-lem {Γ} {.(¬ ψ ∨ φ₂)} Γ⊢simplifyφ  | sdisj₅ .(¬ ψ) φ₂ | neg ψ
  with ψ ∈∨ φ₂
... | yes p₁ =
      ⇒-elim
        (⇒-intro
          (∨-elim {Γ = Γ}
            (∨-intro₂ (¬ ψ)
              (subst (sym p₁) (reorder-∨-lem (assume {Γ = Γ} ψ) φ₂)))
            (∨-intro₁ φ₂ (assume {Γ = Γ} (¬ ψ)))))
      (PEM {φ = ψ})
... | no _
    with (¬ ψ) ∈∨ φ₂
... | yes p₂ =
      ∨-intro₂ (¬ ψ) (from-simplify-∨-lem Γ⊢simplifyφ)
... | no _
    with eq (simplify-∨ φ₂) ⊤
...     | yes p₃ =
     ∨-intro₂ (¬ ψ) (from-simplify-∨-lem (subst (sym p₃) Γ⊢simplifyφ))
...     | no _
        with eq (simplify-∨ φ₂) ⊥
...     | yes p₄ = ∨-intro₁ φ₂ Γ⊢simplifyφ
...     | no _ =
        ⇒-elim
          (⇒-intro
            (∨-elim {Γ = Γ}
              (∨-intro₁ φ₂ (assume {Γ = Γ} (¬ ψ)))
              (∨-intro₂ (¬ ψ)
                (from-simplify-∨-lem (assume {Γ = Γ} (simplify-∨ φ₂))))))
          Γ⊢simplifyφ
from-simplify-∨-lem {Γ} {.(φ₁ ∨ φ₂)} Γ⊢simplifyφ  | sdisj₅ φ₁ φ₂ | pos .φ₁
  with (¬ φ₁) ∈∨ φ₂
... | yes p₅ =
      ⇒-elim
        (⇒-intro
          (∨-elim {Γ = Γ}
            (∨-intro₁ φ₂ (assume {Γ = Γ} φ₁))
            (∨-intro₂ φ₁
              (subst (sym p₅) (reorder-∨-lem (assume {Γ = Γ} (¬ φ₁)) φ₂)))))
        (PEM {φ = φ₁})
... | no _
    with φ₁ ∈∨ φ₂
... | yes p₆ = ∨-intro₂ φ₁ (from-simplify-∨-lem Γ⊢simplifyφ)
... | no _
    with eq (simplify-∨ φ₂) ⊤
...     | yes p₇ =
       ∨-intro₂ φ₁ (from-simplify-∨-lem (subst (sym p₇) Γ⊢simplifyφ))
...     | no _
        with eq (simplify-∨ φ₂) ⊥
...     | yes p₈ = ∨-intro₁ φ₂ Γ⊢simplifyφ
...     | no _ =
          ⇒-elim
            (⇒-intro
              (∨-elim {Γ = Γ}
                (∨-intro₁ φ₂ (assume {Γ = Γ} φ₁))
                (∨-intro₂ φ₁
                  (from-simplify-∨-lem (assume {Γ = Γ} (simplify-∨ φ₂))))))
              Γ⊢simplifyφ
--------------------------------------------------------------------------- ■



data simplify-∧-Cases : PropFormula  → Set where

  sconj₁ : (φ : PropFormula)     → simplify-∧-Cases (⊥ ∧ φ)
  sconj₂ : (φ : PropFormula)     → simplify-∧-Cases (φ ∧ ⊥)
  sconj₃ : (φ : PropFormula)     → simplify-∧-Cases (⊤ ∧ φ)
  sconj₄ : (φ : PropFormula)     → simplify-∧-Cases (φ ∧ ⊤)
  sconj₅ : (φ₁ φ₂ : PropFormula) → simplify-∧-Cases (φ₁ ∧ φ₂)
  other  : (φ : PropFormula)     → simplify-∧-Cases φ

simplify-∧-cases : (φ : PropFormula) → simplify-∧-Cases φ
simplify-∧-cases (⊥ ∧ φ)   = sconj₁ _
simplify-∧-cases (φ ∧ ⊥)   = sconj₂ _
simplify-∧-cases (⊤ ∧ φ)   = sconj₃ _
simplify-∧-cases (φ ∧ ⊤)   = sconj₄ _
simplify-∧-cases (φ₁ ∧ φ₂) = sconj₅ _ _
simplify-∧-cases  φ        = other _

-- Def.
_∈∧_ : (ψ φ : PropFormula) → Dec (ψ ≡ (conjunct φ ψ))
ψ ∈∧ φ = eq ψ (conjunct φ ψ)

-- Def.
simplify-∧ : PropFormula → PropFormula
simplify-∧ φ
  with simplify-∧-cases φ
simplify-∧ .(⊥ ∧ φ) | sconj₁ φ = ⊥
simplify-∧ .(φ ∧ ⊥) | sconj₂ φ = ⊥
simplify-∧ .(⊤ ∧ φ) | sconj₃ φ = simplify-∧ φ
simplify-∧ .(φ ∧ ⊤) | sconj₄ φ = simplify-∧ φ
simplify-∧ φ        | other .φ  = φ
simplify-∧ .(φ₁ ∧ φ₂)  | sconj₅ φ₁ φ₂
  with neg-view  φ₁
simplify-∧ .(¬ ψ ∧ φ₂) | sconj₅ .(¬ ψ) φ₂ | neg ψ
  with ⌊ ψ ∈∧ φ₂ ⌋
... | true  = ⊥
... | false
    with ⌊ (¬ ψ) ∈∧ φ₂ ⌋
... | true  = simplify-∧ φ₂
... | false
    with ⌊ eq (simplify-∧ φ₂) ⊥ ⌋
...     | true  = ⊥
...     | false
        with ⌊ eq (simplify-∧ φ₂) ⊤ ⌋
...     | true  = ¬ ψ
...     | false = ¬ ψ ∧ simplify-∧ φ₂
simplify-∧ .(φ₁ ∧ φ₂) | sconj₅ φ₁ φ₂ | pos .φ₁
  with ⌊ (¬ φ₁) ∈∧ φ₂ ⌋
... | true  = ⊥
... | false
    with ⌊ φ₁ ∈∧ φ₂ ⌋
... | true  = simplify-∧ φ₂
... | false
    with ⌊ eq (simplify-∧ φ₂) ⊥ ⌋
...     | true  = ⊥
...     | false
        with ⌊ eq (simplify-∧ φ₂) ⊤ ⌋
...     | true  = φ₁
...     | false = φ₁ ∧ simplify-∧ φ₂

-- Lemma.
simplify-∧-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ simplify-∧ φ

-- Proof.
simplify-∧-lem {Γ} {φ} Γ⊢φ
  with simplify-∧-cases φ
simplify-∧-lem {Γ} {.(⊥ ∧ φ)}   Γ⊢φ | sconj₁ φ = ∧-proj₁ Γ⊢φ
simplify-∧-lem {Γ} {.(φ ∧ ⊥)}   Γ⊢φ | sconj₂ φ = ∧-proj₂ Γ⊢φ
simplify-∧-lem {Γ} {.(⊤ ∧ φ)}   Γ⊢φ | sconj₃ φ = simplify-∧-lem (∧-proj₂ Γ⊢φ)
simplify-∧-lem {Γ} {.(φ ∧ ⊤)}   Γ⊢φ | sconj₄ φ = simplify-∧-lem (∧-proj₁ Γ⊢φ)
simplify-∧-lem {Γ} {φ}          Γ⊢φ | other .φ = Γ⊢φ
simplify-∧-lem {Γ} {.(φ₁ ∧ φ₂)} Γ⊢φ | sconj₅ φ₁ φ₂
  with neg-view  φ₁
simplify-∧-lem {Γ} {.(¬ ψ ∧ φ₂)} Γ⊢φ | sconj₅ .(¬ ψ) φ₂ | neg ψ
  with ψ ∈∧ φ₂
... | yes p₁ =
  ¬-elim (∧-proj₁ Γ⊢φ) (subst (sym p₁) (conjunct-thm ψ (∧-proj₂ Γ⊢φ)))
... | no _
    with (¬ ψ) ∈∧ φ₂
... | yes p₂ = simplify-∧-lem (∧-proj₂ Γ⊢φ)
... | no _
    with eq (simplify-∧ φ₂) ⊥
...     | yes p₃ = subst p₃ (simplify-∧-lem (∧-proj₂ Γ⊢φ))
...     | no _
        with eq (simplify-∧ φ₂) ⊤
...     | yes p₄ = ∧-proj₁ Γ⊢φ
...     | no _ =  ∧-intro (∧-proj₁ Γ⊢φ) (simplify-∧-lem (∧-proj₂ Γ⊢φ))
simplify-∧-lem {Γ} {.(φ₁ ∧ φ₂)} Γ⊢φ | sconj₅ φ₁ φ₂ | pos .φ₁
  with (¬ φ₁) ∈∧ φ₂
... | yes p₅ =
  ¬-elim (subst (sym p₅) (conjunct-thm (¬ φ₁) (∧-proj₂ Γ⊢φ))) (∧-proj₁ Γ⊢φ)
... | no _
    with φ₁ ∈∧ φ₂
... | yes p₆ = simplify-∧-lem (∧-proj₂ Γ⊢φ)
... | no _
    with eq (simplify-∧ φ₂) ⊥
...     | yes p₇ = subst p₇ (simplify-∧-lem (∧-proj₂ Γ⊢φ))
...     | no _
        with eq (simplify-∧ φ₂) ⊤
...     | yes p₈ = ∧-proj₁ Γ⊢φ
...     | no _   = ∧-intro (∧-proj₁ Γ⊢φ) (simplify-∧-lem (∧-proj₂ Γ⊢φ))
--------------------------------------------------------------------------- ■

-- Lemma.
from-simplify-∧-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ simplify-∧ φ
  → Γ ⊢ φ

-- Proof.
from-simplify-∧-lem {Γ} {φ} Γ⊢φ
  with simplify-∧-cases φ
from-simplify-∧-lem {Γ} {.(⊥ ∧ φ)}   Γ⊢φ | sconj₁ φ = ⊥-elim (⊥ ∧ φ) Γ⊢φ
from-simplify-∧-lem {Γ} {.(φ ∧ ⊥)}   Γ⊢φ | sconj₂ φ = ⊥-elim (φ ∧ ⊥) Γ⊢φ
from-simplify-∧-lem {Γ} {.(⊤ ∧ φ)}   Γ⊢φ | sconj₃ φ =
  ∧-intro ⊤-intro (from-simplify-∧-lem Γ⊢φ)
from-simplify-∧-lem {Γ} {.(φ ∧ ⊤)}   Γ⊢φ | sconj₄ φ =
  ∧-intro (from-simplify-∧-lem Γ⊢φ) ⊤-intro
from-simplify-∧-lem {Γ} {φ}          Γ⊢φ | other .φ = Γ⊢φ
from-simplify-∧-lem {Γ} {.(φ₁ ∧ φ₂)} Γ⊢φ | sconj₅ φ₁ φ₂
  with neg-view  φ₁
from-simplify-∧-lem {Γ} {.(¬ ψ ∧ φ₂)} Γ⊢φ | sconj₅ .(¬ ψ) φ₂ | neg ψ
  with ψ ∈∧ φ₂
... | yes p₁ = ⊥-elim (¬ ψ ∧ φ₂) Γ⊢φ
... | no _
    with (¬ ψ) ∈∧ φ₂
... | yes p₂ =
  ∧-intro
    (subst (sym p₂)
      (conjunct-thm {Γ = Γ} {φ = φ₂} (¬ ψ)
        (from-simplify-∧-lem Γ⊢φ)))
    (from-simplify-∧-lem Γ⊢φ)
... | no _
    with eq (simplify-∧ φ₂) ⊥
...     | yes p₃ = ⊥-elim (¬ ψ ∧ φ₂) Γ⊢φ
...     | no _
        with eq (simplify-∧ φ₂) ⊤
...     | yes p₄ = ∧-intro Γ⊢φ (from-simplify-∧-lem (subst (sym p₄) ⊤-intro))
...     | no _   = ∧-intro (∧-proj₁ Γ⊢φ) (from-simplify-∧-lem (∧-proj₂ Γ⊢φ))
from-simplify-∧-lem {Γ} {.(φ₁ ∧ φ₂)} Γ⊢φ | sconj₅ φ₁ φ₂ | pos .φ₁
  with (¬ φ₁) ∈∧ φ₂
... | yes p₅ = ⊥-elim (φ₁ ∧ φ₂) Γ⊢φ
... | no _
    with φ₁ ∈∧ φ₂
... | yes p₆ =
  ∧-intro
    (subst (sym p₆)
      (conjunct-thm {Γ = Γ} {φ = φ₂} φ₁
        (from-simplify-∧-lem Γ⊢φ)))
    (from-simplify-∧-lem Γ⊢φ)
... | no _
    with eq (simplify-∧ φ₂) ⊥
...     | yes p₇ = ⊥-elim (φ₁ ∧ φ₂) Γ⊢φ
...     | no _
        with eq (simplify-∧ φ₂) ⊤
...     | yes p₈ = ∧-intro Γ⊢φ (from-simplify-∧-lem (subst (sym p₈) ⊤-intro))
...     | no _   = ∧-intro (∧-proj₁ Γ⊢φ) (from-simplify-∧-lem (∧-proj₂ Γ⊢φ))
--------------------------------------------------------------------------- ■



{-
-- Def.
data Polarity : Set where
  ⊕ : Polarity
  ⊖ : Polarity

data nnf-Cases : PropFormula  → Set where

  case₁ : (φ₁ φ₂ : PropFormula) → nnf-Cases (φ₁ ∧ φ₂)
  case₂ : (φ₁ φ₂ : PropFormula) → nnf-Cases (φ₁ ∨ φ₂)
  case₃ : (φ₁ φ₂ : PropFormula) → nnf-Cases (φ₁ ⇒ φ₂)
  case₄ : (φ : PropFormula)     → nnf-Cases (¬ φ)
  case₅ : (φ : PropFormula)     → nnf-Cases ⊥
  case₆ : (φ : PropFormula)     → nnf-Cases ⊤
  other : (φ : PropFormula)     → nnf-Cases φ

nnf-cases : (φ : PropFormula) → nnf-Cases φ
nnf-cases (φ₁ ∧ φ₂) = case₁ _ _
nnf-cases (φ₁ ∨ φ₂) = case₂ _ _
nnf-cases (φ₁ ⇒ φ₂) = case₃ _ _
nnf-cases (¬ φ)     = case₄ _
nnf-cases ⊥         = case₅ ⊥
nnf-cases ⊤         = case₆ ⊤
nnf-cases φ         = other _

-- Def.
nnf₀ : Polarity → PropFormula → PropFormula
nnf₀ ⊕ φ
  with nnf-cases φ
nnf₀ ⊕ .(φ₁ ∧ φ₂) | case₁ φ₁ φ₂ = simplify-∧ (assoc-∧ (nnf₀ ⊕ φ₁ ∧ nnf₀ ⊕ φ₂))
nnf₀ ⊕ .(φ₁ ∨ φ₂) | case₂ φ₁ φ₂ = simplify-∨ (assoc-∨ (nnf₀ ⊕ φ₁ ∨ nnf₀ ⊕ φ₂))
nnf₀ ⊕ .(φ₁ ⇒ φ₂) | case₃ φ₁ φ₂ = simplify-∨ (assoc-∨ (nnf₀ ⊖ φ₁ ∨ nnf₀ ⊕ φ₂))
nnf₀ ⊕ .(¬ φ)     | case₄ φ     = nnf₀ ⊖ φ
nnf₀ ⊕ .(⊥)       | case₅ φ     = ⊥
nnf₀ ⊕ .(⊤)       | case₆ φ     = ⊤
nnf₀ ⊕ φ          | other .φ    = φ
nnf₀ ⊖ φ
  with nnf-cases φ
nnf₀ ⊖ .(φ₁ ∧ φ₂) | case₁ φ₁ φ₂ = simplify-∨ (assoc-∨ (nnf₀ ⊖ φ₁ ∨ nnf₀ ⊖ φ₂))
nnf₀ ⊖ .(φ₁ ∨ φ₂) | case₂ φ₁ φ₂ = simplify-∧ (assoc-∧ (nnf₀ ⊖ φ₁ ∧ nnf₀ ⊖ φ₂))
nnf₀ ⊖ .(φ₁ ⇒ φ₂) | case₃ φ₁ φ₂ = simplify-∧ (assoc-∧ (nnf₀ ⊖ φ₂ ∧ nnf₀ ⊕ φ₁))
nnf₀ ⊖ .(¬ φ)     | case₄ φ     = nnf₀ ⊕ φ
nnf₀ ⊖ .(⊥)       | case₅ φ     = ⊤
nnf₀ ⊖ .(⊤)       | case₆ φ     = ⊥
nnf₀ ⊖ φ          | other .φ    = ¬ φ

-- Lemma.
postulate
  nnf₀-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → (pol : Polarity)
    → Γ ⊢ nnf₀ pol φ

postulate
  from-nnf₀-lem
    : ∀ {Γ} {φ}
    → (pol : Polarity)
    → Γ ⊢ nnf₀ pol φ
    → Γ ⊢ φ

-- Def.
nnf : PropFormula → PropFormula
nnf φ = nnf₀ ⊕ φ

postulate
  nnf-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ nnf φ

postulate
  from-nnf-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ nnf φ
    → Γ ⊢ φ
-}

-- Using bounded recursion.

data nnfCases : PropFormula  → Set where
  case₁  : (φ₁ φ₂ : PropFormula) → nnfCases (φ₁ ∧ φ₂)
  case₂  : (φ₁ φ₂ : PropFormula) → nnfCases (φ₁ ∨ φ₂)
  case₃  : (φ₁ φ₂ : PropFormula) → nnfCases (φ₁ ⇒ φ₂)
  case₄  : (φ₁ φ₂ : PropFormula) → nnfCases (¬ (φ₁ ∧ φ₂))
  case₅  : (φ₁ φ₂ : PropFormula) → nnfCases (¬ (φ₁ ∨ φ₂))
  case₆  : (φ₁ : PropFormula)    → nnfCases (¬ ¬ φ₁)
  case₇  : (φ₁ φ₂ : PropFormula) → nnfCases (¬ (φ₁ ⇒ φ₂))
  case₈  : nnfCases (¬ ⊤)
  case₉  : nnfCases (¬ ⊥)
  other  : (φ₁ : PropFormula)    → nnfCases φ₁

nnf-cases : (φ : PropFormula) → nnfCases φ
nnf-cases (φ₁ ∧ φ₂)     = case₁ _ _
nnf-cases (φ₁ ∨ φ₂)     = case₂ _ _
nnf-cases (φ₁ ⇒ φ₂)     = case₃ _ _
nnf-cases (¬ (φ₁ ∧ φ₂)) = case₄ _ _
nnf-cases (¬ (φ₁ ∨ φ₂)) = case₅ _ _
nnf-cases (¬ (φ₁ ⇒ φ₂)) = case₇ _ _
nnf-cases (¬ (¬ φ))     = case₆ _
nnf-cases (¬ ⊤)         = case₈
nnf-cases (¬ ⊥)         = case₉
nnf-cases φ             = other _

-- Def.
nnf₀ : PropFormula → Nat → PropFormula
nnf₀ φ (suc n)
  with nnf-cases φ
...  | case₁ φ₁ φ₂  = simplify-∧ (assoc-∧ (nnf₀ φ₁ n ∧ nnf₀ φ₂ n))
...  | case₂ φ₁ φ₂  = simplify-∨ (assoc-∨ (nnf₀ φ₁ n ∨ nnf₀ φ₂ n))
...  | case₃ φ₁ φ₂  = simplify-∨ (assoc-∨ (nnf₀ ((¬ φ₁) ∨ φ₂) n))
...  | case₄ φ₁ φ₂  = simplify-∨ (assoc-∨ (nnf₀ ((¬ φ₁) ∨ (¬ φ₂)) n))
...  | case₅ φ₁ φ₂  = simplify-∧ (assoc-∧ (nnf₀ ((¬ φ₁) ∧ (¬ φ₂)) n))
...  | case₆ φ₁     = nnf₀ φ₁ n
...  | case₇ φ₁ φ₂  = simplify-∧ (assoc-∧ (nnf₀ ((¬ φ₂) ∧ φ₁) n))
...  | case₈        = ⊥
...  | case₉        = ⊤
...  | other .φ     = φ
nnf₀ φ  zero        = φ

-- Lemma.
nnf₀-lem
  : ∀ {Γ} {φ}
  → (n : Nat)
  → Γ ⊢ φ
  → Γ ⊢ nnf₀ φ n

-- Proof.
nnf₀-lem {Γ} {φ} (suc n) Γ⊢φ
  with nnf-cases φ
...  | case₁ φ₁ φ₂ =
  simplify-∧-lem
    (assoc-∧-lem
      (∧-intro
        (nnf₀-lem n (∧-proj₁ Γ⊢φ))
        (nnf₀-lem n (∧-proj₂ Γ⊢φ))))
...  | case₂ φ₁ φ₂ =
  simplify-∨-lem
    (assoc-∨-lem
      (⇒-elim
        (⇒-intro
         (∨-elim {Γ = Γ}
           (∨-intro₁
             (nnf₀ φ₂ n)
             (nnf₀-lem n (assume {Γ = Γ} φ₁)))
           (∨-intro₂
             (nnf₀ φ₁ n)
             (nnf₀-lem n (assume {Γ = Γ} φ₂)))))
          Γ⊢φ))
...  | case₃ φ₁ φ₂   =
  simplify-∨-lem
    (assoc-∨-lem
      (nnf₀-lem n (⇒-to-¬∨ Γ⊢φ)))
...  | case₄ φ₁ φ₂  =
  simplify-∨-lem
    (assoc-∨-lem
      (nnf₀-lem n (¬∧-to-¬∨¬ Γ⊢φ)))
...  | case₅ φ₁ φ₂  =
  simplify-∧-lem
    (assoc-∧-lem
      (nnf₀-lem n (¬∨-to-¬∧¬ Γ⊢φ)))
...  | case₆ φ₁      = nnf₀-lem n (¬¬-equiv₁ Γ⊢φ)
...  | case₇ φ₁ φ₂  =
  simplify-∧-lem
    (assoc-∧-lem
      (nnf₀-lem n helper))
 where

   helper₂ : Γ ⊢ φ₂ ∨ ¬ φ₁ ⇒ (φ₁ ⇒ φ₂)
   helper₂ = ⇒-intro (¬∨-to-⇒ (∨-comm (assume {Γ = Γ} (φ₂ ∨ ¬ φ₁))))

   helper₁ : Γ ⊢ ¬ (φ₂ ∨ ¬ φ₁)
   helper₁ = subst⊢¬ helper₂ Γ⊢φ

   helper₀ : Γ ⊢ ¬ φ₂ ∧ (¬ ¬ φ₁)
   helper₀ = ¬∨-to-¬∧¬ helper₁

   helper  : Γ ⊢ ¬ φ₂ ∧ φ₁
   helper = ∧-intro (∧-proj₁ helper₀) (¬¬-equiv₁ (∧-proj₂ helper₀))

...  | case₈       = ¬-elim Γ⊢φ ⊤-intro
...  | case₉       = ⊤-intro
...  | other .φ   = Γ⊢φ
nnf₀-lem zero Γ⊢φ = Γ⊢φ
--------------------------------------------------------------------------- ■

-- Lemma.
from-nnf₀-lem
  : ∀ {Γ} {φ} {n}
  → Γ ⊢ nnf₀ φ n
  → Γ ⊢ φ

-- Proof.
from-nnf₀-lem {Γ} {φ} {(suc n)} Γ⊢φ
  with nnf-cases φ
...  | case₁ φ₁ φ₂ =
  ∧-intro
    (from-nnf₀-lem {n = n} (∧-proj₁ helper))
    (from-nnf₀-lem {n = n} (∧-proj₂ helper))
  where
    helper : Γ ⊢ nnf₀ φ₁ n ∧ nnf₀ φ₂ n
    helper = from-assoc-∧-lem (from-simplify-∧-lem Γ⊢φ)
...  | case₂ φ₁ φ₂ =
   ⇒-elim
     (⇒-intro
       (∨-elim {Γ = Γ}
         (∨-intro₁ φ₂ (from-nnf₀-lem {n = n} (assume {Γ = Γ} (nnf₀ φ₁ n))))
         (∨-intro₂ φ₁ (from-nnf₀-lem {n = n} (assume {Γ = Γ} (nnf₀ φ₂ n))))))
     helper
  where
    helper : Γ ⊢ nnf₀ φ₁ n ∨ nnf₀ φ₂ n
    helper = from-assoc-∨-lem (from-simplify-∨-lem Γ⊢φ)
...  | case₃ φ₁ φ₂   =
  ¬∨-to-⇒ (from-nnf₀-lem {n = n} helper)
  where
    helper : Γ ⊢ nnf₀ (¬ φ₁ ∨ φ₂) n
    helper = from-assoc-∨-lem (from-simplify-∨-lem Γ⊢φ)
...  | case₄ φ₁ φ₂  =
  ¬∨¬-to-¬∧ (from-nnf₀-lem {n = n} helper)
  where
    helper : Γ ⊢ nnf₀ (¬ φ₁ ∨  ¬ φ₂) n
    helper = from-assoc-∨-lem (from-simplify-∨-lem Γ⊢φ)
...  | case₅ φ₁ φ₂  =
  ¬∧¬-to-¬∨ (from-nnf₀-lem {n = n} helper)
  where
    helper : Γ ⊢ nnf₀ (¬ φ₁ ∧ ¬ φ₂) n
    helper = from-assoc-∧-lem (from-simplify-∧-lem Γ⊢φ)
...  | case₆ φ₁     = ¬¬-equiv₂ (from-nnf₀-lem {n = n} Γ⊢φ)
...  | case₇ φ₁ φ₂  =
       (¬-intro
          (¬-elim
            (weaken (φ₁ ⇒ φ₂) (∧-proj₁ helper₁))
            (⇒-elim
              (assume {Γ = Γ} (φ₁ ⇒ φ₂))
              (weaken (φ₁ ⇒ φ₂) (∧-proj₂ helper₁)))))
  where
    helper₁ : Γ ⊢ (¬ φ₂ ∧ φ₁)
    helper₁ =
      from-nnf₀-lem {n = n} (from-assoc-∧-lem (from-simplify-∧-lem Γ⊢φ))

...  | case₈       = ⊥-elim (¬ ⊤) Γ⊢φ
...  | case₉       = ¬-intro (assume {Γ = Γ} ⊥)
...  | other .φ   = Γ⊢φ
from-nnf₀-lem {_} {_} {zero} Γ⊢φ = Γ⊢φ


-- Complexity measure.
nnf-cm : PropFormula → Nat
nnf-cm φ with nnf-cases φ
... | case₁ φ₁ φ₂   = nnf-cm φ₁ + nnf-cm φ₂ + 1
... | case₂ φ₁ φ₂   = nnf-cm φ₁ + nnf-cm φ₂ + 1
... | case₃ φ₁ φ₂   = 2 * nnf-cm φ₁  + nnf-cm φ₂ + 1
... | case₄ φ₁ φ₂   = nnf-cm (¬ φ₁) + nnf-cm (¬ φ₂) + 1
... | case₅ φ₁ φ₂   = nnf-cm (¬ φ₁) + nnf-cm (¬ φ₂) + 1
... | case₆ φ₁      = nnf-cm (¬ φ₁) + 1
... | case₇ φ₁ φ₂   = nnf-cm φ₁ + nnf-cm (¬ φ₂) + 3
... | case₈         = 1
... | case₉         = 1
... | other .φ      = 1

-- Def.
nnf : PropFormula → PropFormula
nnf φ = nnf₀ φ (nnf-cm φ)

-- Lemma.
nnf-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ nnf φ

-- Proof.
nnf-lem {_} {φ} Γ⊢φ = nnf₀-lem (nnf-cm φ) Γ⊢φ
--------------------------------------------------------------------------- ■

-- Lemma.
from-nnf-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ nnf φ
  → Γ ⊢ φ
-- Proof.
from-nnf-lem {Γ} {φ} Γ⊢nnf = from-nnf₀-lem {Γ = Γ} {n = nnf-cm φ} Γ⊢nnf
--------------------------------------------------------------------------- ■

------------------------------------------------------------------------------
-- Conjunctive Normal Forms (CNF)
------------------------------------------------------------------------------

-- Def.
cnf : PropFormula → PropFormula
cnf φ = cnf-dist (nnf φ)

-- Lemma.
cnf-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ cnf φ

-- Proof.
cnf-lem Γ⊢φ = cnf-dist-lem (nnf-lem Γ⊢φ)
--------------------------------------------------------------------------- ■

-- Lemma.
from-cnf-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ cnf φ
  → Γ ⊢ φ

-- Proof.
from-cnf-lem {Γ} {φ} Γ⊢cnfφ = from-nnf-lem (from-cnf-dist-lem  Γ⊢cnfφ)
--------------------------------------------------------------------------- ■
