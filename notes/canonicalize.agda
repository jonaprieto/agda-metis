
data Polarity : Set where
  ⊕ : Polarity
  ⊝ : Polarity

data nnfView : PropFormula  → Set where
  conj   : (φ₁ φ₂ : PropFormula) → nnfView (φ₁ ∧ φ₂)
  disj   : (φ₁ φ₂ : PropFormula) → nnfView (φ₁ ∨ φ₂)
  impl   : (φ₁ φ₂ : PropFormula) → nnfView (φ₁ ⇒ φ₂)
  biimpl : (φ₁ φ₂ : PropFormula) → nnfView (φ₁ ⇔ φ₂)
  nneg   : (φ₁ : PropFormula)    → nnfView (¬ φ₁)
  other  : (φ₁ : PropFormula)    → nnfView φ₁

nnf-view : (φ : PropFormula) → nnfView φ
nnf-view (φ₁ ∧ φ₂) = conj _ _
nnf-view (φ₁ ∨ φ₂) = disj _ _
nnf-view (φ₁ ⇒ φ₂) = impl _ _
nnf-view (φ₁ ⇔ φ₂) = biimpl _ _
nnf-view (¬ φ)     = nneg _
nnf-view φ         = other _

nnf₀ : Polarity → PropFormula → PropFormula
nnf₀ ⊕ φ
  with nnf-view φ
nnf₀ ⊕ .(φ₁ ∧ φ₂) | conj φ₁ φ₂   = (nnf₀ ⊕ φ₁) ∧ (nnf₀ ⊕ φ₂)
nnf₀ ⊕ .(φ₁ ∨ φ₂) | disj φ₁ φ₂   = (nnf₀ ⊕ φ₁) ∨ (nnf₀ ⊕ φ₂)
nnf₀ ⊕ .(φ₁ ⇒ φ₂) | impl φ₁ φ₂   = (nnf₀ ⊝ φ₁) ∨ (nnf₀ ⊕ φ₂)
nnf₀ ⊕ .(φ₁ ⇔ φ₂) | biimpl φ₁ φ₂ = ((nnf₀ ⊝ φ₁) ∨ (nnf₀ ⊕ φ₂)) ∧ ((nnf₀ ⊝ φ₂) ∨ (nnf₀ ⊕ φ₁))
nnf₀ ⊕ .(¬ φ)     | nneg φ       = nnf₀ ⊝ φ
nnf₀ ⊕ φ          | other .φ     = φ
nnf₀ ⊝ φ
  with nnf-view φ
nnf₀ ⊝ .(φ₁ ∧ φ₂) | conj φ₁ φ₂   = (nnf₀ ⊝ φ₁) ∨ (nnf₀ ⊝ φ₂)
nnf₀ ⊝ .(φ₁ ∨ φ₂) | disj φ₁ φ₂   = (nnf₀ ⊝ φ₁) ∧ (nnf₀ ⊝ φ₂)
nnf₀ ⊝ .(φ₁ ⇒ φ₂) | impl φ₁ φ₂   = (nnf₀ ⊝ φ₂) ∧ (nnf₀ ⊕ φ₁)
nnf₀ ⊝ .(φ₁ ⇔ φ₂) | biimpl φ₁ φ₂ = ((nnf₀ ⊝ φ₂) ∧ (nnf₀ ⊕ φ₁)) ∨ ((nnf₀ ⊝ φ₁) ∧ (nnf₀ ⊕ φ₂))
nnf₀ ⊝ .(¬ φ)     | nneg φ       = nnf₀ ⊕ φ
nnf₀ ⊝ φ          | other .φ     = ¬ φ

polarity : PropFormula → Polarity
polarity φ
  with neg-view φ
polarity .(¬ φ) | neg φ  = ⊝
polarity φ      | pos .φ = ⊕

postulate
  thm-nnf₀
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ nnf₀ ⊕ φ

postulate
  thm-from-nnf₀
    : ∀ {Γ} {φ}
    → Γ ⊢ nnf₀ ⊕ φ
    → Γ ⊢ ¬ φ

nnf : PropFormula → PropFormula
nnf φ = nnf₀ ⊕ φ

postulate
  thm-nnf
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ nnf φ

postulate
  thm-from-nnf
    : ∀ {Γ} {φ}
    → Γ ⊢ nnf φ
    → Γ ⊢ φ

cnf-nnf : PropFormula → PropFormula
cnf-nnf φ = rconj (cnf-dist φ)

postulate
  thm-cnf-nnf
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ cnf-nnf φ

postulate
  thm-from-cnf-nnf
    : ∀ {Γ} {φ}
    → Γ ⊢ cnf-nnf φ
    → Γ ⊢ φ

dnf-nnf : PropFormula → PropFormula
dnf-nnf φ = rdisj (dnf-dist φ)

postulate
  thm-dnf-nnf
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ dnf-nnf φ

postulate
  thm-from-dnf-nnf
    : ∀ {Γ} {φ}
    → Γ ⊢ dnf-nnf φ
    → Γ ⊢ φ

canon-cnf : PropFormula → PropFormula → PropFormula
canon-cnf φ ψ
  with ⌊ eq (reorder-∧∨ (cnf-nnf φ) (cnf-nnf (nnf ψ))) (cnf-nnf (nnf ψ)) ⌋
canon-cnf φ ψ | false = φ
canon-cnf φ ψ | true  = ψ

postulate
  thm-canon-cnf
    : ∀ {Γ} {φ}
      → Γ ⊢ φ
      → (ψ : PropFormula)
      → Γ ⊢ canon-cnf φ ψ

canon-dnf : PropFormula → PropFormula → PropFormula
canon-dnf φ ψ
  with ⌊ eq (reorder-∨ (dnf-nnf φ) (dnf-nnf (nnf ψ))) (dnf-nnf (nnf ψ)) ⌋
canon-dnf φ ψ | false = φ
canon-dnf φ ψ | true  = ψ

postulate
  thm-canon-dnf
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → (ψ : PropFormula)
    → Γ ⊢ canon-dnf φ ψ

------------------------------------------------------------------------------

const : PropFormula → (PropFormula → PropFormula)
const φ = λ x → φ

nform : PropFormula → PropFormula → PropFormula
nform φ =
  (
    canon-cnf
  ● (↑f nnf)
  ● (↑f id)
  ) φ

postulate
  thm-nform
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → (ψ : PropFormula)
    → Γ ⊢ nform φ ψ
-}

------------------------------------------------------------------------------



_∈-∨_ : PropFormula → PropFormula → Bool
φ ∈-∨ ψ
  with ⌊ eq φ ψ ⌋
...  | true = true
...  | false
     with disj-view ψ
...     | other .ψ   = false
...     | disj ψ₁ ψ₂ = φ ∈-∨ ψ₁ or φ ∈-∨ ψ₂

-- We assumed here that the formula is a disjunction and its right-associated.
rm-∨ : PropFormula → PropFormula
rm-∨ φ
  with disj-view φ
... | other _  = φ
... | disj φ₁ φ₂
    with φ₁ ∈-∨ φ₂
...    | true  = rm-∨ φ₂
...    | false = φ₁ ∨ rm-∨ φ₂

-- We assumed here that the formula is a disjunction and its right-associated.
rm-∧∨ : PropFormula → PropFormula
rm-∧∨ φ
  with conj-view φ
...  | other _    = rm-∨ (rdisj φ)
...  | conj φ₁ φ₂ = rm-∧∨ φ₁ ∧ rm-∧∨ φ₂

_∈-∧_ : PropFormula → PropFormula → Bool
φ ∈-∧ ψ
  with ⌊ eq (reorder-∨ φ ψ) ψ ⌋
...  | true = true
...  | false
     with conj-view ψ
...     | other .ψ   = false
...     | conj ψ₁ ψ₂ = φ ∈-∧ ψ₁ or φ ∈-∧ ψ₂

rm-∧ : PropFormula → PropFormula
rm-∧ φ
  with conj-view φ
...  | other _  = φ
...  | conj φ₁ φ₂
     with φ₁ ∈-∧ φ₂
...     | true  = rm-∧ φ₂
...     | false = φ₁ ∧ rm-∧ φ₂

redun₀ : PropFormula → PropFormula
redun₀ = rm-∧ ∘ rm-∧∨

-- With the following theorem, we aim to remove from the proposition
-- redundancies of the following two kinds:
--       φ ∨ φ             φ ∧ φ
--      --------   and    --------.
--         φ                 φ

redun : PropFormula → PropFormula
redun φ = reorder-∧∨ φ (redun₀ φ)

thm-redun
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ redun φ
thm-redun {Γ}{φ} Γ⊢φ = thm-reorder-∧∨ Γ⊢φ (redun₀ φ)

-----------------------------------------------------------------------------

-- φ ∨ ¬ φ deletions in a right-associated formula.
rmPEM-∨ : PropFormula → PropFormula
rmPEM-∨ φ
  with disj-view φ
... | other .φ   = φ
... | disj φ₁ φ₂
    with neg-view φ₁
rmPEM-∨ .(¬ φ ∨ φ₂) | disj .(¬ φ) φ₂ | neg φ
    with φ ∈-∨ φ₂
rmPEM-∨ .(¬ φ ∨ φ₂) | disj .(¬ φ) φ₂ | neg φ | true  = ⊤
rmPEM-∨ .(¬ φ ∨ φ₂) | disj .(¬ φ) φ₂ | neg φ | false
   with ⌊ eq (rmPEM-∨ φ₂) ⊤ ⌋
rmPEM-∨ .(¬ φ ∨ φ₂) | disj .(¬ φ) φ₂ | neg φ | false | false = ¬ φ ∨ rmPEM-∨ φ₂
rmPEM-∨ .(¬ φ ∨ φ₂) | disj .(¬ φ) φ₂ | neg φ | false | true  = ⊤
rmPEM-∨ .(φ₁ ∨ φ₂)  | disj φ₁ φ₂     | pos .φ₁
    with (¬ φ₁) ∈-∨ φ₂
rmPEM-∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ | pos .φ₁ | true  = ⊤
rmPEM-∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ | pos .φ₁ | false
  with ⌊ eq (rmPEM-∨ φ₂) ⊤ ⌋
rmPEM-∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ | pos .φ₁ | false | false = φ₁ ∨ rmPEM-∨ φ₂
rmPEM-∨ .(φ₁ ∨ φ₂) | disj φ₁ φ₂ | pos .φ₁ | false | true  = ⊤

thm-rmPEM-∨
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ rmPEM-∨ φ

thm-rmPEM-∨ {Γ} {φ} Γ⊢φ
  with disj-view φ
... | other .φ   = Γ⊢φ
... | disj φ₁ φ₂
  with neg-view φ₁
thm-rmPEM-∨ {Γ} {.(¬ φ ∨ φ₂)} Γ⊢φ | disj .(¬ φ) φ₂ | neg φ
  with φ ∈-∨ φ₂
thm-rmPEM-∨ {Γ} {.(¬ φ ∨ φ₂)} Γ⊢φ | disj .(¬ φ) φ₂ | neg φ | true  = ⊤-intro
thm-rmPEM-∨ {Γ} {.(¬ φ ∨ φ₂)} Γ⊢φ | disj .(¬ φ) φ₂ | neg φ | false
  with ⌊ eq (rmPEM-∨ φ₂) ⊤ ⌋
thm-rmPEM-∨ {Γ} {.(¬ φ ∨ φ₂)} Γ⊢φ | disj .(¬ φ) φ₂ | neg φ | false | false =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (rmPEM-∨ φ₂) (assume {Γ = Γ} (¬ φ)))
        (∨-intro₂ (¬ φ) (thm-rmPEM-∨ (assume {Γ = Γ} φ₂)))))
    Γ⊢φ
thm-rmPEM-∨ {Γ} {.(¬ φ ∨ φ₂)} Γ⊢φ | disj .(¬ φ) φ₂ | neg φ | false | true  = ⊤-intro
thm-rmPEM-∨ {Γ} {.(φ₁ ∨ φ₂) } Γ⊢φ | disj φ₁ φ₂     | pos .φ₁
  with (¬ φ₁) ∈-∨ φ₂
thm-rmPEM-∨ {Γ} {.(φ₁ ∨ φ₂) } Γ⊢φ | disj φ₁ φ₂ | pos .φ₁ | true  = ⊤-intro
thm-rmPEM-∨ {Γ} {.(φ₁ ∨ φ₂) } Γ⊢φ | disj φ₁ φ₂ | pos .φ₁ | false
  with ⌊ eq (rmPEM-∨ φ₂) ⊤ ⌋
thm-rmPEM-∨ {Γ} {.(φ₁ ∨ φ₂) } Γ⊢φ | disj φ₁ φ₂ | pos .φ₁ | false | false =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (rmPEM-∨ φ₂) (assume {Γ = Γ} (φ₁)))
        (∨-intro₂ (φ₁) (thm-rmPEM-∨ (assume {Γ = Γ} φ₂)))))
    Γ⊢φ
thm-rmPEM-∨ {Γ} {.(φ₁ ∨ φ₂) } Γ⊢φ | disj φ₁ φ₂ | pos .φ₁ | false | true  = ⊤-intro


-- apply rmPEM-∨ in a CNF
-- The conjunction, again, have to be a right-associative conjunction.
rmPEM-∧∨ : PropFormula → PropFormula
rmPEM-∧∨ φ
  with conj-view φ
...  | other _    = rmPEM-∨ φ
...  | conj φ₁ φ₂ = rmPEM-∨ φ₁ ∧ rmPEM-∧∨ φ₂

thm-rmPEM-∧∨
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ rmPEM-∧∨ φ

thm-rmPEM-∧∨ {Γ} {φ} Γ⊢φ
  with conj-view φ
...  | other _    = thm-rmPEM-∨ Γ⊢φ
...  | conj φ₁ φ₂ =
            ∧-intro
              (thm-rmPEM-∨ (∧-proj₁ Γ⊢φ))
              (thm-rmPEM-∧∨ (∧-proj₂ Γ⊢φ))


rmBot-∧ : PropFormula → PropFormula
rmBot-∧ φ
  with conj-view φ
... | other .φ   = φ
... | conj φ₁ φ₂
    with neg-view φ₁
rmBot-∧ .(¬ φ ∧ φ₂) | conj .(¬ φ) φ₂ | neg φ
    with ⌊ eq (conjunct φ₂ φ) φ ⌋
rmBot-∧ .(¬ φ ∧ φ₂) | conj .(¬ φ) φ₂ | neg φ | true  = ⊥
rmBot-∧ .(¬ φ ∧ φ₂) | conj .(¬ φ) φ₂ | neg φ | false
  with ⌊ eq (rmBot-∧ φ₂) ⊥ ⌋
rmBot-∧ .(¬ φ ∧ φ₂) | conj .(¬ φ) φ₂ | neg φ | false | false = ¬ φ ∧ rmBot-∧ φ₂
rmBot-∧ .(¬ φ ∧ φ₂) | conj .(¬ φ) φ₂ | neg φ | false | true  = ⊥
rmBot-∧ .(φ₁ ∧ φ₂)  | conj φ₁ φ₂     | pos .φ₁
  with ⌊ eq (conjunct φ₂ (¬ φ₁)) (¬ φ₁) ⌋
rmBot-∧ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ | pos .φ₁ | true  = ⊥
rmBot-∧ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ | pos .φ₁ | false
  with ⌊ eq (rmBot-∧ φ₂) ⊥ ⌋
rmBot-∧ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ | pos .φ₁ | false | true  = ⊥
rmBot-∧ .(φ₁ ∧ φ₂) | conj φ₁ φ₂ | pos .φ₁ | false | false = φ₁ ∧ rmBot-∧ φ₂

thm-rmBot-∧
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ rmBot-∧ φ

thm-rmBot-∧ {Γ} {φ} Γ⊢φ
  with conj-view φ
...  | other .φ   = Γ⊢φ
...  | conj φ₁ φ₂
  with neg-view φ₁
thm-rmBot-∧ {Γ} {.(¬ φ ∧ φ₂)} Γ⊢φ | conj .(¬ φ) φ₂ | neg φ
  with eq (conjunct φ₂ φ) φ
thm-rmBot-∧ {Γ} {.(¬ φ ∧ φ₂)} Γ⊢φ | conj .(¬ φ) φ₂ | neg φ | yes p₁  =
  ¬∧-to-⊥
    (∧-intro
      (∧-proj₁ Γ⊢φ)
      (subst p₁ (thm-conjunct φ (∧-proj₂ Γ⊢φ))))
thm-rmBot-∧ {Γ} {.(¬ φ ∧ φ₂)} Γ⊢φ | conj .(¬ φ) φ₂ | neg φ | no _
  with eq (rmBot-∧ φ₂) ⊥
thm-rmBot-∧ {Γ} {.(¬ φ ∧ φ₂)} Γ⊢φ | conj .(¬ φ) φ₂ | neg φ | no _ | no _ =
  ∧-intro (∧-proj₁ Γ⊢φ) (thm-rmBot-∧ (∧-proj₂ Γ⊢φ))
thm-rmBot-∧ {Γ} {.(¬ φ ∧ φ₂)} Γ⊢φ | conj .(¬ φ) φ₂ | neg φ | no _ | yes p₂ =
  subst p₂ (thm-rmBot-∧ (∧-proj₂ Γ⊢φ))
thm-rmBot-∧ {Γ} {.(φ₁ ∧ φ₂) } Γ⊢φ | conj φ₁ φ₂     | pos .φ₁
  with eq (conjunct φ₂ (¬ φ₁)) (¬ φ₁)
thm-rmBot-∧ {Γ} {.(φ₁ ∧ φ₂) } Γ⊢φ | conj φ₁ φ₂ | pos .φ₁ | yes p₃  =
  ¬∧-to-⊥
    (∧-comm
      (∧-intro
        (∧-proj₁ Γ⊢φ)
        (subst p₃ (thm-conjunct (¬ φ₁) (∧-proj₂ Γ⊢φ)))))
thm-rmBot-∧ {Γ} {.(φ₁ ∧ φ₂) } Γ⊢φ | conj φ₁ φ₂ | pos .φ₁ | no _
  with eq (rmBot-∧ φ₂) ⊥
thm-rmBot-∧ {Γ} {.(φ₁ ∧ φ₂) } Γ⊢φ | conj φ₁ φ₂ | pos .φ₁ | no _ | no _ =
  ∧-intro (∧-proj₁ Γ⊢φ) (thm-rmBot-∧ (∧-proj₂ Γ⊢φ))
thm-rmBot-∧ {Γ} {.(φ₁ ∧ φ₂) } Γ⊢φ | conj φ₁ φ₂ | pos .φ₁ | no _ | yes p₄  =
  subst p₄ (thm-rmBot-∧ (∧-proj₂ Γ⊢φ))


data canonView : PropFormula  → Set where

-- Conjunction simplification cases.
  sconj₁ : (φ₁ : PropFormula)    → canonView (φ₁ ∧ ⊤)     -- φ ∧ ⊤ ==> φ.
  sconj₂ : (φ₁ : PropFormula)    → canonView (⊤ ∧ φ₁)     -- ⊤ ∧ φ ==> φ.
  sconj₃ : (φ₁ : PropFormula)    → canonView (φ₁ ∧ ⊥)     -- φ ∧ ⊥ ==> ⊥.
  sconj₄ : (φ₁ : PropFormula)    → canonView (⊥ ∧ φ₁)     -- ⊥ ∧ φ ==> ⊥.
  sconj₅ : (φ₁ φ₂ : PropFormula) → canonView (φ₁ ∧ φ₂)

-- Disjunction simplification cases.
  sdisj₁ : (φ₁ : PropFormula)    → canonView (φ₁ ∨ ⊤)     -- φ ∨ ⊤ ==> ⊤.
  sdisj₂ : (φ₁ : PropFormula)    → canonView (⊤ ∨ φ₁)     -- ⊤ ∨ φ ==> ⊤.
  sdisj₃ : (φ₁ : PropFormula)    → canonView (φ₁ ∨ ⊥)     -- φ ∨ ⊥ ==> φ.
  sdisj₄ : (φ₁ : PropFormula)    → canonView (⊥ ∨ φ₁)     -- ⊥ ∨ φ ==> φ.
  sdisj₅ : (φ₁ φ₂ : PropFormula) → canonView (φ₁ ∨ φ₂)
  other  : (φ₁ : PropFormula)    → canonView φ₁


canon-view : (φ : PropFormula) → canonView φ
canon-view (φ ∧ ⊤)  = sconj₁ _
canon-view (⊤ ∧ φ)  = sconj₂ _
canon-view (φ ∧ ⊥)  = sconj₃ _
canon-view (⊥ ∧ φ)  = sconj₄ _
canon-view (φ ∧ ψ)  = sconj₅ _ _
canon-view (φ ∨ ⊤)  = sdisj₁ _
canon-view (⊤ ∨ φ)  = sdisj₂ _
canon-view (φ ∨ ⊥)  = sdisj₃ _
canon-view (⊥ ∨ φ)  = sdisj₄ _
canon-view (φ ∨ φ₁) = sdisj₅ _ _
canon-view  φ       = other _


-- We assumed here that the formula is a disjunction and its right-associated.
canon : PropFormula → PropFormula
canon φ
  with canon-view φ
canon .(φ₁ ∧ ⊤)  | sconj₁ φ₁ = canon φ₁
canon .(⊤ ∧ φ₁)  | sconj₂ φ₁ = canon φ₁
canon .(φ₁ ∧ ⊥)  | sconj₃ φ₁ = ⊥
canon .(⊥ ∧ φ₁)  | sconj₄ φ₁ = ⊥
canon .(φ₁ ∧ φ₂) | sconj₅ φ₁ φ₂
  with ⌊ eq (canon φ₁) ⊤ ⌋
...  | true = canon φ₂
...  | false
     with ⌊ eq (canon φ₁) ⊥ ⌋
...     | true = ⊥
...     | false
        with ⌊ eq (canon φ₂) ⊤ ⌋
...        | true = canon φ₁
...        | false
           with  ⌊ eq (canon φ₂) ⊥ ⌋
...           | true  = ⊥
...           | false = canon φ₁ ∧ canon φ₂

canon .(φ₁ ∨ ⊤)  | sdisj₁ φ₁ = ⊤
canon .(⊤ ∨ φ₁)  | sdisj₂ φ₁ = ⊤
canon .(φ₁ ∨ ⊥)  | sdisj₃ φ₁ = canon φ₁
canon .(⊥ ∨ φ₁)  | sdisj₄ φ₁ = canon φ₁
canon .(φ₁ ∨ φ₂) | sdisj₅ φ₁ φ₂
  with ⌊ eq (canon φ₁) ⊤ ⌋
...  | true = ⊤
...  | false
     with ⌊ eq (canon φ₁) ⊥ ⌋
...     | true = canon φ₂
...     | false
        with ⌊ eq (canon φ₂) ⊤ ⌋
...        | true = ⊤
...        | false
           with  ⌊ eq (canon φ₂) ⊥ ⌋
...           | true  = canon φ₁
...           | false = canon φ₁ ∨ canon φ₂

canon φ         | other .φ = φ

lem-canon
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ canon φ

lem-canon {Γ} {φ} Γ⊢φ
  with canon-view φ
lem-canon {Γ} {.(φ₁ ∧ ⊤) } Γ⊢φ | sconj₁ φ₁ = lem-canon (∧-proj₁ Γ⊢φ)
lem-canon {Γ} {.(⊤ ∧ φ₁) } Γ⊢φ | sconj₂ φ₁ = lem-canon (∧-proj₂ Γ⊢φ)
lem-canon {Γ} {.(φ₁ ∧ ⊥) } Γ⊢φ | sconj₃ φ₁ = ∧-proj₂ Γ⊢φ
lem-canon {Γ} {.(⊥ ∧ φ₁) } Γ⊢φ | sconj₄ φ₁ = ∧-proj₁ Γ⊢φ
lem-canon {Γ} {.(φ₁ ∧ φ₂)} Γ⊢φ | sconj₅ φ₁ φ₂
  with eq (canon φ₁) ⊤
...  | yes p = lem-canon (∧-proj₂ Γ⊢φ)
...  | no _
     with eq (canon φ₁) ⊥
...     | yes p = subst p (lem-canon (∧-proj₁ Γ⊢φ))
...     | no _
        with eq (canon φ₂) ⊤
...        | yes p = lem-canon (∧-proj₁ Γ⊢φ)
...        | no _
           with  eq (canon φ₂) ⊥
...           | yes p  = subst p (lem-canon (∧-proj₂ Γ⊢φ))
...           | no _ = ∧-intro (lem-canon (∧-proj₁ Γ⊢φ)) (lem-canon (∧-proj₂ Γ⊢φ))

lem-canon {Γ} {.(φ₁ ∨ ⊤) } Γ⊢φ | sdisj₁ φ₁ = ⊤-intro
lem-canon {Γ} {.(⊤ ∨ φ₁) } Γ⊢φ | sdisj₂ φ₁ = ⊤-intro
lem-canon {Γ} {.(φ₁ ∨ ⊥) } Γ⊢φ | sdisj₃ φ₁ = lem-canon (φ∨⊥-to-φ Γ⊢φ)
lem-canon {Γ} {.(⊥ ∨ φ₁) } Γ⊢φ | sdisj₄ φ₁ = lem-canon (φ∨⊥-to-φ (∨-comm Γ⊢φ))
lem-canon {Γ} {.(φ₁ ∨ φ₂)} Γ⊢φ | sdisj₅ φ₁ φ₂
  with eq (canon φ₁) ⊤
...  | yes p = ⊤-intro
...  | no _
     with eq (canon φ₁) ⊥
...     | yes p =
            ⇒-elim
              (⇒-intro
                (∨-elim {Γ = Γ}
                  (⊥-elim (canon φ₂) (subst p (lem-canon (assume {Γ = Γ} φ₁))))
                  (lem-canon (assume {Γ = Γ} φ₂))))
             Γ⊢φ
...     | no _
        with eq (canon φ₂) ⊤
...        | yes _ = ⊤-intro
...        | no _
           with  eq (canon φ₂) ⊥
...           | yes p₂  =
                  ⇒-elim
                    (⇒-intro
                      (∨-elim {Γ = Γ}
                      (lem-canon (assume {Γ = Γ} φ₁))
                      (⊥-elim (canon φ₁)
                        (subst p₂
                          (lem-canon (assume {Γ = Γ} φ₂))))))
                    Γ⊢φ
...           | no _ =
                  ⇒-elim
                   (⇒-intro
                     (∨-elim {Γ = Γ}
                       (∨-intro₁ (canon φ₂)
                         (lem-canon (assume {Γ = Γ} φ₁)))
                       (∨-intro₂ (canon φ₁)
                         (lem-canon (assume {Γ = Γ} φ₂)))))
                     Γ⊢φ
lem-canon {Γ} {φ} Γ⊢φ | other .φ = Γ⊢φ

------------------------------------------------------------------------------
-- Canonicalize functions.

s₁ : PropFormula → PropFormula → PropFormula
s₁ φ ψ = (right-assoc-∧ ∘ cnf) φ

thm-s₁
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : PropFormula)
  → Γ ⊢ s₁ φ ψ
thm-s₁ Γ⊢φ _ = (thm-right-assoc-∧ ∘ thm-cnf) Γ⊢φ

s₂ : PropFormula → PropFormula → PropFormula
s₂ φ ψ = redun φ

thm-s₂
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : PropFormula)
  → Γ ⊢ s₂ φ ψ
thm-s₂ Γ⊢φ _ = thm-redun Γ⊢φ

s₃ : PropFormula → PropFormula → PropFormula
s₃ φ ψ = rmPEM-∧∨ φ

thm-s₃
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : PropFormula)
  → Γ ⊢ s₃ φ ψ
thm-s₃ Γ⊢φ _ = thm-rmPEM-∧∨ Γ⊢φ

s₄ : PropFormula → PropFormula → PropFormula
s₄ φ ψ =  rmBot-∧ φ

thm-s₄
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : PropFormula)
  → Γ ⊢ s₄ φ ψ
thm-s₄ Γ⊢φ _ = thm-rmBot-∧ Γ⊢φ

s₅ : PropFormula → PropFormula → PropFormula
s₅ φ ψ =  canon φ

thm-s₅
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : PropFormula)
  → Γ ⊢ s₅ φ ψ
thm-s₅ Γ⊢φ _ = lem-canon Γ⊢φ

s₆ : PropFormula → PropFormula → PropFormula
s₆ φ ψ
  with conj-view φ
... | conj φ₁ φ₂ = resolve φ₁ φ₂ φ₁ ψ
... | other .φ   = φ

thm-s₆
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : PropFormula)
  → Γ ⊢ s₆ φ ψ
thm-s₆ {Γ} {φ} Γ⊢φ ψ
  with conj-view φ
...  | conj φ₁ φ₂ = thm-resolve ψ φ₁ (∧-proj₁ Γ⊢φ) (∧-proj₂ Γ⊢φ)
...  | other .φ   = Γ⊢φ


canonicalize : PropFormula → PropFormula → PropFormula
canonicalize =
  -- s₆ ●
  s₅ ●
  s₄ ●
  s₃ ●
  s₂ ●
  s₁ ●
  nform


thm-canonicalize
  : ∀ {Γ} {φ}
  → (ψ : PropFormula)
  → Γ ⊢ φ
  → Γ ⊢ canonicalize φ ψ

thm-canonicalize {Γ} {φ} ψ Γ⊢φ =
  (
  thm-s₅ ●⊢
  thm-s₄ ●⊢
  thm-s₃ ●⊢
  thm-s₂ ●⊢
  thm-s₁ ●⊢
  thm-nform
  ) Γ⊢φ ψ

canonicalize-axiom : PropFormula → PropFormula → PropFormula
canonicalize-axiom = (↑f dnf) ● (↑f nnf) ● (↑f id)

postulate
  thm-canonicalize-axiom
    : ∀ {Γ} {φ}
    → (ψ : PropFormula)
    → Γ ⊢ φ
    → Γ ⊢ canonicalize-axiom φ ψ
