------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Reordering module.
------------------------------------------------------------------------------

open import Data.Nat
  using ( suc; zero; _+_ )
  renaming ( ℕ to Nat )

module ATP.Metis.Rules.Reordering ( n : Nat ) where

------------------------------------------------------------------------------

open import ATP.Metis.Synonyms n

open import Data.PropFormula.Syntax n
open import Data.PropFormula.Dec n                  using ( yes; no; ⌊_⌋ )
open import Data.PropFormula.Properties n           using ( eq; subst )
open import Data.PropFormula.Views n
  using    ( DisjView; disj-view; other; conj-view; conj)
  renaming ( disj to disjshape )

open import Data.PropFormula.Theorems n -- using ( ∨-assoc₂; ∧-assoc₂)

open import Data.Bool                             using ( true; false )
open import Function                              using ( _$_; id; _∘_ )
open import Relation.Binary.PropositionalEquality using ( sym )

open import ATP.Metis.Rules.Conjunct n using ( conjunct; conjunct-thm )

------------------------------------------------------------------------------

-- Right associative functions.

data assoc-∨-Cases : PropFormula → Set where
  case₁ : (φ₁ φ₂ φ₃ : PropFormula) → assoc-∨-Cases ((φ₁ ∨ φ₂) ∨ φ₃)
  case₂ : (φ₁ φ₂ : PropFormula)    → assoc-∨-Cases (φ₁ ∨ φ₂)
  other : (φ : PropFormula)        → assoc-∨-Cases φ

assoc-∨-cases : (φ : PropFormula) → assoc-∨-Cases φ
assoc-∨-cases ((φ₁ ∨ φ₂) ∨ φ₃) = case₁ _ _ _
assoc-∨-cases (φ ∨ ψ)          = case₂ _ _
assoc-∨-cases φ                = other _

-- Def.
assoc-∨₁ : PropFormula → Nat → PropFormula
assoc-∨₁ φ (suc n)
  with assoc-∨-cases φ
... | case₁ φ₁ φ₂ φ₃ = assoc-∨₁ (φ₁ ∨ (φ₂ ∨ φ₃)) n
... | case₂ φ₁ φ₂    = φ₁ ∨ assoc-∨₁ φ₂ n
... | other .φ       = φ
assoc-∨₁ φ _  = φ

-- Complexity measure.
assoc-∨-cm : PropFormula → Nat
assoc-∨-cm φ
  with assoc-∨-cases φ
... | case₁ φ₁ φ₂ φ₃ = assoc-∨-cm φ₂ + assoc-∨-cm φ₃ + 2
... | case₂ φ₁ φ₂    = assoc-∨-cm φ₂ + 2
... | other .φ       = 1

-- Lemma.
assoc-∨₁-lem
  : ∀ {Γ} {φ}
  → (n : Nat)
  → Γ ⊢ φ
  → Γ ⊢ assoc-∨₁ φ n

-- Proof.
assoc-∨₁-lem zero Γ⊢φ = Γ⊢φ
assoc-∨₁-lem {Γ} {φ} (suc n) Γ⊢φ
  with assoc-∨-cases φ
... | case₁ φ₁ φ₂ φ₃ =
  assoc-∨₁-lem n(∨-assoc₂ Γ⊢φ)
... | case₂ φ₁ φ₂    =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ (assoc-∨₁ φ₂ n)
          (assume {Γ = Γ} φ₁))
        (∨-intro₂ φ₁ (assoc-∨₁-lem n
          (assume {Γ = Γ} φ₂)))))
    Γ⊢φ
... | other _ = Γ⊢φ

-- Lemma.
from-assoc-∨₁-lem
  : ∀ {Γ} {φ}
  → (n : Nat)
  → Γ ⊢ assoc-∨₁ φ n
  → Γ ⊢ φ

-- Proof.
from-assoc-∨₁-lem zero Γ⊢φ = Γ⊢φ
from-assoc-∨₁-lem {Γ} {φ} (suc n) Γ⊢assocφ
  with assoc-∨-cases φ
... | case₁ φ₁ φ₂ φ₃ =
  ∨-assoc₁ (from-assoc-∨₁-lem n Γ⊢assocφ)
... | case₂ φ₁ φ₂    =
  ⇒-elim
    (⇒-intro
      (∨-elim {Γ = Γ}
        (∨-intro₁ φ₂ (assume {Γ = Γ} φ₁))
        (∨-intro₂ φ₁ (from-assoc-∨₁-lem n
          (assume {Γ = Γ} (assoc-∨₁ φ₂ n))))))
    Γ⊢assocφ
... | other _ = Γ⊢assocφ  -- ■


-- Def.
assoc-∨ : PropFormula → PropFormula
assoc-∨ φ = assoc-∨₁ φ (assoc-∨-cm φ)

-- Lemma.
assoc-∨-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ assoc-∨ φ

-- Proof.
assoc-∨-lem {_}{φ} Γ⊢φ = assoc-∨₁-lem (assoc-∨-cm φ) Γ⊢φ -- ▩


-- Lemma.
postulate
  from-assoc-∨-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ assoc-∨ φ
    → Γ ⊢ φ


-- Conjunctions in a right-associative form.

data assoc-∧-Cases : PropFormula → Set where
  case₁ : (φ₁ φ₂ φ₃ : PropFormula) → assoc-∧-Cases ((φ₁ ∧ φ₂) ∧ φ₃)
  case₂ : (φ₁ φ₂ : PropFormula)    → assoc-∧-Cases (φ₁ ∧ φ₂)
  other : (φ : PropFormula)        → assoc-∧-Cases φ

assoc-∧-cases : (φ : PropFormula) → assoc-∧-Cases φ
assoc-∧-cases ((φ₁ ∧ φ₂) ∧ φ₃) = case₁ _ _ _
assoc-∧-cases (φ ∧ ψ)          = case₂ _ _
assoc-∧-cases φ                = other _

-- Def.
assoc-∧₁ : PropFormula → Nat → PropFormula
assoc-∧₁ φ (suc n)
  with assoc-∧-cases φ
... | case₁ φ₁ φ₂ φ₃ = assoc-∧₁ (φ₁ ∧ (φ₂ ∧ φ₃)) n
... | case₂ φ₁ φ₂    = φ₁ ∧ assoc-∧₁ φ₂ n
... | other .φ       = φ
assoc-∧₁ φ _  = φ

-- Complexity measure.
assoc-∧-cm : PropFormula → Nat
assoc-∧-cm φ
  with assoc-∧-cases φ
... | case₁ φ₁ φ₂ φ₃ = assoc-∧-cm φ₂ + assoc-∧-cm φ₃ + 2
... | case₂ φ₁ φ₂    = assoc-∧-cm φ₂ + 2
... | other .φ       = 1

assoc-∧₁-lem
  : ∀ {Γ} {φ}
  → (n : Nat)
  → Γ ⊢ φ
  → Γ ⊢ assoc-∧₁ φ n

assoc-∧₁-lem zero Γ⊢φ = Γ⊢φ
assoc-∧₁-lem {Γ} {φ} (suc n) Γ⊢φ
  with assoc-∧-cases φ
... | case₁ φ₁ φ₂ φ₃ = assoc-∧₁-lem n (∧-assoc₂ Γ⊢φ)
... | case₂ φ₁ φ₂ =
      ∧-intro
        (∧-proj₁ Γ⊢φ)
        (assoc-∧₁-lem n (∧-proj₂ Γ⊢φ))
... | other _ = Γ⊢φ

-- Lemma.
postulate
  from-assoc-∧₁-lem
    : ∀ {Γ} {φ}
    → (n : Nat)
    → Γ ⊢ assoc-∧₁ φ n
    → Γ ⊢ φ

-- Def.
assoc-∧ : PropFormula → PropFormula
assoc-∧ φ = assoc-∧₁ φ (assoc-∧-cm φ)

-- Lemma.
assoc-∧-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → Γ ⊢ assoc-∧ φ

-- Proof.
assoc-∧-lem {_}{φ} Γ⊢φ = assoc-∧₁-lem (assoc-∧-cm φ) Γ⊢φ -- ▩


postulate
  from-assoc-∧
    : ∀ {Γ} {φ}
    → Γ ⊢ assoc-∧ φ
    → Γ ⊢ φ

----------------------------------------------------------------------

-- Def.
build-∨ : Premise → Conclusion → PropFormula
build-∨ φ ψ
  with ⌊ eq φ ψ ⌋
... | true  = ψ
... | false
    with disj-view ψ
...    | other _    = φ
...    | disjshape ψ₁ ψ₂
       with ⌊ eq ψ₁ (build-∨ φ ψ₁)⌋
...       | true = ψ₁ ∨ ψ₂
...       | false
          with ⌊ eq  ψ₂ (build-∨ φ ψ₂) ⌋
...          | true  = ψ₁ ∨ ψ₂
...          | false = φ

-- Lemma.
build-∨-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : Conclusion)
  → Γ ⊢ build-∨ φ ψ

-- Proof.
build-∨-lem {_} {φ} Γ⊢φ ψ
  with eq φ ψ
... | yes φ≡ψ = subst φ≡ψ Γ⊢φ
... | no  _
    with disj-view ψ
...    | other _    = Γ⊢φ
...    | disjshape ψ₁ ψ₂
       with eq ψ₁ (build-∨ φ ψ₁)
...       | yes p₁ = ∨-intro₁ ψ₂ (subst (sym p₁) (build-∨-lem Γ⊢φ ψ₁))
...       | no  _
          with eq ψ₂ (build-∨ φ ψ₂)
...          | yes p₂ = ∨-intro₂ ψ₁ (subst (sym p₂) (build-∨-lem Γ⊢φ ψ₂))
...          | no  _  = Γ⊢φ -- ▩

postulate
  from-build-∨-lem
    : ∀ {Γ} {φ ψ}
    → Γ ⊢ build-∨ φ ψ
    → Γ ⊢ φ

-- Def.
factor : PropFormula → PropFormula
factor φ
  with disj-view φ
... | other _ = φ
... | disjshape φ₁ φ₂
    with eq φ₁ (factor φ₂)
...    | yes _ = φ₁
...    | no _  = φ

-- Lemma.
factor-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ φ
    → Γ ⊢ factor φ

-- Proof.
factor-lem {Γ}{φ} Γ⊢φ
  with disj-view φ
...  | other _ = Γ⊢φ
...  | disjshape φ₁ φ₂
     with eq φ₁ (factor φ₂)
...     | yes φ₁≡factorφ₂ =
           ⇒-elim
             (⇒-intro
               (∨-elim {Γ = Γ}
                 (assume {Γ = Γ} φ₁)
                 (subst
                   (sym φ₁≡factorφ₂)
                   (factor-lem $ assume {Γ = Γ} φ₂))))
             Γ⊢φ
...     | no _ = Γ⊢φ  -- ▩

-- Corollary.
-- Lemma.
postulate
  from-factor-lem
    : ∀ {Γ} {φ}
    → Γ ⊢ factor φ
    → Γ ⊢ φ

-- Def.
sbuild-∨ : Premise → Conclusion → PropFormula
sbuild-∨ φ ψ
  with disj-view φ
... | disjshape φ₁ φ₂ = factor (build-∨ φ₁ ψ ∨ sbuild-∨ φ₂ ψ)
... | other _    = build-∨ φ ψ

-- Lemma.
sbuild-∨-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : Conclusion)
  → Γ ⊢ sbuild-∨ φ ψ

-- Proof.
sbuild-∨-lem {Γ} {φ} Γ⊢φ ψ
  with disj-view φ
... | other _    = build-∨-lem Γ⊢φ ψ
... | disjshape φ₁ φ₂ =
        factor-lem
         (⇒-elim
            (⇒-intro
              (∨-elim {Γ = Γ}
                (∨-intro₁ (sbuild-∨ φ₂ ψ)
                  (build-∨-lem (assume {Γ = Γ} φ₁) ψ))
                (∨-intro₂ (build-∨ φ₁ ψ)
                  (sbuild-∨-lem (assume {Γ = Γ} φ₂) ψ))))
            Γ⊢φ)  -- ▩

-- Lemma.
postulate
  from-sbuild-∨-lem
    : ∀ {Γ} {φ ψ}
    → Γ ⊢ sbuild-∨ φ ψ
    → Γ ⊢ φ

-- Def.
reorder-∨ : Premise → Conclusion → PropFormula
reorder-∨ φ ψ = sbuild-∨ (assoc-∨ φ) ψ

-- Lemma.
reorder-∨-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : Conclusion)
  → Γ ⊢ reorder-∨ φ ψ

-- Proof.
reorder-∨-lem Γ⊢φ ψ = sbuild-∨-lem (assoc-∨-lem Γ⊢φ) ψ -- ▩

postulate
  from-reorder-∨-lem
    : ∀ {Γ} {φ ψ}
    → Γ ⊢ reorder-∨ φ ψ
    → Γ ⊢ φ

------------------------------------------------------------------------------
-- Reordering conjunctions.
------------------------------------------------------------------------------

-- Def.
reorder-∧ : Premise → Conclusion → PropFormula
reorder-∧ φ ψ
  with ⌊ eq φ ψ ⌋
...  | true = φ
...  | false
     with conj-view ψ
...     | other _ = conjunct φ ψ
...     | conj ψ₁ ψ₂
        with ⌊ eq ψ₁ (reorder-∧ φ ψ₁)⌋
...        | false = φ
...        | true
           with ⌊ eq ψ₂ (reorder-∧ φ ψ₂) ⌋
...           | true  = ψ₁ ∧ ψ₂
...           | false = φ

-- Lemma.
reorder-∧-lem
  : ∀ {Γ} {φ}
  → Γ ⊢ φ
  → (ψ : Conclusion)
  → Γ ⊢ reorder-∧ φ ψ

-- Proof.
reorder-∧-lem {Γ} {φ} Γ⊢φ ψ
  with ⌊ eq φ ψ ⌋
...  | true = Γ⊢φ
...  | false
     with conj-view ψ
...     | other _  = conjunct-thm ψ Γ⊢φ
...     | conj ψ₁ ψ₂
        with eq ψ₁ (reorder-∧ φ ψ₁)
...        | no  _ = Γ⊢φ
...        | yes p₁
           with eq ψ₂ (reorder-∧ φ ψ₂)
...           | no  _  = Γ⊢φ
...           | yes p₂ =
                  ∧-intro
                    (subst (sym p₁) (reorder-∧-lem Γ⊢φ ψ₁))
                    (subst (sym p₂) (reorder-∧-lem Γ⊢φ ψ₂))  -- ▩

-- Lemma.
postulate
  from-reorder-∧-lem
    : ∀ {Γ} {φ ψ}
    → Γ ⊢ reorder-∧ φ ψ
    → Γ ⊢ φ

-------------------------------------------------------------------------------
-- Reordering a conjunction of disjunctions.
-- Conversion from a CNF formula φ to another CNF formula ψ.
------------------------------------------------------------------------------

-- Def.
disj : Premise → Conclusion → PropFormula
disj φ ψ
  with ⌊ eq φ ψ ⌋
disj φ ψ | true  = ψ
disj φ ψ | false
  with ⌊ eq ψ (reorder-∨ φ ψ) ⌋
... | true  = ψ
... | false
  with conj-view ψ
disj φ .(ψ₁ ∧ ψ₂) | false | false | conj ψ₁ ψ₂
  with  ⌊ eq ψ₁ (disj φ ψ₁) ⌋
... | false = φ
... | true
  with ⌊ eq ψ₂ (reorder-∨ φ ψ₂) ⌋
...  | false = φ
...  | true  = ψ₁ ∧ ψ₂
disj φ ψ | false | false | other .ψ
  with conj-view φ
disj φ ψ          | false | false | other .ψ | (other .φ)  = φ
disj .(φ₁ ∧ φ₂) ψ | false | false | other .ψ | (conj φ₁ φ₂)
  with ⌊ eq ψ (disj φ₁ ψ) ⌋
...  | true = ψ
...  | false
  with ⌊ eq ψ (disj φ₂ ψ) ⌋
...  | true  = ψ
...  | false = φ₁ ∧ φ₂

-- Lemma.
disj-lem
  : ∀ {Γ} {φ}
  → (ψ : Conclusion)
  → Γ ⊢ φ
  → Γ ⊢ disj φ ψ

-- Proof.
disj-lem {Γ}{φ} ψ Γ⊢φ
  with eq φ ψ
... | yes φ≡ψ = subst φ≡ψ Γ⊢φ
... | no  _
  with eq ψ (reorder-∨ φ ψ)
... | yes p₁ = subst (sym p₁) (reorder-∨-lem Γ⊢φ ψ)
... | no _
    with conj-view ψ
disj-lem {Γ}{φ} .(ψ₁ ∧ ψ₂) Γ⊢φ | no _ | no _ | conj ψ₁ ψ₂
  with  eq ψ₁ (disj φ ψ₁)
... | no _ = Γ⊢φ
... | yes p₂
  with  eq ψ₂ (reorder-∨ φ ψ₂)
... | no _   = Γ⊢φ
... | yes p₃ =
        ∧-intro
          (subst (sym p₂) (disj-lem ψ₁ Γ⊢φ))
          (subst (sym p₃) (reorder-∨-lem Γ⊢φ ψ₂))
disj-lem {Γ}{φ} ψ Γ⊢φ          | no _ | no _ | other .ψ
  with conj-view φ
disj-lem {Γ}{φ} ψ Γ⊢φ          | no _ | no _ | other .ψ | (other .φ)
  = Γ⊢φ
disj-lem {Γ}{.(φ₁ ∧ φ₂)} ψ Γ⊢φ | no _ | no _ | other .ψ | (conj φ₁ φ₂)
  with eq ψ (disj φ₁ ψ)
... | yes p₄ = subst (sym p₄) (disj-lem ψ (∧-proj₁ Γ⊢φ))
... | no _
  with eq ψ (disj φ₂ ψ)
... | yes p₅ = subst (sym p₅) (disj-lem ψ (∧-proj₂ Γ⊢φ))
... | no  _ = Γ⊢φ -- ■

postulate
  from-disj-lem
    : ∀ {Γ} {φ ψ}
    → Γ ⊢ disj φ ψ
    → Γ ⊢ φ

-- Def.
reorder-∧∨ : Premise → Conclusion → PropFormula
reorder-∧∨ φ ψ
  with ⌊ eq φ ψ ⌋
... | true  = ψ
... | false
  with ⌊ eq ψ (reorder-∨ φ ψ) ⌋
...  | true  = ψ
...  | false
     with conj-view ψ
...     | other _  = disj φ ψ
...     | conj ψ₁ ψ₂
        with ⌊ eq ψ₁ (reorder-∧∨ φ ψ₁) ⌋
...        | false = φ
...        | true
           with ⌊ eq ψ₂ (reorder-∧∨ φ ψ₂) ⌋
...           | true  = ψ₁ ∧ ψ₂
...           | false = φ

-- Lemma.
reorder-∧∨-lem
  : ∀ {Γ} {φ : Premise}
  → Γ ⊢ φ
  → (ψ : Conclusion)
  → Γ ⊢ reorder-∧∨ φ ψ

-- Proof.
reorder-∧∨-lem {Γ} {φ} Γ⊢φ ψ
  with eq φ ψ
...  | yes φ≡ψ = subst φ≡ψ Γ⊢φ
...  | no  _
  with eq ψ (reorder-∨ φ ψ)
...  | yes p₀ = subst (sym p₀) (reorder-∨-lem Γ⊢φ ψ)
...  | no  _
     with conj-view ψ
...     | other _  = disj-lem ψ Γ⊢φ
...     | conj ψ₁ ψ₂
        with eq ψ₁ (reorder-∧∨ φ ψ₁)
...        | no  _  = Γ⊢φ
...        | yes p₁
           with eq ψ₂ (reorder-∧∨ φ ψ₂)
...           | yes p₂ =
                    ∧-intro
                      (subst (sym p₁) (reorder-∧∨-lem Γ⊢φ ψ₁))
                      (subst (sym p₂) (reorder-∧∨-lem Γ⊢φ ψ₂))
...           | no  _  = Γ⊢φ  -- ■


-- Lemma.
postulate
  from-reorder-∧∨-lem
    : ∀ {Γ} {φ ψ}
    → Γ ⊢ reorder-∧∨ φ ψ
    → Γ ⊢ φ

