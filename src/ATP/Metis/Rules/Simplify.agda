------------------------------------------------------------------------------
-- Agda-Metis Library.
-- Simplify inference rule.
------------------------------------------------------------------------------

open import Data.Nat using ( ℕ )

module ATP.Metis.Rules.Simplify ( n : ℕ ) where

------------------------------------------------------------------------------

open import ATP.Metis.Synonyms n
open import ATP.Metis.Rules.Normalization n
open import ATP.Metis.Rules.Conjunct n
open import ATP.Metis.Rules.Canonicalize n
open import ATP.Metis.Rules.Resolve n

open import Data.Bool.Base
  using    ( Bool; true; false )
  renaming ( _∨_ to _or_; _∧_ to _and_ )

open import Data.PropFormula.Dec n        using ( ⌊_⌋; yes; no )
open import Data.PropFormula.Properties n using ( eq ; subst )
open import Data.PropFormula.Syntax n
open import Data.PropFormula.Theorems n

open import Data.PropFormula.Views n
  using (literal-view ; disj-view; neg-view; conj-view; conj)
  using (disj;neg;pos; other; yes; no )
open import Data.PropFormula.NormalForms n
  hiding ( dnf; cnf; nnf-lem; dnf-lem; cnf-lem)
  renaming (nnf to justNNF )

open import Function using ( id ; _∘_ ; _$_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym )

------------------------------------------------------------------------------

rm-∨ :  PropFormula → Lit → PropFormula
rm-∨ φ ℓ
  with literal-view ℓ
... | no _
  with conj-view ℓ
...    | conj ψ₁ ψ₂ = rm-∨ (rm-∨ φ ψ₁) ψ₂
...    | other _    = φ
rm-∨ φ ℓ | yes _
  with disj-view φ
... | other _
    with literal-view φ
...      | no _ = φ
...      | yes _
         with ⌊ eq φ (nnf (¬ ℓ)) ⌋
...         | false = φ
...         | true  = ⊥
rm-∨ φ ℓ | yes _ | disj φ₁ φ₂
         with ⌊ eq (rm-∨ φ₁ ℓ) ⊥ ⌋
...        | true  = rm-∨ φ₂ ℓ
...        | false
           with ⌊ eq (rm-∨ φ₂ ℓ) ⊥ ⌋
...        | true  = rm-∨ φ₁ ℓ
...        | false = rm-∨ φ₁ ℓ ∨ rm-∨ φ₂ ℓ


sdisj : PropFormula → PropFormula → PropFormula
sdisj φ ψ
  with literal-view ψ
... | no  _
  with conj-view ψ
... | conj ψ₁ ψ₂ = sdisj (sdisj φ ψ₁) ψ₂
... | other _    = φ
-- now, we extract the positive literal to use resolution.
sdisj φ ψ | yes _
  with neg-view ψ
... | neg ℓ = resolve φ ψ ℓ (rm-∨ φ ψ)
... | pos ℓ = resolve ψ φ ℓ (rm-∨ φ ψ)


data simplifyCases : PropFormula → Set where
  case₁ : (γ₁ γ₂ : PropFormula) → simplifyCases (γ₁ ∧ γ₂)
  case₂ : (γ₁ γ₂ : PropFormula) → simplifyCases (γ₁ ∨ γ₂)
  case₃ : simplifyCases ⊥
  case₄ : simplifyCases ⊤
  other : (φ : PropFormula)     → simplifyCases φ

simplify-cases : (φ : PropFormula) → simplifyCases φ
simplify-cases (γ₁ ∧ γ₂) = case₁ _ _
simplify-cases (γ₁ ∨ γ₂) = case₂ _ _
simplify-cases ⊥         = case₃
simplify-cases ⊤         = case₄
simplify-cases φ         = other _

-- Def.
simplify₀ : Premise → Premise → Conclusion → PropFormula
simplify₀ φ₁ φ₂ ψ
  with ⌊ eq φ₁ ψ ⌋
... | true = ψ
... | false
  with ⌊ eq φ₂ ψ ⌋
...   | true = ψ
...   | false
  with simplify-cases φ₁
simplify₀ .⊥ φ₂ ψ | false | false | case₃ = ψ
simplify₀ .⊤ φ₂ ψ | false | false | case₄ = φ₂
simplify₀ .(γ₁ ∧ γ₂) φ₂ ψ | false | false | case₁ γ₁ γ₂ = (γ₁ ∧ γ₂)
simplify₀ .(γ₁ ∨ γ₂) φ₂ ψ | false | false | case₂ γ₁ γ₂
  with ⌊ eq γ₁ (nnf (¬ φ₂)) ⌋
...   | true = γ₂
...   | false
  with ⌊ eq γ₂ (nnf (¬ φ₂)) ⌋
...   | true = γ₁
...   | false
  with ⌊ eq (nnf (¬ (γ₁ ∨ γ₂))) (conjunct φ₂ (nnf (¬ (γ₁ ∨ γ₂)))) ⌋
... | true  = ψ
... | false
  with ⌊ eq (¬ (γ₁ ∨ γ₂)) (canonicalize φ₂ (¬ (γ₁ ∨ γ₂))) ⌋
... | true  = ψ
... | false = γ₁ ∨ γ₂
simplify₀ φ₁ φ₂ ψ | false | false | other .φ₁
  with ⌊ eq (nnf (¬ φ₁)) (conjunct φ₂ (nnf (¬ φ₁))) ⌋
... | true  = ⊥
... | false
  with ⌊ eq (¬ φ₁) (canonicalize φ₂ (¬ φ₁)) ⌋
... | true  = ⊥
... | false = φ₁

-- Lemma.
postulate
  simplify₀-lem
    : ∀ {Γ} {φ₁ φ₂ : Premise}
    → Γ ⊢ φ₁
    → Γ ⊢ φ₂
    → (ψ : Conclusion)
    → Γ ⊢ simplify₀ φ₁ φ₂ ψ

{-
-- Proof.
simplify₀-lem {Γ} {φ₁}  {φ₂}  Γ⊢φ₁ Γ⊢φ₂ ψ
  with eq φ₁ ψ
... | yes p₁ = subst p₁ Γ⊢φ₁
... | no _
  with eq φ₂ ψ
... | yes p₂ = subst p₂ Γ⊢φ₂
... | no _
  with simplify-cases φ₁
simplify₀-lem {Γ} {.⊥} {φ₂} Γ⊢φ₁ Γ⊢φ₂ ψ | no _ | no _ | case₃ = ⊥-elim ψ Γ⊢φ₁
simplify₀-lem {Γ} {.⊤} {φ₂} Γ⊢φ₁ Γ⊢φ₂ ψ | no _ | no _ | case₄ = Γ⊢φ₂
simplify₀-lem {Γ} {.(γ₁ ⇒ γ₂)} {φ₂} Γ⊢φ₁ Γ⊢φ₂ ψ | no _ | no _ | case₁ γ₁ γ₂
  with eq γ₁ φ₂
...   | yes p₃  = ⇒-elim Γ⊢φ₁ (subst (sym p₃) Γ⊢φ₂)
...   | no _
  with eq γ₂ (nnf (¬ φ₂))
...   | yes p₄ =
         nnf-lem
           (¬-intro
             (¬-elim
               (from-nnf-lem
                 (subst p₄
                   (⇒-elim
                     (weaken γ₁ Γ⊢φ₁)
                     (assume {Γ = Γ} γ₁))))
               (weaken γ₁ Γ⊢φ₂)))
...   | no _
  with eq (nnf (¬ (γ₁ ⇒ γ₂))) (conjunct φ₂ (nnf (¬ (γ₁ ⇒ γ₂))))
... | yes p₅ =
       ⊥-elim ψ ( ¬-elim
           (from-nnf-lem
              (subst (sym p₅) (conjunct-thm (nnf (¬ (γ₁ ⇒ γ₂))) Γ⊢φ₂)))
            Γ⊢φ₁)
... | no _
  with eq (¬ (γ₁ ⇒ γ₂)) (canonicalize φ₂ (¬ (γ₁ ⇒ γ₂)))
... | yes p₆  =
      ⊥-elim ψ
        (¬-elim
          (subst (sym p₆) (canonicalize-thm (¬ (γ₁ ⇒ γ₂)) Γ⊢φ₂))
          Γ⊢φ₁)
... | no _ = Γ⊢φ₁
simplify₀-lem {Γ} {.(γ₁ ∨ γ₂)} {φ₂} Γ⊢φ₁ Γ⊢φ₂ ψ | no _ | no _ | case₂ γ₁ γ₂
  with eq γ₁ (nnf (¬ φ₂))
...   | yes p₇   =
        ⇒-elim
          (⇒-intro
            (∨-elim {Γ = Γ}
              (⊥-elim γ₂
                (¬-elim
                  (from-nnf-lem
                    (subst p₇ (assume {Γ = Γ} γ₁)))
                  (weaken γ₁ Γ⊢φ₂)))
              (assume {Γ = Γ} γ₂)))
           Γ⊢φ₁

...   | no _
  with eq γ₂ (nnf (¬ φ₂))
...   | yes p₈ =
        ⇒-elim
          (⇒-intro
            (∨-elim {Γ = Γ}
              (assume {Γ = Γ} γ₁)
              (⊥-elim γ₁
                (¬-elim
                  (from-nnf-lem (subst p₈ (assume {Γ = Γ} γ₂)))
                  (weaken γ₂ Γ⊢φ₂)))))
          Γ⊢φ₁
...   | no _
  with eq (nnf (¬ (γ₁ ∨ γ₂))) (conjunct φ₂ (nnf (¬ (γ₁ ∨ γ₂))))
... | yes p₉ =
        ⊥-elim ψ
          (¬-elim
            (from-nnf-lem
              (subst
                (sym p₉) (conjunct-thm (nnf (¬ (γ₁ ∨ γ₂))) Γ⊢φ₂)))
              Γ⊢φ₁)
... | no _
  with eq (¬ (γ₁ ∨ γ₂)) (canonicalize φ₂ (¬ (γ₁ ∨ γ₂)))
... | yes p₁₀ =
        ⊥-elim ψ
          (¬-elim
            (subst (sym p₁₀) (canonicalize-thm (¬ (γ₁ ∨ γ₂)) Γ⊢φ₂))
            Γ⊢φ₁)
... | no _ = Γ⊢φ₁

simplify₀-lem {Γ} {φ₁} {φ₂}  Γ⊢φ₁ Γ⊢φ₂ ψ | no _ | no _ | other .φ₁
  with eq (nnf (¬ φ₁)) (conjunct φ₂ (nnf (¬ φ₁)))
... | yes p₁₁ =
  ¬-elim
    (from-nnf-lem
      (subst (sym p₁₁)
         (conjunct-thm (nnf (¬ φ₁)) Γ⊢φ₂)))
    Γ⊢φ₁
... | no _
  with eq (¬ φ₁) (canonicalize φ₂ (¬ φ₁))
... | yes p₁₂ =
    ¬-elim (subst (sym p₁₂) (canonicalize-thm (¬ φ₁) Γ⊢φ₂)) Γ⊢φ₁
... | no _    = Γ⊢φ₁
--------------------------------------------------------------------------- ■
-}

data S-View : Premise → Premise → Conclusion → Set where
  case₁ : (φ₁ φ₂ ψ : PropFormula) → S-View φ₁ φ₂ ψ
  case₂ : (φ₁ φ₂ ψ : PropFormula) → S-View φ₁ φ₂ ψ
  case₃ : (φ₁ φ₂ ψ : PropFormula) → S-View φ₁ φ₂ ψ
  case₄ : (φ₁ φ₂ ψ : PropFormula) → S-View φ₁ φ₂ ψ
  nothing  : (φ₁ φ₂ ψ : PropFormula) → S-View φ₁ φ₂ ψ

s-view : (φ₁ φ₂ ψ : PropFormula) → S-View φ₁ φ₂ ψ
s-view φ₁ φ₂ ψ
  with ⌊ eq ψ (simplify₀ φ₁ φ₂ ψ)⌋
... | true = case₁ φ₁ φ₂ ψ
... | false
  with ⌊ eq ψ (simplify₀ (nnf φ₁) φ₂ ψ)⌋
... | true = case₂ φ₁ φ₂ ψ
... | false
  with ⌊ eq ψ (simplify₀ (dnf φ₁) φ₂ ψ)⌋
... | true = case₃ φ₁ φ₂ ψ
... | false
  with ⌊ eq ψ (simplify₀ (cnf φ₁) φ₂ ψ)⌋
... | true  = case₄ φ₁ φ₂ ψ
... | false = nothing φ₁ φ₂ ψ

-- Def.
simplify : Premise → Premise → Conclusion → PropFormula
simplify φ₁ φ₂ ψ with s-view φ₁ φ₂ ψ
simplify φ₁ φ₂ ψ | case₁ .φ₁ .φ₂ .ψ  = simplify₀ φ₁ φ₂ ψ
simplify φ₁ φ₂ ψ | case₂ .φ₁ .φ₂ .ψ  = simplify₀ (nnf φ₁) φ₂ ψ
simplify φ₁ φ₂ ψ | case₃ .φ₁ .φ₂ .ψ  = simplify₀ (dnf φ₁) φ₂ ψ
simplify φ₁ φ₂ ψ | case₄ .φ₁ .φ₂ .ψ  = simplify₀ (cnf φ₁) φ₂ ψ
simplify φ₁ φ₂ ψ | nothing .φ₁ .φ₂ .ψ = φ₁

postulate
-- Theorem.
  simplify-thm
    : ∀ {Γ} {φ₁ φ₂ : Premise}
    → (ψ : Conclusion)
    → Γ ⊢ φ₁
    → Γ ⊢ φ₂
    → Γ ⊢ simplify φ₁ φ₂ ψ

{-
-- Proof.
simplify-thm {Γ} {φ₁} {φ₂} ψ Γ⊢φ₁ Γ⊢φ₂
  with s-view φ₁ φ₂ ψ
... | case₁ .φ₁ .φ₂ .ψ  = simplify₀-lem Γ⊢φ₁ Γ⊢φ₂ ψ
... | case₂ .φ₁ .φ₂ .ψ  = simplify₀-lem (nnf-lem Γ⊢φ₁) Γ⊢φ₂ ψ
... | case₃ .φ₁ .φ₂ .ψ  = simplify₀-lem (dnf-lem Γ⊢φ₁) Γ⊢φ₂ ψ
... | case₄ .φ₁ .φ₂ .ψ  = simplify₀-lem (cnf-lem Γ⊢φ₁) Γ⊢φ₂ ψ
... | nothing .φ₁ .φ₂ .ψ = Γ⊢φ₁
--------------------------------------------------------------------------- ■
-}
