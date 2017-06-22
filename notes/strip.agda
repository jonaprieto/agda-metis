-- Splitting a Goal

-- Based on Metis' source code, we believe that strip inference rules performs
-- the following transformations.

-- atp-strip := ∀ {Γ} {φ} → atp-contract ∘ atp-strip₀ Γ⊢φ
--  where
--    atp-strip₀ :=
--     Γ ⊢ ⊤
--       ──────
--       Γ ⊢ ⊤

--       Γ ⊢ φ₁ ∧ φ₂
--       ────────────
--       atp-strip₀ (Γ ⊢ φ₁) ∧ atp-strip₀ (Γ ⊢ φ₁ ⇒ φ₂)

--       Γ ⊢ φ₁ ∨ φ₂
--       ────────────
--       atp-strip₀ (Γ ⊢ ¬ φ₁ ⇒ φ₂)


--       Γ ⊢ ¬ (¬ φ)
--       ────────────
--       Γ ⊢ strip φ

--       Γ ⊢ ¬ (φ₁ ∧ φ₂)
--       ──────────────
--       Γ , ¬ φ₁ ⊢ ¬ φ₂
--       ───────────────
--       Γ ⊢ strip (¬ φ₁ ⇒ φ₂)

--       Γ ⊢ ¬ (φ₁ ∨ φ₂)
--       ──────────────
--       Γ ⊢ ¬ φ₁ ∨ ¬ φ₂
--       ───────────────
--       atp-strip₀ (Γ ⊢ ¬ φ₁) ∧ atp-strip₀ (Γ ⊢ ¬ φ₁ ⇒ φ₂)

--       Γ ⊢ ¬ (φ₁ ⇒ φ₂)
--       ───────────────
--       atp-strip₀ (Γ ⊢ φ₁) ∧ atp-strip₀ (Γ ⊢ φ₁ ⇒ ¬ φ₂)



