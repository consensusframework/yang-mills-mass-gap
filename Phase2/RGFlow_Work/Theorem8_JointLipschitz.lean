import Mathlib
import RGFlow_Work.Basic
import RGFlow_Work.GeminiValidation5
import RGFlow_Work.GeminiValidation6

/-
  RGFlow_Work/Theorem8_JointLipschitz.lean

  THEOREM 8: JOINT LIPSCHITZ CONTINUITY (reconstructed)

  NOTE (Etapa 1): the original file was committed with its entire
  declaration section missing — it contained only banner comments and an
  unterminated doc comment, further evidence that Phase 2 never compiled.
  The intended statement (joint Lipschitz bound via triangle inequality
  from Theorems 5 and 6) is reconstructed below as an honest CONDITIONAL
  theorem: both Lipschitz properties are unproven assumptions.
-/

namespace RGFlow

/-- **Theorem 8 (conditional): joint Lipschitz continuity in (g, a).**
    Given the (assumed) Lipschitz properties in g and in a separately,
    the gap satisfies an L¹ joint bound with constant max(L_g, L_a) = 3.0. -/
theorem mass_gap_joint_lipschitz_L1
    (g₁ g₂ a₁ a₂ : ℝ)
    (hg₁ : 0.5 ≤ g₁ ∧ g₁ ≤ 1.18)
    (hg₂ : 0.5 ≤ g₂ ∧ g₂ ≤ 1.18)
    (ha₁ : 0 < a₁ ∧ a₁ ≤ 0.2)
    (ha₂ : 0 < a₂ ∧ a₂ ≤ 0.2)
    (h_lipg : LipschitzInGAssumption)
    (h_lipa : LipschitzInAAssumption) :
    |mass_gap g₁ a₁ - mass_gap g₂ a₂| ≤
      3.0 * (|g₁ - g₂| + |a₁ - a₂|) := by
  have h1 : |mass_gap g₁ a₁ - mass_gap g₂ a₁| ≤ 2.0 * |g₁ - g₂| :=
    h_lipg g₁ g₂ a₁ hg₁ hg₂ ha₁
  have h2 : |mass_gap g₂ a₁ - mass_gap g₂ a₂| ≤ 3.0 * |a₁ - a₂| :=
    h_lipa g₂ a₁ a₂ hg₂ ha₁ ha₂
  have htri : |mass_gap g₁ a₁ - mass_gap g₂ a₂| ≤
      |mass_gap g₁ a₁ - mass_gap g₂ a₁| + |mass_gap g₂ a₁ - mass_gap g₂ a₂| := by
    have := abs_sub_le (mass_gap g₁ a₁) (mass_gap g₂ a₁) (mass_gap g₂ a₂)
    linarith [this]
  have habs1 : (0:ℝ) ≤ |g₁ - g₂| := abs_nonneg _
  have habs2 : (0:ℝ) ≤ |a₁ - a₂| := abs_nonneg _
  linarith

end RGFlow
