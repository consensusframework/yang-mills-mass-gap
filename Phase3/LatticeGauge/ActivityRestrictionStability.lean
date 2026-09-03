/-
LatticeGauge/ActivityRestrictionStability.lean — PEDRA 51,
Gate 51-E: THE CAPSTONE — FINITE-VOLUME EXPONENTIAL STABILITY OF A
LOCAL OBSERVABLE FUNCTIONAL UNDER REMOTE HARD RESTRICTION OF
POLYMER ACTIVITIES (architecture: Sol/GPT-5.6; execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): this gate creates
no machinery. It combines three verified theorems —
  * the exact connector + bridge ledger (51-C),
  * the allowed-column bound (51-D, κ = 3 → exp(8 D_s/113)),
  * the bridge-column bound (51-D, κ = 1 → exp(4 D_s/113)),
by the triangle inequality and the monotonicity of the bridge
prefactor into the allowed one, and reads off the constant 2:

  |gibbsExpectation − activityRestrictedExpectation|
    ≤ 2 · Cf · exp(8 D_s/113) · exp(−n/2),

with D_s = card(supportLinkFinset s), under WalkBarrierSeparated
s r n only (no Disjoint s r). Global constant 2, decay rate 1/2,
explicit local prefactor exp(8 D_s/113); no dependence on the
ambient volume, on card r, on supportLinkFinset r or on
barrierLinkFinset ∅ r.

Language: local exponential stability of the normalized polymer
functional under remote activity suppression. `gibbsExpectation`
is the name of the original formalized expectation; the second
object, `activityRestrictedExpectation`, remains a normalized
polymer functional. This is NOT a statement about two Gibbs
measures, a modified action, a boundary condition, weak or strong
spatial mixing, the thermodynamic limit, infinite volume, a mass
gap, or the Clay problem.

HARD HOLD (not here): integration into main, release, Zenodo, any
of the above interpretations. No project-local scientific axioms;
0 sorry.
-/
import Mathlib
import LatticeGauge.ActivityRestrictionColumnBounds

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## 51-E — CAPSTONE -/

/-- **CAPSTONE 51 — LOCAL EXPONENTIAL STABILITY UNDER REMOTE
    ACTIVITY SUPPRESSION**: the difference between the original
    expectation and the normalized activity-restricted functional
    of a local observable f (support s, bound Cf) decays like
    exp(−n/2) in the walk-barrier separation n of s from the
    suppressed region r, with the explicit local prefactor
    2·Cf·exp(8 D_s/113). Ledger (51-C) + triangle inequality +
    the two column bounds (51-D); the bridge prefactor is
    dominated by the allowed one. -/
theorem abs_gibbsExpectation_sub_activityRestrictedExpectation_le_local_exp_decay
    {β : ℝ} (hβ : 0 ≤ β)
    {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)}
    {f : Config N G → ℝ}
    (hf : DependsOnlyOn f s)
    (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf)
    (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n) :
    |gibbsExpectation (N := N) μm β χ f
        - activityRestrictedExpectation μm β χ f s r|
      ≤ 2 * Cf
        * Real.exp
            (8 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
        * Real.exp (-(n : ℝ) / 2) := by
  -- the two verified column bounds
  have hA := abs_activityAllowedColumn_sum_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf hsep
  have hB := abs_activityBridgeColumn_sum_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf hsep
  -- 5.1 — the bridge prefactor is dominated by the allowed one
  have hD : (0:ℝ) ≤ ((supportLinkFinset (N := N) s).card : ℝ) :=
    Nat.cast_nonneg _
  have hmono : Real.exp
      (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
      ≤ Real.exp
        (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  -- 5.2 — scaling by the common nonnegative factor
  have hpos : (0:ℝ) ≤ Real.exp (-(n : ℝ) / 2) * Cf :=
    mul_nonneg (Real.exp_pos _).le hCf0
  have hB' := le_trans hB (mul_le_mul_of_nonneg_left hmono hpos)
  -- 5.4 — the final constant, scalar only
  have hconst : 2 * Cf
      * Real.exp
          (8 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
      * Real.exp (-(n : ℝ) / 2)
      = 2 * (Real.exp (-(n : ℝ) / 2) * Cf
          * Real.exp
              (4 * ((supportLinkFinset (N := N) s).card : ℝ)
                * (2/113))) := by
    rw [show (8:ℝ) * ((supportLinkFinset (N := N) s).card : ℝ) / 113
        = 4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)
      from by ring]
    ring
  -- 5.3 — exact ledger, then the triangle inequality
  rw [gibbsExpectation_sub_activityRestrictedExpectation_eq_connector_bridge_ledger
      μm hβ mχ hχabs hsmall hf mf hCf r,
    hconst]
  refine le_trans (abs_add _ _) ?_
  linarith [hA, hB']

#print axioms abs_gibbsExpectation_sub_activityRestrictedExpectation_le_local_exp_decay

end LatticeGauge
