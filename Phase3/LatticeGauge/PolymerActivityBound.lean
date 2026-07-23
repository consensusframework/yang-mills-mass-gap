/-
LatticeGauge/PolymerActivityBound.lean — Phase 3, forty-fourth stone.

THE EXPONENTIAL BOUND ON A SINGLE POLYMER ACTIVITY
(architecture: Sol/GPT-5.6; execution: Fable). Purely analytic stone:
for β ≥ 0 and ANY finite plaquette set C,
    |polymerWeight β χ C| ≤ (2β)^|C| —
the stone-32 LOCAL bound |plaquetteActivity| ≤ 2β pushed through the
product (stone 34 blockActivity) and the β = 0 probability state
(stones 11/35): triangle inequality for the integral, pointwise
monotonicity, and the integral of a constant under a probability
measure — NO independence between the plaquettes of C is used
anywhere (they may share links freely).

UNIFORMITY, stated precisely: this bound is independent of the total
lattice volume; it depends only on β and on the number of plaquettes
of C. It provides NO decay in distance or diameter, does NOT sum over
polymers, does NOT establish convergence of any cluster series, does
NOT establish a Kotecký–Preiss criterion, and implies NOTHING about
clustering or a mass gap. "Uniform in the volume" refers to THIS
local bound only, not to any full expansion. The geometric predicate
IsPlaquettePolymer is NOT required for the analytic bound (the lemma
holds for arbitrary blocks); the polymer version is a documented
corollary. The empty set (not a polymer; algebraic unit) saturates
the bound: |w(∅)| = 1 = (2β)^0. At β = 0 every nonempty block has
weight exactly 0. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.Beta0
import LatticeGauge.PlaquetteActivity
import LatticeGauge.PlaquetteConnectivity
import LatticeGauge.ComponentFactorization
import LatticeGauge.PolymerGeometry

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ}
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## 2. Pointwise bound on the block (no independence) -/

/-- **Pointwise product bound**: |blockActivity C U| ≤ (2β)^|C| for
    every configuration — plaquettes inside C may share links; only
    the stone-32 local bound and |·| of a product are used. -/
theorem abs_blockActivity_le [NeZero N]
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (hχabs : ∀ g : G, |χ g| ≤ 1)
    (C : Finset (Site N × Dir × Dir)) (U : Config N G) :
    |blockActivity β χ C U| ≤ (2 * β) ^ C.card := by
  unfold blockActivity
  rw [Finset.abs_prod]
  calc ∏ p ∈ C, |plaquetteActivity β χ U p|
      ≤ ∏ _p ∈ C, (2 * β) :=
        Finset.prod_le_prod (fun p _ => abs_nonneg _)
          (fun p _ => abs_plaquetteActivity_le hβ hχabs U p)
    _ = (2 * β) ^ C.card := Finset.prod_const _

/-! ## 3. Nonnegativity of the majorant -/

theorem twoBeta_pow_nonneg {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) :
    0 ≤ (2 * β) ^ k :=
  pow_nonneg (by linarith) k

/-! ## 4-5 support: integrability of the absolute block -/

theorem integrable_abs_blockActivity [NeZero N]
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (C : Finset (Site N × Dir × Dir)) :
    Integrable (fun U : Config N G => |blockActivity β χ C U|)
      (configMeasure μm N) := by
  refine (integrable_const ((2 * β) ^ C.card)).mono'
    ((measurable_blockActivity β mχ C).abs.aestronglyMeasurable) ?_
  filter_upwards with U
  rw [Real.norm_of_nonneg (abs_nonneg _)]
  exact abs_blockActivity_le hβ hχabs C U

/-! ## 6. THE CAPSTONE -/

/-- **THE EXPONENTIAL ACTIVITY BOUND**: |w_β(C)| ≤ (2β)^|C| for β ≥ 0
    and ANY Finset C (the geometric polymer predicate is deliberately
    NOT required — the proof uses only cardinality and the local
    product). Independent of the lattice volume; no independence
    inside C; no decay, no sums over polymers, no convergence, no
    Kotecký–Preiss, no clustering, no mass gap. -/
theorem polymerWeight_abs_le [NeZero N] [Fintype (Site N)]
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (C : Finset (Site N × Dir × Dir)) :
    |polymerWeight (N := N) μm β χ C| ≤ (2 * β) ^ C.card := by
  unfold polymerWeight
  rw [gibbsExpectation_zero (N := N) μm χ]
  have h1 : ‖∫ U : Config N G, blockActivity β χ C U
        ∂(configMeasure μm N)‖
      ≤ ∫ U : Config N G, ‖blockActivity β χ C U‖
        ∂(configMeasure μm N) :=
    norm_integral_le_integral_norm _
  simp only [Real.norm_eq_abs] at h1
  have h2 : (∫ U : Config N G, |blockActivity β χ C U|
        ∂(configMeasure μm N))
      ≤ ∫ _U : Config N G, (2 * β) ^ C.card
        ∂(configMeasure μm N) :=
    integral_mono (integrable_abs_blockActivity μm hβ mχ hχabs C)
      (integrable_const _)
      (fun U => abs_blockActivity_le hβ hχabs C U)
  have h3 : (∫ _U : Config N G, (2 * β) ^ C.card
        ∂(configMeasure μm N))
      = (2 * β) ^ C.card := by
    rw [integral_const, measure_univ, ENNReal.one_toReal, one_smul]
  calc |∫ U : Config N G, blockActivity β χ C U
        ∂(configMeasure μm N)|
      ≤ ∫ U : Config N G, |blockActivity β χ C U|
        ∂(configMeasure μm N) := h1
    _ ≤ ∫ _U : Config N G, (2 * β) ^ C.card
        ∂(configMeasure μm N) := h2
    _ = (2 * β) ^ C.card := h3

/-! ## 7. The documented polymer specialization -/

/-- The bound specialized to genuine polymers (interpretation for the
    future sums; the predicate is a hypothesis, never part of the
    weight's type). -/
theorem polymerWeight_abs_le_of_isPlaquettePolymer
    [NeZero N] [Fintype (Site N)]
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    {C : Finset (Site N × Dir × Dir)} (_hC : IsPlaquettePolymer C) :
    |polymerWeight (N := N) μm β χ C| ≤ (2 * β) ^ C.card :=
  polymerWeight_abs_le μm hβ mχ hχabs C

/-! ## 8. The empty block saturates the bound -/

/-- The empty set is NOT a polymer, but appears as algebraic unit:
    |w(∅)| = 1 = (2β)^0 — the bound holds with EQUALITY. -/
theorem polymerWeight_abs_empty [NeZero N] [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) :
    |polymerWeight (N := N) μm β χ (∅ : Finset (Site N × Dir × Dir))|
      = (2 * β) ^ (0 : ℕ) := by
  rw [polymerWeight_empty, pow_zero]
  exact abs_one

/-! ## 9. β = 0: nonempty blocks have weight exactly zero -/

theorem polymerWeight_zero_of_nonempty [NeZero N] [Fintype (Site N)]
    {χ : G → ℝ} (mχ : Measurable χ) (hχabs : ∀ g : G, |χ g| ≤ 1)
    {C : Finset (Site N × Dir × Dir)} (hC : C.Nonempty) :
    polymerWeight (N := N) μm 0 χ C = 0 := by
  have h := polymerWeight_abs_le (N := N) μm le_rfl mχ hχabs C
  rw [mul_zero, zero_pow (Finset.card_pos.mpr hC).ne'] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- Sanity: every genuine polymer is nonempty, hence has zero weight
    at β = 0. -/
theorem polymerWeight_zero_of_isPlaquettePolymer
    [NeZero N] [Fintype (Site N)]
    {χ : G → ℝ} (mχ : Measurable χ) (hχabs : ∀ g : G, |χ g| ≤ 1)
    {C : Finset (Site N × Dir × Dir)} (hC : IsPlaquettePolymer C) :
    polymerWeight (N := N) μm 0 χ C = 0 :=
  polymerWeight_zero_of_nonempty μm mχ hχabs hC.1

/-! ## 10. Small β: the weight never exceeds 1 -/

/-- For 0 ≤ β ≤ 1/2 every block weight has absolute value ≤ 1. NOT a
    convergence statement. -/
theorem polymerWeight_abs_le_one [NeZero N] [Fintype (Site N)]
    {β : ℝ} (hβ : 0 ≤ β) (hβ2 : β ≤ 1 / 2)
    {χ : G → ℝ} (mχ : Measurable χ) (hχabs : ∀ g : G, |χ g| ≤ 1)
    (C : Finset (Site N × Dir × Dir)) :
    |polymerWeight (N := N) μm β χ C| ≤ 1 := by
  refine (polymerWeight_abs_le μm hβ mχ hχabs C).trans ?_
  have h := pow_le_pow_left (by linarith : (0:ℝ) ≤ 2 * β)
    (by linarith : 2 * β ≤ 1) C.card
  rwa [one_pow] at h

end LatticeGauge
