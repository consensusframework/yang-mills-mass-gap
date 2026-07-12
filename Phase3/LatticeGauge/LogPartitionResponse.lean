/-
LatticeGauge/LogPartitionResponse.lean — Phase 3, twenty-third stone.

FINITE-VOLUME LOG-PARTITION RESPONSE IDENTITY (architecture:
Sol/GPT-5.6; execution: Fable): d/dβ log Z_β = −⟨S⟩_β at every
β₀ ≥ 0, plus the pointwise sign of the response and a reusable
positivity lemma for Gibbs expectations. NAMING: this is the LOG
PARTITION FUNCTION, deliberately NOT called "free energy" (that would
involve a different convention, typically −β⁻¹·log Z). LIMITS: finite
periodic lattice; β₀ ≥ 0; exact pointwise identity; pointwise sign of
the derivative only — no global monotonicity claim; no convexity claim
yet; no uniformity in N; no cluster expansion; no thermodynamic-limit
claim. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.WilsonExpectation
import LatticeGauge.FiniteBetaResponse
import LatticeGauge.UnitaryChar
import LatticeGauge.HaarUnitary

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

section Measure

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]
variable {χ : G → ℝ}

/-- **A. The log partition function** log Z_β (NOT the free energy —
    no −β⁻¹ convention is adopted here). -/
noncomputable def logPartition [NeZero N] [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) : ℝ :=
  Real.log (realZ (N := N) μm β χ)

/-- **B. Positivity of the Gibbs expectation** of a nonnegative
    observable. The measurability and boundedness hypotheses are kept
    (underscored) for API uniformity with the response theorems. -/
theorem gibbsExpectation_nonneg [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β B C : ℝ} (hβ : 0 ≤ β)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f : Config N G → ℝ} (_mf : Measurable f)
    (hf0 : ∀ U, 0 ≤ f U) (_hfC : ∀ U, |f U| ≤ C) :
    0 ≤ gibbsExpectation (N := N) μm β χ f := by
  have hz : 0 < realZ (N := N) μm β χ :=
    realZ_pos (N := N) μm mχ hβ hχ hB
  have hnum : 0 ≤ ∫ U : Config N G, f U * gibbsWeight β χ U
      ∂(configMeasure μm N) :=
    integral_nonneg fun U =>
      mul_nonneg (hf0 U) (gibbsWeight_pos β χ U).le
  exact div_nonneg hnum hz.le

/-- **C. CAPSTONE (pedra 23): finite-volume log-partition response
    identity.** d/dβ log Z_β = −⟨S⟩_β at every β₀ ≥ 0. -/
theorem hasDerivAt_logPartition [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β₀ B : ℝ} (hβ₀ : 0 ≤ β₀)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B) :
    HasDerivAt (fun β : ℝ => logPartition (N := N) μm β χ)
      (-(gibbsExpectation (N := N) μm β₀ χ
          (fun U => wilsonAction χ U)))
      β₀ := by
  have hZ := hasDerivAt_realZ_at (N := N) μm mχ hβ₀ hχ hB
  have hz : 0 < realZ (N := N) μm β₀ χ :=
    realZ_pos (N := N) μm mχ hβ₀ hχ hB
  have hlog := hZ.log hz.ne'
  have h2 : HasDerivAt (fun β : ℝ => logPartition (N := N) μm β χ)
      ((-(∫ U : Config N G, wilsonAction χ U * gibbsWeight β₀ χ U
          ∂(configMeasure μm N))) / realZ (N := N) μm β₀ χ)
      β₀ := hlog
  have hval : (-(∫ U : Config N G,
        wilsonAction χ U * gibbsWeight β₀ χ U ∂(configMeasure μm N)))
        / realZ (N := N) μm β₀ χ
      = -(gibbsExpectation (N := N) μm β₀ χ
          (fun U => wilsonAction χ U)) := by
    show _ = -((∫ U : Config N G,
        wilsonAction χ U * gibbsWeight β₀ χ U ∂(configMeasure μm N))
        / realZ (N := N) μm β₀ χ)
    rw [neg_div]
  rw [← hval]
  exact h2

/-- **D. Pointwise sign of the response:** the derivative of log Z_β
    is ≤ 0 at every β₀ ≥ 0 (the action is nonnegative). Pointwise sign
    only — no global monotonicity is claimed. -/
theorem logPartition_derivative_nonpos [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β₀ B : ℝ} (hβ₀ : 0 ≤ β₀)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B) :
    deriv (fun β : ℝ => logPartition (N := N) μm β χ) β₀ ≤ 0 := by
  rw [(hasDerivAt_logPartition (N := N) μm mχ hβ₀ hχ hB).deriv]
  have hSabs : ∀ U : Config N G, |wilsonAction χ U| ≤ B := by
    intro U
    rw [abs_of_nonneg (wilsonAction_nonneg χ hχ U)]
    exact hB U
  have h0 := gibbsExpectation_nonneg (N := N) μm mχ hβ₀ hχ hB
    (measurable_wilsonAction mχ)
    (fun U => wilsonAction_nonneg χ hχ U) hSabs
  linarith

end Measure

/-- **E. UNCONDITIONAL on U(n) with Haar measure:** the log-partition
    response identity with only structural conditions — the action
    bound is produced internally. -/
theorem hasDerivAt_unitaryLogPartition (n : ℕ) [NeZero n]
    {N : ℕ} [NeZero N] [Fintype (Site N)] {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    HasDerivAt
      (fun β : ℝ => logPartition (N := N) (haarU n) β (uChar n))
      (-(gibbsExpectation (N := N) (haarU n) β₀ (uChar n)
          (fun U => wilsonAction (uChar n) U)))
      β₀ := by
  have hχ1 : ∀ g, uChar n g ≤ 1 :=
    fun g => (abs_le.mp (abs_uChar_le_one n g)).2
  have hχm1 : ∀ g, -1 ≤ uChar n g :=
    fun g => (abs_le.mp (abs_uChar_le_one n g)).1
  obtain ⟨B, hB⟩ := exists_wilsonAction_bound (N := N) hχm1
  exact hasDerivAt_logPartition (haarU n) (measurable_uChar n) hβ₀ hχ1 hB

end LatticeGauge
