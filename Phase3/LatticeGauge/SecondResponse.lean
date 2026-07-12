/-
LatticeGauge/SecondResponse.lean — Phase 3, twenty-first stone.

SECOND-RESPONSE / THIRD-CUMULANT IDENTITY IN FINITE VOLUME
(architecture: Sol/GPT-5.6; execution: Fable):
d/dβ [−Cov_β(f, S)] = κ_β(f, S, S), where
κ_β(f,S,S) = Cov_β(f, S²) − 2·⟨S⟩_β·Cov_β(f, S).
Together with stone 20 (d/dβ ⟨f⟩_β = −Cov_β(f,S)) this pair encodes
the second response of ⟨f⟩_β — built ENTIRELY on top of stone 20's
API, applied three times (to f·S, f and S), never touching the
integration/differentiation engine again. NOT an `iteratedDeriv`
theorem: no formal second-derivative wrapper is claimed.
LIMITS: finite volume; β₀ ≥ 0; pointwise third-cumulant identity;
no uniformity in N; no convergent series; no cluster expansion;
no thermodynamic-limit claim. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.FiniteBetaResponse

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

section Measure

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]
variable {χ : G → ℝ}

/-- **Third joint cumulant with the action, κ_β(f,S,S)** =
    Cov_β(f, S²) − 2·⟨S⟩_β·Cov_β(f, S). -/
noncomputable def gibbsActionThirdCumulant [NeZero N] [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ) : ℝ :=
  gibbsCovariance (N := N) μm β χ f
      (fun U => wilsonAction χ U * wilsonAction χ U)
    - 2
      * gibbsExpectation (N := N) μm β χ (fun U => wilsonAction χ U)
      * gibbsCovariance (N := N) μm β χ f (fun U => wilsonAction χ U)

/-- **A. Derivative of the Gibbs covariance with the action.**
    d/dβ Cov_β(f, S) = −κ_β(f, S, S) at every β₀ ≥ 0.
    Proof: stone 20 applied to f·S, f and S; combined by
    HasDerivAt.sub / HasDerivAt.mul; one algebraic identity at the end. -/
theorem hasDerivAt_gibbsCovariance_action [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β₀ B C : ℝ} (hβ₀ : 0 ≤ β₀)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f : Config N G → ℝ} (mf : Measurable f) (hf : ∀ U, |f U| ≤ C) :
    HasDerivAt
      (fun β : ℝ => gibbsCovariance (N := N) μm β χ f
        (fun U => wilsonAction χ U))
      (-(gibbsActionThirdCumulant (N := N) μm β₀ χ f))
      β₀ := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hf (trivialConfig N G))
  have mS : Measurable (fun U : Config N G => wilsonAction χ U) :=
    measurable_wilsonAction mχ
  have hSabs : ∀ U : Config N G, |wilsonAction χ U| ≤ B := by
    intro U
    rw [abs_of_nonneg (wilsonAction_nonneg χ hχ U)]
    exact hB U
  have hfSabs : ∀ U : Config N G, |f U * wilsonAction χ U| ≤ C * B := by
    intro U
    rw [abs_mul]
    exact mul_le_mul (hf U) (hSabs U) (abs_nonneg _) hC
  -- pedra 20, três vezes: em f·S, em f e em S
  have hFS := hasDerivAt_gibbsExpectation_at_covariance (N := N) μm mχ
    hβ₀ hχ hB (mf.mul mS) hfSabs
  have hF := hasDerivAt_gibbsExpectation_at_covariance (N := N) μm mχ
    hβ₀ hχ hB mf hf
  have hS := hasDerivAt_gibbsExpectation_at_covariance (N := N) μm mχ
    hβ₀ hχ hB mS hSabs
  have h := hFS.sub (hF.mul hS)
  -- a função β ↦ Cov_β(f,S) É (defeq) a diferença E[fS] − E[f]·E[S]
  have h2 : HasDerivAt
      (fun β : ℝ => gibbsCovariance (N := N) μm β χ f
        (fun U => wilsonAction χ U))
      (-(gibbsCovariance (N := N) μm β₀ χ
          (fun U => f U * wilsonAction χ U)
          (fun U => wilsonAction χ U))
        - (-(gibbsCovariance (N := N) μm β₀ χ f
              (fun U => wilsonAction χ U))
            * gibbsExpectation (N := N) μm β₀ χ
              (fun U => wilsonAction χ U)
          + gibbsExpectation (N := N) μm β₀ χ f
            * -(gibbsCovariance (N := N) μm β₀ χ
                (fun U => wilsonAction χ U)
                (fun U => wilsonAction χ U))))
      β₀ := h
  -- identidade algébrica, aberta UMA única vez
  have hval : -(gibbsActionThirdCumulant (N := N) μm β₀ χ f)
      = -(gibbsCovariance (N := N) μm β₀ χ
          (fun U => f U * wilsonAction χ U)
          (fun U => wilsonAction χ U))
        - (-(gibbsCovariance (N := N) μm β₀ χ f
              (fun U => wilsonAction χ U))
            * gibbsExpectation (N := N) μm β₀ χ
              (fun U => wilsonAction χ U)
          + gibbsExpectation (N := N) μm β₀ χ f
            * -(gibbsCovariance (N := N) μm β₀ χ
                (fun U => wilsonAction χ U)
                (fun U => wilsonAction χ U))) := by
    unfold gibbsActionThirdCumulant gibbsCovariance
    simp only [mul_assoc]
    ring
  rw [hval]
  exact h2

/-- **B. CAPSTONE (pedra 21): second-response identity.**
    d/dβ [−Cov_β(f, S)] = κ_β(f, S, S) at every β₀ ≥ 0.
    Combined with stone 20, the pair reads:
    d/dβ ⟨f⟩_β = −Cov_β(f,S)  and  d/dβ [−Cov_β(f,S)] = κ_β(f,S,S). -/
theorem hasDerivAt_negative_gibbsCovariance_action [NeZero N]
    [Fintype (Site N)]
    (mχ : Measurable χ) {β₀ B C : ℝ} (hβ₀ : 0 ≤ β₀)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f : Config N G → ℝ} (mf : Measurable f) (hf : ∀ U, |f U| ≤ C) :
    HasDerivAt
      (fun β : ℝ => -(gibbsCovariance (N := N) μm β χ f
        (fun U => wilsonAction χ U)))
      (gibbsActionThirdCumulant (N := N) μm β₀ χ f)
      β₀ := by
  have h := (hasDerivAt_gibbsCovariance_action (N := N) μm mχ
    hβ₀ hχ hB mf hf).neg
  simpa using h

end Measure

end LatticeGauge
