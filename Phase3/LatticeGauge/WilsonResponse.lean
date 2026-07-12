/-
LatticeGauge/WilsonResponse.lean — Phase 3, twenty-second stone.

FIRST- AND SECOND-RESPONSE IDENTITIES FOR WILSON OBSERVABLES
(architecture: Sol/GPT-5.6; execution: Fable): stones 20 and 21
specialized to the physical observable W = χ(holonomy), with the
auxiliary action bound B chosen INSIDE the proofs — the public
signatures expose only measurability of χ, |χ| ≤ 1, β₀ ≥ 0 and the
path. Two API levels: `wilsonPath…` (any path) and `wilsonLoop…`
(with IsClosed, certifying the gauge-invariant physical loop).
Concrete U(n)/Haar corollaries carry only structural conditions.
LIMITS: finite periodic lattice; exact pointwise response identities;
closed path for the physical wrappers; no area law; no confinement
claim; no uniformity in N; no cluster expansion; no
thermodynamic-limit claim; no formal iteratedDeriv theorem. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.WilsonLoop
import LatticeGauge.WilsonExpectation
import LatticeGauge.FiniteBetaResponse
import LatticeGauge.SecondResponse
import LatticeGauge.UnitaryChar
import LatticeGauge.HaarUnitary

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

section Measure

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]
variable {χ : G → ℝ}

/-- **A. FIRST RESPONSE OF A WILSON PATH.** For any path (open or
    closed): d/dβ ⟨W_p⟩_β = −Cov_β(W_p, S) at every β₀ ≥ 0. The action
    bound B is produced internally from |χ| ≤ 1. -/
theorem hasDerivAt_wilsonPathExpectation [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (x : Site N) (p : List Step) :
    HasDerivAt
      (fun β : ℝ => gibbsExpectation (N := N) μm β χ
        (fun U => wilsonLoop χ U x p))
      (-(gibbsCovariance (N := N) μm β₀ χ
          (fun U => wilsonLoop χ U x p)
          (fun U => wilsonAction χ U)))
      β₀ := by
  have hχ1 : ∀ g : G, χ g ≤ 1 := fun g => (abs_le.mp (hχabs g)).2
  have hχm1 : ∀ g : G, -1 ≤ χ g := fun g => (abs_le.mp (hχabs g)).1
  obtain ⟨B, hB⟩ := exists_wilsonAction_bound (N := N) hχm1
  exact hasDerivAt_gibbsExpectation_at_covariance (N := N) μm mχ hβ₀
    hχ1 hB (measurable_wilsonLoop mχ x p) (fun U => hχabs _)

/-- **B. FIRST-RESPONSE IDENTITY FOR CLOSED WILSON LOOPS.** The
    closedness hypothesis certifies that the observable is the
    gauge-invariant physical loop; the differentiation itself does not
    use it. -/
theorem hasDerivAt_wilsonLoopExpectation [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (x : Site N) (p : List Step) (_hp : IsClosed x p) :
    HasDerivAt
      (fun β : ℝ => gibbsExpectation (N := N) μm β χ
        (fun U => wilsonLoop χ U x p))
      (-(gibbsCovariance (N := N) μm β₀ χ
          (fun U => wilsonLoop χ U x p)
          (fun U => wilsonAction χ U)))
      β₀ :=
  hasDerivAt_wilsonPathExpectation μm mχ hβ₀ hχabs x p

/-- **C. SECOND RESPONSE OF A WILSON PATH.**
    d/dβ [−Cov_β(W_p, S)] = κ_β(W_p, S, S) at every β₀ ≥ 0. -/
theorem hasDerivAt_negative_wilsonPathCovariance [NeZero N]
    [Fintype (Site N)]
    (mχ : Measurable χ) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (x : Site N) (p : List Step) :
    HasDerivAt
      (fun β : ℝ => -(gibbsCovariance (N := N) μm β χ
        (fun U => wilsonLoop χ U x p)
        (fun U => wilsonAction χ U)))
      (gibbsActionThirdCumulant (N := N) μm β₀ χ
        (fun U => wilsonLoop χ U x p))
      β₀ := by
  have hχ1 : ∀ g : G, χ g ≤ 1 := fun g => (abs_le.mp (hχabs g)).2
  have hχm1 : ∀ g : G, -1 ≤ χ g := fun g => (abs_le.mp (hχabs g)).1
  obtain ⟨B, hB⟩ := exists_wilsonAction_bound (N := N) hχm1
  exact hasDerivAt_negative_gibbsCovariance_action (N := N) μm mχ hβ₀
    hχ1 hB (measurable_wilsonLoop mχ x p) (fun U => hχabs _)

/-- **D. SECOND-RESPONSE IDENTITY FOR CLOSED WILSON LOOPS.** -/
theorem hasDerivAt_negative_wilsonLoopCovariance [NeZero N]
    [Fintype (Site N)]
    (mχ : Measurable χ) {β₀ : ℝ} (hβ₀ : 0 ≤ β₀)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (x : Site N) (p : List Step) (_hp : IsClosed x p) :
    HasDerivAt
      (fun β : ℝ => -(gibbsCovariance (N := N) μm β χ
        (fun U => wilsonLoop χ U x p)
        (fun U => wilsonAction χ U)))
      (gibbsActionThirdCumulant (N := N) μm β₀ χ
        (fun U => wilsonLoop χ U x p))
      β₀ :=
  hasDerivAt_negative_wilsonPathCovariance μm mχ hβ₀ hχabs x p

end Measure

/-! ## Concrete corollaries on U(n) with Haar measure -/

/-- **E1. UNCONDITIONAL on U(n): first-response identity for closed
    Wilson loops** — only structural conditions remain: NeZero N,
    NeZero n, β₀ ≥ 0, closed path. -/
theorem hasDerivAt_unitaryWilsonLoopExpectation
    (n : ℕ) [NeZero n] {N : ℕ} [NeZero N] [Fintype (Site N)]
    {β₀ : ℝ} (hβ₀ : 0 ≤ β₀)
    (x : Site N) (p : List Step) (_hp : IsClosed x p) :
    HasDerivAt
      (fun β : ℝ => gibbsExpectation (N := N) (haarU n) β (uChar n)
        (fun U => wilsonLoop (uChar n) U x p))
      (-(gibbsCovariance (N := N) (haarU n) β₀ (uChar n)
          (fun U => wilsonLoop (uChar n) U x p)
          (fun U => wilsonAction (uChar n) U)))
      β₀ :=
  hasDerivAt_wilsonPathExpectation (haarU n) (measurable_uChar n) hβ₀
    (abs_uChar_le_one n) x p

/-- **E2. UNCONDITIONAL on U(n): second-response identity for closed
    Wilson loops.** -/
theorem hasDerivAt_negative_unitaryWilsonLoopCovariance
    (n : ℕ) [NeZero n] {N : ℕ} [NeZero N] [Fintype (Site N)]
    {β₀ : ℝ} (hβ₀ : 0 ≤ β₀)
    (x : Site N) (p : List Step) (_hp : IsClosed x p) :
    HasDerivAt
      (fun β : ℝ => -(gibbsCovariance (N := N) (haarU n) β (uChar n)
        (fun U => wilsonLoop (uChar n) U x p)
        (fun U => wilsonAction (uChar n) U)))
      (gibbsActionThirdCumulant (N := N) (haarU n) β₀ (uChar n)
        (fun U => wilsonLoop (uChar n) U x p))
      β₀ :=
  hasDerivAt_negative_wilsonPathCovariance (haarU n) (measurable_uChar n)
    hβ₀ (abs_uChar_le_one n) x p

end LatticeGauge
