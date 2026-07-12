/-
LatticeGauge/GibbsVariance.lean — Phase 3, twenty-fourth stone.

GIBBS VARIANCE POSITIVITY AND ACTION-FLUCTUATION RESPONSE
(architecture: Sol/GPT-5.6, pre-authorized after stone 23; execution:
Fable): Var_β(f) = Cov_β(f,f) ≥ 0 via the CENTERED-SQUARE route (no
abstract Cauchy–Schwarz), and d/dβ[−⟨S⟩_β] = Var_β(S) ≥ 0 — the first
genuine fluctuation inequality of the repository. Stones 23 and 24
provide the response pair and its sign; NO formal Lean wrapper of
second derivative or convexity of log Z is claimed. LIMITS: finite
periodic lattice; β ≥ 0; pointwise identities and signs; no
uniformity in N; no cluster expansion; no thermodynamic-limit claim.
NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.WilsonExpectation
import LatticeGauge.FiniteBetaResponse
import LatticeGauge.LogPartitionResponse
import LatticeGauge.UnitaryChar
import LatticeGauge.HaarUnitary

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

section Measure

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]
variable {χ : G → ℝ}

/-- **A. The Gibbs variance** Var_β(f) = Cov_β(f, f). -/
noncomputable def gibbsVariance [NeZero N] [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ) : ℝ :=
  gibbsCovariance (N := N) μm β χ f f

/-- **B. NONNEGATIVITY OF THE GIBBS VARIANCE** for a bounded measurable
    observable, by the centered-square route:
    Var_β(f) = ⟨(f − ⟨f⟩)²⟩_β ≥ 0. -/
theorem gibbsVariance_nonneg [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β B C : ℝ} (hβ : 0 ≤ β)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f : Config N G → ℝ} (mf : Measurable f) (hf : ∀ U, |f U| ≤ C) :
    0 ≤ gibbsVariance (N := N) μm β χ f := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hf (trivialConfig N G))
  have hz : 0 < realZ (N := N) μm β χ :=
    realZ_pos (N := N) μm mχ hβ hχ hB
  have hzne := hz.ne'
  set m : ℝ := gibbsExpectation (N := N) μm β χ f with hm
  have hmabs : |m| ≤ C := abs_gibbsExpectation_le μm mχ hβ hχ hB mf hf
  have hbound : ∀ U : Config N G, |f U - m| ≤ C + C := by
    intro U
    rw [sub_eq_add_neg]
    refine (abs_add _ _).trans ?_
    rw [abs_neg]
    exact add_le_add (hf U) hmabs
  -- integrabilidade genérica: (limitada) · peso
  have hint : ∀ (g : Config N G → ℝ), Measurable g → ∀ K : ℝ,
      (∀ U, |g U| ≤ K) →
      Integrable (fun U : Config N G => g U * gibbsWeight β χ U)
        (configMeasure μm N) := by
    intro g mg K hK
    refine (integrable_const K).mono'
      ((mg.mul (measurable_gibbsWeight mχ β)).aestronglyMeasurable) ?_
    filter_upwards with U
    calc ‖g U * gibbsWeight β χ U‖
        = |g U| * gibbsWeight β χ U := by
          rw [Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (gibbsWeight_pos β χ U).le]
      _ ≤ K * 1 := mul_le_mul (hK U) (gibbsWeight_le_one hβ hχ U)
            (gibbsWeight_pos β χ U).le
            (le_trans (abs_nonneg _) (hK U))
      _ = K := mul_one K
  have hff := hint (fun U => f U * f U) (mf.mul mf) (C * C)
    (fun U => by
      rw [abs_mul]
      exact mul_le_mul (hf U) (hf U) (abs_nonneg _) hC)
  have hfw := hint f mf C hf
  have hw := hint (fun _ => (1 : ℝ)) measurable_const 1 (fun U => by norm_num)
  simp only [one_mul] at hw
  -- a expectativa do quadrado centrado é ≥ 0 (API da 23ª)
  have hsq0 : 0 ≤ gibbsExpectation (N := N) μm β χ
      (fun U => (f U - m) * (f U - m)) :=
    gibbsExpectation_nonneg (N := N) μm mχ hβ hχ hB
      ((mf.sub measurable_const).mul (mf.sub measurable_const))
      (fun U => mul_self_nonneg _)
      (fun U => by
        rw [abs_mul]
        exact mul_le_mul (hbound U) (hbound U) (abs_nonneg _)
          (by linarith))
  -- expansão do numerador
  have hnum : (∫ U : Config N G, ((f U - m) * (f U - m)) * gibbsWeight β χ U
        ∂(configMeasure μm N))
      = (∫ U : Config N G, (f U * f U) * gibbsWeight β χ U
          ∂(configMeasure μm N))
        - (2 * m) * (∫ U : Config N G, f U * gibbsWeight β χ U
            ∂(configMeasure μm N))
        + (m * m) * realZ (N := N) μm β χ := by
    unfold realZ
    have h1 : Integrable (fun U : Config N G =>
        (f U * f U) * gibbsWeight β χ U
          - (2 * m) * (f U * gibbsWeight β χ U)) (configMeasure μm N) :=
      hff.sub (hfw.const_mul (2 * m))
    have h2 : Integrable (fun U : Config N G =>
        (m * m) * gibbsWeight β χ U) (configMeasure μm N) :=
      hw.const_mul (m * m)
    have hstep : (∫ U : Config N G,
          ((f U - m) * (f U - m)) * gibbsWeight β χ U ∂(configMeasure μm N))
        = ∫ U : Config N G,
            (((f U * f U) * gibbsWeight β χ U
              - (2 * m) * (f U * gibbsWeight β χ U))
              + (m * m) * gibbsWeight β χ U) ∂(configMeasure μm N) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
      show ((f U - m) * (f U - m)) * gibbsWeight β χ U
          = ((f U * f U) * gibbsWeight β χ U
            - (2 * m) * (f U * gibbsWeight β χ U))
            + (m * m) * gibbsWeight β χ U
      ring
    rw [hstep, integral_add h1 h2,
      integral_sub hff (hfw.const_mul (2 * m)),
      integral_mul_left, integral_mul_left]
  -- identidade: ⟨(f−m)²⟩ = Var(f)
  have hEq : gibbsExpectation (N := N) μm β χ
      (fun U => (f U - m) * (f U - m))
      = gibbsVariance (N := N) μm β χ f := by
    have hmval : m = (∫ U : Config N G, f U * gibbsWeight β χ U
        ∂(configMeasure μm N)) / realZ (N := N) μm β χ := rfl
    show (∫ U : Config N G, ((f U - m) * (f U - m)) * gibbsWeight β χ U
        ∂(configMeasure μm N)) / realZ (N := N) μm β χ = _
    rw [hnum]
    show _ = (∫ U : Config N G, (f U * f U) * gibbsWeight β χ U
        ∂(configMeasure μm N)) / realZ (N := N) μm β χ
      - ((∫ U : Config N G, f U * gibbsWeight β χ U
          ∂(configMeasure μm N)) / realZ (N := N) μm β χ)
        * ((∫ U : Config N G, f U * gibbsWeight β χ U
            ∂(configMeasure μm N)) / realZ (N := N) μm β χ)
    rw [hmval]
    field_simp
    ring
  rw [← hEq]
  exact hsq0

/-- **C. Nonnegativity of the action variance.** -/
theorem gibbsActionVariance_nonneg [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β B : ℝ} (hβ : 0 ≤ β)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B) :
    0 ≤ gibbsVariance (N := N) μm β χ
      (fun U => wilsonAction χ U) := by
  have hSabs : ∀ U : Config N G, |wilsonAction χ U| ≤ B := by
    intro U
    rw [abs_of_nonneg (wilsonAction_nonneg χ hχ U)]
    exact hB U
  exact gibbsVariance_nonneg (N := N) μm mχ hβ hχ hB
    (measurable_wilsonAction mχ) hSabs

/-- **D. ACTION-FLUCTUATION RESPONSE (pedra 24, capstone):**
    d/dβ [−⟨S⟩_β] = Var_β(S) at every β₀ ≥ 0 — stone 20 with f := S. -/
theorem hasDerivAt_negative_actionExpectation [NeZero N]
    [Fintype (Site N)]
    (mχ : Measurable χ) {β₀ B : ℝ} (hβ₀ : 0 ≤ β₀)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B) :
    HasDerivAt
      (fun β : ℝ => -(gibbsExpectation (N := N) μm β χ
        (fun U => wilsonAction χ U)))
      (gibbsVariance (N := N) μm β₀ χ (fun U => wilsonAction χ U))
      β₀ := by
  have hSabs : ∀ U : Config N G, |wilsonAction χ U| ≤ B := by
    intro U
    rw [abs_of_nonneg (wilsonAction_nonneg χ hχ U)]
    exact hB U
  have h := (hasDerivAt_gibbsExpectation_at_covariance (N := N) μm mχ
    hβ₀ hχ hB (measurable_wilsonAction mχ) hSabs).neg
  simpa [gibbsVariance] using h

/-- **E. The derived response value is nonnegative** — the pointwise
    sign of the pair (23, 24). No formal convexity of log Z is claimed. -/
theorem negative_actionExpectation_derivative_nonneg [NeZero N]
    [Fintype (Site N)]
    (mχ : Measurable χ) {β₀ B : ℝ} (hβ₀ : 0 ≤ β₀)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B) :
    0 ≤ deriv (fun β : ℝ => -(gibbsExpectation (N := N) μm β χ
      (fun U => wilsonAction χ U))) β₀ := by
  rw [(hasDerivAt_negative_actionExpectation (N := N) μm mχ
    hβ₀ hχ hB).deriv]
  exact gibbsActionVariance_nonneg (N := N) μm mχ hβ₀ hχ hB

end Measure

/-! ## Concrete corollaries on U(n) with Haar measure -/

/-- **F1. UNCONDITIONAL on U(n): nonnegative action variance** — only
    structural conditions remain. -/
theorem unitaryActionVariance_nonneg (n : ℕ) [NeZero n]
    {N : ℕ} [NeZero N] [Fintype (Site N)] {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ gibbsVariance (N := N) (haarU n) β (uChar n)
      (fun U => wilsonAction (uChar n) U) := by
  have hχ1 : ∀ g, uChar n g ≤ 1 :=
    fun g => (abs_le.mp (abs_uChar_le_one n g)).2
  have hχm1 : ∀ g, -1 ≤ uChar n g :=
    fun g => (abs_le.mp (abs_uChar_le_one n g)).1
  obtain ⟨B, hB⟩ := exists_wilsonAction_bound (N := N) hχm1
  exact gibbsActionVariance_nonneg (haarU n) (measurable_uChar n) hβ hχ1 hB

/-- **F2. UNCONDITIONAL on U(n): action-fluctuation response.** -/
theorem hasDerivAt_negative_unitaryActionExpectation (n : ℕ) [NeZero n]
    {N : ℕ} [NeZero N] [Fintype (Site N)] {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) :
    HasDerivAt
      (fun β : ℝ => -(gibbsExpectation (N := N) (haarU n) β (uChar n)
        (fun U => wilsonAction (uChar n) U)))
      (gibbsVariance (N := N) (haarU n) β₀ (uChar n)
        (fun U => wilsonAction (uChar n) U))
      β₀ := by
  have hχ1 : ∀ g, uChar n g ≤ 1 :=
    fun g => (abs_le.mp (abs_uChar_le_one n g)).2
  have hχm1 : ∀ g, -1 ≤ uChar n g :=
    fun g => (abs_le.mp (abs_uChar_le_one n g)).1
  obtain ⟨B, hB⟩ := exists_wilsonAction_bound (N := N) hχm1
  exact hasDerivAt_negative_actionExpectation (haarU n)
    (measurable_uChar n) hβ₀ hχ1 hB

end LatticeGauge
