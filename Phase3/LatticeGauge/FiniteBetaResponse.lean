/-
LatticeGauge/FiniteBetaResponse.lean — Phase 3, twentieth stone.

FLUCTUATION–RESPONSE IDENTITY IN FINITE VOLUME (architecture:
Sol/GPT-5.6; execution: Fable):
d/dβ ⟨f⟩_β = −Cov_β(f, S) at every β₀ ≥ 0 — the response of any
bounded observable to the coupling is governed exactly by its
correlation with the action, at any temperature. Generalizes stone 18
(kept as the pedagogical base case). LIMITS: finite periodic lattice;
β₀ ≥ 0; exact pointwise identity; no uniformity in N; no convergent
series; no cluster expansion; no thermodynamic-limit claim. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.Beta0
import LatticeGauge.BetaPerturbation
import LatticeGauge.LinearResponse

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

section Measure

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]
variable {χ : G → ℝ}

/-- **Gibbs covariance** — first-class citizen for the response
    identities and the cumulants ahead. -/
noncomputable def gibbsCovariance [NeZero N] [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) (f g : Config N G → ℝ) : ℝ :=
  gibbsExpectation (N := N) μm β χ (fun U => f U * g U)
    - gibbsExpectation (N := N) μm β χ f
      * gibbsExpectation (N := N) μm β χ g

/-- **A. Derivative of the weighted numerator at any β₀ ≥ 0.** -/
theorem hasDerivAt_weightedNumerator_at [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β₀ B C : ℝ} (hβ₀ : 0 ≤ β₀)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f : Config N G → ℝ} (mf : Measurable f) (hf : ∀ U, |f U| ≤ C) :
    HasDerivAt
      (fun β : ℝ => ∫ U : Config N G, f U * gibbsWeight β χ U
        ∂(configMeasure μm N))
      (-(∫ U : Config N G,
        (f U * wilsonAction χ U) * gibbsWeight β₀ χ U
        ∂(configMeasure μm N)))
      β₀ := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hf (trivialConfig N G))
  have hB0 : 0 ≤ B :=
    le_trans (wilsonAction_nonneg χ hχ (trivialConfig N G)) (hB _)
  set S : Config N G → ℝ := fun U => wilsonAction χ U with hS
  have mS : Measurable S := measurable_wilsonAction mχ
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun β (U : Config N G) => f U * gibbsWeight β χ U)
    (F' := fun β (U : Config N G) =>
      f U * (Real.exp (-β * S U) * -(S U)))
    (x₀ := β₀) (ε := 1) (μ := configMeasure μm N)
    (bound := fun _ => C * (B * Real.exp ((β₀ + 1) * B))) one_pos
    (Filter.Eventually.of_forall fun β =>
      (mf.mul (measurable_gibbsWeight mχ β)).aestronglyMeasurable)
    ?_ ?_ ?_ ?_ ?_
  · have hval : (∫ U : Config N G,
        f U * (Real.exp (-β₀ * S U) * -(S U)) ∂(configMeasure μm N))
        = -(∫ U : Config N G, (f U * S U) * gibbsWeight β₀ χ U
            ∂(configMeasure μm N)) := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
      show f U * (Real.exp (-β₀ * S U) * -(S U))
          = -((f U * S U) * gibbsWeight β₀ χ U)
      unfold gibbsWeight
      ring
    rw [hval] at h
    exact h.2
  · -- F(β₀) integrável: f·w_{β₀}, com w ≤ 1 pois β₀ ≥ 0
    refine ((integrable_const C).mono'
      ((mf.mul (measurable_gibbsWeight mχ β₀)).aestronglyMeasurable) ?_)
    filter_upwards with U
    calc ‖f U * gibbsWeight β₀ χ U‖
        = |f U| * gibbsWeight β₀ χ U := by
          rw [Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (gibbsWeight_pos β₀ χ U).le]
      _ ≤ C * 1 := by
          refine mul_le_mul (hf U) ?_ (gibbsWeight_pos β₀ χ U).le hC
          exact gibbsWeight_le_one hβ₀ hχ U
      _ = C := mul_one C
  · exact (mf.mul ((Real.measurable_exp.comp
      (mS.const_mul (-β₀))).mul mS.neg)).aestronglyMeasurable
  · -- dominação em ball β₀ 1
    filter_upwards with U
    intro b hb
    have hS0 := wilsonAction_nonneg χ hχ U
    have hSB := hB U
    have hbabs : |b| ≤ β₀ + 1 := by
      have h1 : |b - β₀| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using hb
      have := abs_sub_abs_le_abs_sub b β₀
      have hβ₀abs : |β₀| = β₀ := abs_of_nonneg hβ₀
      linarith [abs_abs_sub_abs_le_abs_sub b β₀]
    have hexp : Real.exp (-b * S U) ≤ Real.exp ((β₀ + 1) * B) := by
      apply Real.exp_le_exp.mpr
      have h1 : -b * S U ≤ |b| * S U := by
        nlinarith [neg_abs_le b, hS0]
      have h2 : |b| * S U ≤ (β₀ + 1) * B := by
        have := mul_le_mul hbabs hSB hS0 (by linarith : (0:ℝ) ≤ β₀ + 1)
        linarith
      linarith
    calc ‖f U * (Real.exp (-b * S U) * -(S U))‖
        = |f U| * (Real.exp (-b * S U) * S U) := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
            abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg hS0]
      _ ≤ C * (Real.exp ((β₀ + 1) * B) * B) := by
          refine mul_le_mul (hf U) ?_ ?_ hC
          · exact mul_le_mul hexp hSB hS0 (Real.exp_pos _).le
          · positivity
      _ = C * (B * Real.exp ((β₀ + 1) * B)) := by ring
  · exact integrable_const _
  · filter_upwards with U
    intro b _
    simpa [hS] using
      (hasDerivAt_gibbsWeight (N := N) (χ := χ) U b).const_mul (f U)

/-- **B. Derivative of the real partition function at any β₀ ≥ 0.** -/
theorem hasDerivAt_realZ_at [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β₀ B : ℝ} (hβ₀ : 0 ≤ β₀)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B) :
    HasDerivAt (fun β : ℝ => realZ (N := N) μm β χ)
      (-(∫ U : Config N G, wilsonAction χ U * gibbsWeight β₀ χ U
        ∂(configMeasure μm N)))
      β₀ := by
  have h := hasDerivAt_weightedNumerator_at (N := N) μm mχ hβ₀ hχ hB
    (f := fun _ : Config N G => (1 : ℝ)) (C := 1) measurable_const
    (fun _ => by norm_num)
  simp only [one_mul] at h
  exact h

/-- **C/D. CAPSTONE (pedra 20): fluctuation–response identity.**
    d/dβ ⟨f⟩_β = −Cov_β(f, S) at every β₀ ≥ 0. -/
theorem hasDerivAt_gibbsExpectation_at_covariance [NeZero N]
    [Fintype (Site N)]
    (mχ : Measurable χ) {β₀ B C : ℝ} (hβ₀ : 0 ≤ β₀)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f : Config N G → ℝ} (mf : Measurable f) (hf : ∀ U, |f U| ≤ C) :
    HasDerivAt (fun β : ℝ => gibbsExpectation (N := N) μm β χ f)
      (-(gibbsCovariance (N := N) μm β₀ χ f
          (fun U => wilsonAction χ U)))
      β₀ := by
  have hA := hasDerivAt_weightedNumerator_at (N := N) μm mχ hβ₀ hχ hB mf hf
  have hZ := hasDerivAt_realZ_at (N := N) μm mχ hβ₀ hχ hB
  have hz : 0 < realZ (N := N) μm β₀ χ :=
    realZ_pos (N := N) μm mχ hβ₀ hχ hB
  -- também a derivada do numerador de f, para o quociente:
  have hNum := hasDerivAt_weightedNumerator_at (N := N) μm mχ hβ₀ hχ hB mf hf
  have h := hNum.div hZ hz.ne'
  -- forma bruta preservada; reescrever só no fim
  set A : ℝ := ∫ U : Config N G,
    (f U * wilsonAction χ U) * gibbsWeight β₀ χ U
    ∂(configMeasure μm N) with hAdef
  set n : ℝ := ∫ U : Config N G, f U * gibbsWeight β₀ χ U
    ∂(configMeasure μm N) with hndef
  set s : ℝ := ∫ U : Config N G, wilsonAction χ U * gibbsWeight β₀ χ U
    ∂(configMeasure μm N) with hsdef
  set z : ℝ := realZ (N := N) μm β₀ χ with hzdef
  have hEfS : gibbsExpectation (N := N) μm β₀ χ
      (fun U => f U * wilsonAction χ U) = A / z := rfl
  have hEf : gibbsExpectation (N := N) μm β₀ χ f = n / z := rfl
  have hES : gibbsExpectation (N := N) μm β₀ χ
      (fun U => wilsonAction χ U) = s / z := by
    show (∫ U : Config N G,
        wilsonAction χ U * gibbsWeight β₀ χ U ∂(configMeasure μm N)) / z
        = s / z
    rw [hsdef]
  have hcov : gibbsCovariance (N := N) μm β₀ χ f
      (fun U => wilsonAction χ U) = A / z - (n / z) * (s / z) := by
    unfold gibbsCovariance
    rw [hEfS, hEf, hES]
  convert h using 1
  rw [hcov]
  field_simp
  ring

end Measure

end LatticeGauge
