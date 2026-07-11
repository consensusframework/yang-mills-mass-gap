/-
LatticeGauge/LinearResponse.lean — Phase 3, eighteenth stone.

LINEAR RESPONSE AT β = 0 (architecture: Sol/GPT-5.6; execution: Fable):
d/dβ ⟨f⟩_β |₀ = −(⟨f·S⟩₀ − ⟨f⟩₀·⟨S⟩₀) = −Cov₀(f, S).
The first explicit bridge between the β-perturbation and a correlation
computed in the product state — the doorway of the strong-coupling
expansion. LIMITS: finite volume; derivative AT β = 0 (not a convergent
series); no uniformity in N; not a cluster expansion. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.Beta0
import LatticeGauge.BetaPerturbation

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

section Measure

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]
variable {χ : G → ℝ}

/-- Pointwise derivative of the weight (bilateral, all β ∈ ℝ). -/
theorem hasDerivAt_gibbsWeight [NeZero N] [Fintype (Site N)]
    (U : Config N G) (β : ℝ) :
    HasDerivAt (fun b : ℝ => gibbsWeight b χ U)
      (Real.exp (-β * wilsonAction χ U) * -(wilsonAction χ U)) β := by
  have hlin : HasDerivAt (fun b : ℝ => -b * wilsonAction χ U)
      (-(wilsonAction χ U)) β := by
    simpa using ((hasDerivAt_id β).neg.mul_const (wilsonAction χ U))
  simpa [gibbsWeight] using hlin.exp

/-- **A. Derivative of the weighted numerator at β = 0.** -/
theorem hasDerivAt_weightedNumerator_zero [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {B C : ℝ}
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f : Config N G → ℝ} (mf : Measurable f) (hf : ∀ U, |f U| ≤ C) :
    HasDerivAt
      (fun β : ℝ => ∫ U : Config N G, f U * gibbsWeight β χ U
        ∂(configMeasure μm N))
      (-(∫ U : Config N G, f U * wilsonAction χ U ∂(configMeasure μm N)))
      0 := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hf (trivialConfig N G))
  have hB0 : 0 ≤ B :=
    le_trans (wilsonAction_nonneg χ hχ (trivialConfig N G)) (hB _)
  set S : Config N G → ℝ := fun U => wilsonAction χ U with hS
  have mS : Measurable S := measurable_wilsonAction mχ
  -- F' β U := f U * (exp(−β·S U) * −S U)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun β (U : Config N G) => f U * gibbsWeight β χ U)
    (F' := fun β (U : Config N G) =>
      f U * (Real.exp (-β * S U) * -(S U)))
    (x₀ := (0 : ℝ)) (ε := 1) (μ := configMeasure μm N)
    (bound := fun _ => C * (B * Real.exp B)) one_pos
    (Filter.Eventually.of_forall fun β =>
      (mf.mul (measurable_gibbsWeight mχ β)).aestronglyMeasurable)
    ?_ ?_ ?_ ?_ ?_
  · -- valor da derivada: ∫ F' 0 = −∫ f·S
    have hval : (∫ U : Config N G,
        f U * (Real.exp (-(0:ℝ) * S U) * -(S U)) ∂(configMeasure μm N))
        = -(∫ U : Config N G, f U * S U ∂(configMeasure μm N)) := by
      rw [← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
      show f U * (Real.exp (-(0:ℝ) * S U) * -(S U)) = -(f U * S U)
      simp
    rw [hval] at h
    exact h.2
  · -- integrabilidade de F 0 = f·w₀
    refine ((integrable_const C).mono'
      ((mf.mul (measurable_gibbsWeight mχ 0)).aestronglyMeasurable) ?_)
    filter_upwards with U
    calc ‖f U * gibbsWeight 0 χ U‖
        = |f U| * gibbsWeight 0 χ U := by
          rw [Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (gibbsWeight_pos 0 χ U).le]
      _ ≤ C * 1 := by
          refine mul_le_mul (hf U) ?_ (gibbsWeight_pos 0 χ U).le hC
          simpa using gibbsWeight_le_one le_rfl hχ U
      _ = C := mul_one C
  · -- mensurabilidade de F' 0
    exact (mf.mul ((Real.measurable_exp.comp
      (mS.const_mul (-(0:ℝ)))).mul mS.neg)).aestronglyMeasurable
  · -- dominação na bola de raio 1
    filter_upwards with U
    intro β hβ
    have hSU0 := wilsonAction_nonneg χ hχ U
    have hSUB := hB U
    have habsβ : |β| < 1 := by simpa [Metric.mem_ball] using hβ
    have hexp : Real.exp (-β * S U) ≤ Real.exp B := by
      apply Real.exp_le_exp.mpr
      have h1 : -β * S U ≤ |β| * S U := by
        have := neg_abs_le β
        nlinarith [abs_nonneg β]
      have h2 : |β| * S U ≤ 1 * S U :=
        mul_le_mul_of_nonneg_right habsβ.le hSU0
      linarith
    calc ‖f U * (Real.exp (-β * S U) * -(S U))‖
        = |f U| * (Real.exp (-β * S U) * S U) := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
            abs_of_nonneg (Real.exp_pos _).le, abs_of_nonneg hSU0]
      _ ≤ C * (Real.exp B * B) := by
          refine mul_le_mul (hf U) ?_ ?_ hC
          · exact mul_le_mul hexp hSUB hSU0 (Real.exp_pos _).le
          · positivity
      _ = C * (B * Real.exp B) := by ring
  · -- integrabilidade do dominador (constante, probabilidade)
    exact integrable_const _
  · -- derivabilidade pontual na bola
    filter_upwards with U
    intro β _
    simpa [hS] using (hasDerivAt_gibbsWeight (N := N) (χ := χ) U β).const_mul (f U)

/-- **B. Derivative of the real partition function at β = 0.** -/
theorem hasDerivAt_realZ_zero [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {B : ℝ}
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B) :
    HasDerivAt (fun β : ℝ => realZ (N := N) μm β χ)
      (-(∫ U : Config N G, wilsonAction χ U ∂(configMeasure μm N))) 0 := by
  have h := hasDerivAt_weightedNumerator_zero (N := N) μm mχ hχ hB
    (f := fun _ : Config N G => (1 : ℝ)) (C := 1) measurable_const
    (fun _ => by norm_num)
  simp only [one_mul] at h
  exact h

/-- **C. Derivative of the Gibbs expectation at β = 0, integral form.** -/
theorem hasDerivAt_gibbsExpectation_zero_integral_form [NeZero N]
    [Fintype (Site N)]
    (mχ : Measurable χ) {B C : ℝ}
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f : Config N G → ℝ} (mf : Measurable f) (hf : ∀ U, |f U| ≤ C) :
    HasDerivAt (fun β : ℝ => gibbsExpectation (N := N) μm β χ f)
      (-(∫ U : Config N G, f U * wilsonAction χ U ∂(configMeasure μm N))
        + (∫ U : Config N G, f U * gibbsWeight 0 χ U ∂(configMeasure μm N))
          * ∫ U : Config N G, wilsonAction χ U ∂(configMeasure μm N)) 0 := by
  have hA := hasDerivAt_weightedNumerator_zero (N := N) μm mχ hχ hB mf hf
  have hZ := hasDerivAt_realZ_zero (N := N) μm mχ hχ hB
  have hz1 : realZ (N := N) μm 0 χ = 1 := realZ_zero (N := N) μm χ
  have hzne : realZ (N := N) μm 0 χ ≠ 0 := by rw [hz1]; norm_num
  have h := hA.div hZ hzne
  have : HasDerivAt (fun β : ℝ => gibbsExpectation (N := N) μm β χ f)
      ((-(∫ U : Config N G, f U * wilsonAction χ U ∂(configMeasure μm N))
          * realZ (N := N) μm 0 χ
        - (∫ U : Config N G, f U * gibbsWeight 0 χ U ∂(configMeasure μm N))
          * -(∫ U : Config N G, wilsonAction χ U ∂(configMeasure μm N)))
        / realZ (N := N) μm 0 χ ^ 2) 0 := h
  rw [hz1] at this
  convert this using 1
  ring

/-- **D. CAPSTONE (pedra 18): linear response as a covariance.**
    d/dβ ⟨f⟩_β |₀ = −(⟨f·S⟩₀ − ⟨f⟩₀·⟨S⟩₀). Finite volume; derivative
    at zero; no thermodynamic uniformity; not a cluster expansion. -/
theorem hasDerivAt_gibbsExpectation_zero_covariance [NeZero N]
    [Fintype (Site N)]
    (mχ : Measurable χ) {B C : ℝ}
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f : Config N G → ℝ} (mf : Measurable f) (hf : ∀ U, |f U| ≤ C) :
    HasDerivAt (fun β : ℝ => gibbsExpectation (N := N) μm β χ f)
      (-(gibbsExpectation (N := N) μm 0 χ (fun U => f U * wilsonAction χ U)
        - gibbsExpectation (N := N) μm 0 χ f
          * gibbsExpectation (N := N) μm 0 χ (fun U => wilsonAction χ U)))
      0 := by
  have h := hasDerivAt_gibbsExpectation_zero_integral_form
    (N := N) μm mχ hχ hB mf hf
  have e1 : gibbsExpectation (N := N) μm 0 χ
      (fun U => f U * wilsonAction χ U)
      = ∫ U : Config N G, f U * wilsonAction χ U ∂(configMeasure μm N) :=
    gibbsExpectation_zero (N := N) μm χ _
  have e2 : gibbsExpectation (N := N) μm 0 χ f
      = ∫ U : Config N G, f U ∂(configMeasure μm N) :=
    gibbsExpectation_zero (N := N) μm χ f
  have e3 : gibbsExpectation (N := N) μm 0 χ (fun U => wilsonAction χ U)
      = ∫ U : Config N G, wilsonAction χ U ∂(configMeasure μm N) :=
    gibbsExpectation_zero (N := N) μm χ _
  have e4 : (∫ U : Config N G, f U * gibbsWeight 0 χ U
      ∂(configMeasure μm N))
      = ∫ U : Config N G, f U ∂(configMeasure μm N) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    show f U * gibbsWeight 0 χ U = f U
    simp
  rw [e1, e2, e3]
  rw [e4] at h
  convert h using 1
  ring

end Measure

end LatticeGauge
