/-
LatticeGauge/Expectation.lean — Phase 3, fifth stone.

Expectation values ⟨f⟩ under the Gibbs measure. Full measurability
plumbing (plaquette → action → weight), integrability, positivity of
the real partition function, normalization ⟨c⟩ = c, and the bound
|⟨f⟩| ≤ C for bounded observables — hence |⟨Wilson loop⟩| ≤ 1.
NO axioms; everything proved.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.WilsonLoop

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- **Proved:** the plaquette map is measurable in the configuration. -/
theorem measurable_plaquette [NeZero N] (x : Site N) (μ ν : Dir) :
    Measurable fun U : Config N G => plaquette U x μ ν := by
  unfold plaquette
  exact (((measurable_pi_apply _).mul (measurable_pi_apply _)).mul
    (measurable_pi_apply _).inv).mul (measurable_pi_apply _).inv

variable {χ : G → ℝ}

/-- **Proved:** the Wilson action is measurable (χ measurable). -/
theorem measurable_wilsonAction [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) :
    Measurable fun U : Config N G => wilsonAction χ U := by
  unfold wilsonAction
  refine Finset.measurable_sum _ fun x _ => ?_
  refine Finset.measurable_sum _ fun μ _ => ?_
  refine Finset.measurable_sum _ fun ν _ => ?_
  by_cases h : μ.val < ν.val
  · simp only [h, if_true]
    exact measurable_const.sub (mχ.comp (measurable_plaquette x μ ν))
  · simp only [h, if_false]
    exact measurable_const

/-- **Proved:** the Gibbs weight is measurable. -/
theorem measurable_gibbsWeight [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) (β : ℝ) :
    Measurable fun U : Config N G => gibbsWeight β χ U := by
  unfold gibbsWeight
  exact Real.measurable_exp.comp ((measurable_wilsonAction mχ).const_mul (-β))

section Expectation

variable (μm : Measure G) [SigmaFinite μm]

/-- Product (path-integral) measure on configurations. -/
noncomputable def configMeasure (N : ℕ) : Measure (Config N G) :=
  Measure.pi fun _ : Link N => μm

/-- Real-valued partition function. -/
noncomputable def realZ [NeZero N] [Fintype (Site N)] (β : ℝ) (χ : G → ℝ) : ℝ :=
  ∫ U : Config N G, gibbsWeight β χ U ∂(configMeasure μm N)

/-- Gibbs expectation value of an observable. -/
noncomputable def gibbsExpectation [NeZero N] [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ) : ℝ :=
  (∫ U : Config N G, f U * gibbsWeight β χ U ∂(configMeasure μm N)) /
    realZ (N := N) μm β χ

variable [IsProbabilityMeasure μm]

/-- **Proved:** the Gibbs weight is integrable (β ≥ 0, χ ≤ 1). -/
theorem integrable_gibbsWeight [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β : ℝ} (hβ : 0 ≤ β) (hχ : ∀ g : G, χ g ≤ 1) :
    Integrable (fun U : Config N G => gibbsWeight β χ U) (configMeasure μm N) := by
  refine (integrable_const (1 : ℝ)).mono'
    ((measurable_gibbsWeight mχ β).aestronglyMeasurable) ?_
  filter_upwards with U
  rw [Real.norm_of_nonneg (gibbsWeight_pos β χ U).le]
  exact gibbsWeight_le_one hβ hχ U

/-- **Proved:** the real partition function is strictly positive
    (under a uniform action bound B). -/
theorem realZ_pos [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β B : ℝ} (hβ : 0 ≤ β) (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B) :
    0 < realZ (N := N) μm β χ := by
  have hint := integrable_gibbsWeight (N := N) μm mχ hβ hχ
  have hlow : ∀ U : Config N G, Real.exp (-β * B) ≤ gibbsWeight β χ U := by
    intro U
    unfold gibbsWeight
    apply Real.exp_le_exp.mpr
    nlinarith [hB U]
  calc (0 : ℝ) < Real.exp (-β * B) := Real.exp_pos _
    _ = ∫ _ : Config N G, Real.exp (-β * B) ∂(configMeasure μm N) := by
        simp [configMeasure]
    _ ≤ ∫ U : Config N G, gibbsWeight β χ U ∂(configMeasure μm N) :=
        integral_mono (integrable_const _) hint hlow

/-- **Proved: normalization.** ⟨c⟩ = c for constant observables. -/
theorem gibbsExpectation_const [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β B : ℝ} (hβ : 0 ≤ β) (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B) (c : ℝ) :
    gibbsExpectation (N := N) μm β χ (fun _ => c) = c := by
  unfold gibbsExpectation
  rw [MeasureTheory.integral_const_mul]
  have hz := (realZ_pos (N := N) μm mχ hβ hχ hB).ne'
  unfold realZ at hz ⊢
  field_simp

/-- **Proved: boundedness.** If |f| ≤ C pointwise (f measurable), then
    |⟨f⟩| ≤ C. In particular |⟨Wilson loop⟩| ≤ 1 whenever |χ| ≤ 1. -/
theorem abs_gibbsExpectation_le [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β B C : ℝ} (hβ : 0 ≤ β) (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f : Config N G → ℝ} (mf : Measurable f) (hf : ∀ U, |f U| ≤ C) :
    |gibbsExpectation (N := N) μm β χ f| ≤ C := by
  have hz := realZ_pos (N := N) μm mχ hβ hχ hB
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hf (trivialConfig N G))
  have hwint := integrable_gibbsWeight (N := N) μm mχ hβ hχ
  have hfwint : Integrable (fun U : Config N G => f U * gibbsWeight β χ U)
      (configMeasure μm N) := by
    refine (hwint.const_mul C).mono'
      ((mf.mul (measurable_gibbsWeight mχ β)).aestronglyMeasurable) ?_
    filter_upwards with U
    rw [Real.norm_of_nonneg]
    · calc |f U * gibbsWeight β χ U|
          = |f U| * gibbsWeight β χ U := by
            rw [abs_mul, abs_of_nonneg (gibbsWeight_pos β χ U).le]
        _ ≤ C * gibbsWeight β χ U :=
            mul_le_mul_of_nonneg_right (hf U) (gibbsWeight_pos β χ U).le
    · positivity
  unfold gibbsExpectation
  rw [abs_div, abs_of_pos hz, div_le_iff hz]
  calc |∫ U : Config N G, f U * gibbsWeight β χ U ∂(configMeasure μm N)|
      ≤ ∫ U : Config N G, |f U * gibbsWeight β χ U| ∂(configMeasure μm N) := by
        exact (abs_integral_le_integral_abs)
    _ ≤ ∫ U : Config N G, C * gibbsWeight β χ U ∂(configMeasure μm N) := by
        refine integral_mono hfwint.abs (hwint.const_mul C) fun U => ?_
        rw [abs_mul, abs_of_nonneg (gibbsWeight_pos β χ U).le]
        exact mul_le_mul_of_nonneg_right (hf U) (gibbsWeight_pos β χ U).le
    _ = C * realZ (N := N) μm β χ := by
        rw [MeasureTheory.integral_const_mul]; rfl

end Expectation

end LatticeGauge
