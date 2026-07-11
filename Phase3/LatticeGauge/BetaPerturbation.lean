/-
LatticeGauge/BetaPerturbation.lean — Phase 3, seventeenth stone.

FINITE-VOLUME CONTINUITY BOUND FROM β = 0 (architecture: Sol/GPT-5.6;
execution: Fable). |⟨f⟩_β − ⟨f⟩₀| ≤ 2·C·B·β·exp(β·B) for β ≥ 0 —
the quantitative neighborhood of the exactly-solved base camp.

HONESTY (docstring-level, per the architect): B is the uniform action
bound of THIS finite lattice, so it grows with the volume N. This is a
finite-volume preparatory lemma — NOT a cluster expansion and NOT a
thermodynamic-limit statement. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.WilsonExpectation
import LatticeGauge.Beta0

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

/-- **L1 (elementary):** for x ≥ 0, |e^(−x) − 1| ≤ x. -/
theorem abs_exp_neg_sub_one_le {x : ℝ} (hx : 0 ≤ x) :
    |Real.exp (-x) - 1| ≤ x := by
  have hup : Real.exp (-x) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hlow : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  rw [abs_le]
  constructor <;> linarith

section Measure

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

variable {χ : G → ℝ}

/-- **L2:** pointwise weight deviation: |w_β(U) − 1| ≤ β·B. -/
theorem abs_gibbsWeight_sub_one_le [NeZero N] [Fintype (Site N)]
    {β B : ℝ} (hβ : 0 ≤ β) (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B) (U : Config N G) :
    |gibbsWeight β χ U - 1| ≤ β * B := by
  have hS0 := wilsonAction_nonneg χ hχ U
  have hx : 0 ≤ β * wilsonAction χ U := mul_nonneg hβ hS0
  have h1 : |Real.exp (-(β * wilsonAction χ U)) - 1| ≤ β * wilsonAction χ U :=
    abs_exp_neg_sub_one_le hx
  have h2 : β * wilsonAction χ U ≤ β * B :=
    mul_le_mul_of_nonneg_left (hB U) hβ
  calc |gibbsWeight β χ U - 1|
      = |Real.exp (-(β * wilsonAction χ U)) - 1| := by
        unfold gibbsWeight
        ring_nf
    _ ≤ β * wilsonAction χ U := h1
    _ ≤ β * B := h2

/-- **L3/L4 (unified):** for |g| ≤ K measurable,
    |∫ g·w_β − ∫ g| ≤ K·β·B. -/
theorem abs_integral_mul_weight_sub_le [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β B K : ℝ} (hβ : 0 ≤ β)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {g : Config N G → ℝ} (mg : Measurable g) (hg : ∀ U, |g U| ≤ K) :
    |(∫ U : Config N G, g U * gibbsWeight β χ U ∂(configMeasure μm N))
      - ∫ U : Config N G, g U ∂(configMeasure μm N)|
      ≤ K * (β * B) := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hg (trivialConfig N G))
  have hB0 : 0 ≤ B :=
    le_trans (wilsonAction_nonneg χ hχ (trivialConfig N G)) (hB _)
  have hwint := integrable_gibbsWeight (N := N) μm mχ hβ hχ
  have hgint : Integrable g (configMeasure μm N) := by
    refine (integrable_const K).mono' mg.aestronglyMeasurable ?_
    filter_upwards with U
    rw [Real.norm_eq_abs]
    exact hg U
  have hgwint : Integrable (fun U : Config N G => g U * gibbsWeight β χ U)
      (configMeasure μm N) := by
    refine (hwint.const_mul K).mono'
      ((mg.mul (measurable_gibbsWeight mχ β)).aestronglyMeasurable) ?_
    filter_upwards with U
    calc ‖g U * gibbsWeight β χ U‖
        = |g U| * gibbsWeight β χ U := by
          rw [Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (gibbsWeight_pos β χ U).le]
      _ ≤ K * gibbsWeight β χ U :=
          mul_le_mul_of_nonneg_right (hg U) (gibbsWeight_pos β χ U).le
  calc |(∫ U : Config N G, g U * gibbsWeight β χ U ∂(configMeasure μm N))
        - ∫ U : Config N G, g U ∂(configMeasure μm N)|
      = |∫ U : Config N G, g U * (gibbsWeight β χ U - 1)
          ∂(configMeasure μm N)| := by
        rw [← integral_sub hgwint hgint]
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        show g U * gibbsWeight β χ U - g U = g U * (gibbsWeight β χ U - 1)
        ring
    _ ≤ ∫ U : Config N G, ‖g U * (gibbsWeight β χ U - 1)‖
          ∂(configMeasure μm N) :=
        by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
    _ ≤ ∫ _U : Config N G, K * (β * B) ∂(configMeasure μm N) := by
        refine integral_mono ?_ (integrable_const _) fun U => ?_
        · exact (hgwint.sub hgint).norm.congr
            (Filter.Eventually.of_forall fun U => by
              rw [Real.norm_eq_abs]
              congr 1
              ring)
        · rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hg U)
            (abs_gibbsWeight_sub_one_le (N := N) hβ hχ hB U)
            (abs_nonneg _) hK
    _ = K * (β * B) := by simp

/-- **CAPSTONE (pedra 17): finite-volume continuity bound from β = 0.**
    For all β ≥ 0: |⟨f⟩_β − ⟨f⟩₀| ≤ 2·C·B·β·exp(β·B).
    B is the uniform action bound of THIS finite lattice (it grows with
    the volume): this is a finite-volume preparatory lemma, not a
    cluster expansion and not a thermodynamic-limit statement. -/
theorem abs_gibbsExpectation_sub_zero_le [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β B C : ℝ} (hβ : 0 ≤ β)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f : Config N G → ℝ} (mf : Measurable f) (hf : ∀ U, |f U| ≤ C) :
    |gibbsExpectation (N := N) μm β χ f
      - gibbsExpectation (N := N) μm 0 χ f|
      ≤ 2 * C * B * β * Real.exp (β * B) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hf (trivialConfig N G))
  have hB0 : 0 ≤ B :=
    le_trans (wilsonAction_nonneg χ hχ (trivialConfig N G)) (hB _)
  have hz := realZ_pos (N := N) μm mχ hβ hχ hB
  set a : ℝ := ∫ U : Config N G, f U * gibbsWeight β χ U
    ∂(configMeasure μm N) with ha
  set a0 : ℝ := ∫ U : Config N G, f U ∂(configMeasure μm N) with ha0
  set z : ℝ := realZ (N := N) μm β χ with hzdef
  -- cotas dos blocos
  have hnum : |a - a0| ≤ C * (β * B) :=
    abs_integral_mul_weight_sub_le (N := N) μm mχ hβ hχ hB mf hf
  have hden : |z - 1| ≤ 1 * (β * B) := by
    have := abs_integral_mul_weight_sub_le (N := N) μm mχ hβ hχ hB
      (g := fun _ => (1 : ℝ)) measurable_const (fun _ => by norm_num)
    simpa [hzdef, realZ] using this
  have ha0_le : |a0| ≤ C := by
    calc |a0| ≤ ∫ U : Config N G, ‖f U‖ ∂(configMeasure μm N) := by
          rw [ha0, ← Real.norm_eq_abs]
          exact norm_integral_le_integral_norm _
      _ ≤ ∫ _U : Config N G, C ∂(configMeasure μm N) := by
          refine integral_mono ?_ (integrable_const _) fun U => ?_
          · exact ((integrable_const C).mono' mf.aestronglyMeasurable
              (Filter.Eventually.of_forall fun U => by
                rw [Real.norm_eq_abs]; exact hf U)).norm
          · rw [Real.norm_eq_abs]; exact hf U
      _ = C := by simp
  have hzlow : Real.exp (-(β * B)) ≤ z := by
    have hlow : ∀ U : Config N G,
        Real.exp (-(β * B)) ≤ gibbsWeight β χ U := by
      intro U
      unfold gibbsWeight
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left (hB U) hβ
      linarith
    have hwint := integrable_gibbsWeight (N := N) μm mχ hβ hχ
    calc Real.exp (-(β * B))
        = ∫ _U : Config N G, Real.exp (-(β * B))
            ∂(configMeasure μm N) := by simp
      _ ≤ z := by
          rw [hzdef]
          unfold realZ
          exact integral_mono (integrable_const _) hwint hlow
  have hzinv : z⁻¹ ≤ Real.exp (β * B) := by
    have h := inv_le_inv_of_le (Real.exp_pos _) hzlow
    rwa [← Real.exp_neg, neg_neg] at h
  -- E_β − E_0 = (a − a0·z)/z
  have hE0 : gibbsExpectation (N := N) μm 0 χ f = a0 := by
    rw [gibbsExpectation_zero (N := N) μm χ]
  have hEβ : gibbsExpectation (N := N) μm β χ f = a / z := rfl
  rw [hEβ, hE0]
  have hdiff : a / z - a0 = (a - a0 * z) / z := by
    field_simp
  rw [hdiff, abs_div, abs_of_pos hz]
  have hsplit : |a - a0 * z| ≤ C * (β * B) + C * (β * B) := by
    calc |a - a0 * z| = |(a - a0) + a0 * (1 - z)| := by ring_nf
      _ ≤ |a - a0| + |a0 * (1 - z)| := abs_add _ _
      _ ≤ C * (β * B) + C * (β * B) := by
          refine add_le_add hnum ?_
          rw [abs_mul]
          calc |a0| * |1 - z| ≤ C * (1 * (β * B)) := by
                refine mul_le_mul ha0_le ?_ (abs_nonneg _) hC
                rw [abs_sub_comm]
                exact hden
            _ = C * (β * B) := by ring
  calc |a - a0 * z| / z = |a - a0 * z| * z⁻¹ := div_eq_mul_inv _ _
    _ ≤ (C * (β * B) + C * (β * B)) * Real.exp (β * B) := by
        refine mul_le_mul hsplit hzinv (inv_nonneg.mpr hz.le) ?_
        positivity
    _ = 2 * C * B * β * Real.exp (β * B) := by ring

/-- **Corolário local-linear:** em qualquer janela 0 ≤ β ≤ β₀. -/
theorem abs_gibbsExpectation_sub_zero_le_of_window [NeZero N]
    [Fintype (Site N)]
    (mχ : Measurable χ) {β β₀ B C : ℝ} (hβ : 0 ≤ β) (hββ₀ : β ≤ β₀)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f : Config N G → ℝ} (mf : Measurable f) (hf : ∀ U, |f U| ≤ C) :
    |gibbsExpectation (N := N) μm β χ f
      - gibbsExpectation (N := N) μm 0 χ f|
      ≤ 2 * C * B * Real.exp (β₀ * B) * β := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hf (trivialConfig N G))
  have hB0 : 0 ≤ B :=
    le_trans (wilsonAction_nonneg χ hχ (trivialConfig N G)) (hB _)
  have h := abs_gibbsExpectation_sub_zero_le (N := N) μm mχ hβ hχ hB mf hf
  have hexp : Real.exp (β * B) ≤ Real.exp (β₀ * B) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hββ₀ hB0)
  calc |gibbsExpectation (N := N) μm β χ f
        - gibbsExpectation (N := N) μm 0 χ f|
      ≤ 2 * C * B * β * Real.exp (β * B) := h
    _ ≤ 2 * C * B * β * Real.exp (β₀ * B) := by
        refine mul_le_mul_of_nonneg_left hexp ?_
        positivity
    _ = 2 * C * B * Real.exp (β₀ * B) * β := by ring

/-- **Corolário Wilson-path (C = 1): a ponte com a 16ª pedra.** -/
theorem abs_wilsonExpectation_sub_zero_le [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β B : ℝ} (hβ : 0 ≤ β)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    (x : Site N) (p : List Step) :
    |gibbsExpectation (N := N) μm β χ (fun U => wilsonLoop χ U x p)
      - gibbsExpectation (N := N) μm 0 χ (fun U => wilsonLoop χ U x p)|
      ≤ 2 * 1 * B * β * Real.exp (β * B) := by
  have hχ1 : ∀ g : G, χ g ≤ 1 := fun g => (abs_le.mp (hχabs g)).2
  exact abs_gibbsExpectation_sub_zero_le (N := N) μm mχ hβ hχ1 hB
    (measurable_wilsonLoop mχ x p) (fun U => hχabs _)

end Measure

end LatticeGauge
