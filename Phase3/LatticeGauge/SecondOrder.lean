/-
LatticeGauge/SecondOrder.lean — Phase 3, nineteenth stone.

FIRST-ORDER TAYLOR REMAINDER AT β = 0 (architecture: Sol/GPT-5.6, route
R3 elementary; execution: Fable):
|⟨f⟩_β − ⟨f⟩₀ + β·Cov₀(f,S)| ≤ 4·C·B²·β²·exp(β·B) for β ≥ 0, β·B ≤ 1.
Closes the β = 0 analysis package (value 11ª, continuity 17ª,
derivative 18ª, remainder 19ª) with NO new differentiation machinery —
only the quadratic remainder of exp and the quotient algebra of the
17th stone. LIMITS: finite volume; β·B ≤ 1; constants not uniform in N;
a first-order remainder bound, not a convergent series nor a cluster
expansion. NO axioms.
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

/-- **A. Pointwise quadratic remainder of the weight:**
    for β ≥ 0 with β·B ≤ 1, |w_β(U) − 1 + β·S(U)| ≤ β²·B². -/
theorem abs_gibbsWeight_sub_one_add_le [NeZero N] [Fintype (Site N)]
    {β B : ℝ} (hβ : 0 ≤ β) (hβB : β * B ≤ 1)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B) (U : Config N G) :
    |gibbsWeight β χ U - 1 + β * wilsonAction χ U| ≤ β ^ 2 * B ^ 2 := by
  have hS0 := wilsonAction_nonneg χ hχ U
  have hSB := hB U
  have hβS : 0 ≤ β * wilsonAction χ U := mul_nonneg hβ hS0
  have hβSβB : β * wilsonAction χ U ≤ β * B :=
    mul_le_mul_of_nonneg_left hSB hβ
  have hx : |(-(β * wilsonAction χ U))| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg hβS]
    linarith
  have h := Real.abs_exp_sub_one_sub_id_le hx
  have heq : gibbsWeight β χ U - 1 + β * wilsonAction χ U
      = Real.exp (-(β * wilsonAction χ U)) - 1 - (-(β * wilsonAction χ U)) := by
    unfold gibbsWeight
    ring_nf
  rw [heq]
  calc |Real.exp (-(β * wilsonAction χ U)) - 1 - (-(β * wilsonAction χ U))|
      ≤ (-(β * wilsonAction χ U)) ^ 2 := h
    _ = (β * wilsonAction χ U) ^ 2 := by ring
    _ ≤ (β * B) ^ 2 := by
        exact pow_le_pow_left hβS hβSβB 2
    _ = β ^ 2 * B ^ 2 := by ring

/-- **B/C (unified). Second-order integral remainder:** for |g| ≤ K,
    |∫ g·w_β − ∫ g + β·∫ g·S| ≤ K·β²·B². -/
theorem abs_integral_secondOrder [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {β B K : ℝ} (hβ : 0 ≤ β) (hβB : β * B ≤ 1)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {g : Config N G → ℝ} (mg : Measurable g) (hg : ∀ U, |g U| ≤ K) :
    |(∫ U : Config N G, g U * gibbsWeight β χ U ∂(configMeasure μm N))
      - (∫ U : Config N G, g U ∂(configMeasure μm N))
      + β * ∫ U : Config N G, g U * wilsonAction χ U ∂(configMeasure μm N)|
      ≤ K * (β ^ 2 * B ^ 2) := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) (hg (trivialConfig N G))
  have hB0 : 0 ≤ B :=
    le_trans (wilsonAction_nonneg χ hχ (trivialConfig N G)) (hB _)
  have mS : Measurable fun U : Config N G => wilsonAction χ U :=
    measurable_wilsonAction mχ
  have hwint := integrable_gibbsWeight (N := N) μm mχ hβ hχ
  have hgint : Integrable g (configMeasure μm N) := by
    refine (integrable_const K).mono' mg.aestronglyMeasurable ?_
    filter_upwards with U
    rw [Real.norm_eq_abs]; exact hg U
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
  have hgSint : Integrable (fun U : Config N G => g U * wilsonAction χ U)
      (configMeasure μm N) := by
    refine (integrable_const (K * B)).mono'
      ((mg.mul mS).aestronglyMeasurable) ?_
    filter_upwards with U
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (wilsonAction_nonneg χ hχ U)]
    exact mul_le_mul (hg U) (hB U) (wilsonAction_nonneg χ hχ U) hK
  have hcomb : (∫ U : Config N G, g U * gibbsWeight β χ U
        ∂(configMeasure μm N))
      - (∫ U : Config N G, g U ∂(configMeasure μm N))
      + β * ∫ U : Config N G, g U * wilsonAction χ U ∂(configMeasure μm N)
      = ∫ U : Config N G,
          g U * (gibbsWeight β χ U - 1 + β * wilsonAction χ U)
          ∂(configMeasure μm N) := by
    have hpt : (fun U : Config N G =>
        g U * (gibbsWeight β χ U - 1 + β * wilsonAction χ U))
        = fun U => (g U * gibbsWeight β χ U - g U)
            + β * (g U * wilsonAction χ U) := by
      funext U
      ring
    conv_rhs => rw [hpt]
    have h1 : Integrable (fun U : Config N G =>
        g U * gibbsWeight β χ U - g U) (configMeasure μm N) :=
      (hgwint.sub hgint).congr
        (Filter.Eventually.of_forall fun U => by
          simp only [Pi.sub_apply])
    rw [integral_add h1 (hgSint.const_mul β),
      integral_sub hgwint hgint, integral_mul_left]
  rw [hcomb]
  have hRint : Integrable
      (fun U : Config N G =>
        g U * (gibbsWeight β χ U - 1 + β * wilsonAction χ U))
      (configMeasure μm N) :=
    ((hgwint.sub hgint).add (hgSint.const_mul β)).congr
      (Filter.Eventually.of_forall fun U => by
        simp only [Pi.add_apply, Pi.sub_apply]
        ring)
  calc |∫ U : Config N G,
        g U * (gibbsWeight β χ U - 1 + β * wilsonAction χ U)
        ∂(configMeasure μm N)|
      ≤ ∫ U : Config N G,
          ‖g U * (gibbsWeight β χ U - 1 + β * wilsonAction χ U)‖
          ∂(configMeasure μm N) := by
        have h1 := norm_integral_le_integral_norm
          (μ := configMeasure μm N)
          (f := fun U : Config N G =>
            g U * (gibbsWeight β χ U - 1 + β * wilsonAction χ U))
        rwa [Real.norm_eq_abs] at h1
    _ ≤ ∫ _U : Config N G, K * (β ^ 2 * B ^ 2)
          ∂(configMeasure μm N) := by
        refine integral_mono hRint.norm (integrable_const _) fun U => ?_
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_mul (hg U)
          (abs_gibbsWeight_sub_one_add_le (N := N) hβ hβB hχ hB U)
          (abs_nonneg _) hK
    _ = K * (β ^ 2 * B ^ 2) := by simp

/-- **D. Covariance bound at β = 0:** |Cov₀(f,S)| ≤ 2·C·B (integral form). -/
theorem abs_cov_integral_le [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ) {B C : ℝ}
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f : Config N G → ℝ} (mf : Measurable f) (hf : ∀ U, |f U| ≤ C) :
    |(∫ U : Config N G, f U * wilsonAction χ U ∂(configMeasure μm N))
      - (∫ U : Config N G, f U ∂(configMeasure μm N))
        * ∫ U : Config N G, wilsonAction χ U ∂(configMeasure μm N)|
      ≤ 2 * C * B := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hf (trivialConfig N G))
  have hB0 : 0 ≤ B :=
    le_trans (wilsonAction_nonneg χ hχ (trivialConfig N G)) (hB _)
  have mS : Measurable fun U : Config N G => wilsonAction χ U :=
    measurable_wilsonAction mχ
  have habs : ∀ (h : Config N G → ℝ), Measurable h → ∀ K, 0 ≤ K →
      (∀ U, |h U| ≤ K) →
      |∫ U : Config N G, h U ∂(configMeasure μm N)| ≤ K := by
    intro h mh K hK hh
    have hint : Integrable h (configMeasure μm N) := by
      refine (integrable_const K).mono' mh.aestronglyMeasurable ?_
      filter_upwards with U
      rw [Real.norm_eq_abs]; exact hh U
    calc |∫ U : Config N G, h U ∂(configMeasure μm N)|
        ≤ ∫ U : Config N G, ‖h U‖ ∂(configMeasure μm N) := by
          have h1 := norm_integral_le_integral_norm
            (μ := configMeasure μm N) (f := h)
          rwa [Real.norm_eq_abs] at h1
      _ ≤ ∫ _U : Config N G, K ∂(configMeasure μm N) := by
          refine integral_mono hint.norm (integrable_const _) fun U => ?_
          rw [Real.norm_eq_abs]; exact hh U
      _ = K := by simp
  have h1 : |∫ U : Config N G, f U * wilsonAction χ U
      ∂(configMeasure μm N)| ≤ C * B := by
    refine habs _ (mf.mul mS) (C * B) (mul_nonneg hC hB0) fun U => ?_
    rw [abs_mul, abs_of_nonneg (wilsonAction_nonneg χ hχ U)]
    exact mul_le_mul (hf U) (hB U) (wilsonAction_nonneg χ hχ U) hC
  have h2 : |∫ U : Config N G, f U ∂(configMeasure μm N)| ≤ C :=
    habs _ mf C hC hf
  have h3 : |∫ U : Config N G, wilsonAction χ U
      ∂(configMeasure μm N)| ≤ B := by
    refine habs _ mS B hB0 fun U => ?_
    rw [abs_of_nonneg (wilsonAction_nonneg χ hχ U)]
    exact hB U
  calc |(∫ U : Config N G, f U * wilsonAction χ U ∂(configMeasure μm N))
        - (∫ U : Config N G, f U ∂(configMeasure μm N))
          * ∫ U : Config N G, wilsonAction χ U ∂(configMeasure μm N)|
      ≤ |∫ U : Config N G, f U * wilsonAction χ U ∂(configMeasure μm N)|
        + |(∫ U : Config N G, f U ∂(configMeasure μm N))
            * ∫ U : Config N G, wilsonAction χ U ∂(configMeasure μm N)| :=
        abs_sub _ _
    _ ≤ C * B + C * B := by
        refine add_le_add h1 ?_
        rw [abs_mul]
        exact mul_le_mul h2 h3 (abs_nonneg _) hC
    _ = 2 * C * B := by ring

/-- **CAPSTONE (pedra 19): first-order Taylor remainder at β = 0.**
    For β ≥ 0 with β·B ≤ 1:
    |⟨f⟩_β − ⟨f⟩₀ + β·Cov₀(f,S)| ≤ 4·C·B²·β²·exp(β·B).
    Finite volume; constants not uniform in N; a remainder bound,
    not a convergent series nor a cluster expansion. -/
theorem abs_gibbsExpectation_taylor_remainder [NeZero N]
    [Fintype (Site N)]
    (mχ : Measurable χ) {β B C : ℝ} (hβ : 0 ≤ β) (hβB : β * B ≤ 1)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f : Config N G → ℝ} (mf : Measurable f) (hf : ∀ U, |f U| ≤ C) :
    |gibbsExpectation (N := N) μm β χ f
      - gibbsExpectation (N := N) μm 0 χ f
      + β * (gibbsExpectation (N := N) μm 0 χ
              (fun U => f U * wilsonAction χ U)
            - gibbsExpectation (N := N) μm 0 χ f
              * gibbsExpectation (N := N) μm 0 χ
                  (fun U => wilsonAction χ U))|
      ≤ 4 * C * B ^ 2 * β ^ 2 * Real.exp (β * B) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hf (trivialConfig N G))
  have hB0 : 0 ≤ B :=
    le_trans (wilsonAction_nonneg χ hχ (trivialConfig N G)) (hB _)
  have hz := realZ_pos (N := N) μm mχ hβ hχ hB
  set A : ℝ := ∫ U : Config N G, f U * gibbsWeight β χ U
    ∂(configMeasure μm N) with hA
  set A0 : ℝ := ∫ U : Config N G, f U ∂(configMeasure μm N) with hA0
  set FS : ℝ := ∫ U : Config N G, f U * wilsonAction χ U
    ∂(configMeasure μm N) with hFS
  set SB : ℝ := ∫ U : Config N G, wilsonAction χ U
    ∂(configMeasure μm N) with hSB
  set z : ℝ := realZ (N := N) μm β χ with hzdef
  set Cov : ℝ := FS - A0 * SB with hCov
  -- blocos
  have hRf : |A - A0 + β * FS| ≤ C * (β ^ 2 * B ^ 2) :=
    abs_integral_secondOrder (N := N) μm mχ hβ hβB hχ hB mf hf
  have hRz : |z - 1 + β * SB| ≤ 1 * (β ^ 2 * B ^ 2) := by
    have h := abs_integral_secondOrder (N := N) μm mχ hβ hβB hχ hB
      (g := fun _ : Config N G => (1 : ℝ)) (K := 1) measurable_const
      (fun _ => by norm_num)
    simp only [one_mul] at h
    have hone : (∫ _U : Config N G, (1 : ℝ) ∂(configMeasure μm N)) = 1 := by
      rw [integral_const]; simp
    rw [hone] at h
    rw [hzdef]; unfold realZ
    simpa using h
  have hCovB : |Cov| ≤ 2 * C * B := by
    rw [hCov, hFS, hA0, hSB]
    exact abs_cov_integral_le (N := N) μm mχ hχ hB mf hf
  have hden1 : |z - 1| ≤ β * B := by
    have h := abs_integral_mul_weight_sub_le (N := N) μm mχ hβ hχ hB
      (g := fun _ : Config N G => (1 : ℝ)) (K := 1) measurable_const
      (fun _ => by norm_num)
    simp only [one_mul] at h
    have hone : (∫ _U : Config N G, (1 : ℝ) ∂(configMeasure μm N)) = 1 := by
      rw [integral_const]; simp
    rw [hone] at h
    rw [hzdef]; unfold realZ
    simpa using h
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
          rw [hzdef]; unfold realZ
          exact integral_mono (integrable_const _) hwint hlow
  have hzinv : z⁻¹ ≤ Real.exp (β * B) := by
    have h := inv_le_inv_of_le (Real.exp_pos _) hzlow
    rwa [← Real.exp_neg, neg_neg] at h
  -- identidade E
  have hE0 : gibbsExpectation (N := N) μm 0 χ f = A0 :=
    gibbsExpectation_zero (N := N) μm χ f
  have hE0FS : gibbsExpectation (N := N) μm 0 χ
      (fun U => f U * wilsonAction χ U) = FS :=
    gibbsExpectation_zero (N := N) μm χ _
  have hE0S : gibbsExpectation (N := N) μm 0 χ
      (fun U => wilsonAction χ U) = SB :=
    gibbsExpectation_zero (N := N) μm χ _
  have hEβ : gibbsExpectation (N := N) μm β χ f = A / z := rfl
  rw [hEβ, hE0, hE0FS, hE0S]
  have hdiff : A / z - A0 + β * (FS - A0 * SB)
      = (A - A0 * z + β * (FS - A0 * SB) * z) / z := by
    field_simp
    ring
  rw [hdiff, abs_div, abs_of_pos hz]
  have hnum : |A - A0 * z + β * (FS - A0 * SB) * z|
      ≤ 4 * C * (β ^ 2 * B ^ 2) := by
    have hid : A - A0 * z + β * (FS - A0 * SB) * z
        = (A - A0 + β * FS) - A0 * (z - 1 + β * SB)
          + β * (FS - A0 * SB) * (z - 1) := by ring
    have hA0abs : |A0| ≤ C := by
      rw [hA0]
      have := abs_cov_integral_le (N := N) μm mχ hχ hB mf hf
      -- só precisamos de |∫f| ≤ C; reprova direta:
      clear this
      have hint : Integrable f (configMeasure μm N) := by
        refine (integrable_const C).mono' mf.aestronglyMeasurable ?_
        filter_upwards with U
        rw [Real.norm_eq_abs]; exact hf U
      calc |∫ U : Config N G, f U ∂(configMeasure μm N)|
          ≤ ∫ U : Config N G, ‖f U‖ ∂(configMeasure μm N) := by
            have h1 := norm_integral_le_integral_norm
              (μ := configMeasure μm N) (f := f)
            rwa [Real.norm_eq_abs] at h1
        _ ≤ ∫ _U : Config N G, C ∂(configMeasure μm N) := by
            refine integral_mono hint.norm (integrable_const _) fun U => ?_
            rw [Real.norm_eq_abs]; exact hf U
        _ = C := by simp
    calc |A - A0 * z + β * (FS - A0 * SB) * z|
        = |(A - A0 + β * FS) - A0 * (z - 1 + β * SB)
            + β * (FS - A0 * SB) * (z - 1)| := by rw [hid]
      _ ≤ |A - A0 + β * FS| + |A0 * (z - 1 + β * SB)|
            + |β * (FS - A0 * SB) * (z - 1)| := by
          calc |_| ≤ |(A - A0 + β * FS) - A0 * (z - 1 + β * SB)|
                + |β * (FS - A0 * SB) * (z - 1)| := abs_add _ _
            _ ≤ _ := by
                refine add_le_add ?_ le_rfl
                exact abs_sub _ _
      _ ≤ C * (β ^ 2 * B ^ 2) + C * (β ^ 2 * B ^ 2)
            + 2 * C * (β ^ 2 * B ^ 2) := by
          refine add_le_add (add_le_add hRf ?_) ?_
          · rw [abs_mul]
            calc |A0| * |z - 1 + β * SB| ≤ C * (1 * (β ^ 2 * B ^ 2)) :=
                  mul_le_mul hA0abs hRz (abs_nonneg _) hC
              _ = C * (β ^ 2 * B ^ 2) := by ring
          · rw [abs_mul, abs_mul, abs_of_nonneg hβ]
            calc β * |FS - A0 * SB| * |z - 1|
                ≤ β * (2 * C * B) * (β * B) := by
                  refine mul_le_mul ?_ hden1 (abs_nonneg _) ?_
                  · exact mul_le_mul_of_nonneg_left hCovB hβ
                  · positivity
              _ = 2 * C * (β ^ 2 * B ^ 2) := by ring
      _ = 4 * C * (β ^ 2 * B ^ 2) := by ring
  calc |A - A0 * z + β * (FS - A0 * SB) * z| / z
      = |A - A0 * z + β * (FS - A0 * SB) * z| * z⁻¹ :=
        div_eq_mul_inv _ _
    _ ≤ (4 * C * (β ^ 2 * B ^ 2)) * Real.exp (β * B) := by
        refine mul_le_mul hnum hzinv (inv_nonneg.mpr hz.le) ?_
        positivity
    _ = 4 * C * B ^ 2 * β ^ 2 * Real.exp (β * B) := by ring

/-- **Corolário-janela: constante absoluta.** Para β·B ≤ 1:
    |⟨f⟩_β − ⟨f⟩₀ + β·Cov₀| ≤ 4·e·C·B²·β². -/
theorem abs_gibbsExpectation_taylor_remainder_window [NeZero N]
    [Fintype (Site N)]
    (mχ : Measurable χ) {β B C : ℝ} (hβ : 0 ≤ β) (hβB : β * B ≤ 1)
    (hχ : ∀ g : G, χ g ≤ 1)
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f : Config N G → ℝ} (mf : Measurable f) (hf : ∀ U, |f U| ≤ C) :
    |gibbsExpectation (N := N) μm β χ f
      - gibbsExpectation (N := N) μm 0 χ f
      + β * (gibbsExpectation (N := N) μm 0 χ
              (fun U => f U * wilsonAction χ U)
            - gibbsExpectation (N := N) μm 0 χ f
              * gibbsExpectation (N := N) μm 0 χ
                  (fun U => wilsonAction χ U))|
      ≤ 4 * Real.exp 1 * C * B ^ 2 * β ^ 2 := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hf (trivialConfig N G))
  have hB0 : 0 ≤ B :=
    le_trans (wilsonAction_nonneg χ hχ (trivialConfig N G)) (hB _)
  have h := abs_gibbsExpectation_taylor_remainder
    (N := N) μm mχ hβ hβB hχ hB mf hf
  have hexp : Real.exp (β * B) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr hβB
  calc _ ≤ 4 * C * B ^ 2 * β ^ 2 * Real.exp (β * B) := h
    _ ≤ 4 * C * B ^ 2 * β ^ 2 * Real.exp 1 := by
        refine mul_le_mul_of_nonneg_left hexp ?_
        positivity
    _ = 4 * Real.exp 1 * C * B ^ 2 * β ^ 2 := by ring

end Measure

end LatticeGauge
