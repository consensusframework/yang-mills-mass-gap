/-
LatticeGauge/Beta0.lean — Phase 3, eleventh stone (part a).

The β = 0 (infinite-temperature) regime: the Gibbs state reduces to the
pure product (Haar) state. This is the trivial-but-real base camp of
the cluster expansion. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.WilsonLoop
import LatticeGauge.WilsonExpectation
import LatticeGauge.Translation

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

/-- **Proved:** at β = 0 the Gibbs weight is identically 1. -/
@[simp] theorem gibbsWeight_zero [NeZero N] [Fintype (Site N)]
    (χ : G → ℝ) (U : Config N G) :
    gibbsWeight 0 χ U = 1 := by
  unfold gibbsWeight
  simp

variable [MeasurableSpace G] (μm : Measure G) [SigmaFinite μm]
  [IsProbabilityMeasure μm]

/-- **Proved:** at β = 0 the real partition function equals 1. -/
theorem realZ_zero [NeZero N] [Fintype (Site N)] (χ : G → ℝ) :
    realZ (N := N) μm 0 χ = 1 := by
  unfold realZ
  simp

/-- **Proved: at β = 0 the Gibbs state IS the product (Haar) state:**
    ⟨f⟩ = ∫ f dμ^⊗links, for every observable. -/
theorem gibbsExpectation_zero [NeZero N] [Fintype (Site N)]
    (χ : G → ℝ) (f : Config N G → ℝ) :
    gibbsExpectation (N := N) μm 0 χ f
      = ∫ U : Config N G, f U ∂(configMeasure μm N) := by
  unfold gibbsExpectation
  rw [realZ_zero (N := N) μm χ]
  simp

/-! ## Independence: the seed of the cluster expansion -/

/-- An observable depends only on the links in `s`. -/
def DependsOnlyOn [NeZero N] (f : Config N G → ℝ) (s : Set (Link N)) : Prop :=
  ∀ U V : Config N G, (∀ ℓ ∈ s, U ℓ = V ℓ) → f U = f V

/-- **Proved: FACTORIZATION over disjoint supports.** Under the product
    measure, observables supported on `s` and on `sᶜ` are independent:
    ∫ f·g = (∫ f)·(∫ g). -/
theorem integral_mul_of_disjoint_support [NeZero N]
    (s : Set (Link N)) [DecidablePred (· ∈ s)]
    {f g : Config N G → ℝ}
    (hf : DependsOnlyOn f s) (hg : DependsOnlyOn g sᶜ)
    (mf : Measurable f) (mg : Measurable g) :
    ∫ U : Config N G, f U * g U ∂(configMeasure μm N)
      = (∫ U : Config N G, f U ∂(configMeasure μm N))
        * ∫ U : Config N G, g U ∂(configMeasure μm N) := by
  classical
  set e := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Link N => G) (· ∈ s) with he
  have hmp := measurePreserving_piEquivPiSubtypeProd
    (μ := fun _ : Link N => μm) (· ∈ s)
  set F : (∀ _ : {ℓ : Link N // ℓ ∈ s}, G) → ℝ :=
    fun y => f (fun ℓ => if h : ℓ ∈ s then y ⟨ℓ, h⟩ else 1) with hF
  set Gg : (∀ _ : {ℓ : Link N // ¬ ℓ ∈ s}, G) → ℝ :=
    fun z => g (fun ℓ => if h : ℓ ∈ s then 1 else z ⟨ℓ, h⟩) with hG
  have hFmeas : Measurable F := by
    apply mf.comp
    apply measurable_pi_lambda
    intro ℓ
    by_cases h : ℓ ∈ s
    · simpa [h] using measurable_pi_apply (⟨ℓ, h⟩ : {ℓ : Link N // ℓ ∈ s})
    · simpa [h] using measurable_const
  have hGmeas : Measurable Gg := by
    apply mg.comp
    apply measurable_pi_lambda
    intro ℓ
    by_cases h : ℓ ∈ s
    · simpa [h] using measurable_const
    · simpa [h] using measurable_pi_apply (⟨ℓ, h⟩ : {ℓ : Link N // ¬ ℓ ∈ s})
  have hfF : ∀ U : Config N G, f U = F ((e U).1) := by
    intro U
    apply hf
    intro ℓ hℓ
    simp [he, hF, MeasurableEquiv.piEquivPiSubtypeProd, hℓ]
  have hgG : ∀ U : Config N G, g U = Gg ((e U).2) := by
    intro U
    apply hg
    intro ℓ hℓ
    simp only [Set.mem_compl_iff] at hℓ
    simp [he, hG, MeasurableEquiv.piEquivPiSubtypeProd, hℓ]
  have hemb := e.measurableEmbedding
  have key : ∀ (φ : (∀ _ : {ℓ : Link N // ℓ ∈ s}, G) → ℝ)
      (ψ : (∀ _ : {ℓ : Link N // ¬ ℓ ∈ s}, G) → ℝ),
      ∫ U : Config N G, φ ((e U).1) * ψ ((e U).2) ∂(configMeasure μm N)
        = (∫ y, φ y ∂(Measure.pi fun _ => μm))
          * ∫ z, ψ z ∂(Measure.pi fun _ => μm) := by
    intro φ ψ
    calc ∫ U : Config N G, φ ((e U).1) * ψ ((e U).2) ∂(configMeasure μm N)
        = ∫ w, φ w.1 * ψ w.2
            ∂((Measure.pi fun _ : {ℓ : Link N // ℓ ∈ s} => μm).prod
              (Measure.pi fun _ : {ℓ : Link N // ¬ ℓ ∈ s} => μm)) :=
          hmp.integral_comp hemb (fun w => φ w.1 * ψ w.2)
      _ = _ := integral_prod_mul φ ψ
  have h1 := key F Gg
  have h2 := key F (fun _ => 1)
  have h3 := key (fun _ => 1) Gg
  have hint1 : ∫ _y : (∀ _ : {ℓ : Link N // ℓ ∈ s}, G), (1 : ℝ)
      ∂(Measure.pi fun _ => μm) = 1 := by simp
  have hint2 : ∫ _z : (∀ _ : {ℓ : Link N // ¬ ℓ ∈ s}, G), (1 : ℝ)
      ∂(Measure.pi fun _ => μm) = 1 := by simp
  rw [hint2, mul_one] at h2
  rw [hint1, one_mul] at h3
  have hFf : (∫ y, F y ∂(Measure.pi fun _ => μm))
      = ∫ U : Config N G, f U ∂(configMeasure μm N) := by
    rw [← h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    show F ((e U).1) = f U
    exact (hfF U).symm
  have hGg : (∫ z, Gg z ∂(Measure.pi fun _ => μm))
      = ∫ U : Config N G, g U ∂(configMeasure μm N) := by
    rw [← h3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    show Gg ((e U).2) = g U
    exact (hgG U).symm
  calc ∫ U : Config N G, f U * g U ∂(configMeasure μm N)
      = ∫ U : Config N G, F ((e U).1) * Gg ((e U).2) ∂(configMeasure μm N) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        show f U * g U = F ((e U).1) * Gg ((e U).2)
        rw [← hfF U, ← hgG U]
    _ = (∫ y, F y ∂(Measure.pi fun _ => μm))
        * ∫ z, Gg z ∂(Measure.pi fun _ => μm) := h1
    _ = (∫ U : Config N G, f U ∂(configMeasure μm N))
        * ∫ U : Config N G, g U ∂(configMeasure μm N) := by
        rw [hFf, hGg]

/-- **Proved: CLUSTERING AT β = 0.** Truncated correlations of
    observables with disjoint supports vanish identically at infinite
    temperature — the first proven instance of clustering in this
    repository (the trivial regime, honestly labelled). -/
theorem truncatedCorrelation_zero_beta_zero [NeZero N] [Fintype (Site N)]
    (χ : G → ℝ) (s : Set (Link N)) [DecidablePred (· ∈ s)]
    {f g : Config N G → ℝ}
    (hf : DependsOnlyOn f s) (hg : DependsOnlyOn g sᶜ)
    (mf : Measurable f) (mg : Measurable g) :
    truncatedCorrelation (N := N) μm 0 χ f g = 0 := by
  unfold truncatedCorrelation
  rw [gibbsExpectation_zero (N := N) μm χ,
    gibbsExpectation_zero (N := N) μm χ,
    gibbsExpectation_zero (N := N) μm χ,
    integral_mul_of_disjoint_support (N := N) μm s hf hg mf mg,
    sub_self]

end LatticeGauge
