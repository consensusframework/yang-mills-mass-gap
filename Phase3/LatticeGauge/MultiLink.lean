/-
LatticeGauge/MultiLink.lean — Phase 3, fourteenth stone.

n-LINK INDEPENDENCE: any finite injective family of links has joint law
equal to the product measure, and products of single-link observables
factorize. Architecture: Sol (GPT-5.6) — split (piEquivPiSubtypeProd),
project (fst of prod, complement is probability), reindex
(piCongrLeft). Execution: Claude Fable 5. Judge: CI.

EPISTEMIC NOTE (Sol's veto, recorded): this does NOT give
⟨Wilson loop⟩₀ = ∏ character integrals — χ does not distribute over
group multiplication. The correct follow-up (stone 15) is: the holonomy
of distinct links is Haar-distributed, hence ⟨W⟩₀ = ∫ χ dμ.
NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.Beta0
import LatticeGauge.SingleLink

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]
variable [MeasurableSpace G] (μm : Measure G) [SigmaFinite μm]
  [IsProbabilityMeasure μm]

/-- **Proved: the joint law of any finite injective family of links is
    the product measure.** -/
theorem measurePreserving_multiLink [NeZero N]
    {ι : Type*} [Fintype ι]
    (ℓ : ι → Link N) (hℓ : Function.Injective ℓ) :
    MeasurePreserving
      (fun U : Config N G => fun i => U (ℓ i))
      (configMeasure μm N)
      (Measure.pi fun _ : ι => μm) := by
  classical
  have hmeas_full : Measurable fun U : Config N G => fun i => U (ℓ i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (ℓ i)
  refine ⟨hmeas_full, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.map_apply hmeas_full (MeasurableSet.univ_pi hs)]
  set F : Link N → Set G := fun a =>
    if h : a ∈ Set.range ℓ
    then s ((Equiv.ofInjective ℓ hℓ).symm ⟨a, h⟩)
    else Set.univ with hF
  have hpre : (fun U : Config N G => fun i => U (ℓ i)) ⁻¹'
      (Set.pi Set.univ s) = Set.pi Set.univ F := by
    ext U
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hU a
      by_cases h : a ∈ Set.range ℓ
      · rw [hF]
        simp only [dif_pos h]
        have ha : ℓ ((Equiv.ofInjective ℓ hℓ).symm ⟨a, h⟩) = a :=
          Equiv.apply_ofInjective_symm hℓ ⟨a, h⟩
        rw [← ha]
        exact hU _
      · rw [hF]
        simp [dif_neg h]
    · intro hFU i
      have h := hFU (ℓ i)
      rw [hF] at h
      have hmem : ℓ i ∈ Set.range ℓ := ⟨i, rfl⟩
      simp only [dif_pos hmem] at h
      rwa [Equiv.ofInjective_symm_apply] at h
  rw [hpre]
  unfold configMeasure
  rw [Measure.pi_pi]
  rw [← Finset.prod_subset
    (Finset.subset_univ (Finset.image ℓ Finset.univ)) ?_,
    Finset.prod_image (fun i _ j _ h => hℓ h)]
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hmem : ℓ i ∈ Set.range ℓ := ⟨i, rfl⟩
    rw [hF]
    simp only [dif_pos hmem]
    rw [Equiv.ofInjective_symm_apply]
  · intro a _ ha
    have hnot : ¬ a ∈ Set.range ℓ := by
      simpa [Set.mem_range, Finset.mem_image] using ha
    rw [hF]
    simp [dif_neg hnot]

/-- **Proved: n-point factorization.** For a finite injective family of
    links, ∫ ∏ᵢ fᵢ(U ℓᵢ) = ∏ᵢ ∫ fᵢ dμ. -/
theorem integral_multiLink [NeZero N]
    {ι : Type*} [Fintype ι]
    (ℓ : ι → Link N) (hℓ : Function.Injective ℓ)
    (f : ι → G → ℝ) (mf : ∀ i, Measurable (f i)) :
    ∫ U : Config N G, ∏ i, f i (U (ℓ i)) ∂(configMeasure μm N)
      = ∏ i, ∫ g, f i g ∂μm := by
  classical
  have hmp := measurePreserving_multiLink (N := N) μm ℓ hℓ
  have hmeas : Measurable fun U : Config N G => fun i => U (ℓ i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (ℓ i)
  have hintmeas : AEStronglyMeasurable
      (fun y : ι → G => ∏ i, f i (y i))
      (Measure.pi fun _ : ι => μm) := by
    exact (Finset.measurable_prod Finset.univ
      fun i _ => (mf i).comp (measurable_pi_apply i)).aestronglyMeasurable
  calc ∫ U : Config N G, ∏ i, f i (U (ℓ i)) ∂(configMeasure μm N)
      = ∫ y : ι → G, ∏ i, f i (y i)
          ∂(Measure.map (fun U : Config N G => fun i => U (ℓ i))
            (configMeasure μm N)) := by
        exact (integral_map hmeas.aemeasurable
          (by rw [hmp.map_eq]; exact hintmeas)).symm
    _ = ∫ y : ι → G, ∏ i, f i (y i)
          ∂(Measure.pi fun _ : ι => μm) := by
        rw [hmp.map_eq]
    _ = ∏ i, ∫ g, f i g ∂μm := by
        letI : MeasureSpace G := ⟨μm⟩
        exact MeasureTheory.integral_fintype_prod_eq_prod (f := f)

/-- **Proved: at β = 0 the Gibbs expectation of a product of
    single-link observables over distinct links is the product of the
    character integrals.** -/
theorem gibbsExpectation_multi_zero [NeZero N] [Fintype (Site N)]
    (χ : G → ℝ) {ι : Type*} [Fintype ι]
    (ℓ : ι → Link N) (hℓ : Function.Injective ℓ)
    (f : ι → G → ℝ) (mf : ∀ i, Measurable (f i)) :
    gibbsExpectation (N := N) μm 0 χ (fun U => ∏ i, f i (U (ℓ i)))
      = ∏ i, linkCharacterIntegral μm (f i) := by
  rw [gibbsExpectation_zero (N := N) μm χ]
  exact integral_multiLink (N := N) μm ℓ hℓ f mf

end LatticeGauge
