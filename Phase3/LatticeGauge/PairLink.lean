/-
LatticeGauge/PairLink.lean — Phase 3, thirteenth stone.

Two DISTINCT links are independent Haar variables: the joint law of
(U ℓ₁, U ℓ₂) under the product configuration measure is μ ⊗ μ, and
two-point functions of single-link observables factorize at β = 0.
Route: direct marginal (Sol style), no subtypes. NO axioms.
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

/-- **Proved: the joint law of two distinct links is μ ⊗ μ.** -/
theorem measurePreserving_pairLink [NeZero N] {ℓ₁ ℓ₂ : Link N}
    (hne : ℓ₁ ≠ ℓ₂) :
    MeasurePreserving (fun U : Config N G => (U ℓ₁, U ℓ₂))
      (configMeasure μm N) (μm.prod μm) := by
  classical
  have hmeas : Measurable fun U : Config N G => (U ℓ₁, U ℓ₂) :=
    (measurable_pi_apply ℓ₁).prod_mk (measurable_pi_apply ℓ₂)
  refine ⟨hmeas, ?_⟩
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply hmeas (hs.prod ht)]
  have hpre : (fun U : Config N G => (U ℓ₁, U ℓ₂)) ⁻¹' (s ×ˢ t)
      = Set.pi Set.univ
          (Function.update
            (Function.update (fun _ : Link N => (Set.univ : Set G)) ℓ₁ s)
            ℓ₂ t) := by
    ext U
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi, Set.mem_univ,
      forall_true_left, true_implies]
    constructor
    · rintro ⟨h1, h2⟩ ℓ
      by_cases e2 : ℓ = ℓ₂
      · subst e2
        simpa [Function.update_apply] using h2
      · by_cases e1 : ℓ = ℓ₁
        · subst e1
          simpa [Function.update_apply, e2] using h1
        · simp [Function.update_apply, e1, e2]
    · intro h
      refine ⟨?_, ?_⟩
      · have := h ℓ₁
        simpa [Function.update_apply, hne] using this
      · have := h ℓ₂
        simpa [Function.update_apply] using this
  rw [hpre]
  unfold configMeasure
  rw [Measure.pi_pi]
  have hval : ∀ ℓ : Link N,
      μm (Function.update
        (Function.update (fun _ : Link N => (Set.univ : Set G)) ℓ₁ s)
        ℓ₂ t ℓ)
      = if ℓ = ℓ₂ then μm t else if ℓ = ℓ₁ then μm s else 1 := by
    intro ℓ
    by_cases e2 : ℓ = ℓ₂
    · simp [Function.update_apply, e2]
    · by_cases e1 : ℓ = ℓ₁
      · simp [Function.update_apply, e1, e2]
      · simp [Function.update_apply, e1, e2]
  simp_rw [hval]
  rw [← Finset.prod_subset
    (Finset.subset_univ ({ℓ₁, ℓ₂} : Finset (Link N))) ?_]
  · rw [Finset.prod_insert (by simpa using hne), Finset.prod_singleton]
    have hℓ₁ : (if ℓ₁ = ℓ₂ then μm t else if ℓ₁ = ℓ₁ then μm s else 1)
        = μm s := by simp [hne]
    have hℓ₂ : (if ℓ₂ = ℓ₂ then μm t else if ℓ₂ = ℓ₁ then μm s else 1)
        = μm t := by simp
    rw [hℓ₁, hℓ₂]
  · intro ℓ _ hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    simp [hnot.1, hnot.2]

/-- **Proved: two-point factorization.** For distinct links,
    ∫ f(U ℓ₁)·g(U ℓ₂) dμ^⊗ = (∫ f dμ)·(∫ g dμ). -/
theorem integral_pairLink [NeZero N] {ℓ₁ ℓ₂ : Link N} (hne : ℓ₁ ≠ ℓ₂)
    {f₀ g₀ : G → ℝ} (mf₀ : Measurable f₀) (mg₀ : Measurable g₀) :
    ∫ U : Config N G, f₀ (U ℓ₁) * g₀ (U ℓ₂) ∂(configMeasure μm N)
      = (∫ g, f₀ g ∂μm) * ∫ g, g₀ g ∂μm := by
  have hmp := measurePreserving_pairLink (N := N) μm hne
  have hmeas : Measurable fun U : Config N G => (U ℓ₁, U ℓ₂) :=
    (measurable_pi_apply ℓ₁).prod_mk (measurable_pi_apply ℓ₂)
  calc ∫ U : Config N G, f₀ (U ℓ₁) * g₀ (U ℓ₂) ∂(configMeasure μm N)
      = ∫ p : G × G, f₀ p.1 * g₀ p.2
          ∂(Measure.map (fun U : Config N G => (U ℓ₁, U ℓ₂))
            (configMeasure μm N)) := by
        exact (integral_map hmeas.aemeasurable
          ((mf₀.comp measurable_fst).mul
            (mg₀.comp measurable_snd)).aestronglyMeasurable).symm
    _ = ∫ p : G × G, f₀ p.1 * g₀ p.2 ∂(μm.prod μm) := by
        rw [hmp.map_eq]
    _ = (∫ g, f₀ g ∂μm) * ∫ g, g₀ g ∂μm := integral_prod_mul f₀ g₀

/-- **Proved: the two-point function at β = 0 factorizes exactly** —
    the connected correlator of distinct single-link observables is 0. -/
theorem gibbsExpectation_pair_zero [NeZero N] [Fintype (Site N)]
    (χ : G → ℝ) {ℓ₁ ℓ₂ : Link N} (hne : ℓ₁ ≠ ℓ₂)
    {f₀ g₀ : G → ℝ} (mf₀ : Measurable f₀) (mg₀ : Measurable g₀) :
    gibbsExpectation (N := N) μm 0 χ (fun U => f₀ (U ℓ₁) * g₀ (U ℓ₂))
      = linkCharacterIntegral μm f₀ * linkCharacterIntegral μm g₀ := by
  rw [gibbsExpectation_zero (N := N) μm χ]
  exact integral_pairLink (N := N) μm hne mf₀ mg₀

end LatticeGauge
