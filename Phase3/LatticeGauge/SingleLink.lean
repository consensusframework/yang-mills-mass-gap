/-
LatticeGauge/SingleLink.lean — Phase 3, twelfth stone.

The ATOMIC BRICK of the character expansion: under the product measure,
a single link variable is exactly Haar-distributed, so single-link
observables integrate to their group integral:
⟨f(U_ℓ)⟩ = ∫_G f dμ. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.Beta0

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]
variable [MeasurableSpace G] (μm : Measure G) [SigmaFinite μm]
  [IsProbabilityMeasure μm]

/-- **Proved: the law of a single link is the group measure.**
    ∫ f(U_ℓ) dμ^⊗links = ∫ f dμ. -/
theorem integral_singleLink [NeZero N] (ℓ₀ : Link N)
    {f₀ : G → ℝ} (mf₀ : Measurable f₀) :
    ∫ U : Config N G, f₀ (U ℓ₀) ∂(configMeasure μm N)
      = ∫ g, f₀ g ∂μm := by
  classical
  letI : DecidablePred (· ∈ ({ℓ₀} : Set (Link N))) := fun _ => Classical.dec _
  letI : Fintype {ℓ : Link N // ℓ ∈ ({ℓ₀} : Set (Link N))} :=
    Subtype.fintype _
  letI : Fintype {ℓ : Link N // ¬ ℓ ∈ ({ℓ₀} : Set (Link N))} :=
    Subtype.fintype _
  haveI huniq : Unique {ℓ : Link N // ℓ ∈ ({ℓ₀} : Set (Link N))} := by
    refine ⟨⟨⟨ℓ₀, rfl⟩⟩, ?_⟩
    rintro ⟨x, hx⟩
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    rfl
  set E : Config N G ≃ᵐ
      G × (∀ _ : {ℓ : Link N // ¬ ℓ ∈ ({ℓ₀} : Set (Link N))}, G) :=
    (MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Link N => G) (· ∈ ({ℓ₀} : Set (Link N)))).trans
      ((MeasurableEquiv.funUnique
        {ℓ : Link N // ℓ ∈ ({ℓ₀} : Set (Link N))} G).prodCongr
        (MeasurableEquiv.refl _)) with hE
  have hmpE : MeasurePreserving E (configMeasure μm N)
      (μm.prod (Measure.pi
        fun _ : {ℓ : Link N // ¬ ℓ ∈ ({ℓ₀} : Set (Link N))} => μm)) := by
    have h1 := measurePreserving_piEquivPiSubtypeProd
      (μ := fun _ : Link N => μm) (· ∈ ({ℓ₀} : Set (Link N)))
    have h2 := (measurePreserving_funUnique μm
      {ℓ : Link N // ℓ ∈ ({ℓ₀} : Set (Link N))}).prod
      (MeasurePreserving.id (Measure.pi
        fun _ : {ℓ : Link N // ¬ ℓ ∈ ({ℓ₀} : Set (Link N))} => μm))
    exact h2.comp h1
  have hemb := E.measurableEmbedding
  calc ∫ U : Config N G, f₀ (U ℓ₀) ∂(configMeasure μm N)
      = ∫ U : Config N G, (fun w => f₀ w.1 * 1) (E U)
        ∂(configMeasure μm N) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        show f₀ (U ℓ₀) = f₀ ((E U).1) * 1
        rw [mul_one, hE]
        rfl
    _ = ∫ w, f₀ w.1 * 1
        ∂(μm.prod (Measure.pi
          fun _ : {ℓ : Link N // ¬ ℓ ∈ ({ℓ₀} : Set (Link N))} => μm)) :=
        hmpE.integral_comp hemb (fun w => f₀ w.1 * 1)
    _ = (∫ g, f₀ g ∂μm) * ∫ _z, (1 : ℝ)
        ∂(Measure.pi
          fun _ : {ℓ : Link N // ¬ ℓ ∈ ({ℓ₀} : Set (Link N))} => μm) :=
        integral_prod_mul f₀ (fun _ => (1 : ℝ))
    _ = ∫ g, f₀ g ∂μm := by simp

/-- The single-link character integral — the atomic coefficient of the
    strong-coupling character expansion. -/
noncomputable def linkCharacterIntegral (χ : G → ℝ) : ℝ := ∫ g, χ g ∂μm

/-- **Proved:** at β = 0 the Gibbs expectation of a single-link
    character observable is exactly the character integral:
    ⟨χ(U_ℓ)⟩₀ = ∫_G χ dμ. -/
theorem gibbsExpectation_singleLink_zero [NeZero N] [Fintype (Site N)]
    (χ ψ : G → ℝ) (mψ : Measurable ψ) (ℓ₀ : Link N) :
    gibbsExpectation (N := N) μm 0 χ (fun U => ψ (U ℓ₀))
      = linkCharacterIntegral μm ψ := by
  rw [gibbsExpectation_zero (N := N) μm χ]
  exact integral_singleLink (N := N) μm ℓ₀ mψ

end LatticeGauge
