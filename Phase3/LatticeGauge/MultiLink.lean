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
  set e : ι ≃ Set.range ℓ := Equiv.ofInjective ℓ hℓ with he
  -- 1. split: links selecionados × complemento
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (μ := fun _ : Link N => μm) (· ∈ Set.range ℓ)
  -- 2. fst: projetar fora o complemento (probabilidade ⇒ fator 1)
  have hfst : MeasurePreserving
      (Prod.fst : ((∀ _ : {x : Link N // x ∈ Set.range ℓ}, G) ×
        (∀ _ : {x : Link N // ¬ x ∈ Set.range ℓ}, G)) → _)
      ((Measure.pi fun _ : {x : Link N // x ∈ Set.range ℓ} => μm).prod
        (Measure.pi fun _ : {x : Link N // ¬ x ∈ Set.range ℓ} => μm))
      (Measure.pi fun _ : {x : Link N // x ∈ Set.range ℓ} => μm) := by
    refine ⟨measurable_fst, ?_⟩
    rw [Measure.map_fst_prod]
    simp
  -- 3. reindex: Set.range ℓ → ι
  have hre := measurePreserving_piCongrLeft
    (μ := fun _ : ι => μm) e.symm
  -- 4. composição
  have hcomp := (hre.comp hfst).comp hsplit
  -- 5. a composta é exatamente U ↦ (fun i => U (ℓ i))
  have hco : (⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => G) e.symm)) ∘
      (Prod.fst ∘ ⇑(MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : Link N => G) (· ∈ Set.range ℓ)))
      = fun U : Config N G => fun i => U (ℓ i) := by
    funext U
    funext i
    have h := MeasurableEquiv.piCongrLeft_apply_apply e.symm
      ((MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : Link N => G) (· ∈ Set.range ℓ)) U).1 (e i)
    simpa [Equiv.symm_apply_apply, he] using h
  rw [← hco]
  exact hcomp

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
        exact MeasureTheory.integral_fintype_prod_eq_prod f

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
