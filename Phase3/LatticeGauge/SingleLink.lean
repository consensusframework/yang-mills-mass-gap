/-
LatticeGauge/SingleLink.lean — Phase 3, twelfth stone.

ASSENTADA em colaboração inter-laboratórios (2026-07-10):
estratégia de Sol (GPT-5.6, OpenAI) — cilindro → marginal → integral_map,
sem subtipos — após 5 tentativas de Claude Fable 5 (Anthropic) na rota
piEquivPiSubtypeProd (histórico preservado no git como mapa do campo
minado). Execução e ajustes locais: Fable. Juiz: lake build no CI.
A rota vencedora foi a (ii) das sugestões da versão estacionada:
marginal direta, no nível natural da Measure.pi.

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

/-- Evaluation at a fixed link pushes the product configuration measure
forward to the one-link measure. (Route: Sol/GPT-5.6, cylinder → marginal.) -/
theorem measurePreserving_singleLink [NeZero N] (ℓ₀ : Link N) :
    MeasurePreserving (fun U : Config N G => U ℓ₀)
      (configMeasure μm N) μm := by
  classical
  refine ⟨measurable_pi_apply ℓ₀, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply ℓ₀) hs]
  change Measure.pi (fun _ : Link N => μm)
      ((Function.eval ℓ₀) ⁻¹' s) = μm s
  rw [Set.eval_preimage, Measure.pi_pi]
  simp [Function.update_apply, apply_ite μm, Finset.prod_ite_eq']

/-- **Proved: the law of a single link is the group measure.**
    ∫ f(U_ℓ) dμ^⊗links = ∫ f dμ. -/
theorem integral_singleLink [NeZero N] (ℓ₀ : Link N)
    {f₀ : G → ℝ} (mf₀ : Measurable f₀) :
    ∫ U : Config N G, f₀ (U ℓ₀) ∂(configMeasure μm N)
      = ∫ g, f₀ g ∂μm := by
  have hmp := measurePreserving_singleLink (N := N) μm ℓ₀
  calc
    ∫ U : Config N G, f₀ (U ℓ₀) ∂(configMeasure μm N)
        =
      ∫ g, f₀ g
        ∂Measure.map (fun U : Config N G => U ℓ₀)
          (configMeasure μm N) := by
      exact
        (integral_map
          (μ := configMeasure μm N)
          (φ := fun U : Config N G => U ℓ₀)
          (f := f₀)
          (measurable_pi_apply ℓ₀).aemeasurable
          mf₀.aestronglyMeasurable).symm
    _ = ∫ g, f₀ g ∂μm := by
      rw [hmp.map_eq]

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
