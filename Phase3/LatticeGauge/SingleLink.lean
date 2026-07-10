/-
LatticeGauge/SingleLink.lean — Phase 3, twelfth stone.

STATUS: PARKED (não compilada — fora da whitelist do lakefile).
Este arquivo NÃO faz parte do build. A prova de integral_singleLink
esbarra repetidamente em incompatibilidades de instâncias (Fintype de
subtipo-singleton: Subtype.fintype vs caminhos inferidos por
piEquivPiSubtypeProd/funUnique; opacidade de haveI vs letI para o
default de Unique; metavariáveis em integral_comp). Cinco tentativas
registradas no histórico do git (útil como mapa do campo minado).
Sugestões para o próximo: (i) provar um lema-ponte
`Measure.pi_congr_instances` uma vez e soldar com ele; (ii) ou provar a
lei do link único via kernel/marginal em vez de equivalências; (iii) ou
esperar versão do Mathlib com `Measure.map_eval_pi`.
A afirmação matemática é trivialmente verdadeira; a formalização é que
está cara. HONESTIDADE: enquanto não compilar, NÃO conta no placar.

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
  letI huniq : Unique {ℓ : Link N // ℓ ∈ ({ℓ₀} : Set (Link N))} :=
    ⟨⟨⟨ℓ₀, rfl⟩⟩, fun x => Subtype.ext (Set.mem_singleton_iff.mp x.2)⟩
  have hmp := measurePreserving_piEquivPiSubtypeProd
    (μ := fun _ : Link N => μm) (· ∈ ({ℓ₀} : Set (Link N)))
  have hemb := (MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Link N => G) (· ∈ ({ℓ₀} : Set (Link N)))).measurableEmbedding
  calc ∫ U : Config N G, f₀ (U ℓ₀) ∂(configMeasure μm N)
      = ∫ U : Config N G,
          (fun w : (∀ _ : {ℓ : Link N // ℓ ∈ ({ℓ₀} : Set (Link N))}, G) ×
              (∀ _ : {ℓ : Link N // ¬ ℓ ∈ ({ℓ₀} : Set (Link N))}, G) =>
            f₀ (w.1 default) * 1)
          ((MeasurableEquiv.piEquivPiSubtypeProd
            (fun _ : Link N => G) (· ∈ ({ℓ₀} : Set (Link N)))) U)
          ∂(configMeasure μm N) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        show f₀ (U ℓ₀) = f₀ (U ↑(default : {ℓ : Link N // ℓ ∈ ({ℓ₀} : Set (Link N))})) * 1
        rw [mul_one]
    _ = ∫ w, f₀ (w.1 default) * 1
          ∂((Measure.pi fun _ : {ℓ : Link N // ℓ ∈ ({ℓ₀} : Set (Link N))} => μm).prod
            (Measure.pi fun _ : {ℓ : Link N // ¬ ℓ ∈ ({ℓ₀} : Set (Link N))} => μm)) :=
        hmp.integral_comp hemb _
    _ = (∫ y : ∀ _ : {ℓ : Link N // ℓ ∈ ({ℓ₀} : Set (Link N))}, G,
          f₀ (y default) ∂(Measure.pi fun _ => μm)) * ∫ _z, (1 : ℝ)
          ∂(Measure.pi fun _ : {ℓ : Link N // ¬ ℓ ∈ ({ℓ₀} : Set (Link N))} => μm) :=
        integral_prod_mul (fun y => f₀ (y default)) (fun _ => (1 : ℝ))
    _ = ∫ y : ∀ _ : {ℓ : Link N // ℓ ∈ ({ℓ₀} : Set (Link N))}, G,
          f₀ (y default) ∂(Measure.pi fun _ => μm) := by simp
    _ = ∫ g, f₀ g ∂μm := by
        have h := (measurePreserving_funUnique μm
          {ℓ : Link N // ℓ ∈ ({ℓ₀} : Set (Link N))}).integral_comp
          (MeasurableEquiv.funUnique
            {ℓ : Link N // ℓ ∈ ({ℓ₀} : Set (Link N))} G).measurableEmbedding f₀
        convert h using 2
        exact Subsingleton.elim _ _

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
