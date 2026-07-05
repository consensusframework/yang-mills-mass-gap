/-
LatticeGauge/GaugeSymmetry.lean — Phase 3, seventh stone.

Gauge invariance of the GIBBS EXPECTATION itself: for a bi-invariant
(Haar) probability measure on G and a class-function character,
⟨f ∘ gauge⟩ = ⟨f⟩ for EVERY integrable observable. Physics does not
see the gauge. NO axioms; everything proved.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.GaugeInvariance
import LatticeGauge.Gibbs
import LatticeGauge.Expectation

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- The gauge action on configurations, as a measurable equivalence:
    coordinatewise left multiplication by g(x) and right multiplication
    by g(x+μ)⁻¹. -/
noncomputable def gaugeEquiv [NeZero N] (g : GaugeTransform N G) :
    Config N G ≃ᵐ Config N G :=
  MeasurableEquiv.piCongrRight fun ℓ : Link N =>
    (MeasurableEquiv.mulLeft (g ℓ.1)).trans
      (MeasurableEquiv.mulRight (g (shift ℓ.1 ℓ.2))⁻¹)

@[simp] theorem gaugeEquiv_apply [NeZero N]
    (g : GaugeTransform N G) (U : Config N G) :
    gaugeEquiv g U = gaugeAct g U := rfl

variable (μm : Measure G) [SigmaFinite μm]

/-- **Proved:** for a bi-invariant measure on G, the gauge action
    preserves the product measure on configurations. -/
theorem measurePreserving_gaugeAct [NeZero N]
    [μm.IsMulLeftInvariant] [μm.IsMulRightInvariant]
    (g : GaugeTransform N G) :
    MeasurePreserving (gaugeAct g)
      (configMeasure (G := G) μm N) (configMeasure (G := G) μm N) := by
  have h : ∀ ℓ : Link N,
      MeasurePreserving
        (fun u : G => g ℓ.1 * u * (g (shift ℓ.1 ℓ.2))⁻¹) μm μm := by
    intro ℓ
    exact (measurePreserving_mul_right μm (g (shift ℓ.1 ℓ.2))⁻¹).comp
      (measurePreserving_mul_left μm (g ℓ.1))
  have := MeasureTheory.measurePreserving_pi
    (fun _ : Link N => μm) (fun _ : Link N => μm)
    (fun ℓ => h ℓ)
  exact this

/-- **Proved: GAUGE INVARIANCE OF THE GIBBS EXPECTATION.**
    For Haar-like (bi-invariant) μ and a class function χ,
    ⟨f ∘ gauge⟩ = ⟨f⟩ for every observable f. -/
theorem gibbsExpectation_gauge_invariant [NeZero N] [Fintype (Site N)]
    [μm.IsMulLeftInvariant] [μm.IsMulRightInvariant]
    {χ : G → ℝ} (hχ : IsClassFunction χ) (β : ℝ)
    (g : GaugeTransform N G) (f : Config N G → ℝ) :
    gibbsExpectation (N := N) μm β χ (fun U => f (gaugeAct g U))
      = gibbsExpectation (N := N) μm β χ f := by
  have hmp := measurePreserving_gaugeAct (N := N) μm g
  have hemb : MeasurableEmbedding (gaugeAct (N := N) g) := by
    have := (gaugeEquiv (N := N) g).measurableEmbedding
    simpa [funext_iff] using this
  unfold gibbsExpectation
  congr 1
  calc ∫ U : Config N G, f (gaugeAct g U) * gibbsWeight β χ U
        ∂(configMeasure μm N)
      = ∫ U : Config N G, f (gaugeAct g U) * gibbsWeight β χ (gaugeAct g U)
        ∂(configMeasure μm N) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        unfold gibbsWeight
        rw [wilsonAction_gauge_invariant χ hχ g U]
    _ = ∫ V : Config N G, f V * gibbsWeight β χ V ∂(configMeasure μm N) :=
        hmp.integral_comp hemb _

end LatticeGauge
