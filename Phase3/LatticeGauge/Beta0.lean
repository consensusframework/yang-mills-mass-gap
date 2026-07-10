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

end LatticeGauge
