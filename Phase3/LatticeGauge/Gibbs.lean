/-
LatticeGauge/Gibbs.lean — Phase 3, third stone.

Gibbs weight and partition function of lattice gauge theory over an
arbitrary probability measure on the gauge group (Haar on SU(n) being
the intended instance). NO axioms; all statements proved.
-/
import Mathlib
import LatticeGauge.Basic

open MeasureTheory ENNReal

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

/-- Boltzmann–Gibbs weight e^{-β S(U)}. -/
noncomputable def gibbsWeight [NeZero N] [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) (U : Config N G) : ℝ :=
  Real.exp (-β * wilsonAction χ U)

/-- **Proved:** the Gibbs weight is strictly positive. -/
theorem gibbsWeight_pos [NeZero N] [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) (U : Config N G) :
    0 < gibbsWeight β χ U :=
  Real.exp_pos _

/-- **Proved:** for β ≥ 0 and a normalized character (χ ≤ 1),
    the Gibbs weight is at most 1. -/
theorem gibbsWeight_le_one [NeZero N] [Fintype (Site N)]
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (hχ : ∀ g : G, χ g ≤ 1)
    (U : Config N G) :
    gibbsWeight β χ U ≤ 1 := by
  have hS := wilsonAction_nonneg χ hχ U
  have : -β * wilsonAction χ U ≤ 0 := by
    have := mul_nonneg hβ hS
    linarith
  simpa [gibbsWeight] using Real.exp_le_one_iff.mpr this

section PartitionFunction

variable [MeasurableSpace G] (μ : Measure G)

/-- Partition function as a lower integral over the product measure
    on configurations (no integrability side conditions needed). -/
noncomputable def partitionFunction [NeZero N] [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) : ℝ≥0∞ :=
  ∫⁻ U : Config N G, ENNReal.ofReal (gibbsWeight β χ U)
    ∂(Measure.pi fun _ : Link N => μ)

variable [SigmaFinite μ]

/-- **Proved:** Z ≤ 1 for β ≥ 0, normalized character, probability μ. -/
theorem partitionFunction_le_one [NeZero N] [Fintype (Site N)]
    [IsProbabilityMeasure μ]
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (hχ : ∀ g : G, χ g ≤ 1) :
    partitionFunction μ β χ ≤ 1 := by
  unfold partitionFunction
  calc ∫⁻ U : Config N G, ENNReal.ofReal (gibbsWeight β χ U)
        ∂(Measure.pi fun _ : Link N => μ)
      ≤ ∫⁻ _ : Config N G, 1 ∂(Measure.pi fun _ : Link N => μ) := by
        exact lintegral_mono fun U => ENNReal.ofReal_le_one.mpr
          (gibbsWeight_le_one hβ hχ U)
    _ = 1 := by simp

/-- **Proved:** if the action is uniformly bounded by B, then
    Z ≥ e^{-βB} — in particular the partition function does not vanish. -/
theorem le_partitionFunction [NeZero N] [Fintype (Site N)]
    [IsProbabilityMeasure μ]
    {β B : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ}
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B) :
    ENNReal.ofReal (Real.exp (-β * B)) ≤ partitionFunction μ β χ := by
  unfold partitionFunction
  calc ENNReal.ofReal (Real.exp (-β * B))
      = ∫⁻ _ : Config N G, ENNReal.ofReal (Real.exp (-β * B))
          ∂(Measure.pi fun _ : Link N => μ) := by simp
    _ ≤ ∫⁻ U : Config N G, ENNReal.ofReal (gibbsWeight β χ U)
          ∂(Measure.pi fun _ : Link N => μ) := by
        refine lintegral_mono fun U => ENNReal.ofReal_le_ofReal ?_
        have h1 : -β * B ≤ -β * wilsonAction χ U := by
          have := hB U
          nlinarith
        simpa [gibbsWeight] using Real.exp_le_exp.mpr h1

/-- **Proved:** under a uniform action bound, Z ≠ 0. -/
theorem partitionFunction_ne_zero [NeZero N] [Fintype (Site N)]
    [IsProbabilityMeasure μ]
    {β B : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ}
    (hB : ∀ U : Config N G, wilsonAction χ U ≤ B) :
    partitionFunction μ β χ ≠ 0 := by
  have h := le_partitionFunction μ hβ hB
  intro hz
  rw [hz] at h
  simp only [le_zero_iff, ENNReal.ofReal_eq_zero] at h
  exact absurd h (not_le.mpr (Real.exp_pos _))

end PartitionFunction

end LatticeGauge
