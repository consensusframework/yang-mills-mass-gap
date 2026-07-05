/-
LatticeGauge/WilsonExpectation.lean — Phase 3, sixth stone.

The Wilson loop expectation value: measurability of holonomies (by
induction), a uniform bound for the Wilson action (removing the ad-hoc
hB hypothesis), and the capstone |⟨W⟩| ≤ 1 combining all previous
stones. NO axioms; everything proved.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.WilsonLoop
import LatticeGauge.Expectation

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

/-- **Proved:** a bounded-below character gives a uniform bound for the
    Wilson action, valid for every configuration. -/
theorem exists_wilsonAction_bound [NeZero N] [Fintype (Site N)]
    {χ : G → ℝ} (hχ : ∀ g : G, -1 ≤ χ g) :
    ∃ B : ℝ, ∀ U : Config N G, wilsonAction χ U ≤ B := by
  refine ⟨∑ _x : Site N, ∑ _μ : Dir, ∑ _ν : Dir, (2 : ℝ), fun U => ?_⟩
  unfold wilsonAction
  refine Finset.sum_le_sum fun x _ => ?_
  refine Finset.sum_le_sum fun μ _ => ?_
  refine Finset.sum_le_sum fun ν _ => ?_
  by_cases h : μ.val < ν.val
  · simp only [h, if_true]
    linarith [hχ (plaquette U x μ ν)]
  · simp only [h, if_false]
    norm_num

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

/-- **Proved (by induction):** the holonomy along any path is a
    measurable function of the configuration. -/
theorem measurable_holonomy [NeZero N] (p : List Step) :
    ∀ x : Site N, Measurable fun U : Config N G => holonomy U x p := by
  induction p with
  | nil =>
    intro x
    simpa [holonomy] using (measurable_const : Measurable fun _ : Config N G => (1 : G))
  | cons s p ih =>
    intro x
    obtain ⟨μ, b⟩ := s
    cases b
    · simpa [holonomy] using ((measurable_pi_apply _).inv.mul (ih _))
    · simpa [holonomy] using ((measurable_pi_apply _).mul (ih _))

/-- **Proved:** the Wilson loop observable is measurable. -/
theorem measurable_wilsonLoop [NeZero N]
    {χ : G → ℝ} (mχ : Measurable χ) (x : Site N) (p : List Step) :
    Measurable fun U : Config N G => wilsonLoop χ U x p :=
  mχ.comp (measurable_holonomy p x)

/-- **CAPSTONE (proved): |⟨Wilson loop⟩| ≤ 1.**
    For β ≥ 0, a measurable character with |χ| ≤ 1 (e.g. the normalized
    real trace on SU(n)), and any probability measure on G, the Gibbs
    expectation of every Wilson loop has absolute value at most 1. -/
theorem abs_wilsonLoopExpectation_le_one [NeZero N] [Fintype (Site N)]
    (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]
    {χ : G → ℝ} (mχ : Measurable χ) {β : ℝ} (hβ : 0 ≤ β)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (x : Site N) (p : List Step) :
    |gibbsExpectation (N := N) μm β χ (fun U => wilsonLoop χ U x p)| ≤ 1 := by
  have hχ1 : ∀ g : G, χ g ≤ 1 := fun g => (abs_le.mp (hχabs g)).2
  have hχm1 : ∀ g : G, -1 ≤ χ g := fun g => (abs_le.mp (hχabs g)).1
  obtain ⟨B, hB⟩ := exists_wilsonAction_bound (N := N) hχm1
  exact abs_gibbsExpectation_le μm mχ hβ hχ1 hB
    (measurable_wilsonLoop mχ x p) (fun U => hχabs _)

end LatticeGauge
