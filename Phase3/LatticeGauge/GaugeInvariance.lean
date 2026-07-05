/-
LatticeGauge/GaugeInvariance.lean — Phase 3, second stone.

THE structural theorem of lattice gauge theory: the Wilson action is
invariant under gauge transformations. NO axioms; fully proved.
-/
import Mathlib
import LatticeGauge.Basic

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

/-- A gauge transformation assigns a group element to every site. -/
abbrev GaugeTransform (N : ℕ) (G : Type*) := Site N → G

/-- Action of a gauge transformation on a configuration:
    U'_μ(x) = g(x) · U_μ(x) · g(x+μ)⁻¹. -/
def gaugeAct [NeZero N] (g : GaugeTransform N G) (U : Config N G) : Config N G :=
  fun ℓ => g ℓ.1 * U ℓ * (g (shift ℓ.1 ℓ.2))⁻¹

/-- **Proved:** lattice shifts in different directions commute. -/
theorem shift_comm [NeZero N] (x : Site N) (μ ν : Dir) :
    shift (shift x μ) ν = shift (shift x ν) μ := by
  fin_cases μ <;> fin_cases ν <;> rfl

/-- **Proved:** the plaquette transforms by conjugation:
    P'(x;μ,ν) = g(x) · P(x;μ,ν) · g(x)⁻¹. -/
theorem plaquette_gaugeAct [NeZero N]
    (g : GaugeTransform N G) (U : Config N G) (x : Site N) (μ ν : Dir) :
    plaquette (gaugeAct g U) x μ ν = g x * plaquette U x μ ν * (g x)⁻¹ := by
  simp only [plaquette, gaugeAct]
  rw [shift_comm x ν μ]
  group

/-- A class function: invariant under conjugation. -/
def IsClassFunction (χ : G → ℝ) : Prop :=
  ∀ (h u : G), χ (h * u * h⁻¹) = χ u

/-- **Proved: GAUGE INVARIANCE OF THE WILSON ACTION.**
    For any class function χ (e.g. the normalized real trace on SU(n)),
    S(U^g) = S(U) for every gauge transformation g. -/
theorem wilsonAction_gauge_invariant [NeZero N] [Fintype (Site N)]
    (χ : G → ℝ) (hχ : IsClassFunction χ)
    (g : GaugeTransform N G) (U : Config N G) :
    wilsonAction χ (gaugeAct g U) = wilsonAction χ U := by
  unfold wilsonAction
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun μ _ => ?_
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases h : μ.val < ν.val
  · simp only [h, if_true, plaquette_gaugeAct, hχ (g x) (plaquette U x μ ν)]
  · simp [h]

end LatticeGauge
