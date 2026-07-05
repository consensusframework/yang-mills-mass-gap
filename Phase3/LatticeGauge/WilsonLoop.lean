/-
LatticeGauge/WilsonLoop.lean — Phase 3, fourth stone.

Wilson loops: holonomy along arbitrary lattice paths and the theorem
that CLOSED loops are gauge-invariant observables. All proved by
induction; no axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.GaugeInvariance

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

/-- Shift a site by one unit backwards in direction `μ`. -/
def shiftBack (x : Site N) (μ : Dir) [NeZero N] : Site N :=
  match μ with
  | ⟨0, _⟩ => (x.1 - 1, x.2.1, x.2.2.1, x.2.2.2)
  | ⟨1, _⟩ => (x.1, x.2.1 - 1, x.2.2.1, x.2.2.2)
  | ⟨2, _⟩ => (x.1, x.2.1, x.2.2.1 - 1, x.2.2.2)
  | ⟨3, _⟩ => (x.1, x.2.1, x.2.2.1, x.2.2.2 - 1)

/-- **Proved:** shifting back then forward returns to the start. -/
@[simp] theorem shift_shiftBack [NeZero N] (x : Site N) (μ : Dir) :
    shift (shiftBack x μ) μ = x := by
  fin_cases μ <;> simp [shift, shiftBack, sub_add_cancel]

/-- A path step: a direction together with an orientation
    (`true` = forward, `false` = backward). -/
abbrev Step := Dir × Bool

/-- Endpoint of a path started at `x`. -/
def pathEnd [NeZero N] (x : Site N) : List Step → Site N
  | [] => x
  | (μ, true) :: p => pathEnd (shift x μ) p
  | (μ, false) :: p => pathEnd (shiftBack x μ) p

/-- A path is closed when it returns to its starting site. -/
def IsClosed [NeZero N] (x : Site N) (p : List Step) : Prop :=
  pathEnd x p = x

/-- Holonomy (ordered product of link variables) along a path. -/
def holonomy [NeZero N] (U : Config N G) (x : Site N) : List Step → G
  | [] => 1
  | (μ, true) :: p => U (x, μ) * holonomy U (shift x μ) p
  | (μ, false) :: p => (U (shiftBack x μ, μ))⁻¹ * holonomy U (shiftBack x μ) p

/-- **Proved (by induction):** under a gauge transformation the holonomy
    transforms as H ↦ g(start) · H · g(end)⁻¹. -/
theorem holonomy_gaugeAct [NeZero N]
    (g : GaugeTransform N G) (U : Config N G) (x : Site N) (p : List Step) :
    holonomy (gaugeAct g U) x p
      = g x * holonomy U x p * (g (pathEnd x p))⁻¹ := by
  induction p generalizing x with
  | nil => simp [holonomy, pathEnd]
  | cons s p ih =>
    obtain ⟨μ, b⟩ := s
    cases b
    · simp only [holonomy, pathEnd, gaugeAct, ih, shift_shiftBack]
      group
    · simp only [holonomy, pathEnd, gaugeAct, ih]
      group

/-- The Wilson loop observable: χ applied to the holonomy. -/
def wilsonLoop [NeZero N] (χ : G → ℝ) (U : Config N G)
    (x : Site N) (p : List Step) : ℝ :=
  χ (holonomy U x p)

/-- **Proved: GAUGE INVARIANCE OF CLOSED WILSON LOOPS.**
    For any class function χ and any closed lattice path, the Wilson
    loop is invariant under all gauge transformations. -/
theorem wilsonLoop_gauge_invariant [NeZero N]
    (χ : G → ℝ) (hχ : IsClassFunction χ)
    (g : GaugeTransform N G) (U : Config N G)
    (x : Site N) (p : List Step) (hp : IsClosed x p) :
    wilsonLoop χ (gaugeAct g U) x p = wilsonLoop χ U x p := by
  unfold wilsonLoop
  rw [holonomy_gaugeAct, hp]
  exact hχ (g x) (holonomy U x p)

end LatticeGauge
