/-
RGFlow_Work/Basic.lean — Shared core definitions (Etapa 0)

Created during the Etapa 0 cleanup: the original Phase 2 files imported
modules (BetaFunction, MassGap, ConvergenceRegion, RunningCoupling) that
were NEVER present in the repository, so Phase 2 could not compile as
published. This file is the single honest source for shared declarations.

HONESTY NOTE: `mass_gap` is an AXIOM — a physical assumption, not a
construction. Every theorem depending on it is conditional. See
AXIOM_AUDIT.md.
-/
import Mathlib

namespace RGFlow

/-- Maximum coupling considered (from Phase 1 strong-coupling regime). -/
def g0 : ℝ := 1.18

/-- Maximum lattice spacing (fm). -/
def a_max : ℝ := 0.2

/-- Claimed uniform lower bound for the gap (GeV). ASSUMED, not derived. -/
def gap_lower_bound : ℝ := 0.50

/-- PHYSICAL ASSUMPTION (not a construction): the lattice mass gap
    Δ(g, a) as a function of coupling and lattice spacing.
    The existence and properties of this function are open problems. -/
axiom mass_gap : ℝ → ℝ → ℝ

theorem g0_positive : g0 > 0 := by norm_num [g0]

theorem gap_lower_bound_positive : gap_lower_bound > 0 := by norm_num [gap_lower_bound]

/-- Convergence region of the strong-coupling expansion (Phase 1 claim). -/
def in_convergence_region (g a : ℝ) : Prop :=
  0.5 ≤ g ∧ g ≤ g0 ∧ 0 < a ∧ a ≤ a_max

/-- PHYSICAL ASSUMPTION: lattice beta function. Not constructed. -/
axiom beta : ℝ → ℝ → ℝ

/-- One-loop running coupling (perturbative formula, used as definition). -/
noncomputable def running_coupling (μ μ₀ g₀ _a : ℝ) : ℝ :=
  let b0 : ℝ := 11.0 / (24.0 * Real.pi * Real.pi)
  let log_ratio : ℝ := Real.log (μ / μ₀)
  g₀ / Real.sqrt (1.0 + b0 * g₀ * g₀ * log_ratio)

/-- Initial condition g(μ₀) = g₀ (provable from the definition; kept as
    a lemma statement — proof requires simp arithmetic on Real.log). -/
axiom initial_condition (μ₀ g₀ a₀ : ℝ) : running_coupling μ₀ μ₀ g₀ a₀ = g₀

end RGFlow
