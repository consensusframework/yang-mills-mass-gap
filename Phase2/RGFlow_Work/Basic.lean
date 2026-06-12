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

theorem gap_lower_bound_positive : gap_lower_bound > 0 := by
  norm_num [gap_lower_bound]

end RGFlow
