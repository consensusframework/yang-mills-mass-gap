-- RGFlow_Work/ConvergenceRegion.lean
-- Phase 2: Renormalization Group Flow
-- Convergence region definition for RG flow theorems

namespace RGFlow

-- Constants frozen by Phase 2 kickoff
def g0 : ℝ := 1.18      -- Maximum coupling (from Phase 1)
def a_max : ℝ := 0.2    -- Maximum lattice spacing (fm)

-- Hooks for additional lattice QCD conditions (stubs for now)
-- These will be refined as needed during numerical validation
axiom lattice_spacing_valid : ℝ → Prop
axiom coupling_in_nonperturbative_regime : ℝ → Prop

-- Main convergence region predicate
-- This defines the domain where our RG flow theorems apply
def in_convergence_region (g a : ℝ) : Prop :=
  0 < g ∧ g ≤ g0 ∧
  0 < a ∧ a ≤ a_max ∧
  lattice_spacing_valid a ∧
  coupling_in_nonperturbative_regime g

-- Physical interpretation:
-- - g ∈ (0, 1.18]: Strong coupling regime (Phase 1 validated)
-- - a ∈ (0, 0.2 fm]: Lattice spacing range (typical for lattice QCD)
-- - Additional conditions ensure numerical stability and physical validity

end RGFlow
