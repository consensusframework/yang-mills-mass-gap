/-
YangMills/Basic.lean — reconstructed stub (Etapa 2)

The original YangMills.Basic was LOST with the previous repository.
This stub reconstructs the shared abstract types referenced across
Phase 1 as PHYSICAL ASSUMPTIONS (Box 3, see VERIFICATION_STATUS.md):
they are opaque placeholders, not constructions.
-/
import Mathlib

namespace YangMills

/-- ASSUMPTION: spacetime manifold (opaque placeholder). -/
axiom Manifold : Type

/-- ASSUMPTION: gauge field configuration space over a manifold. -/
axiom GaugeField : Manifold → Type

/-- ASSUMPTION: gauge connection (opaque placeholder). -/
axiom GaugeConnection : Type

/-- ASSUMPTION: density matrix (opaque placeholder). -/
axiom DensityMatrix : Type

/-- ASSUMPTION: quantum state space (opaque placeholder). -/
axiom QuantumState : Type

end YangMills
