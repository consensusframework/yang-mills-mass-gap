/-
LatticeGauge/KPLogPartition.lean — stone 49C-V, Gate V-2b: THE
LABEL — log Z_β = Σ' B_n (architecture: Sol/GPT-5.6; execution:
Fable).

SEMANTICS: "For 0 ≤ β ≤ 1/40000, the finite-volume log-partition
function equals the absolutely convergent signed unrooted Ursell
cluster series" — a FINITE-VOLUME cluster-expansion identity for
the log-partition function ("log-partition function", coherent
with LogPartitionResponse.lean — NOT called "free energy": the
−β⁻¹/volume conventions are not present).

The proof is three lines and MUST be: the definition of
logPartition consumed literally; V-2a as the sole source of
realZ = exp; Real.log_exp closing the log. Zero positivity
hypothesis, zero nonvanishing hypothesis, zero division, zero
derivative, zero new summability. The nonvanishing proof is not
even consulted — it arrived late, sat in the back row, and the
ceremony was already over.

NOT claimed: thermodynamic limit, pressure density limit,
infinite-volume analyticity, clustering/exponential decay, mass
gap, Clay problem solution. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.LogPartitionResponse
import LatticeGauge.KPPartitionExp

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **CAPSTONE 49C-V — the cluster expansion of the log-partition
    function**: for 0 ≤ β ≤ 1/40000, in finite volume,
    log Z_β = Σ' B_n(w_β). -/
theorem logPartition_eq_tsum_unrooted {β : ℝ} (hβ : 0 ≤ β)
    {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) :
    logPartition (N := N) μm β χ
      = ∑' n, kpSignedUnrootedCoeff (N := N) n
          (fun η => polymerWeight (N := N) μm β χ η.val) := by
  unfold logPartition
  rw [realZ_eq_exp_tsum_unrooted μm hβ mχ hχabs hsmall]
  exact Real.log_exp _

end LatticeGauge
