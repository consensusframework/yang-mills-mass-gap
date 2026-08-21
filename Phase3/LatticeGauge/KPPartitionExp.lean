/-
LatticeGauge/KPPartitionExp.lean — stone 49C-V, Gate V-2a:
Z = e^C — THE PARTITION FUNCTION IS AN EXPONENTIAL
(architecture: Sol/GPT-5.6; execution: Fable).

SEMANTICS: "For 0 ≤ β ≤ 1/40000, the finite-volume partition
function equals the exponential of the absolutely convergent
signed unrooted Ursell series" — Z_β = exp(C_β), and Z_β > 0 as
a COROLLARY. This is a FINITE-VOLUME identity under small β.
It is NOT called: a solution of the mass gap, a proof of the
Clay problem, or a thermodynamic-limit cluster expansion.

The proof shows the TWO equalities separately:
(1) Z = typed gas — Stone 36 / 49C-I, full finite generality,
    smallness NOT used;
(2) typed gas = exp(cluster sum) — V-1 + the concrete KP key
    abstractKP_of_beta_le_one_div_40000: smallness enters
    EXACTLY here and nowhere else.
Positivity comes from Real.exp_pos through the identity — the
preexisting physical realZ_pos (Expectation.lean) is NOT used,
NOT imported by name, and NOT needed: nonvanishing is now an
output of the cluster expansion, not an input.
NOT touched (deferred to V-2b): logPartition, Real.log,
Real.log_exp, derivatives, Gibbs expectation, thermodynamic
limit, infinite-volume pressure, clustering, mass gap.
NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.KPTypedGas
import LatticeGauge.KPSpecialization
import LatticeGauge.KPClusterExpansion

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **CAPSTONE V-2a — Z = e^C**: for 0 ≤ β ≤ 1/40000, the
    finite-volume partition function equals the exponential of
    the absolutely convergent signed unrooted Ursell series. -/
theorem realZ_eq_exp_tsum_unrooted {β : ℝ} (hβ : 0 ≤ β)
    {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) :
    realZ (N := N) μm β χ
      = Real.exp (∑' n, kpSignedUnrootedCoeff (N := N) n
          (fun η => polymerWeight (N := N) μm β χ η.val)) :=
  calc realZ (N := N) μm β χ
      -- (1) Z = typed gas: Stone 36 / 49C-I — smallness NOT used
      = typedPolymerGas (N := N)
          (fun η => polymerWeight (N := N) μm β χ η.val) :=
        realZ_eq_typed_polymer_gas μm hβ mχ hχabs
      -- (2) typed gas = exp: V-1 + concrete KP key — smallness
      -- enters EXACTLY here
    _ = Real.exp (∑' n, kpSignedUnrootedCoeff n
          (fun η => polymerWeight (N := N) μm β χ η.val)) :=
        typedPolymerGas_eq_exp_tsum_of_KP
          (fun γ => Nat.cast_nonneg _)
          (abstractKP_of_beta_le_one_div_40000 μm hβ mχ
            hχabs hsmall)

/-- **Z_β > 0 as a corollary of the cluster expansion** — the
    physical realZ_pos is never consulted. -/
theorem realZ_pos_of_clusterExpansion {β : ℝ} (hβ : 0 ≤ β)
    {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) :
    0 < realZ (N := N) μm β χ := by
  rw [realZ_eq_exp_tsum_unrooted μm hβ mχ hχabs hsmall]
  exact Real.exp_pos _

/-- Nonvanishing — an output of the expansion, not an input. -/
theorem realZ_ne_zero_of_clusterExpansion {β : ℝ} (hβ : 0 ≤ β)
    {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) :
    realZ (N := N) μm β χ ≠ 0 :=
  ne_of_gt (realZ_pos_of_clusterExpansion μm hβ mχ hχabs hsmall)

end LatticeGauge
