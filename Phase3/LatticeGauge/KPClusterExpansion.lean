/-
LatticeGauge/KPClusterExpansion.lean — stone 49C-V, Gate V-1:
THE SEMANTIC BRIDGE — typed gas = exp(cluster sum)
(architecture: Sol/GPT-5.6; execution: Fable).

One rewrite and its corollaries, nothing else: the 49C-II
decomposition typedPolymerGas_eq_sum_gasCoeff (whose cut
card(Polymer N)+1 coincides EXACTLY with the engine's) composed
with the 49C-IV capstone sum_kpGasCoeff_eq_exp_tsum(_of_KP).

SEMANTICS: "Under the abstract KP hypothesis, the finite typed
hard-core polymer gas equals the exponential of the absolutely
convergent signed unrooted Ursell series" — typed gas =
exp(cluster sum); and typed gas > 0, with positivity as a
COROLLARY of Real.exp_pos, never a hypothesis.

NOT touched (deferred to V-2): realZ, logPartition, Real.log,
β, χ, polymerWeight, β ≤ 1/40000, realZ_pos, Gibbs positivity,
thermodynamic limit, clustering, mass gap. z is NOT specialized
to polymerWeight here. No new summability (49B consumed through
the IV-4 interface), no new combinatorics, no nonvanishing
hypothesis anywhere. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.KPTypedGas
import LatticeGauge.KPGasCoefficients
import LatticeGauge.KPExpIdentity

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-- **Typed gas = exp(cluster sum), general form**: absolute
    summability as the only analytic hypothesis. -/
theorem typedPolymerGas_eq_exp_tsum (z : Polymer N → ℝ)
    (habs : Summable
      (fun n => |kpSignedUnrootedCoeff (N := N) n z|)) :
    typedPolymerGas (N := N) z
      = Real.exp (∑' n, kpSignedUnrootedCoeff n z) := by
  rw [typedPolymerGas_eq_sum_gasCoeff]
  exact sum_kpGasCoeff_eq_exp_tsum z habs

/-- **CAPSTONE V-1**: under the abstract KP hypothesis, the
    finite typed hard-core polymer gas equals the exponential of
    the absolutely convergent signed unrooted Ursell series. -/
theorem typedPolymerGas_eq_exp_tsum_of_KP
    {z a : Polymer N → ℝ} (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a) :
    typedPolymerGas (N := N) z
      = Real.exp (∑' n, kpSignedUnrootedCoeff n z) := by
  rw [typedPolymerGas_eq_sum_gasCoeff]
  exact sum_kpGasCoeff_eq_exp_tsum_of_KP ha hKP

/-- **Positivity as a corollary** — the gas is an exponential,
    hence positive. No Gibbs input, no hypothesis. -/
theorem typedPolymerGas_pos_of_KP
    {z a : Polymer N → ℝ} (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a) :
    0 < typedPolymerGas (N := N) z := by
  rw [typedPolymerGas_eq_exp_tsum_of_KP ha hKP]
  exact Real.exp_pos _

/-- **Nonvanishing arrives late to the meeting** — as a
    consequence, never a premise. -/
theorem typedPolymerGas_ne_zero_of_KP
    {z a : Polymer N → ℝ} (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a) :
    typedPolymerGas (N := N) z ≠ 0 :=
  ne_of_gt (typedPolymerGas_pos_of_KP ha hKP)

end LatticeGauge
