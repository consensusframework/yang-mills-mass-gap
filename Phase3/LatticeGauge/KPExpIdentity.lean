/-
LatticeGauge/KPExpIdentity.lean — stone 49C-IV, Gate IV-4: THE
CEREMONY (architecture: Sol/GPT-5.6; execution: Fable).

One thin specialization and nothing else: the abstract exp
engine (ExpRecurrenceEngine.lean, UNTOUCHED by this gate)
receives the five certificates of the model —
  A₀ = 1               kpGasCoeff_zero            (49C-II);
  B₀ = 0               kpSignedUnrootedCoeff_zero (49A);
  finite support of A  kpGasCoeff_eq_zero_of_gt   (49C-II);
  ABSOLUTE summability summable_abs_kpSignedUnrootedCoeff (49B);
  the recurrence       kpGasCoeff_succ_recurrence (49C-III) —
and yields Σ Aₙ = exp(Σ' Bₙ).

SEMANTICS: "Under the abstract KP hypothesis, the finite-volume
all-graph coefficient sum equals the exponential of the
absolutely convergent signed unrooted Ursell series."
NOT stated here (deliberately deferred to 49C-V, even though
49C-II would make the rewrite immediate): typedPolymerGas =
exp(…). NOT touched: realZ, logPartition, Real.log, β,
polymerWeight, χ, β ≤ 1/40000, positivity/nonvanishing,
thermodynamic limit, clustering, mass gap. NOT reopened:
root-component split, choose, factorial normalization, Cauchy
diagonal, tsum derivation, mean-value theorem — all consumed
through their interfaces. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.KPUnrooted
import LatticeGauge.KPGasCoefficients
import LatticeGauge.KPRootComponent
import LatticeGauge.ExpRecurrenceEngine

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-- **Σ Aₙ = exp(Σ' Bₙ), general form**: absolute summability of
    the unrooted series as the only analytic hypothesis. -/
theorem sum_kpGasCoeff_eq_exp_tsum (z : Polymer N → ℝ)
    (habs : Summable
      (fun n => |kpSignedUnrootedCoeff (N := N) n z|)) :
    (∑ n ∈ Finset.range (Fintype.card (Polymer N) + 1),
        kpGasCoeff n z)
      = Real.exp (∑' n, kpSignedUnrootedCoeff n z) :=
  sum_a_eq_exp_tsum_b
    (fun n => kpGasCoeff (N := N) n z)
    (fun n => kpSignedUnrootedCoeff (N := N) n z)
    (Fintype.card (Polymer N))
    (kpGasCoeff_zero z)
    (kpSignedUnrootedCoeff_zero z)
    (fun n hn => kpGasCoeff_eq_zero_of_gt n z hn)
    habs
    (fun n => kpGasCoeff_succ_recurrence n z)

/-- **CAPSTONE 49C-IV (concrete)**: under the abstract KP
    hypothesis, the finite-volume all-graph coefficient sum
    equals the exponential of the absolutely convergent signed
    unrooted Ursell series — Σ Aₙ = exp(Σ Bₙ). -/
theorem sum_kpGasCoeff_eq_exp_tsum_of_KP {z a : Polymer N → ℝ}
    (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (N := N)
      (fun η => |z η|) a) :
    (∑ n ∈ Finset.range (Fintype.card (Polymer N) + 1),
        kpGasCoeff n z)
      = Real.exp (∑' n, kpSignedUnrootedCoeff n z) :=
  sum_kpGasCoeff_eq_exp_tsum z
    (summable_abs_kpSignedUnrootedCoeff ha hKP)

end LatticeGauge
