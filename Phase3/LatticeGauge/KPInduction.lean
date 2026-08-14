/-
LatticeGauge/KPInduction.lean — stone 47c, GATE A, increment 1:
NONNEGATIVITY, PARTIAL SUMS AND THE SUM SWAP
(architecture: Sol/GPT-5.6; execution: Fable).

The analysis chapter opens: S_M (the finite partial sum of the
rooted cluster coefficients) and X_M (the partial sum of the G
kernels) are defined, every layer is proved nonnegative under
pointwise nonnegative activities (the FIRST time hρ enters the
stone-47 formal chain), and the exact sum swap
X_M(γ₀) = Σ_η incompat(γ₀,η)·ρ(η)·S_M(η) is recorded — the identity
through which the simultaneous induction motive will flow.
NOT here: the domain extension inequality (the red-tape step),
the truncated exponential, the KP induction, the β ≤ 1/40000
specialization (increments 2+ / Gates B, C); no Summable, no
limits, no log Z. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.UrsellCoefficients
import LatticeGauge.PolymerTreeBound
import LatticeGauge.KPCoefficients
import LatticeGauge.RootDecomposition
import LatticeGauge.KPEnumerations
import LatticeGauge.KPOrderedDecomposition
import LatticeGauge.KPWeightFactorization
import LatticeGauge.KPRootedTransport
import LatticeGauge.KPBlockSum
import LatticeGauge.KPMarkedBlock
import LatticeGauge.KPPartitionCount
import LatticeGauge.KPStratification

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## 47c-A.1 — the finite partial sums -/

/-- S_M: the finite partial sum of the rooted cluster
    coefficients (no limit is taken anywhere in stone 47c). -/
noncomputable def kpPartialSum (M : ℕ) (ρ : Polymer N → ℝ)
    (γ : Polymer N) : ℝ :=
  ∑ n ∈ Finset.range (M + 1), kpTreeCoeff n ρ γ

/-- X_M: the partial sum of the G kernels. -/
noncomputable def kpX (M : ℕ) (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) : ℝ :=
  ∑ m ∈ Finset.range (M + 1), kpG ρ γ₀ m

/-! ## 47c-A.2 — nonnegativity (hρ enters the chain for the first
    time; everything before this file is sign-free) -/

theorem rootedTreeSum_nonneg {ρ : Polymer N → ℝ}
    (hρ : ∀ γ, 0 ≤ ρ γ) (n : ℕ) (γ₀ : Polymer N) :
    0 ≤ rootedTreeSum n ρ γ₀ :=
  Finset.sum_nonneg fun γ _ =>
    Finset.sum_nonneg fun ET _ =>
      rootedTreeWeight_nonneg hρ γ₀ γ ET

theorem kpTreeCoeff_nonneg {ρ : Polymer N → ℝ}
    (hρ : ∀ γ, 0 ≤ ρ γ) (n : ℕ) (γ₀ : Polymer N) :
    0 ≤ kpTreeCoeff n ρ γ₀ :=
  div_nonneg (rootedTreeSum_nonneg hρ n γ₀) (Nat.cast_nonneg _)

theorem kpG_nonneg {ρ : Polymer N → ℝ}
    (hρ : ∀ γ, 0 ≤ ρ γ) (m : ℕ) (γ₀ : Polymer N) :
    0 ≤ kpG ρ γ₀ m :=
  Finset.sum_nonneg fun η _ =>
    mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hρ η))
      (kpTreeCoeff_nonneg hρ m η)

theorem kpPartialSum_nonneg {ρ : Polymer N → ℝ}
    (hρ : ∀ γ, 0 ≤ ρ γ) (M : ℕ) (γ : Polymer N) :
    0 ≤ kpPartialSum M ρ γ :=
  Finset.sum_nonneg fun n _ => kpTreeCoeff_nonneg hρ n γ

theorem kpX_nonneg {ρ : Polymer N → ℝ}
    (hρ : ∀ γ, 0 ≤ ρ γ) (M : ℕ) (γ₀ : Polymer N) :
    0 ≤ kpX M ρ γ₀ :=
  Finset.sum_nonneg fun m _ => kpG_nonneg hρ m γ₀

/-! ## 47c-A.3 — the exact sum swap (the identity the simultaneous
    induction motive flows through; no inequality here) -/

/-- X_M(γ₀) = Σ_η incompat(γ₀,η)·ρ(η)·S_M(η) — pure finite sum
    commutation, valid for arbitrary ρ. -/
theorem kpX_eq_sum_partial (M : ℕ) (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) :
    kpX M ρ γ₀
      = ∑ η : Polymer N,
          (incompatibilityIndicator γ₀ η : ℝ) * ρ η
            * kpPartialSum M ρ η := by
  unfold kpX kpG kpPartialSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun η _ => ?_)
  rw [Finset.mul_sum]

/-- Monotonicity of the partial sums in M (under hρ) — the shape
    stone 48 will consume together with the uniform bound. -/
theorem kpPartialSum_mono {ρ : Polymer N → ℝ}
    (hρ : ∀ γ, 0 ≤ ρ γ) {M M' : ℕ} (h : M ≤ M') (γ : Polymer N) :
    kpPartialSum M ρ γ ≤ kpPartialSum M' ρ γ :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset.mpr (by omega))
    (fun n _ _ => kpTreeCoeff_nonneg hρ n γ)

end LatticeGauge
