/-
LatticeGauge/KPBarrierConnectorPositive.lean — PEDRA 50, Gate
50-A9 (module 1/3, editorial split 50-A9E; architecture: Sol;
execution: Fable).

A9.1/A9.2 — the FILTERED positive connector coefficient (the
barrier information preserved under the natAbs domination) and
the forbidden-root coefficient/envelope. Finite dominations only:
  signed connector ≤ positive filtered connector ≤ global B⁺,
plus P/Q symmetry and nonnegativity. The occurrence-marking
argument lives in KPBarrierMarkedRoot; the series and capstones
in KPBarrierMarkedSeries.

NOT here (hard hold): no tilted activity, no exp(λ·card), no
tupleTotalCard, no WalkBarrierSeparated, no tail in n, no
exp(-n)/q^n/rate, no two-root KP, no covariance, no
SimpleGraph.dist/edist/cdist/confinedLengths, no clustering, no
thermodynamic limit, no continuum, no mass gap, no Clay claim.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.KPAbsoluteUnrooted

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## A9.1 — the filtered positive connector -/

noncomputable def kpAbsConnectorUnrootedCoeff (k : ℕ)
    (ρ : Polymer N → ℝ) (P Q : Polymer N → Prop) : ℝ :=
  (∑ δ : Fin k → Polymer N,
      if TupleHitsBothForbidden P Q δ then
        (((ursellCoeff (N := N) (fun i => (δ i).val)).natAbs : ℕ) : ℝ)
          * ∏ i : Fin k, ρ (δ i)
      else 0)
    / ((Nat.factorial k : ℕ) : ℝ)

/-- The positive tuple weight (named so every lemma below is
    first-order; definitionally the summand above). -/
noncomputable def kpAbsSummand {k : ℕ} (ρ : Polymer N → ℝ)
    (δ : Fin k → Polymer N) : ℝ :=
  ((ursellCoeff (N := N) (fun i => (δ i).val)).natAbs : ℝ)
    * ∏ i : Fin k, ρ (δ i)

theorem kpAbsConnectorUnrootedCoeff_eq (k : ℕ)
    (ρ : Polymer N → ℝ) (P Q : Polymer N → Prop) :
    kpAbsConnectorUnrootedCoeff k ρ P Q
      = (∑ δ : Fin k → Polymer N,
          if TupleHitsBothForbidden P Q δ then kpAbsSummand ρ δ
          else 0)
        / ((Nat.factorial k : ℕ) : ℝ) := rfl

theorem kpAbsSummand_nonneg {k : ℕ} {ρ : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (δ : Fin k → Polymer N) :
    0 ≤ kpAbsSummand ρ δ :=
  mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg (fun i _ => hρ (δ i)))

theorem kpAbsConnectorUnrootedCoeff_zero (ρ : Polymer N → ℝ)
    (P Q : Polymer N → Prop) :
    kpAbsConnectorUnrootedCoeff 0 ρ P Q = 0 := by
  unfold kpAbsConnectorUnrootedCoeff
  rw [Finset.univ_unique, Finset.sum_singleton,
    if_neg (fun h => h.1 (fun i => i.elim0)), zero_div]

theorem kpAbsConnectorUnrootedCoeff_nonneg (k : ℕ)
    {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    (P Q : Polymer N → Prop) :
    0 ≤ kpAbsConnectorUnrootedCoeff k ρ P Q := by
  rw [kpAbsConnectorUnrootedCoeff_eq]
  refine div_nonneg (Finset.sum_nonneg (fun δ _ => ?_))
    (Nat.cast_nonneg _)
  by_cases h : TupleHitsBothForbidden P Q δ
  · rw [if_pos h]; exact kpAbsSummand_nonneg hρ δ
  · rw [if_neg h]

/-- **P/Q symmetry** (the connector predicate is a conjunction). -/
theorem kpAbsConnectorUnrootedCoeff_symm (k : ℕ)
    (ρ : Polymer N → ℝ) (P Q : Polymer N → Prop) :
    kpAbsConnectorUnrootedCoeff k ρ P Q
      = kpAbsConnectorUnrootedCoeff k ρ Q P := by
  unfold kpAbsConnectorUnrootedCoeff
  congr 1
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  by_cases h : TupleHitsBothForbidden P Q δ
  · rw [if_pos h,
      if_pos (show TupleHitsBothForbidden Q P δ from ⟨h.2, h.1⟩)]
  · rw [if_neg h,
      if_neg (fun h' : TupleHitsBothForbidden Q P δ =>
        h ⟨h'.2, h'.1⟩)]

/-- **Filtered domination**: the signed connector is dominated
    coefficient-wise WITH the barrier information preserved. -/
theorem abs_kpConnectorUnrootedCoeff_le_filtered (k : ℕ)
    (z : Polymer N → ℝ) (P Q : Polymer N → Prop) :
    |kpConnectorUnrootedCoeff (N := N) k z P Q|
      ≤ kpAbsConnectorUnrootedCoeff k (fun η => |z η|) P Q := by
  unfold kpConnectorUnrootedCoeff kpAbsConnectorUnrootedCoeff
  rw [abs_div, Nat.abs_cast]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _)
    (Finset.sum_le_sum (fun δ _ => ?_))
  by_cases h : TupleHitsBothForbidden P Q δ
  · rw [if_pos h, if_pos h, abs_mul, Finset.abs_prod,
      ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  · rw [if_neg h, if_neg h, abs_zero]

/-- **Forgetting the filter**: filtered ≤ global B⁺ (A8). -/
theorem kpAbsConnectorUnrootedCoeff_le_abs (k : ℕ)
    {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    (P Q : Polymer N → Prop) :
    kpAbsConnectorUnrootedCoeff k ρ P Q
      ≤ kpAbsUnrootedCoeff k ρ := by
  unfold kpAbsConnectorUnrootedCoeff kpAbsUnrootedCoeff
  refine div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun δ _ => ?_)) (by positivity)
  by_cases h : TupleHitsBothForbidden P Q δ
  · rw [if_pos h]
  · rw [if_neg h]
    exact mul_nonneg (Nat.cast_nonneg _)
      (Finset.prod_nonneg (fun i _ => hρ (δ i)))

/-! ## A9.2 — the forbidden-root coefficient and envelope -/

noncomputable def kpForbiddenRootCoeff (n : ℕ)
    (ρ : Polymer N → ℝ) (P : Polymer N → Prop) : ℝ :=
  ∑ γ₀ : Polymer N,
    if P γ₀ then 0
    else ρ γ₀ * kpUrsellCoeff n ρ γ₀

noncomputable def kpForbiddenRootEnvelope
    (ρ a : Polymer N → ℝ) (P : Polymer N → Prop) : ℝ :=
  ∑ γ₀ : Polymer N,
    if P γ₀ then 0
    else ρ γ₀ * Real.exp (a γ₀)

theorem kpForbiddenRootCoeff_nonneg (n : ℕ)
    {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    (P : Polymer N → Prop) :
    0 ≤ kpForbiddenRootCoeff n ρ P := by
  refine Finset.sum_nonneg (fun γ₀ _ => ?_)
  by_cases h : P γ₀
  · rw [if_pos h]
  · rw [if_neg h]
    exact mul_nonneg (hρ γ₀) (kpUrsellCoeff_nonneg n hρ γ₀)

theorem kpForbiddenRootEnvelope_nonneg
    {ρ a : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    (P : Polymer N → Prop) :
    0 ≤ kpForbiddenRootEnvelope ρ a P := by
  refine Finset.sum_nonneg (fun γ₀ _ => ?_)
  by_cases h : P γ₀
  · rw [if_pos h]
  · rw [if_neg h]
    exact mul_nonneg (hρ γ₀) (Real.exp_pos _).le

end LatticeGauge
