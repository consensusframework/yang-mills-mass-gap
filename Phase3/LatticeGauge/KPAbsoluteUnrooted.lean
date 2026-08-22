/-
LatticeGauge/KPAbsoluteUnrooted.lean — PEDRA 50, Gate 50-A8:
ABSOLUTE UNROOTING — THE POSITIVE MAJORANT (architecture: Sol;
execution: Fable).

The missing link, and ONLY the missing link:
  connector coefficient ≤ positive unrooted coefficient
                        ≤ rooted KP majorant,
so that Σ' |connector| inherits the finite-root envelope
Σ_γ₀ ρ(γ₀)·exp(a γ₀) from the stone-47/48 KP machinery, consumed
— never redone. The (n+1) factor of the exact unrooting identity
stays visible (1/n! versus 1/(n+1)!), exactly as in 49A; tuples
with repeated polymers remain distinct by occurrence — no orbits,
no quotients, no stabilizers, no representatives.

NOT here (hard hold): no tilted activity, no exp(λ·card), no
tupleTotalCard, no WalkBarrierSeparated, no tail in n, no exp(-n)
or q^n or any rate, no root marked by a barrier, no two-root KP
(KPMarkedBlock is stone-47 tree combinatorics, NOT a barrier
root), no Stone 45 on clusters, no covariance, no second
insertion, no SimpleGraph.dist/edist, no clustering, no
thermodynamic limit, no continuum, no mass gap, no Clay claim.
Individual polymers remain different from clusters.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.KPUnrooted
import LatticeGauge.ConnectorClusters

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## A8.1 — the positive unrooted coefficient (birth) -/

/-- **The absolute unrooted Ursell coefficient**:
    B⁺_k(ρ) = (1/k!)·Σ_δ |φ(δ)|·Π ρ(δᵢ) — natAbs of the stone-37
    coefficient, nonnegative activities, no root, no sign. -/
noncomputable def kpAbsUnrootedCoeff (k : ℕ)
    (ρ : Polymer N → ℝ) : ℝ :=
  (∑ δ : Fin k → Polymer N,
      (((ursellCoeff (N := N) (fun i => (δ i).val)).natAbs : ℕ) : ℝ)
        * ∏ i : Fin k, ρ (δ i))
    / ((Nat.factorial k : ℕ) : ℝ)

/-- **B⁺₀ = 0** (the empty tuple carries no connected structure —
    stone-42b consumed, as in 49A). -/
theorem kpAbsUnrootedCoeff_zero (ρ : Polymer N → ℝ) :
    kpAbsUnrootedCoeff 0 ρ = 0 := by
  unfold kpAbsUnrootedCoeff ursellCoeff
  rw [Finset.univ_unique, Finset.sum_singleton,
    graphUrsellCoeff_fin_zero, Int.natAbs_zero, Nat.cast_zero,
    zero_mul, zero_div]

/-- **B⁺_k ≥ 0** under nonnegative activities. -/
theorem kpAbsUnrootedCoeff_nonneg (k : ℕ)
    {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η) :
    0 ≤ kpAbsUnrootedCoeff k ρ := by
  unfold kpAbsUnrootedCoeff
  refine div_nonneg (Finset.sum_nonneg (fun δ _ => ?_))
    (Nat.cast_nonneg _)
  exact mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg (fun i _ => hρ (δ i)))

/-! ## A8.2 — the connector is dominated by the positive object
    (triangle inequality on the finite sum; the barrier indicator
    majorized by the full summand — NO four-series
    inclusion-exclusion) -/

theorem abs_kpConnectorUnrootedCoeff_le (k : ℕ)
    (z : Polymer N → ℝ) (P Q : Polymer N → Prop) :
    |kpConnectorUnrootedCoeff (N := N) k z P Q|
      ≤ kpAbsUnrootedCoeff k (fun η => |z η|) := by
  unfold kpConnectorUnrootedCoeff kpAbsUnrootedCoeff
  rw [abs_div, Nat.abs_cast]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _)
    (Finset.sum_le_sum (fun δ _ => ?_))
  by_cases h : TupleHitsBothForbidden P Q δ
  · rw [if_pos h, abs_mul, Finset.abs_prod, ← Int.cast_abs,
      Int.abs_eq_natAbs, Int.cast_natCast]
  · rw [if_neg h, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _)
      (Finset.prod_nonneg (fun i _ => abs_nonneg _))

/-! ## A8.3 — EXACT POSITIVE UNROOTING (the 49A identity with
    natAbs in place of the sign; the (n+1) is the normalization
    mismatch 1/n! vs 1/(n+1)!, nothing else) -/

/-- The pointwise repackaging of one rooted natAbs summand
    (named, so the sum step is first-order — the 49A recipe). -/
theorem abs_rooted_summand_eq (n : ℕ) (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) (γ : Fin n → Polymer N) :
    ((ursellCoeff (rootedTuple γ₀ γ)).natAbs : ℝ)
        * (ρ γ₀ * ∏ i : Fin n, ρ (γ i))
      = ((ursellCoeff (fun i =>
          ((Fin.cons γ₀ γ : Fin (n + 1) → Polymer N) i).val)
            ).natAbs : ℝ)
          * ∏ j : Fin (n + 1),
              ρ ((Fin.cons γ₀ γ : Fin (n + 1) → Polymer N) j) := by
  have hact : (∏ j : Fin (n + 1),
      ρ ((Fin.cons γ₀ γ : Fin (n + 1) → Polymer N) j))
      = ρ γ₀ * ∏ i : Fin n, ρ (γ i) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  rw [← rootedTuple_eq_cons_val, hact]

/-- **THE EXACT POSITIVE ROOT-REMOVAL IDENTITY**:
    Σ_γ₀ ρ(γ₀)·A_n(ρ, γ₀) = (n+1)·B⁺_{n+1}(ρ).
    Canonical (root, tail) ≃ tuple reindexation via the 49A
    consTupleEquiv — the root is index 0, no multiplicity; the
    (n+1) enters through `succ_mul_div_factorial_succ` ONLY. -/
theorem sum_root_activity_eq_succ_mul_absUnrooted (n : ℕ)
    (ρ : Polymer N → ℝ) :
    (∑ γ₀ : Polymer N, ρ γ₀ * kpUrsellCoeff n ρ γ₀)
      = ((n + 1 : ℕ) : ℝ) * kpAbsUnrootedCoeff (n + 1) ρ := by
  unfold kpAbsUnrootedCoeff
  rw [succ_mul_div_factorial_succ]
  calc (∑ γ₀ : Polymer N, ρ γ₀ * kpUrsellCoeff n ρ γ₀)
      = ∑ γ₀ : Polymer N,
          (ρ γ₀ * ∑ γ : Fin n → Polymer N,
            ((ursellCoeff (rootedTuple γ₀ γ)).natAbs : ℝ)
              * ∏ i : Fin n, ρ (γ i))
            / ((Nat.factorial n : ℕ) : ℝ) :=
        Finset.sum_congr rfl (fun γ₀ _ => by
          unfold kpUrsellCoeff
          rw [mul_div_assoc])
    _ = (∑ γ₀ : Polymer N,
          ρ γ₀ * ∑ γ : Fin n → Polymer N,
            ((ursellCoeff (rootedTuple γ₀ γ)).natAbs : ℝ)
              * ∏ i : Fin n, ρ (γ i))
          / ((Nat.factorial n : ℕ) : ℝ) :=
        (Finset.sum_div _ _ _).symm
    _ = (∑ δ : Fin (n + 1) → Polymer N,
          ((ursellCoeff (fun i => (δ i).val)).natAbs : ℝ)
            * ∏ j : Fin (n + 1), ρ (δ j))
          / ((Nat.factorial n : ℕ) : ℝ) := by
        congr 1
        calc (∑ γ₀ : Polymer N,
              ρ γ₀ * ∑ γ : Fin n → Polymer N,
                ((ursellCoeff (rootedTuple γ₀ γ)).natAbs : ℝ)
                  * ∏ i : Fin n, ρ (γ i))
            = ∑ γ₀ : Polymer N, ∑ γ : Fin n → Polymer N,
                ((ursellCoeff (rootedTuple γ₀ γ)).natAbs : ℝ)
                  * (ρ γ₀ * ∏ i : Fin n, ρ (γ i)) :=
              Finset.sum_congr rfl (fun γ₀ _ => by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl (fun γ _ => by ring))
          _ = ∑ p : Polymer N × (Fin n → Polymer N),
                ((ursellCoeff (rootedTuple p.1 p.2)).natAbs : ℝ)
                  * (ρ p.1 * ∏ i : Fin n, ρ (p.2 i)) :=
              (Fintype.sum_prod_type
                (fun p : Polymer N × (Fin n → Polymer N) =>
                  ((ursellCoeff (rootedTuple p.1 p.2)).natAbs : ℝ)
                    * (ρ p.1 * ∏ i : Fin n, ρ (p.2 i)))).symm
          _ = ∑ p : Polymer N × (Fin n → Polymer N),
                ((ursellCoeff (fun i =>
                    ((Fin.cons p.1 p.2
                      : Fin (n + 1) → Polymer N) i).val)
                      ).natAbs : ℝ)
                  * ∏ j : Fin (n + 1),
                      ρ ((Fin.cons p.1 p.2
                        : Fin (n + 1) → Polymer N) j) := by
              refine Finset.sum_congr rfl ?_
              rintro ⟨γ₀, γ⟩ -
              dsimp only
              exact abs_rooted_summand_eq n ρ γ₀ γ
          _ = ∑ δ : Fin (n + 1) → Polymer N,
                ((ursellCoeff (fun i => (δ i).val)).natAbs : ℝ)
                  * ∏ j : Fin (n + 1), ρ (δ j) :=
              sum_pairs_eq_sum_tuples n
                (fun δ =>
                  ((ursellCoeff (fun i => (δ i).val)).natAbs : ℝ)
                    * ∏ j : Fin (n + 1), ρ (δ j))

/-! ## A8.4 — the rooted termwise majorant (the (n+1) discarded
    by (n+1) ≥ 1 ONLY, after the exact identity) -/

theorem kpAbsUnrootedCoeff_succ_le_sum_root (n : ℕ)
    {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η) :
    kpAbsUnrootedCoeff (n + 1) ρ
      ≤ ∑ γ₀ : Polymer N, ρ γ₀ * kpUrsellCoeff n ρ γ₀ := by
  rw [sum_root_activity_eq_succ_mul_absUnrooted]
  exact le_mul_of_one_le_left
    (kpAbsUnrootedCoeff_nonneg (n + 1) hρ)
    (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))

/-! ## A8.5 — the abstract KP package (47/48 machinery consumed,
    never redone) -/

/-- **Uniform partial-sum bound**: every finite partial sum of
    B⁺_k is bounded by the finite-root envelope
    Σ_γ₀ ρ(γ₀)·exp(a γ₀) — the 49B recipe with the positive
    object: B⁺₀ = 0 splits off, sum_comm is rectangular, per root
    the 48C-α tsum bound absorbs the range sum. -/
theorem sum_range_kpAbsUnrootedCoeff_le {ρ a : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis ρ a) :
    ∀ K : ℕ, (∑ k ∈ Finset.range K, kpAbsUnrootedCoeff k ρ)
      ≤ ∑ γ₀ : Polymer N, ρ γ₀ * Real.exp (a γ₀) := by
  have hRHS : (0 : ℝ)
      ≤ ∑ γ₀ : Polymer N, ρ γ₀ * Real.exp (a γ₀) :=
    Finset.sum_nonneg (fun γ₀ _ =>
      mul_nonneg (hρ γ₀) (Real.exp_pos _).le)
  intro K
  rcases K with _ | M
  · rw [Finset.range_zero, Finset.sum_empty]
    exact hRHS
  · rw [Finset.sum_range_succ'
      (fun k => kpAbsUnrootedCoeff k ρ) M,
      kpAbsUnrootedCoeff_zero, add_zero]
    calc (∑ n ∈ Finset.range M, kpAbsUnrootedCoeff (n + 1) ρ)
        ≤ ∑ n ∈ Finset.range M, ∑ γ₀ : Polymer N,
            ρ γ₀ * kpUrsellCoeff n ρ γ₀ :=
          Finset.sum_le_sum (fun n _ =>
            kpAbsUnrootedCoeff_succ_le_sum_root n hρ)
      _ = ∑ γ₀ : Polymer N, ∑ n ∈ Finset.range M,
            ρ γ₀ * kpUrsellCoeff n ρ γ₀ :=
          Finset.sum_comm
      _ = ∑ γ₀ : Polymer N,
            ρ γ₀ * ∑ n ∈ Finset.range M, kpUrsellCoeff n ρ γ₀ :=
          Finset.sum_congr rfl (fun γ₀ _ => by
            rw [Finset.mul_sum])
      _ ≤ ∑ γ₀ : Polymer N, ρ γ₀ * Real.exp (a γ₀) := by
          refine Finset.sum_le_sum (fun γ₀ _ => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (hρ γ₀)
          calc (∑ n ∈ Finset.range M, kpUrsellCoeff n ρ γ₀)
              ≤ ∑' n : ℕ, kpUrsellCoeff n ρ γ₀ :=
                sum_le_tsum (Finset.range M)
                  (fun n _ => kpUrsellCoeff_nonneg n hρ γ₀)
                  (summable_kpUrsellCoeff hρ ha hKP γ₀)
            _ ≤ Real.exp (a γ₀) :=
                tsum_kpUrsellCoeff_le_exp hρ ha hKP γ₀

/-- **A8 Summability**: the positive unrooted series converges. -/
theorem summable_kpAbsUnrootedCoeff {ρ a : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis ρ a) :
    Summable (fun k => kpAbsUnrootedCoeff (N := N) k ρ) :=
  summable_of_sum_range_le
    (fun k => kpAbsUnrootedCoeff_nonneg k hρ)
    (sum_range_kpAbsUnrootedCoeff_le hρ ha hKP)

/-- **CAPSTONE 50-A8**: the tsum of the positive unrooted series
    is bounded by the finite-root KP envelope. This — through
    A8.2 — is the summable positive majorant every future
    connector estimate will stand on. -/
theorem tsum_kpAbsUnrootedCoeff_le {ρ a : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis ρ a) :
    (∑' k : ℕ, kpAbsUnrootedCoeff (N := N) k ρ)
      ≤ ∑ γ₀ : Polymer N, ρ γ₀ * Real.exp (a γ₀) :=
  Real.tsum_le_of_sum_range_le
    (fun k => kpAbsUnrootedCoeff_nonneg k hρ)
    (sum_range_kpAbsUnrootedCoeff_le hρ ha hKP)

#print axioms sum_root_activity_eq_succ_mul_absUnrooted
#print axioms abs_kpConnectorUnrootedCoeff_le
#print axioms tsum_kpAbsUnrootedCoeff_le

end LatticeGauge
