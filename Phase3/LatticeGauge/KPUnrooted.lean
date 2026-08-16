/-
LatticeGauge/KPUnrooted.lean — stones 49A AND 49B
(architecture: Sol/GPT-5.6; execution: Fable; 49A adversarially
audited by Kimi 3 at 06c4d1928e4ff1b694e16c5f4746b80a125480c3 —
APPROVED, no substantive correction).

49A — THE FINITE UNROOTING: the unrooted signed Ursell coefficient
B_k(z) and the exact root-removal identity
Σ_{γ₀} z(γ₀)·Cₙ(z,γ₀) = (n+1)·B_{n+1}(z), by canonical
reindexation only (the LOCAL non-dependent `consTupleEquiv`, an
opaque-weight sum reindexer, and Fin.prod_univ_succ). No orbits,
no quotients, no permutation machinery, no hidden multiplicity:
the root is canonically index 0 and tuples with repeated polymers
stay distinct by occurrence. The (n+1) factor is born EXCLUSIVELY
from the 1/n! vs 1/(n+1)! normalization mismatch, isolated in
`succ_mul_div_factorial_succ`.

49B — ABSOLUTE SUMMABILITY OF THE UNROOTED SERIES: Summable and
tsum bounds ARE present in this file now — the termwise
finite-root majorant (the 1/(n+1) factor discarded via (n+1) ≥ 1),
everything kept finite until the two trusted 48A bridges
(summable_of_sum_range_le / Real.tsum_le_of_sum_range_le), plus
the signed corollaries. The finite-root envelope anticipated by
48D.4 is recovered through the abstract specialization.

STILL ABSENT (49C, not started): Real.log, logPartition, realZ,
exp identities, the finite polymer-gas representation,
thermodynamic limits, clustering, mass gap. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.UrsellCoefficients
import LatticeGauge.KPCoefficients
import LatticeGauge.KPInduction

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## 49A.1 — the unrooted signed coefficient (birth) -/

/-- **The unrooted signed Ursell coefficient**:
    B_k(z) = (1/k!)·Σ_{δ : Fin k → Polymer} φ(δ)·Π z(δᵢ) — the
    signed stone-37 coefficient on the raw tuple, signed
    activities, no root, no natAbs. -/
noncomputable def kpSignedUnrootedCoeff (k : ℕ)
    (z : Polymer N → ℝ) : ℝ :=
  (∑ δ : Fin k → Polymer N,
      ((ursellCoeff (fun i => (δ i).val) : ℤ) : ℝ)
        * ∏ i : Fin k, z (δ i))
    / ((Nat.factorial k : ℕ) : ℝ)

/-! ## 49A.2 — the degenerate cases -/

/-- **B₀ = 0** (the empty tuple carries no connected structure —
    the stone-42b lemma `graphUrsellCoeff_fin_zero` consumed, not
    reproved). -/
theorem kpSignedUnrootedCoeff_zero (z : Polymer N → ℝ) :
    kpSignedUnrootedCoeff 0 z = 0 := by
  unfold kpSignedUnrootedCoeff ursellCoeff
  rw [Finset.univ_unique, Finset.sum_singleton,
    graphUrsellCoeff_fin_zero, Int.cast_zero, zero_mul, zero_div]

/-- **B₁(z) = Σ_η z(η)** (the single polymer has φ = 1). -/
theorem kpSignedUnrootedCoeff_one (z : Polymer N → ℝ) :
    kpSignedUnrootedCoeff 1 z = ∑ η : Polymer N, z η := by
  unfold kpSignedUnrootedCoeff
  rw [Nat.factorial_one, Nat.cast_one, div_one]
  calc (∑ δ : Fin 1 → Polymer N,
        ((ursellCoeff (fun i => (δ i).val) : ℤ) : ℝ)
          * ∏ i : Fin 1, z (δ i))
      = ∑ δ : Fin 1 → Polymer N, z (δ 0) :=
        Finset.sum_congr rfl (fun δ _ => by
          rw [ursellCoeff_single, Int.cast_one, one_mul,
            Fin.prod_univ_one])
    _ = ∑ η : Polymer N, z η :=
        Fintype.sum_equiv
          (Equiv.funUnique (Fin 1) (Polymer N))
          (fun δ => z (δ 0)) (fun η => z η) (fun δ => rfl)

/-! ## 49A.3 — the root+tail lemma (rootedTuple IS Fin.cons) -/

/-- The trivial cons equivalence, LOCAL and non-dependent (iota
    only — the deep-unification vaccine). -/
noncomputable def consTupleEquiv (n : ℕ) :
    Polymer N × (Fin n → Polymer N) ≃ (Fin (n + 1) → Polymer N) where
  toFun p := Fin.cons p.1 p.2
  invFun δ := (δ 0, Fin.tail δ)
  left_inv p := by
    obtain ⟨a, f⟩ := p
    simp only [Fin.cons_zero, Fin.tail_cons]
  right_inv δ := Fin.cons_self_tail δ

/-- The generic pair↔tuple reindexation with an OPAQUE weight — the
    unifier never touches the concrete summand (whnf vaccine). -/
theorem sum_pairs_eq_sum_tuples (n : ℕ)
    (F : (Fin (n + 1) → Polymer N) → ℝ) :
    (∑ p : Polymer N × (Fin n → Polymer N),
        F (Fin.cons p.1 p.2))
      = ∑ δ : Fin (n + 1) → Polymer N, F δ :=
  Fintype.sum_equiv (consTupleEquiv (N := N) n)
    (fun p => F (Fin.cons p.1 p.2)) (fun δ => F δ)
    (fun p => rfl)

/-- The rooted raw tuple is literally the valuewise Fin.cons of the
    Polymer-level cons — the canonical split, no new structure. -/
theorem rootedTuple_eq_cons_val (γ₀ : Polymer N)
    (γ : Fin n → Polymer N) :
    rootedTuple γ₀ γ
      = fun i => ((Fin.cons γ₀ γ : Fin (n + 1) → Polymer N) i).val := by
  funext i
  refine Fin.cases rfl (fun j => rfl) i

/-- The pointwise repackaging of one rooted summand (named, so the
    sum step below is first-order). -/
theorem rooted_summand_eq (n : ℕ) (z : Polymer N → ℝ)
    (γ₀ : Polymer N) (γ : Fin n → Polymer N) :
    ((ursellCoeff (rootedTuple γ₀ γ) : ℤ) : ℝ)
        * (z γ₀ * ∏ i : Fin n, z (γ i))
      = ((ursellCoeff (fun i =>
          ((Fin.cons γ₀ γ : Fin (n + 1) → Polymer N) i).val)
            : ℤ) : ℝ)
          * ∏ j : Fin (n + 1),
              z ((Fin.cons γ₀ γ : Fin (n + 1) → Polymer N) j) := by
  have hact : (∏ j : Fin (n + 1),
      z ((Fin.cons γ₀ γ : Fin (n + 1) → Polymer N) j))
      = z γ₀ * ∏ i : Fin n, z (γ i) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  rw [← rootedTuple_eq_cons_val, hact]

/-- The ONLY scalar step: (n+1)·(x/(n+1)!) = x/n! — the birthplace
    of the (n+1) factor, isolated. -/
theorem succ_mul_div_factorial_succ (n : ℕ) (x : ℝ) :
    ((n + 1 : ℕ) : ℝ)
        * (x / ((Nat.factorial (n + 1) : ℕ) : ℝ))
      = x / ((Nat.factorial n : ℕ) : ℝ) := by
  have h1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((Nat.factorial n : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-! ## 49A.4 — THE ROOT-REMOVAL CAPSTONE -/

/-- **THE EXACT FINITE ROOT-REMOVAL IDENTITY**:
    Σ_{γ₀} z(γ₀)·Cₙ(z, γ₀) = (n+1)·B_{n+1}(z).
    Canonical reindexation only: pairs (root, tail) ≃ tuples via
    Fin.consEquiv (the root is canonically index 0 — NO additional
    multiplicity; repeated polymers stay distinct by occurrence);
    the activity regroups by Fin.prod_univ_succ; the (n+1) is the
    normalization mismatch, nothing else. -/
theorem sum_root_activity_eq_succ_mul_unrooted (n : ℕ)
    (z : Polymer N → ℝ) :
    (∑ γ₀ : Polymer N, z γ₀ * kpSignedUrsellCoeff n z γ₀)
      = ((n + 1 : ℕ) : ℝ) * kpSignedUnrootedCoeff (n + 1) z := by
  unfold kpSignedUnrootedCoeff
  rw [succ_mul_div_factorial_succ]
  calc (∑ γ₀ : Polymer N, z γ₀ * kpSignedUrsellCoeff n z γ₀)
      = ∑ γ₀ : Polymer N,
          (z γ₀ * ∑ γ : Fin n → Polymer N,
            ((ursellCoeff (rootedTuple γ₀ γ) : ℤ) : ℝ)
              * ∏ i : Fin n, z (γ i))
            / ((Nat.factorial n : ℕ) : ℝ) :=
        Finset.sum_congr rfl (fun γ₀ _ => by
          unfold kpSignedUrsellCoeff
          rw [mul_div_assoc])
    _ = (∑ γ₀ : Polymer N,
          z γ₀ * ∑ γ : Fin n → Polymer N,
            ((ursellCoeff (rootedTuple γ₀ γ) : ℤ) : ℝ)
              * ∏ i : Fin n, z (γ i))
          / ((Nat.factorial n : ℕ) : ℝ) :=
        (Finset.sum_div _ _ _).symm
    _ = (∑ δ : Fin (n + 1) → Polymer N,
          ((ursellCoeff (fun i => (δ i).val) : ℤ) : ℝ)
            * ∏ j : Fin (n + 1), z (δ j))
          / ((Nat.factorial n : ℕ) : ℝ) := by
        congr 1
        calc (∑ γ₀ : Polymer N,
              z γ₀ * ∑ γ : Fin n → Polymer N,
                ((ursellCoeff (rootedTuple γ₀ γ) : ℤ) : ℝ)
                  * ∏ i : Fin n, z (γ i))
            = ∑ γ₀ : Polymer N, ∑ γ : Fin n → Polymer N,
                ((ursellCoeff (rootedTuple γ₀ γ) : ℤ) : ℝ)
                  * (z γ₀ * ∏ i : Fin n, z (γ i)) :=
              Finset.sum_congr rfl (fun γ₀ _ => by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl (fun γ _ => by ring))
          _ = ∑ p : Polymer N × (Fin n → Polymer N),
                ((ursellCoeff (rootedTuple p.1 p.2) : ℤ) : ℝ)
                  * (z p.1 * ∏ i : Fin n, z (p.2 i)) :=
              (Fintype.sum_prod_type
                (fun p : Polymer N × (Fin n → Polymer N) =>
                  ((ursellCoeff (rootedTuple p.1 p.2) : ℤ) : ℝ)
                    * (z p.1 * ∏ i : Fin n, z (p.2 i)))).symm
          _ = ∑ p : Polymer N × (Fin n → Polymer N),
                ((ursellCoeff (fun i =>
                    ((Fin.cons p.1 p.2
                      : Fin (n + 1) → Polymer N) i).val)
                      : ℤ) : ℝ)
                  * ∏ j : Fin (n + 1),
                      z ((Fin.cons p.1 p.2
                        : Fin (n + 1) → Polymer N) j) := by
              refine Finset.sum_congr rfl ?_
              rintro ⟨γ₀, γ⟩ -
              dsimp only
              exact rooted_summand_eq n z γ₀ γ
          _ = ∑ δ : Fin (n + 1) → Polymer N,
                ((ursellCoeff (fun i => (δ i).val) : ℤ) : ℝ)
                  * ∏ j : Fin (n + 1), z (δ j) :=
              sum_pairs_eq_sum_tuples n
                (fun δ =>
                  ((ursellCoeff (fun i => (δ i).val) : ℤ) : ℝ)
                    * ∏ j : Fin (n + 1), z (δ j))
/-! ## 49B — ABSOLUTE SUMMABILITY OF THE UNROOTED SIGNED SERIES
    (abstract level). The 49A identity plus the triangle inequality
    give the termwise finite-root majorant; the 1/(n+1) factor is
    DISCARDED via (n+1) ≥ 1 (architect's ruling: it buys nothing
    here); both capstones flow through the SAME trusted 48A bridges
    (summable_of_sum_range_le / Real.tsum_le_of_sum_range_le) —
    everything else is finite. NOT here: realZ, logPartition,
    Real.log, exp identities, the polymer-gas representation,
    limits, clustering, mass gap. -/

/-- **49B termwise majorant**: |B_{n+1}(z)| ≤ Σ_γ₀ |z(γ₀)|·|Cₙ(z,γ₀)|
    — 49A + triangle; the (n+1) discarded by (n+1) ≥ 1. -/
theorem abs_unrooted_succ_le (n : ℕ) (z : Polymer N → ℝ) :
    |kpSignedUnrootedCoeff (n + 1) z|
      ≤ ∑ γ₀ : Polymer N,
          |z γ₀| * |kpSignedUrsellCoeff n z γ₀| := by
  have h1 : |kpSignedUnrootedCoeff (n + 1) z|
      ≤ ((n + 1 : ℕ) : ℝ) * |kpSignedUnrootedCoeff (n + 1) z| :=
    le_mul_of_one_le_left (abs_nonneg _)
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  calc |kpSignedUnrootedCoeff (n + 1) z|
      ≤ ((n + 1 : ℕ) : ℝ)
          * |kpSignedUnrootedCoeff (n + 1) z| := h1
    _ = |((n + 1 : ℕ) : ℝ)
          * kpSignedUnrootedCoeff (n + 1) z| := by
        rw [abs_mul, abs_of_nonneg
          (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]
    _ = |∑ γ₀ : Polymer N,
          z γ₀ * kpSignedUrsellCoeff n z γ₀| := by
        rw [sum_root_activity_eq_succ_mul_unrooted]
    _ ≤ ∑ γ₀ : Polymer N,
          |z γ₀ * kpSignedUrsellCoeff n z γ₀| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ γ₀ : Polymer N,
          |z γ₀| * |kpSignedUrsellCoeff n z γ₀| :=
        Finset.sum_congr rfl (fun γ₀ _ => abs_mul _ _)

/-- **49B: the finite-root majorant is Summable** (finite sum of
    the 48C-β summable series, scaled). -/
theorem summable_rootMajorant {z a : Polymer N → ℝ}
    (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (fun η => |z η|) a) :
    Summable (fun n => ∑ γ₀ : Polymer N,
      |z γ₀| * |kpSignedUrsellCoeff n z γ₀|) :=
  summable_sum (fun γ₀ _ =>
    Summable.mul_left _
      (summable_abs_kpSignedUrsellCoeff ha hKP γ₀))

/-- **49B range bound**: every finite partial sum of |B_k| is
    bounded by the finite-root envelope Σ_γ₀ |z(γ₀)|·exp(a γ₀) —
    B₀ = 0 splits off; sum_comm is rectangular; per root the 48C-β
    tsum bound absorbs the range sum via sum_le_tsum. -/
theorem sum_range_abs_unrooted_le {z a : Polymer N → ℝ}
    (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (fun η => |z η|) a) :
    ∀ K : ℕ, (∑ k ∈ Finset.range K, |kpSignedUnrootedCoeff k z|)
      ≤ ∑ γ₀ : Polymer N, |z γ₀| * Real.exp (a γ₀) := by
  have hRHS : (0 : ℝ)
      ≤ ∑ γ₀ : Polymer N, |z γ₀| * Real.exp (a γ₀) :=
    Finset.sum_nonneg (fun γ₀ _ =>
      mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
  intro K
  rcases K with _ | M
  · rw [Finset.range_zero, Finset.sum_empty]
    exact hRHS
  · rw [Finset.sum_range_succ'
      (fun k => |kpSignedUnrootedCoeff k z|) M,
      kpSignedUnrootedCoeff_zero, abs_zero, add_zero]
    calc (∑ n ∈ Finset.range M,
        |kpSignedUnrootedCoeff (n + 1) z|)
        ≤ ∑ n ∈ Finset.range M, ∑ γ₀ : Polymer N,
            |z γ₀| * |kpSignedUrsellCoeff n z γ₀| :=
          Finset.sum_le_sum (fun n _ => abs_unrooted_succ_le n z)
      _ = ∑ γ₀ : Polymer N, ∑ n ∈ Finset.range M,
            |z γ₀| * |kpSignedUrsellCoeff n z γ₀| :=
          Finset.sum_comm
      _ = ∑ γ₀ : Polymer N,
            |z γ₀| * ∑ n ∈ Finset.range M,
              |kpSignedUrsellCoeff n z γ₀| :=
          Finset.sum_congr rfl (fun γ₀ _ => by
            rw [Finset.mul_sum])
      _ ≤ ∑ γ₀ : Polymer N, |z γ₀| * Real.exp (a γ₀) := by
          refine Finset.sum_le_sum (fun γ₀ _ => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          calc (∑ n ∈ Finset.range M,
              |kpSignedUrsellCoeff n z γ₀|)
              ≤ ∑' n : ℕ, |kpSignedUrsellCoeff n z γ₀| :=
                sum_le_tsum (Finset.range M)
                  (fun n _ => abs_nonneg _)
                  (summable_abs_kpSignedUrsellCoeff ha hKP γ₀)
            _ ≤ Real.exp (a γ₀) :=
                tsum_abs_kpSignedUrsellCoeff_le_exp ha hKP γ₀

/-- **49B CAPSTONE 1 (abstract)**: the unrooted signed Ursell
    series is absolutely Summable. -/
theorem summable_abs_kpSignedUnrootedCoeff {z a : Polymer N → ℝ}
    (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (fun η => |z η|) a) :
    Summable (fun k => |kpSignedUnrootedCoeff k z|) :=
  summable_of_sum_range_le (fun k => abs_nonneg _)
    (sum_range_abs_unrooted_le ha hKP)

/-- **49B CAPSTONE 2 (abstract)**: the finite-root tsum bound. -/
theorem tsum_abs_kpSignedUnrootedCoeff_le {z a : Polymer N → ℝ}
    (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (fun η => |z η|) a) :
    (∑' k : ℕ, |kpSignedUnrootedCoeff k z|)
      ≤ ∑ γ₀ : Polymer N, |z γ₀| * Real.exp (a γ₀) :=
  Real.tsum_le_of_sum_range_le (fun k => abs_nonneg _)
    (sum_range_abs_unrooted_le ha hKP)

/-- **The signed corollary (certified, as in 48C-β)**: the unrooted
    signed series itself is Summable. -/
theorem summable_kpSignedUnrootedCoeff {z a : Polymer N → ℝ}
    (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (fun η => |z η|) a) :
    Summable (fun k => kpSignedUnrootedCoeff k z) :=
  Summable.of_norm_bounded
    (fun k => |kpSignedUnrootedCoeff k z|)
    (summable_abs_kpSignedUnrootedCoeff ha hKP)
    (fun k => le_of_eq (Real.norm_eq_abs _))

end LatticeGauge
