/-
LatticeGauge/KPUnrooted.lean — stone 49A: THE FINITE UNROOTING OF
THE SIGNED URSELL SERIES (architecture: Sol/GPT-5.6; execution:
Fable).

Pure finite combinatorics/algebra: the UNROOTED signed Ursell
coefficient B_k(z) is born, and the exact root-removal identity
  Σ_{γ₀} z(γ₀)·Cₙ(z, γ₀) = (n+1)·B_{n+1}(z)
is proved by canonical reindexation ONLY: every tuple
δ : Fin (n+1) → Polymer splits canonically as (δ 0, tail), and
rootedTuple was BUILT as Fin.cons — so the identity is
`Fin.consEquiv` + `Fin.prod_univ_succ` + (n+1)! = (n+1)·n!.
NO orbits, NO quotients, NO permutation machinery (stone 38 not
needed), NO hidden multiplicity: the root is canonically index 0,
and tuples with repeated polymers remain distinct tuples by
occurrence, exactly as in stones 37/38/47 — audit target, stated
here openly. The (n+1) factor is born EXCLUSIVELY from the
normalization mismatch between 1/n! (rooted) and 1/(n+1)!
(unrooted).
NOT here (49B/49C, not authorized): Summable, tsum, concrete
polymerWeight, β ≤ 1/40000, Real.exp, Real.log, logPartition,
realZ, the finite polymer-gas identity, thermodynamic limit,
clustering, mass gap. NOT claimed: convergence of the unrooted
series, any cluster-expansion/log Z statement. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.UrsellCoefficients
import LatticeGauge.PolymerTreeBound
import LatticeGauge.KPCoefficients
import LatticeGauge.KPStratification
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
              (Fintype.sum_prod_type _).symm
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
end LatticeGauge
