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

theorem kpG_nonneg {ρ : Polymer N → ℝ}
    (hρ : ∀ γ, 0 ≤ ρ γ) (m : ℕ) (γ₀ : Polymer N) :
    0 ≤ kpG ρ γ₀ m :=
  Finset.sum_nonneg fun η _ =>
    mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (hρ η))
      (kpTreeCoeff_nonneg m hρ η)

theorem kpPartialSum_nonneg {ρ : Polymer N → ℝ}
    (hρ : ∀ γ, 0 ≤ ρ γ) (M : ℕ) (γ : Polymer N) :
    0 ≤ kpPartialSum M ρ γ :=
  Finset.sum_nonneg fun n _ => kpTreeCoeff_nonneg n hρ γ

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
    (fun n _ _ => kpTreeCoeff_nonneg n hρ γ)

/-! ## 47c-A2 — restricted profiles ≤ independent choices = X_M^k
    (the audit shape: = = ≤ = =; the ONE inequality isolated) -/

/-- The common ambient type for all profiles up to total M+1. -/
abbrev IndependentSizes (M k : ℕ) := Fin k → Fin (M + 1)

/-- The bounded profiles AS A FINSET of the ambient type — both
    sides of the red-tape inequality live in the same type. -/
noncomputable def boundedProfilesFinset (M k : ℕ) :
    Finset (IndependentSizes M k) :=
  Finset.univ.filter (fun t => (∑ j, ((t j : ℕ) + 1)) ≤ M + 1)

/-- **The named zero-extension**: k > n kills the stratum — the
    triangle becomes a rectangle because the extra terms are
    LITERALLY zero, visibly, not inside a simp. -/
theorem profileSum_eq_zero_of_gt {n k : ℕ} (hk : n < k)
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) :
    (∑ s : SizeProfile n k,
      ∏ j : Fin k, kpG ρ γ₀ (profileNat s j)) = 0 := by
  haveI := sizeProfile_isEmpty_of_gt hk
  rw [Finset.univ_eq_empty, Finset.sum_empty]

/-- The recurrence with the RECTANGULAR window (extension by the
    named zeros; the downstream swap is a plain sum_comm). -/
theorem kpTreeCoeff_recurrence_rect (M : ℕ) {n : ℕ}
    (hn1 : 1 ≤ n) (hn2 : n ≤ M + 1)
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) :
    kpTreeCoeff n ρ γ₀
      = ∑ i ∈ Finset.range (M + 1),
          (1 / ((Nat.factorial (i + 1) : ℕ) : ℝ))
            * ∑ s : SizeProfile n (i + 1),
                ∏ j : Fin (i + 1), kpG ρ γ₀ (profileNat s j) := by
  rw [kpTreeCoeff_recurrence n (by omega) ρ γ₀]
  refine Finset.sum_subset (Finset.range_subset.mpr (by omega)) ?_
  intro i _ hin
  rw [Finset.mem_range] at hin
  rw [profileSum_eq_zero_of_gt (by omega) ρ γ₀, mul_zero]

/-- The cast into the ambient type; the bound is delivered by the
    profile ITSELF (t_j + 1 ≤ Σ_ℓ (t_ℓ + 1) = n ≤ M + 1). -/
noncomputable def profileCast (M : ℕ) {n k : ℕ} (hn : n ≤ M + 1)
    (s : SizeProfile n k) : IndependentSizes M k :=
  fun j => ⟨profileNat s j, by
    have h1 : profileNat s j + 1 ≤ ∑ l, (profileNat s l + 1) :=
      Finset.single_le_sum
        (f := fun l => profileNat s l + 1)
        (fun l _ => by omega) (Finset.mem_univ j)
    have h2 : (∑ l, (profileNat s l + 1)) = n := s.2
    omega⟩

/-- **The EXACT disjoint-union reindexation** (no inequality): the
    strata n+1 = 1,…,M+1 correspond exactly to the bounded finset;
    n is recovered from the profile itself, and the return to
    Fin (n+1) is certified by t_j + 1 ≤ Σ_ℓ (t_ℓ + 1) = n + 1, NOT
    merely by t_j ≤ M. -/
theorem sum_profileSum_eq_boundedSum (M k : ℕ) (hk : 1 ≤ k)
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) :
    (∑ n ∈ Finset.range (M + 1),
      ∑ s : SizeProfile (n + 1) k,
        ∏ j : Fin k, kpG ρ γ₀ (profileNat s j))
      = ∑ t ∈ boundedProfilesFinset M k,
          ∏ j : Fin k, kpG ρ γ₀ ((t j : ℕ)) := by
  rw [← Finset.sum_sigma (Finset.range (M + 1))
    (fun _ => Finset.univ)
    (fun x => ∏ j : Fin k, kpG ρ γ₀ (profileNat x.2 j))]
  refine Finset.sum_bij
    (i := fun x hx => profileCast M (by
      have := Finset.mem_range.mp (Finset.mem_sigma.mp hx).1
      omega) x.2) ?_ ?_ ?_ ?_
  · intro x hx
    unfold boundedProfilesFinset
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show (∑ j, (profileNat x.2 j + 1)) ≤ M + 1
    have h2 : (∑ j, (profileNat x.2 j + 1)) = x.1 + 1 := x.2.2
    have h3 := Finset.mem_range.mp (Finset.mem_sigma.mp hx).1
    omega
  · intro x hx y hy h
    have hval : ∀ j, profileNat x.2 j = profileNat y.2 j := by
      intro j
      have h4 := congrFun h j
      exact congrArg Subtype.val h4
    have hxn : (∑ j, (profileNat x.2 j + 1)) = x.1 + 1 := x.2.2
    have hyn : (∑ j, (profileNat y.2 j + 1)) = y.1 + 1 := y.2.2
    have hsum : (∑ j, (profileNat x.2 j + 1))
        = (∑ j, (profileNat y.2 j + 1)) :=
      Finset.sum_congr rfl (fun j _ => by rw [hval j])
    obtain ⟨n₁, s₁⟩ := x
    obtain ⟨n₂, s₂⟩ := y
    dsimp only at hval hxn hyn hsum
    have hn : n₁ = n₂ := by omega
    subst hn
    have hs : s₁ = s₂ :=
      SizeProfile.ext' (fun j => Fin.ext (hval j))
    subst hs
    rfl
  · intro t ht
    unfold boundedProfilesFinset at ht
    rw [Finset.mem_filter] at ht
    have hpos : 1 ≤ (∑ j, ((t j : ℕ) + 1)) := by
      calc 1 ≤ k := hk
        _ = ∑ _j : Fin k, 1 := by
            rw [Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, smul_eq_mul, mul_one]
        _ ≤ ∑ j, ((t j : ℕ) + 1) :=
            Finset.sum_le_sum (fun j _ => by omega)
    obtain ⟨n, hn⟩ : ∃ n, (∑ j, ((t j : ℕ) + 1)) = n + 1 :=
      ⟨(∑ j, ((t j : ℕ) + 1)) - 1, by omega⟩
    refine ⟨⟨n, (⟨fun j => ⟨(t j : ℕ), ?_⟩, ?_⟩
        : SizeProfile (n + 1) k)⟩,
      Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (by
        have h5 := ht.2
        omega), Finset.mem_univ _⟩, ?_⟩
    · have h1 : (t j : ℕ) + 1 ≤ ∑ l, ((t l : ℕ) + 1) :=
        Finset.single_le_sum
          (f := fun l => (t l : ℕ) + 1)
          (fun l _ => by omega) (Finset.mem_univ j)
      omega
    · show (∑ j, ((t j : ℕ) + 1)) = n + 1
      exact hn
    · funext j
      exact Fin.ext rfl
  · intro x hx
    rfl

/-- 🚩 **THE RED-TAPE STEP — the only inequality of A2**: the
    restricted sum grows into the independent sum by ENLARGING THE
    DOMAIN — a literal Finset inclusion (filter ⊆ univ) inside the
    ambient type, valid only through nonnegativity. NEVER a
    reindexation. -/
theorem boundedSum_le_indepSum {ρ : Polymer N → ℝ}
    (hρ : ∀ γ, 0 ≤ ρ γ) (M k : ℕ) (γ₀ : Polymer N) :
    (∑ t ∈ boundedProfilesFinset M k,
        ∏ j : Fin k, kpG ρ γ₀ ((t j : ℕ)))
      ≤ ∑ t : IndependentSizes M k,
          ∏ j : Fin k, kpG ρ γ₀ ((t j : ℕ)) :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _)
    (fun t _ _ => Finset.prod_nonneg
      (fun j _ => kpG_nonneg hρ _ γ₀))

/-- Back to EQUALITY: the independent sum is the k-th power of X_M
    (sum_pi_prod + constant product). -/
theorem indepSum_eq_kpX_pow (M k : ℕ) (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) :
    (∑ t : IndependentSizes M k,
        ∏ j : Fin k, kpG ρ γ₀ ((t j : ℕ)))
      = (kpX M ρ γ₀) ^ k := by
  have hc : (∑ x : Fin (M + 1), kpG ρ γ₀ ((x : ℕ)))
      = kpX M ρ γ₀ :=
    Fin.sum_univ_eq_sum_range (fun m => kpG ρ γ₀ m) (M + 1)
  calc (∑ t : IndependentSizes M k,
        ∏ j : Fin k, kpG ρ γ₀ ((t j : ℕ)))
      = ∏ _j : Fin k, ∑ x : Fin (M + 1), kpG ρ γ₀ ((x : ℕ)) :=
        sum_pi_prod (A := fun _ : Fin k => Fin (M + 1))
          (f := fun _ x => kpG ρ γ₀ ((x : ℕ)))
    _ = (∑ x : Fin (M + 1), kpG ρ γ₀ ((x : ℕ))) ^ k := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = (kpX M ρ γ₀) ^ k := by rw [hc]

/-- **47c-A2 CAPSTONE**: the truncated-exponential majorant of the
    partial sums, already in the X^k / k! spelling the exponential
    API will consume. No Real.exp, no KP, no IH. -/
theorem kpPartialSum_succ_le_truncated {ρ : Polymer N → ℝ}
    (hρ : ∀ γ, 0 ≤ ρ γ) (M : ℕ) (γ₀ : Polymer N) :
    kpPartialSum (M + 1) ρ γ₀
      ≤ ∑ k ∈ Finset.range (M + 2),
          (kpX M ρ γ₀) ^ k / ((Nat.factorial k : ℕ) : ℝ) := by
  unfold kpPartialSum
  rw [Finset.sum_range_succ'
      (fun n => kpTreeCoeff n ρ γ₀) (M + 1),
    Finset.sum_range_succ'
      (fun k => (kpX M ρ γ₀) ^ k
        / ((Nat.factorial k : ℕ) : ℝ)) (M + 1)]
  refine add_le_add ?_ ?_
  · calc (∑ n ∈ Finset.range (M + 1), kpTreeCoeff (n + 1) ρ γ₀)
        = ∑ n ∈ Finset.range (M + 1), ∑ i ∈ Finset.range (M + 1),
            (1 / ((Nat.factorial (i + 1) : ℕ) : ℝ))
              * ∑ s : SizeProfile (n + 1) (i + 1),
                  ∏ j : Fin (i + 1), kpG ρ γ₀ (profileNat s j) :=
          Finset.sum_congr rfl (fun n hn =>
            kpTreeCoeff_recurrence_rect M (by omega)
              (by have := Finset.mem_range.mp hn; omega) ρ γ₀)
      _ = ∑ i ∈ Finset.range (M + 1), ∑ n ∈ Finset.range (M + 1),
            (1 / ((Nat.factorial (i + 1) : ℕ) : ℝ))
              * ∑ s : SizeProfile (n + 1) (i + 1),
                  ∏ j : Fin (i + 1), kpG ρ γ₀ (profileNat s j) :=
          Finset.sum_comm
      _ = ∑ i ∈ Finset.range (M + 1),
            (1 / ((Nat.factorial (i + 1) : ℕ) : ℝ))
              * ∑ n ∈ Finset.range (M + 1),
                  ∑ s : SizeProfile (n + 1) (i + 1),
                    ∏ j : Fin (i + 1), kpG ρ γ₀ (profileNat s j) :=
          Finset.sum_congr rfl (fun i _ => by
            rw [Finset.mul_sum])
      _ = ∑ i ∈ Finset.range (M + 1),
            (1 / ((Nat.factorial (i + 1) : ℕ) : ℝ))
              * ∑ t ∈ boundedProfilesFinset M (i + 1),
                  ∏ j : Fin (i + 1), kpG ρ γ₀ ((t j : ℕ)) :=
          Finset.sum_congr rfl (fun i _ => by
            rw [sum_profileSum_eq_boundedSum M (i + 1)
              (by omega) ρ γ₀])
      _ ≤ ∑ i ∈ Finset.range (M + 1),
            (1 / ((Nat.factorial (i + 1) : ℕ) : ℝ))
              * (kpX M ρ γ₀) ^ (i + 1) :=
          Finset.sum_le_sum (fun i _ =>
            mul_le_mul_of_nonneg_left
              (le_of_le_of_eq
                (boundedSum_le_indepSum hρ M (i + 1) γ₀)
                (indepSum_eq_kpX_pow M (i + 1) ρ γ₀))
              (by positivity))
      _ = ∑ i ∈ Finset.range (M + 1),
            (kpX M ρ γ₀) ^ (i + 1)
              / ((Nat.factorial (i + 1) : ℕ) : ℝ) :=
          Finset.sum_congr rfl (fun i _ => by
            rw [one_div, inv_mul_eq_div])
  · rw [kpTreeCoeff_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one]

end LatticeGauge
