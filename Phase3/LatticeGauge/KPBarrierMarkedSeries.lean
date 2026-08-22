/-
LatticeGauge/KPBarrierMarkedSeries.lean — PEDRA 50, Gate 50-A9
(module 3/3, editorial split 50-A9E; architecture: Sol;
execution: Fable).

A9.4/A9.5 — the LOCAL rooted KP package and the signed
capstones: partial sums ≤ P-localized envelope, summability,
positive tsums (P and Q), and
  Σ'ₖ |connector| ≤ kpForbiddenRootEnvelope(|z|, a, P) (and Q),
the domination passing through the FILTERED positive connector
— the global B⁺ of A8 has already forgotten where the barrier
is. Stones 47/48 consumed, never redone. Real.exp (a γ) appears
ONLY in the inherited KP envelope — it is not a tilt.

Hard holds as in KPBarrierConnectorPositive.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.KPBarrierMarkedRoot

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## A9.4 — the LOCAL rooted KP package (47/48 consumed) -/

theorem sum_range_kpAbsConnector_le {ρ a : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis ρ a) (P Q : Polymer N → Prop) :
    ∀ K : ℕ, (∑ k ∈ Finset.range K,
        kpAbsConnectorUnrootedCoeff k ρ P Q)
      ≤ kpForbiddenRootEnvelope ρ a P := by
  intro K
  rcases K with _ | M
  · rw [Finset.range_zero, Finset.sum_empty]
    exact kpForbiddenRootEnvelope_nonneg hρ P
  · rw [Finset.sum_range_succ'
      (fun k => kpAbsConnectorUnrootedCoeff k ρ P Q) M,
      kpAbsConnectorUnrootedCoeff_zero, add_zero]
    calc (∑ n ∈ Finset.range M,
        kpAbsConnectorUnrootedCoeff (n + 1) ρ P Q)
        ≤ ∑ n ∈ Finset.range M, kpForbiddenRootCoeff n ρ P :=
          Finset.sum_le_sum (fun n _ =>
            kpAbsConnector_succ_le_forbiddenRoot n hρ P Q)
      _ ≤ kpForbiddenRootEnvelope ρ a P := by
          unfold kpForbiddenRootCoeff kpForbiddenRootEnvelope
          rw [Finset.sum_comm]
          refine Finset.sum_le_sum (fun γ₀ _ => ?_)
          by_cases h : P γ₀
          · simp only [if_pos h]
            rw [Finset.sum_const_zero]
          · simp only [if_neg h]
            rw [← Finset.mul_sum]
            refine mul_le_mul_of_nonneg_left ?_ (hρ γ₀)
            calc (∑ n ∈ Finset.range M, kpUrsellCoeff n ρ γ₀)
                ≤ ∑' n : ℕ, kpUrsellCoeff n ρ γ₀ :=
                  sum_le_tsum (Finset.range M)
                    (fun n _ => kpUrsellCoeff_nonneg n hρ γ₀)
                    (summable_kpUrsellCoeff hρ ha hKP γ₀)
              _ ≤ Real.exp (a γ₀) :=
                  tsum_kpUrsellCoeff_le_exp hρ ha hKP γ₀

theorem summable_kpAbsConnectorUnrootedCoeff
    {ρ a : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis ρ a) (P Q : Polymer N → Prop) :
    Summable (fun k =>
      kpAbsConnectorUnrootedCoeff (N := N) k ρ P Q) :=
  summable_of_sum_range_le
    (fun k => kpAbsConnectorUnrootedCoeff_nonneg k hρ P Q)
    (sum_range_kpAbsConnector_le hρ ha hKP P Q)

/-- **A9.4 positive capstone (P side)**. -/
theorem tsum_kpAbsConnector_le {ρ a : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis ρ a) (P Q : Polymer N → Prop) :
    (∑' k : ℕ, kpAbsConnectorUnrootedCoeff (N := N) k ρ P Q)
      ≤ kpForbiddenRootEnvelope ρ a P :=
  Real.tsum_le_of_sum_range_le
    (fun k => kpAbsConnectorUnrootedCoeff_nonneg k hρ P Q)
    (sum_range_kpAbsConnector_le hρ ha hKP P Q)

/-- **A9.4 positive capstone (Q side)** — by P/Q symmetry. -/
theorem tsum_kpAbsConnector_le_Q {ρ a : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis ρ a) (P Q : Polymer N → Prop) :
    (∑' k : ℕ, kpAbsConnectorUnrootedCoeff (N := N) k ρ P Q)
      ≤ kpForbiddenRootEnvelope ρ a Q :=
  calc (∑' k : ℕ, kpAbsConnectorUnrootedCoeff (N := N) k ρ P Q)
      = ∑' k : ℕ, kpAbsConnectorUnrootedCoeff (N := N) k ρ Q P :=
        tsum_congr (fun k =>
          kpAbsConnectorUnrootedCoeff_symm k ρ P Q)
    _ ≤ kpForbiddenRootEnvelope ρ a Q :=
        tsum_kpAbsConnector_le hρ ha hKP Q P

/-! ## A9.5 — the SIGNED local capstones (the domination passes
    through the FILTERED positive connector — the global B⁺ of A8
    has already forgotten where the barrier is) -/

/-- **CAPSTONE 50-A9 (P side)**. -/
theorem tsum_abs_kpConnectorUnrootedCoeff_le
    {z a : Polymer N → ℝ} (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (fun η => |z η|) a)
    (P Q : Polymer N → Prop) :
    (∑' k : ℕ, |kpConnectorUnrootedCoeff (N := N) k z P Q|)
      ≤ kpForbiddenRootEnvelope (fun η => |z η|) a P := by
  have hρ : ∀ η : Polymer N, 0 ≤ |z η| := fun η => abs_nonneg _
  exact le_trans
    (tsum_le_tsum
      (fun k => abs_kpConnectorUnrootedCoeff_le_filtered k z P Q)
      (Summable.of_nonneg_of_le (fun k => abs_nonneg _)
        (fun k =>
          abs_kpConnectorUnrootedCoeff_le_filtered k z P Q)
        (summable_kpAbsConnectorUnrootedCoeff hρ ha hKP P Q))
      (summable_kpAbsConnectorUnrootedCoeff hρ ha hKP P Q))
    (tsum_kpAbsConnector_le hρ ha hKP P Q)

/-- **CAPSTONE 50-A9 (Q side)**. -/
theorem tsum_abs_kpConnectorUnrootedCoeff_le_Q
    {z a : Polymer N → ℝ} (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (fun η => |z η|) a)
    (P Q : Polymer N → Prop) :
    (∑' k : ℕ, |kpConnectorUnrootedCoeff (N := N) k z P Q|)
      ≤ kpForbiddenRootEnvelope (fun η => |z η|) a Q := by
  have hρ : ∀ η : Polymer N, 0 ≤ |z η| := fun η => abs_nonneg _
  exact le_trans
    (tsum_le_tsum
      (fun k => abs_kpConnectorUnrootedCoeff_le_filtered k z P Q)
      (Summable.of_nonneg_of_le (fun k => abs_nonneg _)
        (fun k =>
          abs_kpConnectorUnrootedCoeff_le_filtered k z P Q)
        (summable_kpAbsConnectorUnrootedCoeff hρ ha hKP P Q))
      (summable_kpAbsConnectorUnrootedCoeff hρ ha hKP P Q))
    (tsum_kpAbsConnector_le_Q hρ ha hKP P Q)

#print axioms tsum_abs_kpConnectorUnrootedCoeff_le
#print axioms tsum_abs_kpConnectorUnrootedCoeff_le_Q

end LatticeGauge
