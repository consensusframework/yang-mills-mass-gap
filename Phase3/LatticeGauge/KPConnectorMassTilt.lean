/-
LatticeGauge/KPConnectorMassTilt.lean — PEDRA 50, Gate 50-A10:
THE MASS TILT AND THE ABSTRACT CONNECTOR TAIL (architecture: Sol;
execution: Fable).

The abstract mass-tilted connector tail under a tilted KP
hypothesis. The chain in the kernel:
  tuple total mass ≥ n (A7, consumed ONCE)
    ⟹ tilted tuple weight = exp(λ·mass)·original ≥ exp(λn)·original
    ⟹ original connector ≤ exp(-λn)·tilted connector
    ⟹ Σ'|signed connector| ≤ exp(-λn)·tilted localized KP envelope.
The exp(-λn) is born from exp(-λn)·exp(λn) = 1 — a legitimate
exponential factor in the separation n. λ ≥ 0 and ρ ≥ 0 are
abstract; the KP hypothesis FOR THE TILTED ACTIVITY is received
as a hypothesis — its concrete verification for polymerWeight/β
belongs to the NEXT gate and is NOT claimed here.

NOT here (hard hold): no specialization to polymerWeight, no
λ = 1, no new numerical condition on β, no 1/40000-supports-tilt
claim, no Stone 45 / 64^d / 16·64^(2m) / geometric series, no
estimate of the forbidden-root envelope, no covariance, no second
insertion, no SimpleGraph.dist/edist/cdist, no changes to A7/A9,
no volume-uniform clustering, no correlation decay/clustering
naming, no thermodynamic limit, no continuum, no mass gap, no
Clay claim.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.WalkSeparation
import LatticeGauge.KPBarrierMarkedSeries

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## A10.1 — the mass-tilted activity -/

noncomputable def massTiltActivity (lam : ℝ) (ρ : Polymer N → ℝ)
    (η : Polymer N) : ℝ :=
  Real.exp (lam * ((η.val.card : ℕ) : ℝ)) * ρ η

/-- Nonnegativity of the tilted activity (exp > 0 makes the
    λ ≥ 0 hypothesis unnecessary here — recorded, not consumed). -/
theorem massTiltActivity_nonneg {lam : ℝ} {ρ : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) :
    ∀ η, 0 ≤ massTiltActivity lam ρ η :=
  fun η => mul_nonneg (Real.exp_pos _).le (hρ η)

/-! ## A10.2 — exact factorization on the tuple -/

/-- **The tilt factorizes exactly through the additive mass**:
    Π tilted = exp(λ·tupleTotalCard)·Π original — the visible
    bridge prod_mul_distrib → exp_sum → mul_sum → cast. -/
theorem prod_massTiltActivity (lam : ℝ) (ρ : Polymer N → ℝ)
    {k : ℕ} (δ : Fin k → Polymer N) :
    (∏ i : Fin k, massTiltActivity lam ρ (δ i))
      = Real.exp (lam * ((tupleTotalCard δ : ℕ) : ℝ))
          * ∏ i : Fin k, ρ (δ i) := by
  unfold massTiltActivity
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  unfold tupleTotalCard
  rw [Nat.cast_sum, Finset.mul_sum]

/-- **The central tilt identity**: the tilted positive tuple
    weight is exp(λ·mass) times the original. -/
theorem kpAbsSummand_massTilt (lam : ℝ) (ρ : Polymer N → ℝ)
    {k : ℕ} (δ : Fin k → Polymer N) :
    kpAbsSummand (massTiltActivity lam ρ) δ
      = Real.exp (lam * ((tupleTotalCard δ : ℕ) : ℝ))
          * kpAbsSummand ρ δ := by
  unfold kpAbsSummand
  rw [prod_massTiltActivity]
  ring

/-! ## A10.3 — the A7 mass enters (consumed exactly once) -/

/-- **exp(λn)·summand ≤ tilted summand** for a connected
    connector tuple across walk-separated barriers — the visible
    chain n ≤ tupleTotalCard δ ⟹ λn ≤ λ·mass ⟹ exp mono. -/
theorem exp_mass_mul_kpAbsSummand_le_tilt {lam : ℝ}
    (hlam : 0 ≤ lam) {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    {k : ℕ} {δ : Fin k → Polymer N}
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hconn : (polymerIncompatibilityGraph (N := N)
      (fun i => (δ i).val)).Connected)
    (hhit : TupleHitsBothForbidden
      (remoteAllowed (N := N) T s)
      (remoteAllowed (N := N) T' s') δ)
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    Real.exp (lam * (n : ℝ)) * kpAbsSummand ρ δ
      ≤ kpAbsSummand (massTiltActivity lam ρ) δ := by
  rw [kpAbsSummand_massTilt]
  refine mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr ?_) (kpAbsSummand_nonneg hρ δ)
  exact mul_le_mul_of_nonneg_left
    (Nat.cast_le.mpr
      (connector_tupleTotalCard_ge hconn hhit hwsep)) hlam

/-- **Disconnected ⟹ zero absolute summand** (Stone 37
    consumed, not redone). -/
theorem kpAbsSummand_eq_zero_of_not_connected {k : ℕ}
    (ρ : Polymer N → ℝ) {δ : Fin k → Polymer N}
    (h : ¬ (polymerIncompatibilityGraph (N := N)
      (fun i => (δ i).val)).Connected) :
    kpAbsSummand ρ δ = 0 := by
  unfold kpAbsSummand
  rw [ursellCoeff_of_not_connected _ h, Int.natAbs_zero,
    Nat.cast_zero, zero_mul]

/-! ## A10.4 — lifting to the coefficient -/

/-- **exp(λn)·connector ≤ tilted connector** — summand by
    summand: hits+connected pays the toll (A10.3), disconnected
    is zero on both sides, non-hits is zero on both sides. -/
theorem exp_mass_mul_kpAbsConnector_le_tilt {lam : ℝ}
    (hlam : 0 ≤ lam) {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    {k : ℕ}
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    Real.exp (lam * (n : ℝ))
        * kpAbsConnectorUnrootedCoeff k ρ
            (remoteAllowed (N := N) T s)
            (remoteAllowed (N := N) T' s')
      ≤ kpAbsConnectorUnrootedCoeff k (massTiltActivity lam ρ)
          (remoteAllowed (N := N) T s)
          (remoteAllowed (N := N) T' s') := by
  rw [kpAbsConnectorUnrootedCoeff_eq,
    kpAbsConnectorUnrootedCoeff_eq, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun δ _ => ?_)
  by_cases hhit : TupleHitsBothForbidden
    (remoteAllowed (N := N) T s)
    (remoteAllowed (N := N) T' s') δ
  · rw [if_pos hhit, if_pos hhit]
    by_cases hconn : (polymerIncompatibilityGraph (N := N)
      (fun i => (δ i).val)).Connected
    · exact exp_mass_mul_kpAbsSummand_le_tilt
        hlam hρ hconn hhit hwsep
    · rw [kpAbsSummand_eq_zero_of_not_connected ρ hconn,
        kpAbsSummand_eq_zero_of_not_connected
          (massTiltActivity lam ρ) hconn, mul_zero]
  · rw [if_neg hhit, if_neg hhit, mul_zero]

/-- **The consumable form**: original ≤ exp(-λn)·tilted, born
    from exp(-λn)·exp(λn) = 1 — the exact birthplace of the
    exponential factor. -/
theorem kpAbsConnector_le_exp_neg_mul_tilt {lam : ℝ}
    (hlam : 0 ≤ lam) {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    {k : ℕ}
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    kpAbsConnectorUnrootedCoeff k ρ
        (remoteAllowed (N := N) T s)
        (remoteAllowed (N := N) T' s')
      ≤ Real.exp (-lam * (n : ℝ))
          * kpAbsConnectorUnrootedCoeff k (massTiltActivity lam ρ)
              (remoteAllowed (N := N) T s)
              (remoteAllowed (N := N) T' s') := by
  have h1 : Real.exp (-lam * (n : ℝ))
      * Real.exp (lam * (n : ℝ)) = 1 := by
    have h0 : -lam * (n : ℝ) + lam * (n : ℝ) = 0 := by ring
    rw [← Real.exp_add, h0, Real.exp_zero]
  calc (kpAbsConnectorUnrootedCoeff k ρ
        (remoteAllowed (N := N) T s)
        (remoteAllowed (N := N) T' s'))
      = (Real.exp (-lam * (n : ℝ)) * Real.exp (lam * (n : ℝ)))
          * kpAbsConnectorUnrootedCoeff k ρ
              (remoteAllowed (N := N) T s)
              (remoteAllowed (N := N) T' s') := by
        rw [h1, one_mul]
    _ = Real.exp (-lam * (n : ℝ))
          * (Real.exp (lam * (n : ℝ))
            * kpAbsConnectorUnrootedCoeff k ρ
                (remoteAllowed (N := N) T s)
                (remoteAllowed (N := N) T' s')) :=
        mul_assoc _ _ _
    _ ≤ Real.exp (-lam * (n : ℝ))
          * kpAbsConnectorUnrootedCoeff k (massTiltActivity lam ρ)
              (remoteAllowed (N := N) T s)
              (remoteAllowed (N := N) T' s') :=
        mul_le_mul_of_nonneg_left
          (exp_mass_mul_kpAbsConnector_le_tilt hlam hρ hwsep)
          (Real.exp_pos _).le

/-! ## A10.5 — summability and the positive tail (A9 consumed
    for the TILTED activity; the KP induction never reopened) -/

theorem summable_kpAbsConnector_of_massTilt {lam : ℝ}
    (hlam : 0 ≤ lam) {ρ a : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (massTiltActivity lam ρ) a)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    Summable (fun k => kpAbsConnectorUnrootedCoeff (N := N) k ρ
      (remoteAllowed (N := N) T s)
      (remoteAllowed (N := N) T' s')) :=
  Summable.of_nonneg_of_le
    (fun k => kpAbsConnectorUnrootedCoeff_nonneg k hρ _ _)
    (fun _ => kpAbsConnector_le_exp_neg_mul_tilt hlam hρ hwsep)
    (Summable.mul_left _
      (summable_kpAbsConnectorUnrootedCoeff
        (massTiltActivity_nonneg hρ) ha hKP _ _))

/-- **A10 positive capstone (P side)**: the untilted positive
    connector tail pays exp(-λn) against the tilted localized
    envelope. -/
theorem tsum_kpAbsConnector_le_exp_neg_mul_tiltedEnvelope
    {lam : ℝ} (hlam : 0 ≤ lam) {ρ a : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (massTiltActivity lam ρ) a)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    (∑' k : ℕ, kpAbsConnectorUnrootedCoeff (N := N) k ρ
        (remoteAllowed (N := N) T s)
        (remoteAllowed (N := N) T' s'))
      ≤ Real.exp (-lam * (n : ℝ))
          * kpForbiddenRootEnvelope (massTiltActivity lam ρ) a
              (remoteAllowed (N := N) T s) := by
  calc (∑' k : ℕ, kpAbsConnectorUnrootedCoeff (N := N) k ρ
      (remoteAllowed (N := N) T s)
      (remoteAllowed (N := N) T' s'))
      ≤ ∑' k : ℕ, Real.exp (-lam * (n : ℝ))
          * kpAbsConnectorUnrootedCoeff (N := N) k
              (massTiltActivity lam ρ)
              (remoteAllowed (N := N) T s)
              (remoteAllowed (N := N) T' s') :=
        tsum_le_tsum
          (fun k => kpAbsConnector_le_exp_neg_mul_tilt
            hlam hρ hwsep)
          (summable_kpAbsConnector_of_massTilt
            hlam hρ ha hKP hwsep)
          (Summable.mul_left _
            (summable_kpAbsConnectorUnrootedCoeff
              (massTiltActivity_nonneg hρ) ha hKP _ _))
    _ = Real.exp (-lam * (n : ℝ))
          * ∑' k : ℕ, kpAbsConnectorUnrootedCoeff (N := N) k
              (massTiltActivity lam ρ)
              (remoteAllowed (N := N) T s)
              (remoteAllowed (N := N) T' s') := tsum_mul_left
    _ ≤ Real.exp (-lam * (n : ℝ))
          * kpForbiddenRootEnvelope (massTiltActivity lam ρ) a
              (remoteAllowed (N := N) T s) :=
        mul_le_mul_of_nonneg_left
          (tsum_kpAbsConnector_le
            (massTiltActivity_nonneg hρ) ha hKP _ _)
          (Real.exp_pos _).le

/-- **A10 positive capstone (Q side)**. -/
theorem tsum_kpAbsConnector_le_exp_neg_mul_tiltedEnvelope_Q
    {lam : ℝ} (hlam : 0 ≤ lam) {ρ a : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (massTiltActivity lam ρ) a)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    (∑' k : ℕ, kpAbsConnectorUnrootedCoeff (N := N) k ρ
        (remoteAllowed (N := N) T s)
        (remoteAllowed (N := N) T' s'))
      ≤ Real.exp (-lam * (n : ℝ))
          * kpForbiddenRootEnvelope (massTiltActivity lam ρ) a
              (remoteAllowed (N := N) T' s') := by
  calc (∑' k : ℕ, kpAbsConnectorUnrootedCoeff (N := N) k ρ
      (remoteAllowed (N := N) T s)
      (remoteAllowed (N := N) T' s'))
      ≤ ∑' k : ℕ, Real.exp (-lam * (n : ℝ))
          * kpAbsConnectorUnrootedCoeff (N := N) k
              (massTiltActivity lam ρ)
              (remoteAllowed (N := N) T s)
              (remoteAllowed (N := N) T' s') :=
        tsum_le_tsum
          (fun k => kpAbsConnector_le_exp_neg_mul_tilt
            hlam hρ hwsep)
          (summable_kpAbsConnector_of_massTilt
            hlam hρ ha hKP hwsep)
          (Summable.mul_left _
            (summable_kpAbsConnectorUnrootedCoeff
              (massTiltActivity_nonneg hρ) ha hKP _ _))
    _ = Real.exp (-lam * (n : ℝ))
          * ∑' k : ℕ, kpAbsConnectorUnrootedCoeff (N := N) k
              (massTiltActivity lam ρ)
              (remoteAllowed (N := N) T s)
              (remoteAllowed (N := N) T' s') := tsum_mul_left
    _ ≤ Real.exp (-lam * (n : ℝ))
          * kpForbiddenRootEnvelope (massTiltActivity lam ρ) a
              (remoteAllowed (N := N) T' s') :=
        mul_le_mul_of_nonneg_left
          (tsum_kpAbsConnector_le_Q
            (massTiltActivity_nonneg hρ) ha hKP _ _)
          (Real.exp_pos _).le

/-! ## A10.6 — the SIGNED capstones: the abstract mass-tilted
    connector tail under a tilted KP hypothesis -/

/-- **CAPSTONE 50-A10 (P side)**. -/
theorem tsum_abs_kpConnector_le_exp_neg_mul_tiltedEnvelope
    {lam : ℝ} (hlam : 0 ≤ lam) {z a : Polymer N → ℝ}
    (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis
      (massTiltActivity lam (fun η => |z η|)) a)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    (∑' k : ℕ, |kpConnectorUnrootedCoeff (N := N) k z
        (remoteAllowed (N := N) T s)
        (remoteAllowed (N := N) T' s')|)
      ≤ Real.exp (-lam * (n : ℝ))
          * kpForbiddenRootEnvelope
              (massTiltActivity lam (fun η => |z η|)) a
              (remoteAllowed (N := N) T s) := by
  have hρ : ∀ η : Polymer N, 0 ≤ |z η| := fun η => abs_nonneg _
  exact le_trans
    (tsum_le_tsum
      (fun k => abs_kpConnectorUnrootedCoeff_le_filtered
        k z _ _)
      (Summable.of_nonneg_of_le (fun k => abs_nonneg _)
        (fun k => abs_kpConnectorUnrootedCoeff_le_filtered
          k z _ _)
        (summable_kpAbsConnector_of_massTilt
          hlam hρ ha hKP hwsep))
      (summable_kpAbsConnector_of_massTilt
        hlam hρ ha hKP hwsep))
    (tsum_kpAbsConnector_le_exp_neg_mul_tiltedEnvelope
      hlam hρ ha hKP hwsep)

/-- **CAPSTONE 50-A10 (Q side)**. -/
theorem tsum_abs_kpConnector_le_exp_neg_mul_tiltedEnvelope_Q
    {lam : ℝ} (hlam : 0 ≤ lam) {z a : Polymer N → ℝ}
    (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis
      (massTiltActivity lam (fun η => |z η|)) a)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    (∑' k : ℕ, |kpConnectorUnrootedCoeff (N := N) k z
        (remoteAllowed (N := N) T s)
        (remoteAllowed (N := N) T' s')|)
      ≤ Real.exp (-lam * (n : ℝ))
          * kpForbiddenRootEnvelope
              (massTiltActivity lam (fun η => |z η|)) a
              (remoteAllowed (N := N) T' s') := by
  have hρ : ∀ η : Polymer N, 0 ≤ |z η| := fun η => abs_nonneg _
  exact le_trans
    (tsum_le_tsum
      (fun k => abs_kpConnectorUnrootedCoeff_le_filtered
        k z _ _)
      (Summable.of_nonneg_of_le (fun k => abs_nonneg _)
        (fun k => abs_kpConnectorUnrootedCoeff_le_filtered
          k z _ _)
        (summable_kpAbsConnector_of_massTilt
          hlam hρ ha hKP hwsep))
      (summable_kpAbsConnector_of_massTilt
        hlam hρ ha hKP hwsep))
    (tsum_kpAbsConnector_le_exp_neg_mul_tiltedEnvelope_Q
      hlam hρ ha hKP hwsep)

#print axioms tsum_abs_kpConnector_le_exp_neg_mul_tiltedEnvelope
#print axioms tsum_abs_kpConnector_le_exp_neg_mul_tiltedEnvelope_Q

end LatticeGauge
