/-
LatticeGauge/ConnectorClusters.lean — PEDRA 50, Gate 50-A5: THE
DOUBLE BARRIER — connector clusters born from inclusion-exclusion,
with no metric anywhere (architecture: Sol/GPT-5.6; execution:
Fable).

The identity of this gate:
  B_k(z) − B_k(z|P) − B_k(z|Q) + B_k(z|P∧Q)
    = Connector_k(z,P,Q),
the coefficient supported EXACTLY on connected clusters containing
at least one P-forbidden AND at least one Q-forbidden polymer.
At the cluster-sum level (all four series absolutely convergent
under KP by restriction monotonicity) the same inclusion-exclusion
holds, and the gas cross-ratio
  gas(z)·gas(z|P∧Q) / (gas(z|P)·gas(z|Q)) = exp(connectorSum)
follows by pure exp arithmetic.

NOT claimed: Cov(f,g) = connector series (the wiring to
Z[fg]·Z − Z[f]·Z[g] is a LATER gate); no distance, no cdist, no
SimpleGraph/plaquetteGraph distance, no 64^d, no q^d, no walks,
no geometric tails, no exponential clustering, no thermodynamic
limit, no continuum, no mass gap. After this gate the geometric
question finally has a legitimate object to measure: a CONNECTED
thing that hits here and hits there.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.ForbiddenClusters

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## A5.1 — double restriction and the allowed-conjunction -/

/-- Restricting a restriction is restricting by the conjunction. -/
theorem restrictedActivity_restrictedActivity
    (z : Polymer N → ℝ) (P Q : Polymer N → Prop) :
    restrictedActivity (restrictedActivity z P) Q
      = restrictedActivity z (fun η => P η ∧ Q η) := by
  funext η
  unfold restrictedActivity
  by_cases hQ : Q η
  · by_cases hP : P η
    · rw [if_pos hQ, if_pos hP, if_pos ⟨hP, hQ⟩]
    · rw [if_pos hQ, if_neg hP, if_neg (fun h => hP h.1)]
  · rw [if_neg hQ, if_neg (fun h => hQ h.2)]

theorem tupleAllowed_and_iff (P Q : Polymer N → Prop) {k : ℕ}
    (δ : Fin k → Polymer N) :
    TupleAllowed (fun η => P η ∧ Q η) δ
      ↔ TupleAllowed P δ ∧ TupleAllowed Q δ := by
  unfold TupleAllowed
  exact forall_and

/-! ## A5.2 — the connector coefficient -/

/-- A tuple hits BOTH barriers: some entry is P-forbidden and
    some entry is Q-forbidden (light API, following the A4
    style: negations of TupleAllowed, no new structure). -/
def TupleHitsBothForbidden (P Q : Polymer N → Prop) {k : ℕ}
    (δ : Fin k → Polymer N) : Prop :=
  ¬ TupleAllowed P δ ∧ ¬ TupleAllowed Q δ

noncomputable def kpConnectorUnrootedCoeff (k : ℕ)
    (z : Polymer N → ℝ) (P Q : Polymer N → Prop) : ℝ :=
  (∑ δ : Fin k → Polymer N,
      if TupleHitsBothForbidden P Q δ then
        ((ursellCoeff (N := N) (fun i => (δ i).val) : ℤ) : ℝ)
          * ∏ i : Fin k, z (δ i)
      else 0)
    / ((Nat.factorial k : ℕ) : ℝ)

/-! ## A5.3 — COEFFICIENT INCLUSION-EXCLUSION -/

theorem kpConnector_inclusion_exclusion (k : ℕ)
    (z : Polymer N → ℝ) (P Q : Polymer N → Prop) :
    kpSignedUnrootedCoeff (N := N) k z
      - kpSignedUnrootedCoeff k (restrictedActivity z P)
      - kpSignedUnrootedCoeff k (restrictedActivity z Q)
      + kpSignedUnrootedCoeff k
          (restrictedActivity z (fun η => P η ∧ Q η))
      = kpConnectorUnrootedCoeff k z P Q := by
  unfold kpSignedUnrootedCoeff kpConnectorUnrootedCoeff
  rw [div_sub_div_same, div_sub_div_same, div_add_div_same]
  congr 1
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  rw [prod_restrictedActivity_eq, prod_restrictedActivity_eq,
    prod_restrictedActivity_eq]
  by_cases hP : TupleAllowed P δ <;>
    by_cases hQ : TupleAllowed Q δ
  · rw [if_pos hP, if_pos hQ,
      if_pos ((tupleAllowed_and_iff P Q δ).mpr ⟨hP, hQ⟩),
      if_neg (fun h => h.1 hP)]
    ring
  · rw [if_pos hP, if_neg hQ,
      if_neg (fun h => hQ ((tupleAllowed_and_iff P Q δ).mp h).2),
      if_neg (fun h => h.1 hP)]
    ring
  · rw [if_neg hP, if_pos hQ,
      if_neg (fun h => hP ((tupleAllowed_and_iff P Q δ).mp h).1),
      if_neg (fun h => h.2 hQ)]
    ring
  · rw [if_neg hP, if_neg hQ,
      if_neg (fun h => hP ((tupleAllowed_and_iff P Q δ).mp h).1),
      if_pos ⟨hP, hQ⟩]
    ring

/-! ## A5.4 — connected-only localization (stone 37 again) -/

theorem kpConnectorUnrootedCoeff_eq_connected_sum (k : ℕ)
    (z : Polymer N → ℝ) (P Q : Polymer N → Prop) :
    kpConnectorUnrootedCoeff (N := N) k z P Q
      = (∑ δ ∈ Finset.univ.filter
          (fun δ : Fin k → Polymer N =>
            (polymerIncompatibilityGraph (N := N)
              (fun i => (δ i).val)).Connected
              ∧ TupleHitsBothForbidden P Q δ),
          ((ursellCoeff (N := N) (fun i => (δ i).val) : ℤ) : ℝ)
            * ∏ i : Fin k, z (δ i))
        / ((Nat.factorial k : ℕ) : ℝ) := by
  unfold kpConnectorUnrootedCoeff
  congr 1
  have h1 : (∑ δ : Fin k → Polymer N,
      if TupleHitsBothForbidden P Q δ then
        ((ursellCoeff (N := N) (fun i => (δ i).val) : ℤ) : ℝ)
          * ∏ i : Fin k, z (δ i)
      else 0)
      = ∑ δ ∈ Finset.univ.filter
          (fun δ : Fin k → Polymer N =>
            TupleHitsBothForbidden P Q δ),
          ((ursellCoeff (N := N) (fun i => (δ i).val) : ℤ) : ℝ)
            * ∏ i : Fin k, z (δ i) :=
    (Finset.sum_filter _ _).symm
  rw [h1]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro δ hδ
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hδ).2.2⟩
  · intro δ hδ hδnot
    have hnc : ¬ (polymerIncompatibilityGraph (N := N)
        (fun i => (δ i).val)).Connected := by
      intro hc
      exact hδnot (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,
          ⟨hc, (Finset.mem_filter.mp hδ).2⟩⟩)
    rw [ursellCoeff_of_not_connected _ hnc]
    simp

/-! ## A5.5 — absolute summability and the CONNECTOR SUM -/

theorem summable_abs_kpConnectorUnrootedCoeff
    {z a : Polymer N → ℝ} (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a)
    (P Q : Polymer N → Prop) :
    Summable (fun k =>
      |kpConnectorUnrootedCoeff (N := N) k z P Q|) := by
  have hid : ∀ k, kpConnectorUnrootedCoeff (N := N) k z P Q
      = kpSignedUnrootedCoeff k z
        - kpSignedUnrootedCoeff k (restrictedActivity z P)
        - kpSignedUnrootedCoeff k (restrictedActivity z Q)
        + kpSignedUnrootedCoeff k
            (restrictedActivity z (fun η => P η ∧ Q η)) :=
    fun k => (kpConnector_inclusion_exclusion k z P Q).symm
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _)
    (fun k => ?_)
    ((((summable_abs_kpSignedUnrootedCoeff ha hKP).add
      (summable_abs_kpSignedUnrootedCoeff ha
        (abstractKP_restrictedActivity P hKP))).add
      (summable_abs_kpSignedUnrootedCoeff ha
        (abstractKP_restrictedActivity Q hKP))).add
      (summable_abs_kpSignedUnrootedCoeff ha
        (abstractKP_restrictedActivity
          (fun η => P η ∧ Q η) hKP)))
  rw [hid k]
  calc |kpSignedUnrootedCoeff (N := N) k z
        - kpSignedUnrootedCoeff k (restrictedActivity z P)
        - kpSignedUnrootedCoeff k (restrictedActivity z Q)
        + kpSignedUnrootedCoeff k
            (restrictedActivity z (fun η => P η ∧ Q η))|
      ≤ |kpSignedUnrootedCoeff (N := N) k z
          - kpSignedUnrootedCoeff k (restrictedActivity z P)
          - kpSignedUnrootedCoeff k (restrictedActivity z Q)|
        + |kpSignedUnrootedCoeff k
            (restrictedActivity z (fun η => P η ∧ Q η))| :=
        abs_add _ _
    _ ≤ (|kpSignedUnrootedCoeff (N := N) k z
          - kpSignedUnrootedCoeff k (restrictedActivity z P)|
        + |kpSignedUnrootedCoeff k (restrictedActivity z Q)|)
        + |kpSignedUnrootedCoeff k
            (restrictedActivity z (fun η => P η ∧ Q η))| := by
        exact add_le_add_right (abs_sub _ _) _
    _ ≤ ((|kpSignedUnrootedCoeff (N := N) k z|
          + |kpSignedUnrootedCoeff k (restrictedActivity z P)|)
        + |kpSignedUnrootedCoeff k (restrictedActivity z Q)|)
        + |kpSignedUnrootedCoeff k
            (restrictedActivity z (fun η => P η ∧ Q η))| := by
        exact add_le_add_right
          (add_le_add_right (abs_sub _ _) _) _

/-- The connector cluster sum. -/
noncomputable def connectorClusterSum (z : Polymer N → ℝ)
    (P Q : Polymer N → Prop) : ℝ :=
  ∑' n, kpConnectorUnrootedCoeff (N := N) n z P Q

/-- **CLUSTER-SUM INCLUSION-EXCLUSION**: the double-barrier
    combination of cluster sums IS the connector series. -/
theorem clusterSum_inclusion_exclusion {z a : Polymer N → ℝ}
    (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a)
    (P Q : Polymer N → Prop) :
    (∑' n, kpSignedUnrootedCoeff (N := N) n z)
      - (∑' n, kpSignedUnrootedCoeff n (restrictedActivity z P))
      - (∑' n, kpSignedUnrootedCoeff n (restrictedActivity z Q))
      + (∑' n, kpSignedUnrootedCoeff n
          (restrictedActivity z (fun η => P η ∧ Q η)))
      = connectorClusterSum (N := N) z P Q := by
  have hS0 : Summable
      (fun n => kpSignedUnrootedCoeff (N := N) n z) :=
    summable_kpSignedUnrootedCoeff ha hKP
  have hSP : Summable (fun n =>
      kpSignedUnrootedCoeff n (restrictedActivity z P)) :=
    summable_kpSignedUnrootedCoeff ha
      (abstractKP_restrictedActivity P hKP)
  have hSQ : Summable (fun n =>
      kpSignedUnrootedCoeff n (restrictedActivity z Q)) :=
    summable_kpSignedUnrootedCoeff ha
      (abstractKP_restrictedActivity Q hKP)
  have hSPQ : Summable (fun n =>
      kpSignedUnrootedCoeff n
        (restrictedActivity z (fun η => P η ∧ Q η))) :=
    summable_kpSignedUnrootedCoeff ha
      (abstractKP_restrictedActivity (fun η => P η ∧ Q η) hKP)
  unfold connectorClusterSum
  rw [← tsum_sub hS0 hSP, ← tsum_sub (hS0.sub hSP) hSQ,
    ← tsum_add ((hS0.sub hSP).sub hSQ) hSPQ]
  exact tsum_congr
    (fun k => kpConnector_inclusion_exclusion k z P Q)

/-! ## A5.6 — the gas cross-ratio (pure exp arithmetic) -/

/-- **GAS CROSS-RATIO**: the double ratio of gases is the
    exponential of the connector series — exp arithmetic only,
    nothing assumed nonzero, no covariance claimed. -/
theorem typedPolymerGas_cross_ratio {z a : Polymer N → ℝ}
    (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a)
    (P Q : Polymer N → Prop) :
    (typedPolymerGas (N := N) z
        * typedPolymerGas (N := N)
            (restrictedActivity z (fun η => P η ∧ Q η)))
      / (typedPolymerGas (N := N) (restrictedActivity z P)
        * typedPolymerGas (N := N) (restrictedActivity z Q))
      = Real.exp (connectorClusterSum (N := N) z P Q) := by
  rw [typedPolymerGas_eq_exp_tsum_of_KP ha hKP,
    typedPolymerGas_restricted_eq_exp ha hKP P,
    typedPolymerGas_restricted_eq_exp ha hKP Q,
    typedPolymerGas_restricted_eq_exp ha hKP
      (fun η => P η ∧ Q η),
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_sub,
    ← clusterSum_inclusion_exclusion ha hKP P Q]
  congr 1
  ring

/-! ## A5.7 — the concrete double barrier -/

/-- Specialization: for 0 ≤ β ≤ 1/40000 and TWO barriers of the
    remoteAllowed shape (two cores, two supports), the gas
    cross-ratio is the exponential of the connector series of
    connected clusters hitting BOTH barriers. -/
theorem polymer_cross_ratio_eq_exp_connector {β : ℝ}
    (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T T' : Finset (Polymer N)) (s s' : Set (Link N)) :
    (typedPolymerGas (N := N)
        (fun η => polymerWeight (N := N) μm β χ η.val)
        * typedPolymerGas (N := N)
            (restrictedActivity
              (fun η => polymerWeight (N := N) μm β χ η.val)
              (fun η => remoteAllowed (N := N) T s η
                ∧ remoteAllowed T' s' η)))
      / (typedPolymerGas (N := N)
          (restrictedActivity
            (fun η => polymerWeight (N := N) μm β χ η.val)
            (remoteAllowed T s))
        * typedPolymerGas (N := N)
            (restrictedActivity
              (fun η => polymerWeight (N := N) μm β χ η.val)
              (remoteAllowed T' s')))
      = Real.exp (connectorClusterSum (N := N)
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed T s) (remoteAllowed T' s')) :=
  typedPolymerGas_cross_ratio
    (fun γ => Nat.cast_nonneg _)
    (abstractKP_of_beta_le_one_div_40000 μm hβ mχ hχabs hsmall)
    (remoteAllowed T s) (remoteAllowed T' s')

end LatticeGauge
