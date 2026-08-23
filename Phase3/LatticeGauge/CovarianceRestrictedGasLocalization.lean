/-
LatticeGauge/CovarianceRestrictedGasLocalization.lean — PEDRA 50,
Gate 50-A16: THE REMOTE DOOR DOES NOT REINTRODUCE THE VOLUME
(architecture: Sol; execution: Fable).

The quotient (barrier-restricted gas)/(full gas) is controlled
ONLY by the local size of the barrier:
  restricted/full = exp(restricted C − full C)      (A3, exact)
  restricted C − full C = − Σ' forbidden            (A4, exact)
  |Σ' forbidden| ≤ Σ'|forbidden|
    = Σ'|connector with Q = False|                  (this gate:
      the second barrier EMPTY — a forbidden cluster IS a
      connector whose second barrier is the impossible one)
  ≤ forbidden-root envelope (A9) ≤ card(barrier)·2/113 (A12),
hence  restricted/full ≤ exp(card(barrierLinkFinset)·2/113)
and    0 < restricted/full  (from the exponential representation
— no external nonvanishing hypothesis anywhere). No wrapper is
invented for the restricted gas: the exact expression consumed by
typedPolymerGas_ratio_eq_exp_sub is used as-is.

This gate does NOT consume A15; it prepares the local door for
the future sum of cores.

NOT here (hard hold): no sum over cores T/T', no bridgeCore, no
familyTotalCard, no A15 tilt, no covariance numerator, no
two-barrier cross-ratio, no exp(connector) − 1 estimate, no
correlation decay/clustering, no SimpleGraph.dist, no
thermodynamic limit, no continuum, no mass gap, no Clay claim.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.CovarianceBridgeCoreTilt

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## A16.1 — the empty second barrier (by the logic of the
    definition; no artificial special case) -/

theorem tupleHitsBothForbidden_false_iff {k : ℕ}
    (P : Polymer N → Prop) (δ : Fin k → Polymer N) :
    TupleHitsBothForbidden P (fun _ => False) δ
      ↔ ¬ TupleAllowed P δ := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    have h1 : ¬ ∀ i : Fin k, P (δ i) := h
    obtain ⟨i₀, _⟩ := not_forall.mp h1
    exact fun hfalse => hfalse i₀

/-! ## A16.2 — forbidden = connector with Q = False
    (coefficient-wise; zero new inclusion-exclusion, zero new
    Ursell combinatorics) -/

theorem kpConnector_false_eq_forbidden (k : ℕ)
    (z : Polymer N → ℝ) (P : Polymer N → Prop) :
    kpConnectorUnrootedCoeff (N := N) k z P (fun _ => False)
      = kpForbiddenUnrootedCoeff (N := N) k z P := by
  unfold kpConnectorUnrootedCoeff kpForbiddenUnrootedCoeff
  congr 1
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  by_cases h : TupleAllowed P δ
  · rw [if_neg (fun hc : TupleHitsBothForbidden P
        (fun _ => False) δ => hc.1 h), if_pos h]
  · rw [if_pos ((tupleHitsBothForbidden_false_iff P δ).mpr h),
      if_neg h]

/-! ## A16.3 — the abstract one-barrier majorant (A9's signed
    capstone transported; summability reused, never rebuilt) -/

theorem tsum_abs_kpForbiddenUnrootedCoeff_le
    {z a : Polymer N → ℝ} (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a)
    (P : Polymer N → Prop) :
    (∑' k : ℕ, |kpForbiddenUnrootedCoeff (N := N) k z P|)
      ≤ kpForbiddenRootEnvelope (fun η => |z η|) a P :=
  calc (∑' k : ℕ, |kpForbiddenUnrootedCoeff (N := N) k z P|)
      = ∑' k : ℕ, |kpConnectorUnrootedCoeff (N := N) k z P
          (fun _ => False)| :=
        tsum_congr (fun k => by
          rw [kpConnector_false_eq_forbidden])
    _ ≤ kpForbiddenRootEnvelope (fun η => |z η|) a P :=
        tsum_abs_kpConnectorUnrootedCoeff_le ha hKP P
          (fun _ => False)

/-! ## A16.4 — the local physical specialization -/

theorem tsum_abs_kpForbidden_polymerWeight_le_barrier
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s : Set (Link N)) :
    (∑' k : ℕ, |kpForbiddenUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s)|)
      ≤ ((barrierLinkFinset T s).card : ℝ) * (2 / 113) := by
  have hKP := abstractKP_of_beta_le_one_div_40000
    (N := N) μm hβ mχ hχabs hsmall
  have ha : ∀ γ : Polymer N, 0 ≤ ((γ.val.card : ℕ) : ℝ) :=
    fun γ => Nat.cast_nonneg _
  refine le_trans (tsum_abs_kpForbiddenUnrootedCoeff_le
    ha hKP (remoteAllowed (N := N) T s)) ?_
  have henv : kpForbiddenRootEnvelope
      (fun η => |polymerWeight (N := N) μm β χ η.val|)
      (fun η => ((η.val.card : ℕ) : ℝ))
      (remoteAllowed (N := N) T s)
      = ∑ γ₀ : Polymer N,
          if remoteAllowed (N := N) T s γ₀ then 0
          else |polymerWeight (N := N) μm β χ γ₀.val|
            * Real.exp ((γ₀.val.card : ℕ) : ℝ) := rfl
  rw [henv]
  exact kpForbiddenRootEnvelope_le_barrierLinkCount
    μm hβ mχ hχabs hsmall T s

/-! ## A16.5 — exponent and local quotient (the exact identity
    is A4's tsum_restricted_sub_full, consumed, not rewrapped) -/

/-- The signed series is absolutely bounded by the local barrier
    size (norm_tsum_le_tsum_norm against the A4 summability). -/
theorem abs_tsum_kpForbidden_polymerWeight_le_barrier
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s : Set (Link N)) :
    |∑' k : ℕ, kpForbiddenUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s)|
      ≤ ((barrierLinkFinset T s).card : ℝ) * (2 / 113) := by
  have hKP := abstractKP_of_beta_le_one_div_40000
    (N := N) μm hβ mχ hχabs hsmall
  have ha : ∀ γ : Polymer N, 0 ≤ ((γ.val.card : ℕ) : ℝ) :=
    fun γ => Nat.cast_nonneg _
  have hsum := summable_abs_kpForbiddenUnrootedCoeff
    ha hKP (remoteAllowed (N := N) T s)
  have h1 : ‖∑' k : ℕ, kpForbiddenUnrootedCoeff (N := N) k
      (fun η => polymerWeight (N := N) μm β χ η.val)
      (remoteAllowed (N := N) T s)‖
      ≤ ∑' k : ℕ, ‖kpForbiddenUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s)‖ := by
    refine norm_tsum_le_tsum_norm ?_
    simpa [Real.norm_eq_abs] using hsum
  simp only [Real.norm_eq_abs] at h1
  exact h1.trans (tsum_abs_kpForbidden_polymerWeight_le_barrier
    μm hβ mχ hχabs hsmall T s)

/-- **CAPSTONE 50-A16 (bound)**: the barrier-restricted gas over
    the full gas pays at most the LOCAL exponential — the volume
    does not come back through the remote door. -/
theorem restrictedGas_div_fullGas_le_exp_barrier
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s : Set (Link N)) :
    typedPolymerGas (N := N) (restrictedActivity
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s))
      / typedPolymerGas (N := N)
          (fun η => polymerWeight (N := N) μm β χ η.val)
      ≤ Real.exp
          (((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
  have hKP := abstractKP_of_beta_le_one_div_40000
    (N := N) μm hβ mχ hχabs hsmall
  have ha : ∀ γ : Polymer N, 0 ≤ ((γ.val.card : ℕ) : ℝ) :=
    fun γ => Nat.cast_nonneg _
  rw [typedPolymerGas_ratio_eq_exp_sub ha hKP
    (remoteAllowed (N := N) T s)]
  refine Real.exp_le_exp.mpr ?_
  rw [tsum_restricted_sub_full ha hKP
    (remoteAllowed (N := N) T s)]
  refine le_trans (neg_le_abs _) ?_
  rw [abs_neg]
  exact abs_tsum_kpForbidden_polymerWeight_le_barrier
    μm hβ mχ hχabs hsmall T s

/-- **CAPSTONE 50-A16 (positivity)**: the quotient is positive
    FROM the exponential representation — no external
    nonvanishing hypothesis. -/
theorem restrictedGas_div_fullGas_pos
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s : Set (Link N)) :
    0 < typedPolymerGas (N := N) (restrictedActivity
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s))
      / typedPolymerGas (N := N)
          (fun η => polymerWeight (N := N) μm β χ η.val) := by
  have hKP := abstractKP_of_beta_le_one_div_40000
    (N := N) μm hβ mχ hχabs hsmall
  have ha : ∀ γ : Polymer N, 0 ≤ ((γ.val.card : ℕ) : ℝ) :=
    fun γ => Nat.cast_nonneg _
  rw [typedPolymerGas_ratio_eq_exp_sub ha hKP
    (remoteAllowed (N := N) T s)]
  exact Real.exp_pos _

#print axioms kpConnector_false_eq_forbidden
#print axioms restrictedGas_div_fullGas_le_exp_barrier
#print axioms restrictedGas_div_fullGas_pos

end LatticeGauge
