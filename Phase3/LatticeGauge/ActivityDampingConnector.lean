/-
LatticeGauge/ActivityDampingConnector.lean — PEDRA 52,
Gate 52-C: THE DAMPED CONNECTOR
(architecture: Sol/GPT-5.6; execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): Stone 51-C wrote
the difference between the regional and the full core exponent as
a connector cluster sum between two barriers (the core-relative
one and the regional one). Under continuous remote activity
damping the SAME inclusion–exclusion holds coefficient by
coefficient, with the count weight

    1 − θ^{tupleTouchCount r δ}

riding on every tuple that hits both barriers: positions are
counted (repetitions included), the Ursell factor, the product of
the ORIGINAL activities, the casts and the 1/k! are exactly those
of the Stone 49/50 coefficients. Orientation (consistent with
51-C, `region − full = connector`):

    E_T(θ) − E_T(1) = C_{T,r}(θ),      E_T(1) − E_T(θ) = −C_{T,r}(θ).

This gate builds:

  * kpDampedConnectorUnrootedCoeff — the damped connector
    coefficient (filter `TupleHitsBothForbidden P (regionAllowed r)`,
    weight 1 − θ^{tupleTouchCount});
  * the coefficient-level inclusion–exclusion, from the definitions
    and the 52-A/C1 bridges; the regional filter is inserted using
    only the implication  TupleAllowed (regionAllowed r) δ →
    tupleTouchCount r δ = 0 → weight 0  (never its converse, which
    fails at θ = 1);
  * the domination |c_k| ≤ (1−θ)·k·A_k for 0 ≤ θ ≤ 1 (A_k the
    absolute connector coefficient of |w|), the summability of the
    damped series (52-A0 first moment), and the passage to the
    series: E_T(θ) − E_T(1) = C_{T,r}(θ);
  * the endpoints θ = 0 (the Stone 51 connector), θ = 1 (zero) and
    r = ∅ (zero), with k = 0 and 0⁰ handled explicitly;
  * the eroded bound |C_{T,r}(θ)| ≤ (1−θ)·e^{−((n−m_T:ℕ))/2}·q′
    (q′ = b_T·2/113, natural truncated subtraction BEFORE the cast,
    no 8/(3e) factor — the 52-A0 first moment does not carry it)
    and the exponential control |1 − e^{C}| ≤ d·e^{2q′} with
    d = (1−θ)·e^{−((n−m_T:ℕ))/2}, 0 ≤ d ≤ 1 by the truncation,
    plus the repurchased form with e^{−n/2}·e^{m_T/2}.

HARD HOLD (not here): the sums of the two columns, the budgets
(1/2,3) and (7/8,1) applied, the Stone 52 capstone and its
constant; any general |e^a − e^b| lemma; Gibbs-measure, boundary-
condition, modified-action or switch-off interpretations;
thermodynamic limit, continuum, mass gap. No project-local
scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.ActivityDampingLedger
import LatticeGauge.ActivityRestrictionColumnBounds

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## 52-C.1 — the damped connector coefficient -/

/-- **The damped connector coefficient**: the tuple sum over tuples
    hitting BOTH barriers (P-forbidden somewhere and r-touching
    somewhere), each weighted by 1 − θ^{tupleTouchCount r δ}
    (positions counted, repetitions included), times the Ursell
    factor and the product of the ORIGINAL activities; divided by
    k! outside the sum, exactly as in `kpConnectorUnrootedCoeff`. -/
noncomputable def kpDampedConnectorUnrootedCoeff (k : ℕ)
    (z : Polymer N → ℝ) (P : Polymer N → Prop)
    (r : Set (Link N)) (θ : ℝ) : ℝ :=
  (∑ δ : Fin k → Polymer N,
      if TupleHitsBothForbidden P (regionAllowed (N := N) r) δ then
        (1 - θ ^ tupleTouchCount r δ)
          * (((ursellCoeff (N := N) (fun i => (δ i).val) : ℤ) : ℝ)
              * ∏ i : Fin k, z (δ i))
      else 0)
    / ((Nat.factorial k : ℕ) : ℝ)

/-- The regional allowed-tuple predicate IS the vanishing of the
    position count (definitional unfolding of `TupleAllowed` +
    `tupleTouchCount_eq_zero_iff`). Only the direction
    `TupleAllowed → count = 0` is used to insert the filter. -/
theorem tupleAllowed_regionAllowed_iff_tupleTouchCount_eq_zero
    (r : Set (Link N)) {k : ℕ} (δ : Fin k → Polymer N) :
    TupleAllowed (regionAllowed (N := N) r) δ ↔ tupleTouchCount r δ = 0 := by
  unfold TupleAllowed
  exact (tupleTouchCount_eq_zero_iff r δ).symm

/-- **Order k = 0**: the empty tuple is allowed everywhere, so it
    hits no barrier — the coefficient vanishes (whatever θ, no 0⁰
    issue arises: the weight is never evaluated). -/
theorem kpDampedConnectorUnrootedCoeff_order_zero
    (z : Polymer N → ℝ) (P : Polymer N → Prop) (r : Set (Link N)) (θ : ℝ) :
    kpDampedConnectorUnrootedCoeff (N := N) 0 z P r θ = 0 := by
  unfold kpDampedConnectorUnrootedCoeff
  rw [Finset.univ_unique, Finset.sum_singleton]
  have hP : TupleAllowed P (default : Fin 0 → Polymer N) := fun i => Fin.elim0 i
  rw [if_neg (fun h => h.1 hP), zero_div]

/-! ## 52-C.2 — coefficient-level inclusion–exclusion -/

/-- **DAMPED INCLUSION–EXCLUSION (coefficients)**: the four-term
    combination of the Stone 49 coefficients of the damped and the
    original activity, restricted or not by P, IS the damped
    connector coefficient. Orientation: (damped, restricted) −
    (damped, free) − (original, restricted) + (original, free).
    The regional filter enters only through
    `TupleAllowed (regionAllowed r) δ → tupleTouchCount r δ = 0 →
    1 − θ^0 = 0`; no converse is used. No hypothesis on θ. -/
theorem kpDampedConnector_inclusion_exclusion (k : ℕ)
    (z : Polymer N → ℝ) (P : Polymer N → Prop)
    (r : Set (Link N)) (θ : ℝ) :
    kpSignedUnrootedCoeff (N := N) k
        (restrictedActivity (dampedActivity z r θ) P)
      - kpSignedUnrootedCoeff (N := N) k (dampedActivity z r θ)
      - kpSignedUnrootedCoeff (N := N) k (restrictedActivity z P)
      + kpSignedUnrootedCoeff (N := N) k z
      = kpDampedConnectorUnrootedCoeff k z P r θ := by
  unfold kpSignedUnrootedCoeff kpDampedConnectorUnrootedCoeff
  rw [div_sub_div_same, div_sub_div_same, div_add_div_same]
  congr 1
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  rw [prod_restrictedActivity_eq, prod_restrictedActivity_eq,
    prod_dampedActivity_tuple]
  by_cases hP : TupleAllowed P δ
  · rw [if_pos hP, if_pos hP, if_neg (fun h => h.1 hP)]
    ring
  · by_cases hQ : TupleAllowed (regionAllowed (N := N) r) δ
    · -- the regional filter: allowed ⇒ count 0 ⇒ weight 1 − θ⁰ = 0
      have hc : tupleTouchCount r δ = 0 :=
        (tupleAllowed_regionAllowed_iff_tupleTouchCount_eq_zero r δ).mp hQ
      rw [if_neg hP, if_neg hP, if_neg (fun h => h.2 hQ), hc, pow_zero]
      ring
    · rw [if_neg hP, if_neg hP, if_pos ⟨hP, hQ⟩]
      ring

/-! ## 52-C.3 — domination by the absolute connector coefficient -/

/-- **DOMINATION**: for 0 ≤ θ ≤ 1,
    |c_k^{damped}| ≤ (1 − θ) · k · A_k(|z|), where A_k is the absolute
    connector coefficient (`kpAbsConnectorUnrootedCoeff`) between P
    and the regional barrier. The weight is paid by
    1 − θ^{j} ≤ j(1 − θ) ≤ k(1 − θ) (52-A0 count lemma and
    tupleTouchCount ≤ k). -/
theorem abs_kpDampedConnectorUnrootedCoeff_le (k : ℕ)
    (z : Polymer N → ℝ) (P : Polymer N → Prop)
    (r : Set (Link N)) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |kpDampedConnectorUnrootedCoeff (N := N) k z P r θ|
      ≤ (1 - θ) * (k : ℝ)
          * kpAbsConnectorUnrootedCoeff k (fun η => |z η|) P
              (regionAllowed (N := N) r) := by
  unfold kpDampedConnectorUnrootedCoeff kpAbsConnectorUnrootedCoeff
  rw [← mul_div_assoc, abs_div, Nat.abs_cast]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _)
    (Finset.sum_le_sum (fun δ _ => ?_))
  by_cases h : TupleHitsBothForbidden P (regionAllowed (N := N) r) δ
  · rw [if_pos h, if_pos h, abs_mul, abs_mul, Finset.abs_prod,
      ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    have hw0 : 0 ≤ 1 - θ ^ tupleTouchCount r δ :=
      one_sub_dampedPow_nonneg h0 h1 _
    have hw : |1 - θ ^ tupleTouchCount r δ| ≤ (1 - θ) * (k : ℝ) := by
      rw [abs_of_nonneg hw0]
      calc 1 - θ ^ tupleTouchCount r δ
          ≤ (tupleTouchCount r δ : ℝ) * (1 - θ) :=
            one_sub_dampedPow_le_nat_mul_one_sub h0 h1 _
        _ ≤ (k : ℝ) * (1 - θ) :=
            mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr (tupleTouchCount_le r δ)) (by linarith)
        _ = (1 - θ) * (k : ℝ) := mul_comm _ _
    have hrest : 0 ≤ (((ursellCoeff (N := N) (fun i => (δ i).val)).natAbs : ℕ) : ℝ)
        * ∏ i : Fin k, |z (δ i)| :=
      mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => abs_nonneg _))
    calc |1 - θ ^ tupleTouchCount r δ|
          * ((((ursellCoeff (N := N) (fun i => (δ i).val)).natAbs : ℕ) : ℝ)
              * ∏ i : Fin k, |z (δ i)|)
        ≤ ((1 - θ) * (k : ℝ))
          * ((((ursellCoeff (N := N) (fun i => (δ i).val)).natAbs : ℕ) : ℝ)
              * ∏ i : Fin k, |z (δ i)|) :=
          mul_le_mul_of_nonneg_right hw hrest
      _ = (1 - θ) * (k : ℝ)
          * ((((ursellCoeff (N := N) (fun i => (δ i).val)).natAbs : ℕ) : ℝ)
              * ∏ i : Fin k, |z (δ i)|) := by ring
  · rw [if_neg h, if_neg h, abs_zero, mul_zero]

/-! ## 52-C.4 — the damped connector series -/

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **The damped connector** C_{T,r}(θ): the series of the damped
    connector coefficients of the polymer weight between the
    core-relative barrier (remote-allowed for T at s) and the
    regional barrier r. A connector of clusters between two
    barriers, weighted by the damping count — nothing more. -/
noncomputable def activityDampingConnector (β : ℝ) (χ : G → ℝ)
    (T : Finset (Polymer N)) (s r : Set (Link N)) (θ : ℝ) : ℝ :=
  ∑' k, kpDampedConnectorUnrootedCoeff (N := N) k
    (fun η => polymerWeight (N := N) μm β χ η.val)
    (remoteAllowed (N := N) T s) r θ

/-- **Summability of the damped connector series**, under the
    separation of the two barrier regions (the 52-A0 first moment
    is the majorant; nothing about the connector is assumed). -/
theorem summable_kpDampedConnectorUnrootedCoeff
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {q : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) (∅ : Finset (Polymer N)) r) q)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    Summable (fun k : ℕ =>
      |kpDampedConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s) r θ|) := by
  have hmaj := summable_nat_mul_kpAbsConnector_polymerWeight
    μm hβ mχ hχabs hsmall hwsep
  rw [← regionAllowed_eq_remoteAllowed_empty] at hmaj
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    (Summable.mul_left (1 - θ) hmaj)
  have := abs_kpDampedConnectorUnrootedCoeff_le k
    (fun η => polymerWeight (N := N) μm β χ η.val)
    (remoteAllowed (N := N) T s) r h0 h1
  rw [mul_assoc] at this
  exact this

/-- **DAMPED INCLUSION–EXCLUSION (series)**: E_T(θ) − E_T(1) =
    C_{T,r}(θ). All four cluster series are summable by KP (the
    damped ones through the 52-A transport, which needs 0 ≤ θ ≤ 1);
    the passage is `tsum_sub`/`tsum_add` + the coefficient identity.
    Orientation identical to Stone 51-C. -/
theorem dampedActivityCoreExponent_sub_full_eq_activityDampingConnector
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r : Set (Link N))
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    dampedActivityCoreExponent μm β χ T s r θ
        - fullActivityCoreExponent μm β χ T s
      = activityDampingConnector μm β χ T s r θ := by
  have ha : ∀ γ : Polymer N, 0 ≤ ((γ.val.card : ℕ) : ℝ) :=
    fun γ => Nat.cast_nonneg _
  have hKP := abstractKP_of_beta_le_one_div_40000 (N := N) μm hβ mχ hχabs hsmall
  have hKPθ := abstractKP_dampedActivity r h0 h1 hKP
  have hSPθ : Summable (fun n => kpSignedUnrootedCoeff (N := N) n
      (restrictedActivity
        (dampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) r θ)
        (remoteAllowed (N := N) T s))) :=
    summable_kpSignedUnrootedCoeff ha
      (abstractKP_restrictedActivity (remoteAllowed (N := N) T s) hKPθ)
  have hS0θ : Summable (fun n => kpSignedUnrootedCoeff (N := N) n
      (dampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) r θ)) :=
    summable_kpSignedUnrootedCoeff ha hKPθ
  have hSP : Summable (fun n => kpSignedUnrootedCoeff (N := N) n
      (restrictedActivity (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s))) :=
    summable_kpSignedUnrootedCoeff ha
      (abstractKP_restrictedActivity (remoteAllowed (N := N) T s) hKP)
  have hS0 : Summable (fun n => kpSignedUnrootedCoeff (N := N) n
      (fun η => polymerWeight (N := N) μm β χ η.val)) :=
    summable_kpSignedUnrootedCoeff ha hKP
  unfold dampedActivityCoreExponent fullActivityCoreExponent
    activityDampingConnector
  have hlin : ∀ a b c d : ℝ, (a - b) - (c - d) = a - b - c + d := by
    intro a b c d; ring
  rw [hlin, ← tsum_sub hSPθ hS0θ, ← tsum_sub (hSPθ.sub hS0θ) hSP,
    ← tsum_add ((hSPθ.sub hS0θ).sub hSP) hS0]
  exact tsum_congr (fun k =>
    kpDampedConnector_inclusion_exclusion k _ (remoteAllowed (N := N) T s) r θ)

/-- The inverse orientation: E_T(1) − E_T(θ) = −C_{T,r}(θ). -/
theorem full_sub_dampedActivityCoreExponent_eq_neg_activityDampingConnector
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r : Set (Link N))
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    fullActivityCoreExponent μm β χ T s
        - dampedActivityCoreExponent μm β χ T s r θ
      = - activityDampingConnector μm β χ T s r θ := by
  rw [← dampedActivityCoreExponent_sub_full_eq_activityDampingConnector
    μm hβ mχ hχabs hsmall T s r h0 h1]
  ring

/-- **Exact factorization of the connector column** (the 52-B
    connector column, termwise): e^{E_T(1)} − e^{E_T(θ)}
    = e^{E_T(1)} · (1 − e^{C_{T,r}(θ)}). -/
theorem exp_full_sub_exp_damped_eq_activityDampingConnector
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r : Set (Link N))
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    Real.exp (fullActivityCoreExponent μm β χ T s)
        - Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
      = Real.exp (fullActivityCoreExponent μm β χ T s)
          * (1 - Real.exp (activityDampingConnector μm β χ T s r θ)) := by
  have hC := dampedActivityCoreExponent_sub_full_eq_activityDampingConnector
    μm hβ mχ hχabs hsmall T s r h0 h1
  have hdamped : dampedActivityCoreExponent μm β χ T s r θ
      = fullActivityCoreExponent μm β χ T s
        + activityDampingConnector μm β χ T s r θ := by
    rw [← hC]; ring
  rw [hdamped, Real.exp_add]
  ring

/-! ## 52-C.5 — endpoints -/

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **θ = 1 (coefficients)**: the weight 1 − 1^{count} vanishes
    termwise (whatever the count, including positive counts). -/
theorem kpDampedConnectorUnrootedCoeff_one (k : ℕ)
    (z : Polymer N → ℝ) (P : Polymer N → Prop) (r : Set (Link N)) :
    kpDampedConnectorUnrootedCoeff (N := N) k z P r 1 = 0 := by
  unfold kpDampedConnectorUnrootedCoeff
  rw [Finset.sum_eq_zero, zero_div]
  intro δ _
  split_ifs
  · rw [one_pow, sub_self, zero_mul]
  · rfl

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **θ = 1 (series)**: the damped connector vanishes. -/
theorem activityDampingConnector_one (β : ℝ) (χ : G → ℝ)
    (T : Finset (Polymer N)) (s r : Set (Link N)) :
    activityDampingConnector μm β χ T s r 1 = 0 := by
  unfold activityDampingConnector
  simp only [kpDampedConnectorUnrootedCoeff_one, tsum_zero]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **θ = 0 (coefficients)**: on a tuple hitting the regional
    barrier the count is positive, so 1 − 0^{count} = 1 and the
    coefficient IS the Stone 50 connector coefficient. (0⁰ never
    occurs on the filter: the filter forces count ≥ 1.) -/
theorem kpDampedConnectorUnrootedCoeff_zero (k : ℕ)
    (z : Polymer N → ℝ) (P : Polymer N → Prop) (r : Set (Link N)) :
    kpDampedConnectorUnrootedCoeff (N := N) k z P r 0
      = kpConnectorUnrootedCoeff (N := N) k z P (regionAllowed (N := N) r) := by
  unfold kpDampedConnectorUnrootedCoeff kpConnectorUnrootedCoeff
  congr 1
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  by_cases h : TupleHitsBothForbidden P (regionAllowed (N := N) r) δ
  · rw [if_pos h, if_pos h]
    have hc : tupleTouchCount r δ ≠ 0 := fun hc =>
      h.2 ((tupleAllowed_regionAllowed_iff_tupleTouchCount_eq_zero r δ).mpr hc)
    rw [zero_pow hc, sub_zero, one_mul]
  · rw [if_neg h, if_neg h]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **θ = 0 (series)**: the damped connector IS the Stone 51
    activity-restriction connector. -/
theorem activityDampingConnector_zero (β : ℝ) (χ : G → ℝ)
    (T : Finset (Polymer N)) (s r : Set (Link N)) :
    activityDampingConnector μm β χ T s r 0
      = activityRestrictionConnector μm β χ T s r := by
  unfold activityDampingConnector activityRestrictionConnector
    connectorClusterSum
  exact tsum_congr (fun k => kpDampedConnectorUnrootedCoeff_zero k _ _ r)

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **r = ∅ (coefficients)**: no position touches ∅, the count is
    0, the weight 1 − θ⁰ = 0 (0⁰ = 1 included), the coefficient
    vanishes for every θ. -/
theorem kpDampedConnectorUnrootedCoeff_empty_region (k : ℕ)
    (z : Polymer N → ℝ) (P : Polymer N → Prop) (θ : ℝ) :
    kpDampedConnectorUnrootedCoeff (N := N) k z P (∅ : Set (Link N)) θ = 0 := by
  unfold kpDampedConnectorUnrootedCoeff
  rw [Finset.sum_eq_zero, zero_div]
  intro δ _
  split_ifs
  · rw [tupleTouchCount_empty_region, pow_zero, sub_self, zero_mul]
  · rfl

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **r = ∅ (series)**: the damped connector vanishes. -/
theorem activityDampingConnector_empty_region (β : ℝ) (χ : G → ℝ)
    (T : Finset (Polymer N)) (s : Set (Link N)) (θ : ℝ) :
    activityDampingConnector μm β χ T s (∅ : Set (Link N)) θ = 0 := by
  unfold activityDampingConnector
  simp only [kpDampedConnectorUnrootedCoeff_empty_region, tsum_zero]

/-! ## 52-C.6 — the eroded bound -/

/-- **ERODED BOUND**: under the separation of s and r at scale n
    (`WalkBarrierSeparated s r n`) and T a touching core of s,
      |C_{T,r}(θ)| ≤ (1 − θ) · e^{−((n − m_T : ℕ)) / 2} · q′,
    q′ = card(barrierLinkFinset T s) · (2/113), the subtraction
    n − m_T TRUNCATED in ℕ before the cast (the empty remote core
    has mass 0). Route: 51-D erosion + domination + the 52-A0 first
    moment Σ k·A_k ≤ e^{−q/2}·q′ (which carries no 8/(3e)). -/
theorem abs_activityDampingConnector_le_eroded
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |activityDampingConnector μm β χ T s r θ|
      ≤ (1 - θ)
        * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2)
        * (((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
  have hero := walkBarrierSeparated_barrierRegions_sub_familyMass
    hT (empty_mem_typedTouchingFamilies r) hsep
  have hzero : familyTotalCard (∅ : Finset (Polymer N)) = 0 := by
    unfold familyTotalCard
    exact Finset.sum_empty
  rw [hzero, Nat.add_zero] at hero
  -- the majorant series and its first moment (52-A0)
  have hmaj := summable_nat_mul_kpAbsConnector_polymerWeight
    μm hβ mχ hχabs hsmall hero
  have hmom := tsum_nat_mul_kpAbsConnector_polymerWeight_le_local_P
    μm hβ mχ hχabs hsmall hero
  rw [← regionAllowed_eq_remoteAllowed_empty] at hmaj hmom
  have hdom : ∀ k : ℕ,
      |kpDampedConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s) r θ|
      ≤ (1 - θ) * ((k : ℝ)
          * kpAbsConnectorUnrootedCoeff k
              (fun η => |polymerWeight (N := N) μm β χ η.val|)
              (remoteAllowed (N := N) T s) (regionAllowed (N := N) r)) := by
    intro k
    have := abs_kpDampedConnectorUnrootedCoeff_le k
      (fun η => polymerWeight (N := N) μm β χ η.val)
      (remoteAllowed (N := N) T s) r h0 h1
    rw [mul_assoc] at this
    exact this
  have hsumabs : Summable (fun k : ℕ =>
      |kpDampedConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s) r θ|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hdom
      (Summable.mul_left (1 - θ) hmaj)
  unfold activityDampingConnector
  have h1' : ‖∑' k : ℕ, kpDampedConnectorUnrootedCoeff (N := N) k
      (fun η => polymerWeight (N := N) μm β χ η.val)
      (remoteAllowed (N := N) T s) r θ‖
      ≤ ∑' k : ℕ, ‖kpDampedConnectorUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s) r θ‖ := by
    refine norm_tsum_le_tsum_norm ?_
    simpa [Real.norm_eq_abs] using hsumabs
  simp only [Real.norm_eq_abs] at h1'
  have h2 : (∑' k : ℕ, |kpDampedConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s) r θ|)
      ≤ ∑' k : ℕ, (1 - θ) * ((k : ℝ)
          * kpAbsConnectorUnrootedCoeff k
              (fun η => |polymerWeight (N := N) μm β χ η.val|)
              (remoteAllowed (N := N) T s) (regionAllowed (N := N) r)) :=
    tsum_le_tsum hdom hsumabs (Summable.mul_left (1 - θ) hmaj)
  rw [tsum_mul_left] at h2
  have h3 : (1 - θ) * (∑' k : ℕ, (k : ℝ)
        * kpAbsConnectorUnrootedCoeff k
            (fun η => |polymerWeight (N := N) μm β χ η.val|)
            (remoteAllowed (N := N) T s) (regionAllowed (N := N) r))
      ≤ (1 - θ) * (Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2)
          * (((barrierLinkFinset T s).card : ℝ) * (2 / 113))) :=
    mul_le_mul_of_nonneg_left hmom (by linarith)
  calc |∑' k : ℕ, kpDampedConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s) r θ|
      ≤ _ := h1'
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ = (1 - θ) * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2)
          * (((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by ring

/-! ## 52-C.7 — exponential control of the connector column -/

/-- **EXPONENTIAL CONTROL**: |1 − e^{C_{T,r}(θ)}| ≤ d · e^{2q′} with
    d = (1 − θ) · e^{−((n − m_T : ℕ))/2}. Here 0 ≤ d ≤ 1 in ALL cases
    (including m_T > n): 0 ≤ 1 − θ ≤ 1 and the exponent is
    −(natural)/2 ≤ 0 by the truncated subtraction. Route:
    `abs_exp_sub_one_le_decay_exp` with x = C, q = q′, B = 2q′. -/
theorem abs_one_sub_exp_activityDampingConnector_le_eroded
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |1 - Real.exp (activityDampingConnector μm β χ T s r θ)|
      ≤ ((1 - θ) * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2))
        * Real.exp (2 * (((barrierLinkFinset T s).card : ℝ) * (2 / 113))) := by
  have hC := abs_activityDampingConnector_le_eroded
    μm hβ mχ hχabs hsmall hT hsep h0 h1
  have he0 : (0:ℝ) ≤ Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) :=
    (Real.exp_pos _).le
  have he1 : Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    refine Real.exp_le_exp.mpr ?_
    have hnat : (0:ℝ) ≤ (((n - familyTotalCard T : ℕ)) : ℝ) := Nat.cast_nonneg _
    linarith
  have hd0 : (0:ℝ) ≤ (1 - θ) * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) :=
    mul_nonneg (by linarith) he0
  have hd1 : (1 - θ) * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) ≤ 1 :=
    mul_le_one₀ (by linarith) he0 he1
  have hq0 : (0:ℝ) ≤ ((barrierLinkFinset T s).card : ℝ) * (2 / 113) :=
    mul_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hmain := abs_exp_sub_one_le_decay_exp hd0 hd1 hq0 hC
    (le_refl (2 * (((barrierLinkFinset T s).card : ℝ) * (2 / 113))))
  rw [abs_sub_comm]
  exact hmain

/-- **Repurchased erosion**: the same control with the decay
    e^{−n/2} and the mass repurchased at half rate, e^{m_T/2}
    (`exp_neg_nat_sub_half_le`, valid with the truncation). -/
theorem abs_one_sub_exp_activityDampingConnector_le_decay
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |1 - Real.exp (activityDampingConnector μm β χ T s r θ)|
      ≤ (1 - θ) * Real.exp (-(n : ℝ) / 2)
        * Real.exp ((familyTotalCard T : ℝ) / 2
            + 2 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
  have hmain := abs_one_sub_exp_activityDampingConnector_le_eroded
    μm hβ mχ hχabs hsmall hT hsep h0 h1
  have herode := exp_neg_nat_sub_half_le n (familyTotalCard T)
  have hθ : (0:ℝ) ≤ 1 - θ := by linarith
  calc |1 - Real.exp (activityDampingConnector μm β χ T s r θ)|
      ≤ ((1 - θ) * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2))
          * Real.exp (2 * (((barrierLinkFinset T s).card : ℝ) * (2 / 113))) :=
        hmain
    _ ≤ ((1 - θ) * (Real.exp (-(n : ℝ) / 2)
            * Real.exp ((familyTotalCard T : ℝ) / 2)))
          * Real.exp (2 * (((barrierLinkFinset T s).card : ℝ) * (2 / 113))) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left herode hθ) (Real.exp_pos _).le
    _ = (1 - θ) * Real.exp (-(n : ℝ) / 2)
        * Real.exp ((familyTotalCard T : ℝ) / 2
            + 2 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
        have hb : (2 : ℝ) * (((barrierLinkFinset T s).card : ℝ) * (2 / 113))
            = 2 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113) := by ring
        rw [hb, Real.exp_add]
        ring

#print axioms kpDampedConnectorUnrootedCoeff_order_zero
#print axioms kpDampedConnector_inclusion_exclusion
#print axioms abs_kpDampedConnectorUnrootedCoeff_le
#print axioms summable_kpDampedConnectorUnrootedCoeff
#print axioms dampedActivityCoreExponent_sub_full_eq_activityDampingConnector
#print axioms full_sub_dampedActivityCoreExponent_eq_neg_activityDampingConnector
#print axioms exp_full_sub_exp_damped_eq_activityDampingConnector
#print axioms activityDampingConnector_zero
#print axioms activityDampingConnector_one
#print axioms activityDampingConnector_empty_region
#print axioms abs_activityDampingConnector_le_eroded
#print axioms abs_one_sub_exp_activityDampingConnector_le_eroded
#print axioms abs_one_sub_exp_activityDampingConnector_le_decay

end LatticeGauge
