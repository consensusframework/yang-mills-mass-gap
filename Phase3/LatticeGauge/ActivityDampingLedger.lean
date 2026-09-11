/-
LatticeGauge/ActivityDampingLedger.lean — PEDRA 52,
Gate 52-B: THE EXACT TWO-COLUMN DAMPING LEDGER
(architecture: Sol/GPT-5.6; execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): Stone 51-B wrote
the difference between the Gibbs expectation and the activity-
restricted normalized polymer functional as an exact two-column
ledger. Under continuous remote activity damping the same
bookkeeping holds with the damping weight θ^{touchCount r T}
riding on every touching core: the damped functional is a finite
sum of core weights times θ^{touchCount} times exponentials of a
damped core exponent, and the difference with the Gibbs
expectation is, EXACTLY,

    Σ_{T touching}  θ^{touchCount r T} · W_T · (e^{E_T(1)} − e^{E_T(θ)})
  + Σ_{T bridge}    (1 − θ^{touchCount r T}) · W_T · e^{E_T(1)},

where E_T(1) is the Stone 51 full core exponent and E_T(θ) the
damped core exponent. On region-allowed cores the weight is 1
(touchCount = 0 by definition), so the first column restricts to
the Stone 51 allowed column there; the second column is supported
on bridge cores only. This gate builds:

  * dampedActivityCoreExponent — cluster sum of the damped activity
    restricted to the remote-allowed polymers of T, minus the
    cluster sum of the damped activity (the θ-analogue of
    `regionActivityCoreExponent`);
  * the damped gas ratio as an exponential (KP transported for
    0 ≤ θ ≤ 1; no denominator cancelled, nonvanishing never assumed);
  * the exponential form of the damped functional (weight
    θ^{touchCount} exhibited), and its allowed + bridge split;
  * CAPSTONE: the exact two-column damping ledger — an identity,
    no inequality anywhere;
  * the endpoints: θ = 0 reproduces the Stone 51 ledger literally,
    θ = 1 makes the difference vanish, r = ∅ makes the damping
    trivial (difference 0), and allowed cores carry weight 1.

HARD HOLD (not here): the damped connector coefficients' difference
(1 − θ^{tupleTouchCount}), any bound on either column, the
constants of Stone 52-A0, the Stone 52 capstone; Gibbs-measure,
boundary-condition, modified-action or switch-off interpretations;
thermodynamic limit, continuum, mass gap. No project-local
scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.ActivityDampedObservableGas

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## 52-B.1 — the damped core exponent -/

/-- The damped core exponent E_T(θ): cluster sum of the damped
    activity restricted to the remote-allowed polymers of the core T,
    minus the cluster sum of the damped activity. At θ = 0 it is the
    Stone 51 regional exponent, at θ = 1 the full exponent (proved
    below, not assumed). -/
noncomputable def dampedActivityCoreExponent (β : ℝ) (χ : G → ℝ)
    (T : Finset (Polymer N)) (s r : Set (Link N)) (θ : ℝ) : ℝ :=
  (∑' n, kpSignedUnrootedCoeff n
      (restrictedActivity
        (dampedActivity
          (fun η => polymerWeight (N := N) μm β χ η.val) r θ)
        (remoteAllowed T s)))
    - ∑' n, kpSignedUnrootedCoeff n
        (dampedActivity
          (fun η => polymerWeight (N := N) μm β χ η.val) r θ)

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Endpoint θ = 0**: the damped core exponent IS the Stone 51
    regional core exponent (restriction composed with restriction). -/
theorem dampedActivityCoreExponent_zero (β : ℝ) (χ : G → ℝ)
    (T : Finset (Polymer N)) (s r : Set (Link N)) :
    dampedActivityCoreExponent μm β χ T s r 0
      = regionActivityCoreExponent μm β χ T s r := by
  unfold dampedActivityCoreExponent regionActivityCoreExponent
  rw [dampedActivity_zero, restrictedActivity_regionAllowed_remoteAllowed]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Endpoint θ = 1**: the damped core exponent IS the full core
    exponent of Stone 51. -/
theorem dampedActivityCoreExponent_one (β : ℝ) (χ : G → ℝ)
    (T : Finset (Polymer N)) (s r : Set (Link N)) :
    dampedActivityCoreExponent μm β χ T s r 1
      = fullActivityCoreExponent μm β χ T s := by
  unfold dampedActivityCoreExponent fullActivityCoreExponent
  rw [dampedActivity_one]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Empty remote region**: no damping, the full exponent. -/
theorem dampedActivityCoreExponent_empty_region (β : ℝ) (χ : G → ℝ)
    (T : Finset (Polymer N)) (s : Set (Link N)) (θ : ℝ) :
    dampedActivityCoreExponent μm β χ T s (∅ : Set (Link N)) θ
      = fullActivityCoreExponent μm β χ T s := by
  unfold dampedActivityCoreExponent fullActivityCoreExponent
  rw [dampedActivity_empty_region]

/-! ## 52-B.2 — the damped gas ratio as an exponential -/

/-- **Damped gas ratio**: with the damped activity as base, KP is
    inherited for 0 ≤ θ ≤ 1 and the published ratio identity applies.
    No denominator is cancelled; nonvanishing is never assumed. -/
theorem dampedActivityGas_ratio_eq_exp
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r : Set (Link N))
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    typedPolymerGas (N := N)
        (restrictedActivity
          (dampedActivity
            (fun η => polymerWeight (N := N) μm β χ η.val) r θ)
          (remoteAllowed T s))
      / activityDampedPolymerGas μm β χ r θ
      = Real.exp (dampedActivityCoreExponent μm β χ T s r θ) := by
  unfold activityDampedPolymerGas dampedActivityCoreExponent
  exact typedPolymerGas_ratio_eq_exp_sub
    (fun γ => Nat.cast_nonneg _)
    (abstractKP_dampedActivity r h0 h1
      (abstractKP_of_beta_le_one_div_40000 μm hβ mχ hχabs hsmall))
    (remoteAllowed T s)

/-! ## 52-B.3 — exponential form of the damped functional -/

/-- **Exponential form of the damped functional**: the 52-A weighted
    regrouping divided termwise by the damped gas, each ratio an
    exponential of the damped core exponent, the weight
    θ^{touchCount r T} exhibited. No `DependsOnlyOn`, measurability
    or bound on f is needed on this side. -/
theorem activityDampedExpectation_eq_sum_core_mul_exp
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (f : Config N G → ℝ) (s r : Set (Link N))
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    activityDampedExpectation μm β χ f s r θ
      = ∑ T ∈ typedTouchingFamilies (N := N) s,
          θ ^ touchCount r T
            * typedMarkedCoreWeight μm β χ f T
            * Real.exp (dampedActivityCoreExponent μm β χ T s r θ) := by
  unfold activityDampedExpectation
  rw [activityDampedMarkedGas_eq_sum_core_mul_damped μm β χ f s r θ,
    Finset.sum_div]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [mul_div_assoc]
  congr 1
  exact dampedActivityGas_ratio_eq_exp μm hβ mχ hχabs hsmall T s r h0 h1

/-- **Allowed + bridge split of the damped functional**: on the
    allowed column the weight is 1 (touchCount = 0 by definition). -/
theorem activityDampedExpectation_eq_allowed_add_bridge
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (f : Config N G → ℝ) (s r : Set (Link N))
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    activityDampedExpectation μm β χ f s r θ
      = (∑ T ∈ activityAllowedCores (N := N) s r,
          typedMarkedCoreWeight μm β χ f T
            * Real.exp (dampedActivityCoreExponent μm β χ T s r θ))
        + ∑ T ∈ activityBridgeCores (N := N) s r,
          θ ^ touchCount r T
            * typedMarkedCoreWeight μm β χ f T
            * Real.exp (dampedActivityCoreExponent μm β χ T s r θ) := by
  rw [activityDampedExpectation_eq_sum_core_mul_exp μm hβ mχ hχabs hsmall
      f s r h0 h1,
    sum_touchingFamilies_eq_activityAllowed_add_bridge s r]
  congr 1
  refine Finset.sum_congr rfl (fun T hT => ?_)
  rw [pow_touchCount_eq_one_of_mem_activityAllowedCores θ hT, one_mul]

/-! ## 52-B.4 — CAPSTONE: the exact two-column damping ledger -/

/-- **The Gibbs expectation in the touching-core form with the
    full exponent** (the published Stone 50/51 representation,
    abbreviated by `fullActivityCoreExponent`). -/
theorem gibbsExpectation_eq_sum_core_mul_exp_full
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf) :
    gibbsExpectation (N := N) μm β χ f
      = ∑ T ∈ typedTouchingFamilies (N := N) s,
          typedMarkedCoreWeight μm β χ f T
            * Real.exp (fullActivityCoreExponent μm β χ T s) := by
  rw [gibbsExpectation_eq_sum_core_mul_exp μm hβ mχ hχabs hsmall hf mf hCf]
  rfl

/-- **CAPSTONE 52-B — THE EXACT TWO-COLUMN DAMPING LEDGER**: the
    difference between the Gibbs expectation and the normalized
    polymer functional under continuous remote activity damping is,
    exactly,
      (connector column, ALL touching cores)
          θ^{touchCount r T} · W_T · (e^{E_T(1)} − e^{E_T(θ)})
    + (bridge column, bridge cores only)
          (1 − θ^{touchCount r T}) · W_T · e^{E_T(1)}.
    Finite algebra only; no inequality; nothing cancelled. The weight
    is the count power θ^{touchCount}, never an indicator. -/
theorem gibbsExpectation_sub_activityDampedExpectation_eq_two_column_ledger
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (r : Set (Link N)) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    gibbsExpectation (N := N) μm β χ f
        - activityDampedExpectation μm β χ f s r θ
      = (∑ T ∈ typedTouchingFamilies (N := N) s,
          θ ^ touchCount r T
            * typedMarkedCoreWeight μm β χ f T
            * (Real.exp (fullActivityCoreExponent μm β χ T s)
                - Real.exp (dampedActivityCoreExponent μm β χ T s r θ)))
        + ∑ T ∈ activityBridgeCores (N := N) s r,
          (1 - θ ^ touchCount r T)
            * typedMarkedCoreWeight μm β χ f T
            * Real.exp (fullActivityCoreExponent μm β χ T s) := by
  rw [gibbsExpectation_eq_sum_core_mul_exp_full μm hβ mχ hχabs hsmall
      hf mf hCf,
    activityDampedExpectation_eq_sum_core_mul_exp μm hβ mχ hχabs hsmall
      f s r h0 h1]
  -- split the full-exponent sum into allowed + bridge; on the allowed
  -- column the weight is 1, so the full term is θ^0·W·e^{E(1)} there.
  have hfull : (∑ T ∈ typedTouchingFamilies (N := N) s,
        typedMarkedCoreWeight μm β χ f T
          * Real.exp (fullActivityCoreExponent μm β χ T s))
      = (∑ T ∈ typedTouchingFamilies (N := N) s,
          θ ^ touchCount r T
            * typedMarkedCoreWeight μm β χ f T
            * Real.exp (fullActivityCoreExponent μm β χ T s))
        + ∑ T ∈ activityBridgeCores (N := N) s r,
          (1 - θ ^ touchCount r T)
            * typedMarkedCoreWeight μm β χ f T
            * Real.exp (fullActivityCoreExponent μm β χ T s) := by
    rw [sum_touchingFamilies_eq_activityAllowed_add_bridge s r
        (fun T => typedMarkedCoreWeight μm β χ f T
          * Real.exp (fullActivityCoreExponent μm β χ T s)),
      sum_touchingFamilies_eq_activityAllowed_add_bridge s r
        (fun T => θ ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (fullActivityCoreExponent μm β χ T s))]
    have hallowed : (∑ T ∈ activityAllowedCores (N := N) s r,
          θ ^ touchCount r T
            * typedMarkedCoreWeight μm β χ f T
            * Real.exp (fullActivityCoreExponent μm β χ T s))
        = ∑ T ∈ activityAllowedCores (N := N) s r,
            typedMarkedCoreWeight μm β χ f T
              * Real.exp (fullActivityCoreExponent μm β χ T s) := by
      refine Finset.sum_congr rfl (fun T hT => ?_)
      rw [pow_touchCount_eq_one_of_mem_activityAllowedCores θ hT, one_mul]
    rw [hallowed, add_assoc, ← Finset.sum_add_distrib, add_right_inj]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    ring
  rw [hfull, add_sub_right_comm, ← Finset.sum_sub_distrib, add_left_inj]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  ring

/-! ## 52-B.5 — endpoints of the ledger -/

/-- **θ = 1**: the difference vanishes (the damped functional IS the
    Gibbs expectation; hypotheses of the published representation). -/
theorem gibbsExpectation_sub_activityDampedExpectation_one
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (r : Set (Link N)) :
    gibbsExpectation (N := N) μm β χ f
        - activityDampedExpectation μm β χ f s r 1 = 0 := by
  rw [activityDampedExpectation_one μm hβ mχ hχabs hf mf hCf r, sub_self]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **θ = 1, column by column**: both columns of the ledger vanish
    termwise (pure algebra, no hypothesis). -/
theorem two_column_ledger_one (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s r : Set (Link N)) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        (1 : ℝ) ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (fullActivityCoreExponent μm β χ T s)
              - Real.exp (dampedActivityCoreExponent μm β χ T s r 1)))
      + ∑ T ∈ activityBridgeCores (N := N) s r,
        (1 - (1 : ℝ) ^ touchCount r T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (fullActivityCoreExponent μm β χ T s) = 0 := by
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro T _
    rw [one_pow, sub_self, zero_mul, zero_mul]
  · intro T _
    rw [dampedActivityCoreExponent_one, sub_self, mul_zero]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **θ = 0, column by column**: the damping ledger evaluated at θ = 0
    IS the Stone 51 two-column restriction ledger — the connector
    column collapses to the allowed cores (weight 0^{touchCount} = 0
    on bridge cores, 1 on allowed cores, E_T(0) = regional exponent),
    and the bridge column carries weight 1 − 0 = 1. Pure algebra. -/
theorem two_column_ledger_zero (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s r : Set (Link N)) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        (0 : ℝ) ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (fullActivityCoreExponent μm β χ T s)
              - Real.exp (dampedActivityCoreExponent μm β χ T s r 0)))
      + ∑ T ∈ activityBridgeCores (N := N) s r,
        (1 - (0 : ℝ) ^ touchCount r T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (fullActivityCoreExponent μm β χ T s)
      = (∑ T ∈ activityAllowedCores (N := N) s r,
          typedMarkedCoreWeight μm β χ f T
            * (Real.exp (fullActivityCoreExponent μm β χ T s)
                - Real.exp (regionActivityCoreExponent μm β χ T s r)))
        + ∑ T ∈ activityBridgeCores (N := N) s r,
          typedMarkedCoreWeight μm β χ f T
            * Real.exp (fullActivityCoreExponent μm β χ T s) := by
  rw [sum_touchingFamilies_eq_activityAllowed_add_bridge s r]
  have hbridge0 : (∑ T ∈ activityBridgeCores (N := N) s r,
        (0 : ℝ) ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (fullActivityCoreExponent μm β χ T s)
              - Real.exp (dampedActivityCoreExponent μm β χ T s r 0))) = 0 := by
    refine Finset.sum_eq_zero (fun T hT => ?_)
    rw [zero_pow (Nat.pos_iff_ne_zero.mp
        (touchCount_pos_of_mem_activityBridgeCores hT)), zero_mul, zero_mul]
  have hallowed : (∑ T ∈ activityAllowedCores (N := N) s r,
        (0 : ℝ) ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (fullActivityCoreExponent μm β χ T s)
              - Real.exp (dampedActivityCoreExponent μm β χ T s r 0)))
      = ∑ T ∈ activityAllowedCores (N := N) s r,
          typedMarkedCoreWeight μm β χ f T
            * (Real.exp (fullActivityCoreExponent μm β χ T s)
                - Real.exp (regionActivityCoreExponent μm β χ T s r)) := by
    refine Finset.sum_congr rfl (fun T hT => ?_)
    rw [pow_touchCount_eq_one_of_mem_activityAllowedCores 0 hT, one_mul,
      dampedActivityCoreExponent_zero]
  have hbridge1 : (∑ T ∈ activityBridgeCores (N := N) s r,
        (1 - (0 : ℝ) ^ touchCount r T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (fullActivityCoreExponent μm β χ T s))
      = ∑ T ∈ activityBridgeCores (N := N) s r,
          typedMarkedCoreWeight μm β χ f T
            * Real.exp (fullActivityCoreExponent μm β χ T s) := by
    refine Finset.sum_congr rfl (fun T hT => ?_)
    rw [zero_pow (Nat.pos_iff_ne_zero.mp
        (touchCount_pos_of_mem_activityBridgeCores hT)), sub_zero, one_mul]
  rw [hbridge0, add_zero, hallowed, hbridge1]

/-- **θ = 0 as a theorem about the functionals**: the damping ledger
    specialised at θ = 0 reproduces the Stone 51 capstone
    `gibbsExpectation_sub_activityRestrictedExpectation_eq_two_column_ledger`
    — derived from the 52-B capstone, then compared literally. -/
theorem gibbsExpectation_sub_activityRestrictedExpectation_eq_damping_ledger_zero
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (r : Set (Link N)) :
    gibbsExpectation (N := N) μm β χ f
        - activityRestrictedExpectation μm β χ f s r
      = (∑ T ∈ activityAllowedCores (N := N) s r,
          typedMarkedCoreWeight μm β χ f T
            * (Real.exp (fullActivityCoreExponent μm β χ T s)
                - Real.exp (regionActivityCoreExponent μm β χ T s r)))
        + ∑ T ∈ activityBridgeCores (N := N) s r,
          typedMarkedCoreWeight μm β χ f T
            * Real.exp (fullActivityCoreExponent μm β χ T s) := by
  rw [← activityDampedExpectation_zero μm β χ f s r,
    gibbsExpectation_sub_activityDampedExpectation_eq_two_column_ledger
      μm hβ mχ hχabs hsmall hf mf hCf r (le_refl 0) zero_le_one,
    two_column_ledger_zero]

/-- **Empty remote region**: the damping is trivial and the difference
    vanishes, for every θ. -/
theorem gibbsExpectation_sub_activityDampedExpectation_empty_region
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf) (θ : ℝ) :
    gibbsExpectation (N := N) μm β χ f
        - activityDampedExpectation μm β χ f s (∅ : Set (Link N)) θ = 0 := by
  unfold activityDampedExpectation
  rw [activityDampedMarkedGas_empty_region, activityDampedPolymerGas_empty_region,
    gibbsExpectation_eq_markedGas_div_gas μm hβ mχ hχabs hf mf hCf, sub_self]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Empty remote region, column by column**: both columns vanish
    (every touchCount is 0, E_T(θ) = E_T(1), no bridge core). -/
theorem two_column_ledger_empty_region (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s : Set (Link N)) (θ : ℝ) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        θ ^ touchCount (∅ : Set (Link N)) T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (fullActivityCoreExponent μm β χ T s)
              - Real.exp (dampedActivityCoreExponent μm β χ T s ∅ θ)))
      + ∑ T ∈ activityBridgeCores (N := N) s (∅ : Set (Link N)),
        (1 - θ ^ touchCount (∅ : Set (Link N)) T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (fullActivityCoreExponent μm β χ T s) = 0 := by
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro T _
    rw [touchCount_empty_region, pow_zero, sub_self, zero_mul, zero_mul]
  · intro T _
    rw [dampedActivityCoreExponent_empty_region, sub_self, mul_zero]

/-- **Allowed cores carry weight 1** (recorded for the ledger; from
    the definition of `touchCount` via `touchCount_eq_zero_iff`). -/
theorem ledger_weight_allowed {s r : Set (Link N)} (θ : ℝ)
    {T : Finset (Polymer N)} (hT : T ∈ activityAllowedCores (N := N) s r) :
    θ ^ touchCount r T = 1 :=
  pow_touchCount_eq_one_of_mem_activityAllowedCores θ hT

#print axioms dampedActivityCoreExponent_zero
#print axioms dampedActivityCoreExponent_one
#print axioms dampedActivityGas_ratio_eq_exp
#print axioms activityDampedExpectation_eq_sum_core_mul_exp
#print axioms activityDampedExpectation_eq_allowed_add_bridge
#print axioms gibbsExpectation_sub_activityDampedExpectation_eq_two_column_ledger
#print axioms gibbsExpectation_sub_activityDampedExpectation_one
#print axioms two_column_ledger_one
#print axioms two_column_ledger_zero
#print axioms gibbsExpectation_sub_activityRestrictedExpectation_eq_damping_ledger_zero
#print axioms gibbsExpectation_sub_activityDampedExpectation_empty_region
#print axioms two_column_ledger_empty_region

end LatticeGauge
