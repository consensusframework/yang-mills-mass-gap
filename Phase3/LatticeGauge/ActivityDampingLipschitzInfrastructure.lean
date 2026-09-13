/-
LatticeGauge/ActivityDampingLipschitzInfrastructure.lean — PEDRA 53,
Gate 53-A: ANALYTIC INFRASTRUCTURE FOR THE TWO-PARAMETER (LIPSCHITZ)
STABILITY OF THE DAMPED FUNCTIONAL (architecture: GPT Astra;
feasibility and execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): the target of Stone 53
is a DIRECT estimate between two damping parameters,
    |F(θ) − F(θ′)| ≤ |θ − θ′|·C(Cf, D_s)·e^{−n/2},   θ, θ′ ∈ [0,1],
F(θ) = activityDampedExpectation. The triangle inequality through Gibbs
would only give a factor (2 − θ − θ′), which does not vanish at θ = θ′;
the difference has to be controlled directly. This gate supplies the
analytic pieces, all mirrors of Stones 50/52 with the parameter
difference in place of (1 − θ):

  * the DAMPED core exponent is bounded by the SAME local barrier
    envelope as the full one, |E_T(θ)| ≤ b_T·(2/113), through the
    generic forbidden-cluster series of Stone 50 (A4/A16) transported
    by the damped KP of 52-A — so the damped normalized term
    W_T·e^{E_T(θ)} costs ONE barrier exponential (κ = 1), exactly like
    N_f(s,T); this is what keeps the bridge column inside the
    admissible budget (7/8, 1) (the route through N_f·e^{C_θ} would
    cost κ = 2 and land on the inadmissible (7/8, 2));
  * the difference of powers |θ^j − θ′^j| ≤ j·|θ − θ′| on [0,1]
    (Mathlib's abs_pow_sub_pow_le);
  * the two-parameter domination of the damped connector coefficients,
    |c_k(θ) − c_k(θ′)| ≤ |θ − θ′|·k·A_k, hence
    |C_θ − C_θ′| ≤ |θ − θ′|·e^{−((n − m_T : ℕ))/2}·q′ with the 52-A0
    first moment (natural truncated subtraction, no 8/(3e));
  * E_T(θ) − E_T(θ′) = C_θ − C_θ′ (algebra on the 52-C identity);
  * the exponential control
    |e^{E_T(θ)} − e^{E_T(θ′)}| ≤ |θ − θ′|·e^{−n/2}·e^{m_T/2 + 3 b_T·(2/113)}
    (κ = 3 at tilt 1/2 — the (1/2, 3) budget of the connector column);
  * the damped bridge first moment
    card T·|W_T·e^{E_T(θ)}| ≤ e^{−n/2}·Cf·e^{b_T·(2/113)}·Π massTilt(7/8)
    (κ = 1 at tilt 7/8 — the (7/8, 1) budget of the bridge column).

Nothing is divided by (1 − θ) or |θ − θ′|; no hypothesis
`DependsOnlyOn f s` is used anywhere in this module.

HARD HOLD (not here): the two-column identity, the column sums, the
capstone and the endpoints (53-B); any Disjoint s r, size restriction
on r or volume factor; monotonicity of the deviation in θ;
Gibbs-measure, boundary-condition or modified-action interpretations;
thermodynamic limit, continuum, mass gap. No project-local scientific
axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.ActivityDampingColumnBounds

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## 53-A.1 — scalar lemmas: the parameter interval -/

section ScalarLemmas

/-- **Difference of powers on [0,1]**: |θ^j − θ′^j| ≤ j·|θ − θ′|
    (Mathlib's `abs_pow_sub_pow_le` with max |θ| |θ′| ≤ 1). -/
theorem abs_pow_sub_pow_le_nat_mul_abs_sub {θ θ' : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) (j : ℕ) :
    |θ ^ j - θ' ^ j| ≤ (j : ℝ) * |θ - θ'| := by
  have hmax : max |θ| |θ'| ≤ 1 := by
    rw [abs_of_nonneg h0, abs_of_nonneg h0']
    exact max_le h1 h1'
  have hmax0 : 0 ≤ max |θ| |θ'| := le_max_of_le_left (abs_nonneg _)
  have hpow : max |θ| |θ'| ^ (j - 1) ≤ 1 := pow_le_one₀ hmax0 hmax
  calc |θ ^ j - θ' ^ j|
      ≤ |θ - θ'| * (j : ℝ) * max |θ| |θ'| ^ (j - 1) :=
        abs_pow_sub_pow_le θ θ' j
    _ ≤ |θ - θ'| * (j : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    _ = (j : ℝ) * |θ - θ'| := by ring

/-- Two parameters in [0,1] are at distance at most 1. -/
theorem abs_sub_le_one_of_unit_interval {θ θ' : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    |θ - θ'| ≤ 1 := by
  rw [abs_sub_le_iff]
  constructor <;> linarith

end ScalarLemmas

/-! ## 53-A.2 — the forbidden-root envelope is monotone in the activity -/

/-- Termwise monotonicity of `kpForbiddenRootEnvelope` in ρ (the
    exponential factor is positive; no sign condition on ρ needed). -/
theorem kpForbiddenRootEnvelope_mono {ρ ρ' a : Polymer N → ℝ}
    (hle : ∀ η, ρ η ≤ ρ' η) (P : Polymer N → Prop) :
    kpForbiddenRootEnvelope ρ a P ≤ kpForbiddenRootEnvelope ρ' a P := by
  unfold kpForbiddenRootEnvelope
  refine Finset.sum_le_sum (fun γ₀ _ => ?_)
  by_cases h : P γ₀
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact mul_le_mul_of_nonneg_right (hle γ₀) (Real.exp_pos _).le

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## 53-A.3 — THE DAMPED EXPONENT PAYS ONLY THE LOCAL BARRIER (κ = 1) -/

/-- **Damped exponent bound**: for 0 ≤ θ ≤ 1,
      |E_T(θ)| ≤ card(barrierLinkFinset T s)·(2/113).
    Route (all generic in the activity): the damped KP of 52-A; the
    Stone 50 identity S_P(z) − S(z) = −Σ' forbidden(z)
    (`tsum_restricted_sub_full`); the one-barrier majorant
    Σ'|forbidden(z)| ≤ envelope(|z|) (`tsum_abs_kpForbiddenUnrootedCoeff_le`);
    monotonicity of the envelope under |z_θ| ≤ |z|; and the 2/113
    localization of the envelope of |w| (`kpForbiddenRootEnvelope_le_barrierLinkCount`). -/
theorem abs_dampedActivityCoreExponent_le_barrier
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r : Set (Link N))
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |dampedActivityCoreExponent μm β χ T s r θ|
      ≤ ((barrierLinkFinset T s).card : ℝ) * (2 / 113) := by
  have hKP := abstractKP_of_beta_le_one_div_40000 (N := N) μm hβ mχ hχabs hsmall
  have hKPθ := abstractKP_dampedActivity r h0 h1 hKP
  have ha : ∀ γ : Polymer N, 0 ≤ ((γ.val.card : ℕ) : ℝ) :=
    fun γ => Nat.cast_nonneg _
  unfold dampedActivityCoreExponent
  rw [tsum_restricted_sub_full ha hKPθ (remoteAllowed (N := N) T s), abs_neg]
  have hsum := summable_abs_kpForbiddenUnrootedCoeff ha hKPθ
    (remoteAllowed (N := N) T s)
  have h1' : ‖∑' k : ℕ, kpForbiddenUnrootedCoeff (N := N) k
      (dampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) r θ)
      (remoteAllowed (N := N) T s)‖
      ≤ ∑' k : ℕ, ‖kpForbiddenUnrootedCoeff (N := N) k
          (dampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) r θ)
          (remoteAllowed (N := N) T s)‖ := by
    refine norm_tsum_le_tsum_norm ?_
    simpa [Real.norm_eq_abs] using hsum
  simp only [Real.norm_eq_abs] at h1'
  refine h1'.trans ?_
  refine (tsum_abs_kpForbiddenUnrootedCoeff_le ha hKPθ
    (remoteAllowed (N := N) T s)).trans ?_
  refine (kpForbiddenRootEnvelope_mono
    (fun η => abs_dampedActivity_le _ r h0 h1 η) _).trans ?_
  have henv : kpForbiddenRootEnvelope
      (fun η => |polymerWeight (N := N) μm β χ η.val|)
      (fun η => ((η.val.card : ℕ) : ℝ))
      (remoteAllowed (N := N) T s)
      = ∑ γ₀ : Polymer N,
          if remoteAllowed (N := N) T s γ₀ then 0
          else |polymerWeight (N := N) μm β χ γ₀.val|
            * Real.exp ((γ₀.val.card : ℕ) : ℝ) := rfl
  rw [henv]
  exact kpForbiddenRootEnvelope_le_barrierLinkCount μm hβ mχ hχabs hsmall T s

/-- e^{E_T(θ)} ≤ e^{b_T·(2/113)} for 0 ≤ θ ≤ 1. -/
theorem exp_dampedActivityCoreExponent_le_exp_barrier
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r : Set (Link N))
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
      ≤ Real.exp (((barrierLinkFinset T s).card : ℝ) * (2 / 113)) :=
  Real.exp_le_exp.mpr (le_trans (le_abs_self _)
    (abs_dampedActivityCoreExponent_le_barrier μm hβ mχ hχabs hsmall T s r h0 h1))

/-! ## 53-A.4 — the damped normalized term, κ = 1 -/

/-- **Damped normalized term**: |W_T·e^{E_T(θ)}| ≤ Cf·e^{b_T·(2/113)}·Π M,
    the core weight against the Mayer majorant (no exponential) times
    the damped exponent bound (ONE barrier exponential). -/
theorem abs_typedMarkedCoreWeight_mul_exp_damped_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    (T : Finset (Polymer N)) (s r : Set (Link N))
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |typedMarkedCoreWeight μm β χ f T
        * Real.exp (dampedActivityCoreExponent μm β χ T s r θ)|
      ≤ Cf * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T, mayerCoreMajorant β η := by
  have hW := abs_typedMarkedCoreWeight_le_mayerCoreMajorant
    μm hβ mχ hχabs mf hCf0 hCf T
  have hE := exp_dampedActivityCoreExponent_le_exp_barrier
    μm hβ mχ hχabs hsmall T s r h0 h1
  have hL0 : (0:ℝ) ≤ Cf * ∏ η ∈ T, mayerCoreMajorant β η :=
    le_trans (abs_nonneg _) hW
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |typedMarkedCoreWeight μm β χ f T|
        * Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
      ≤ (Cf * ∏ η ∈ T, mayerCoreMajorant β η)
          * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113)) :=
        mul_le_mul hW hE (Real.exp_pos _).le hL0
    _ = Cf * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T, mayerCoreMajorant β η := by ring

/-! ## 53-A.5 — two-parameter domination of the damped connector coefficients -/

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **DOMINATION (two parameters)**: for θ, θ′ ∈ [0,1],
      |c_k(θ) − c_k(θ′)| ≤ |θ − θ′|·k·A_k(|z|),
    where the weights differ by θ′^{tc} − θ^{tc} on every tuple hitting
    both barriers, |θ′^{tc} − θ^{tc}| ≤ tc·|θ − θ′| ≤ k·|θ − θ′|.
    Mirror of `abs_kpDampedConnectorUnrootedCoeff_le`. -/
theorem abs_kpDampedConnectorUnrootedCoeff_sub_le (k : ℕ)
    (z : Polymer N → ℝ) (P : Polymer N → Prop)
    (r : Set (Link N)) {θ θ' : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    |kpDampedConnectorUnrootedCoeff (N := N) k z P r θ
        - kpDampedConnectorUnrootedCoeff (N := N) k z P r θ'|
      ≤ |θ - θ'| * (k : ℝ)
          * kpAbsConnectorUnrootedCoeff k (fun η => |z η|) P
              (regionAllowed (N := N) r) := by
  unfold kpDampedConnectorUnrootedCoeff kpAbsConnectorUnrootedCoeff
  rw [div_sub_div_same, ← mul_div_assoc, abs_div, Nat.abs_cast]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _)
    (Finset.sum_le_sum (fun δ _ => ?_))
  by_cases h : TupleHitsBothForbidden P (regionAllowed (N := N) r) δ
  · rw [if_pos h, if_pos h, if_pos h, ← sub_mul, abs_mul, abs_mul,
      Finset.abs_prod, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    have hw : |(1 - θ ^ tupleTouchCount r δ) - (1 - θ' ^ tupleTouchCount r δ)|
        ≤ |θ - θ'| * (k : ℝ) := by
      rw [show (1 - θ ^ tupleTouchCount r δ) - (1 - θ' ^ tupleTouchCount r δ)
          = -(θ ^ tupleTouchCount r δ - θ' ^ tupleTouchCount r δ) from by ring,
        abs_neg]
      calc |θ ^ tupleTouchCount r δ - θ' ^ tupleTouchCount r δ|
          ≤ (tupleTouchCount r δ : ℝ) * |θ - θ'| :=
            abs_pow_sub_pow_le_nat_mul_abs_sub h0 h1 h0' h1' _
        _ ≤ (k : ℝ) * |θ - θ'| :=
            mul_le_mul_of_nonneg_right
              (Nat.cast_le.mpr (tupleTouchCount_le r δ)) (abs_nonneg _)
        _ = |θ - θ'| * (k : ℝ) := mul_comm _ _
    have hrest : 0 ≤ (((ursellCoeff (N := N) (fun i => (δ i).val)).natAbs : ℕ) : ℝ)
        * ∏ i : Fin k, |z (δ i)| :=
      mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => abs_nonneg _))
    calc |(1 - θ ^ tupleTouchCount r δ) - (1 - θ' ^ tupleTouchCount r δ)|
          * ((((ursellCoeff (N := N) (fun i => (δ i).val)).natAbs : ℕ) : ℝ)
              * ∏ i : Fin k, |z (δ i)|)
        ≤ (|θ - θ'| * (k : ℝ))
          * ((((ursellCoeff (N := N) (fun i => (δ i).val)).natAbs : ℕ) : ℝ)
              * ∏ i : Fin k, |z (δ i)|) :=
          mul_le_mul_of_nonneg_right hw hrest
      _ = |θ - θ'| * (k : ℝ)
          * ((((ursellCoeff (N := N) (fun i => (δ i).val)).natAbs : ℕ) : ℝ)
              * ∏ i : Fin k, |z (δ i)|) := by ring
  · rw [if_neg h, if_neg h, if_neg h, sub_zero, abs_zero, mul_zero]

/-! ## 53-A.6 — the two-parameter connector difference, eroded -/

/-- **ERODED TWO-PARAMETER BOUND**:
      |C_{T,r}(θ) − C_{T,r}(θ′)| ≤ |θ − θ′|·e^{−((n − m_T : ℕ))/2}·q′,
    q′ = card(barrierLinkFinset T s)·(2/113), natural truncated
    subtraction. Route: 51-D erosion, the 52-C summability of both
    series, the two-parameter domination and the 52-A0 first moment
    Σ k·A_k ≤ e^{−q/2}·q′ (no 8/(3e)). Mirror of
    `abs_activityDampingConnector_le_eroded`. -/
theorem abs_activityDampingConnector_sub_le_eroded
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    |activityDampingConnector μm β χ T s r θ
        - activityDampingConnector μm β χ T s r θ'|
      ≤ |θ - θ'|
        * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2)
        * (((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
  have hero := walkBarrierSeparated_barrierRegions_sub_familyMass
    hT (empty_mem_typedTouchingFamilies r) hsep
  have hzero : familyTotalCard (∅ : Finset (Polymer N)) = 0 := by
    unfold familyTotalCard
    exact Finset.sum_empty
  rw [hzero, Nat.add_zero] at hero
  have hmaj := summable_nat_mul_kpAbsConnector_polymerWeight
    μm hβ mχ hχabs hsmall hero
  have hmom := tsum_nat_mul_kpAbsConnector_polymerWeight_le_local_P
    μm hβ mχ hχabs hsmall hero
  rw [← regionAllowed_eq_remoteAllowed_empty] at hmaj hmom
  -- summability of both damped series (52-C)
  have hSθ : Summable (fun k : ℕ =>
      kpDampedConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s) r θ) :=
    Summable.of_norm (by
      simpa [Real.norm_eq_abs] using
        summable_kpDampedConnectorUnrootedCoeff μm hβ mχ hχabs hsmall hero h0 h1)
  have hSθ' : Summable (fun k : ℕ =>
      kpDampedConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s) r θ') :=
    Summable.of_norm (by
      simpa [Real.norm_eq_abs] using
        summable_kpDampedConnectorUnrootedCoeff μm hβ mχ hχabs hsmall hero h0' h1')
  -- termwise domination of the difference
  have hdom : ∀ k : ℕ,
      |kpDampedConnectorUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s) r θ
        - kpDampedConnectorUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s) r θ'|
      ≤ |θ - θ'| * ((k : ℝ)
          * kpAbsConnectorUnrootedCoeff k
              (fun η => |polymerWeight (N := N) μm β χ η.val|)
              (remoteAllowed (N := N) T s) (regionAllowed (N := N) r)) := by
    intro k
    have := abs_kpDampedConnectorUnrootedCoeff_sub_le k
      (fun η => polymerWeight (N := N) μm β χ η.val)
      (remoteAllowed (N := N) T s) r h0 h1 h0' h1'
    rw [mul_assoc] at this
    exact this
  have hsumabs : Summable (fun k : ℕ =>
      |kpDampedConnectorUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s) r θ
        - kpDampedConnectorUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s) r θ'|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hdom
      (Summable.mul_left |θ - θ'| hmaj)
  unfold activityDampingConnector
  rw [← tsum_sub hSθ hSθ']
  have h1' : ‖∑' k : ℕ, (kpDampedConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s) r θ
      - kpDampedConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s) r θ')‖
      ≤ ∑' k : ℕ, ‖kpDampedConnectorUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s) r θ
        - kpDampedConnectorUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s) r θ'‖ := by
    refine norm_tsum_le_tsum_norm ?_
    simpa [Real.norm_eq_abs] using hsumabs
  simp only [Real.norm_eq_abs] at h1'
  have h2 := tsum_le_tsum hdom hsumabs (Summable.mul_left |θ - θ'| hmaj)
  rw [tsum_mul_left] at h2
  have h3 : |θ - θ'| * (∑' k : ℕ, (k : ℝ)
        * kpAbsConnectorUnrootedCoeff k
            (fun η => |polymerWeight (N := N) μm β χ η.val|)
            (remoteAllowed (N := N) T s) (regionAllowed (N := N) r))
      ≤ |θ - θ'| * (Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2)
          * (((barrierLinkFinset T s).card : ℝ) * (2 / 113))) :=
    mul_le_mul_of_nonneg_left hmom (abs_nonneg _)
  calc _ ≤ _ := h1'
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ = |θ - θ'| * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2)
          * (((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by ring

/-! ## 53-A.7 — the exponent difference IS the connector difference -/

/-- E_T(θ) − E_T(θ′) = C_{T,r}(θ) − C_{T,r}(θ′): algebra on the 52-C
    series identity applied at both parameters. -/
theorem dampedActivityCoreExponent_sub_eq_activityDampingConnector_sub
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r : Set (Link N))
    {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    dampedActivityCoreExponent μm β χ T s r θ
        - dampedActivityCoreExponent μm β χ T s r θ'
      = activityDampingConnector μm β χ T s r θ
        - activityDampingConnector μm β χ T s r θ' := by
  have hθ := dampedActivityCoreExponent_sub_full_eq_activityDampingConnector
    μm hβ mχ hχabs hsmall T s r h0 h1
  have hθ' := dampedActivityCoreExponent_sub_full_eq_activityDampingConnector
    μm hβ mχ hχabs hsmall T s r h0' h1'
  linarith

/-! ## 53-A.8 — exponential control of the exponent difference (κ = 3) -/

/-- **EXPONENTIAL CONTROL (two parameters)**:
      |e^{E_T(θ)} − e^{E_T(θ′)}|
        ≤ |θ − θ′|·e^{−n/2}·e^{m_T/2 + 3·b_T·(2/113)}.
    Route: e^{E(θ)} − e^{E(θ′)} = e^{E(θ′)}·(e^{Δ} − 1) with
    Δ = C_θ − C_θ′; `abs_exp_sub_one_le_decay_exp` with
    d = |θ − θ′|·e^{−((n − m_T : ℕ))/2} ∈ [0,1], q = q′, B = 2q′; the
    damped exponent bound e^{E(θ′)} ≤ e^{q′} (κ = 1 + 2 = 3); the
    repurchased erosion `exp_neg_nat_sub_half_le`. -/
theorem abs_exp_dampedActivityCoreExponent_sub_le_decay
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    |Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
        - Real.exp (dampedActivityCoreExponent μm β χ T s r θ')|
      ≤ |θ - θ'| * Real.exp (-(n : ℝ) / 2)
        * Real.exp ((familyTotalCard T : ℝ) / 2
            + 3 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
  set q' : ℝ := ((barrierLinkFinset T s).card : ℝ) * (2 / 113) with hq'
  have hq0 : (0:ℝ) ≤ q' := mul_nonneg (Nat.cast_nonneg _) (by norm_num)
  -- the factorization e^{E(θ)} − e^{E(θ′)} = e^{E(θ′)}·(e^{E(θ) − E(θ′)} − 1)
  have hfac : Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
      - Real.exp (dampedActivityCoreExponent μm β χ T s r θ')
      = Real.exp (dampedActivityCoreExponent μm β χ T s r θ')
        * (Real.exp (dampedActivityCoreExponent μm β χ T s r θ
            - dampedActivityCoreExponent μm β χ T s r θ') - 1) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring
  -- the eroded bound on the exponent difference
  have hΔ : |dampedActivityCoreExponent μm β χ T s r θ
      - dampedActivityCoreExponent μm β χ T s r θ'|
      ≤ (|θ - θ'| * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2)) * q' := by
    rw [dampedActivityCoreExponent_sub_eq_activityDampingConnector_sub
      μm hβ mχ hχabs hsmall T s r h0 h1 h0' h1']
    have := abs_activityDampingConnector_sub_le_eroded
      μm hβ mχ hχabs hsmall hT hsep h0 h1 h0' h1'
    rw [hq']
    exact this
  have he0 : (0:ℝ) ≤ Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) :=
    (Real.exp_pos _).le
  have he1 : Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    refine Real.exp_le_exp.mpr ?_
    have hnat : (0:ℝ) ≤ (((n - familyTotalCard T : ℕ)) : ℝ) := Nat.cast_nonneg _
    linarith
  have hθ1 : |θ - θ'| ≤ 1 := abs_sub_le_one_of_unit_interval h0 h1 h0' h1'
  have hd0 : (0:ℝ) ≤ |θ - θ'| * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) :=
    mul_nonneg (abs_nonneg _) he0
  have hd1 : |θ - θ'| * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) ≤ 1 :=
    mul_le_one₀ hθ1 he0 he1
  have hmain := abs_exp_sub_one_le_decay_exp hd0 hd1 hq0 hΔ (le_refl (2 * q'))
  have hE' := exp_dampedActivityCoreExponent_le_exp_barrier
    μm hβ mχ hχabs hsmall T s r h0' h1'
  have herode := exp_neg_nat_sub_half_le n (familyTotalCard T)
  rw [hfac, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (dampedActivityCoreExponent μm β χ T s r θ')
        * |Real.exp (dampedActivityCoreExponent μm β χ T s r θ
            - dampedActivityCoreExponent μm β χ T s r θ') - 1|
      ≤ Real.exp q'
          * ((|θ - θ'| * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2))
            * Real.exp (2 * q')) :=
        mul_le_mul hE' hmain (abs_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp q'
          * ((|θ - θ'| * (Real.exp (-(n : ℝ) / 2)
              * Real.exp ((familyTotalCard T : ℝ) / 2)))
            * Real.exp (2 * q')) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left herode (abs_nonneg _)
    _ = |θ - θ'| * Real.exp (-(n : ℝ) / 2)
        * Real.exp ((familyTotalCard T : ℝ) / 2
            + 3 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
        rw [hq', Real.exp_add]
        have h3 : Real.exp (3 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113))
            = Real.exp (((barrierLinkFinset T s).card : ℝ) * (2 / 113))
              * Real.exp (2 * (((barrierLinkFinset T s).card : ℝ) * (2 / 113))) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [h3]
        ring

/-! ## 53-A.9 — the damped bridge first moment (κ = 1, tilt 7/8) -/

/-- **DAMPED FIRST MOMENT OF A BRIDGE CORE**:
      card T·|W_T·e^{E_T(θ)}| ≤ e^{−n/2}·Cf·(e^{1·b_T·(2/113)}·Π massTilt(7/8) M).
    The chain of `nat_card_mul_abs_normalizedMarkedCoreTerm_le_bridge`
    with the damped normalized term (κ = 1) in place of N_f(s,T):
    card T ≤ m_T ≤ (8/(3e))·e^{3 m_T/8} ≤ e^{3 m_T/8} and n ≤ m_T
    pays e^{−n/2}·e^{m_T/2}. -/
theorem nat_card_mul_abs_dampedNormalizedTerm_le_bridge
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ activityBridgeCores (N := N) s r)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (T.card : ℝ) * |typedMarkedCoreWeight μm β χ f T
        * Real.exp (dampedActivityCoreExponent μm β χ T s r θ)|
      ≤ Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) := by
  have hn : n ≤ familyTotalCard T :=
    activityBridgeCore_familyTotalCard_ge hT hsep
  have hnR : (n : ℝ) ≤ (familyTotalCard T : ℝ) := Nat.cast_le.mpr hn
  have hcard : (T.card : ℝ) ≤ (familyTotalCard T : ℝ) :=
    Nat.cast_le.mpr (familyCard_le_familyTotalCard T)
  have habs := nat_le_exp_three_eighths (familyTotalCard T)
  have hM : (0 : ℝ) ≤ ∏ η ∈ T, mayerCoreMajorant β η :=
    Finset.prod_nonneg (fun η _ => mayerCoreMajorant_nonneg hβ η)
  have hN := abs_typedMarkedCoreWeight_mul_exp_damped_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf T s r h0 h1
  have hb0 : (0 : ℝ) ≤ Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113)) :=
    (Real.exp_pos _).le
  have hpay : (1 : ℝ) ≤ Real.exp (-(n : ℝ) / 2)
      * Real.exp ((familyTotalCard T : ℝ) / 2) := by
    rw [← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hprod := prod_family_massTiltActivity (N := N) (7/8)
    (mayerCoreMajorant β) T
  have hL0 : (0:ℝ) ≤ Cf * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
      * ∏ η ∈ T, mayerCoreMajorant β η :=
    mul_nonneg (mul_nonneg hCf0 hb0) hM
  calc (T.card : ℝ) * |typedMarkedCoreWeight μm β χ f T
        * Real.exp (dampedActivityCoreExponent μm β χ T s r θ)|
      ≤ (T.card : ℝ) * (Cf * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T, mayerCoreMajorant β η) :=
        mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg _)
    _ ≤ Real.exp ((3/8 : ℝ) * (familyTotalCard T : ℝ))
          * (Cf * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, mayerCoreMajorant β η) :=
        mul_le_mul_of_nonneg_right (le_trans hcard habs) hL0
    _ ≤ (Real.exp (-(n : ℝ) / 2) * Real.exp ((familyTotalCard T : ℝ) / 2))
          * (Real.exp ((3/8 : ℝ) * (familyTotalCard T : ℝ))
            * (Cf * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
              * ∏ η ∈ T, mayerCoreMajorant β η)) := by
        refine le_mul_of_one_le_left ?_ hpay
        exact mul_nonneg (Real.exp_pos _).le hL0
    _ = Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * (Real.exp ((7/8 : ℝ) * (familyTotalCard T : ℝ))
              * ∏ η ∈ T, mayerCoreMajorant β η)) := by
        have h78 : Real.exp ((familyTotalCard T : ℝ) / 2)
            * Real.exp ((3/8 : ℝ) * (familyTotalCard T : ℝ))
            = Real.exp ((7/8 : ℝ) * (familyTotalCard T : ℝ)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [← h78, one_mul]; ring
    _ = Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) := by
        rw [hprod]

#print axioms abs_pow_sub_pow_le_nat_mul_abs_sub
#print axioms abs_sub_le_one_of_unit_interval
#print axioms kpForbiddenRootEnvelope_mono
#print axioms abs_dampedActivityCoreExponent_le_barrier
#print axioms exp_dampedActivityCoreExponent_le_exp_barrier
#print axioms abs_typedMarkedCoreWeight_mul_exp_damped_le
#print axioms abs_kpDampedConnectorUnrootedCoeff_sub_le
#print axioms abs_activityDampingConnector_sub_le_eroded
#print axioms dampedActivityCoreExponent_sub_eq_activityDampingConnector_sub
#print axioms abs_exp_dampedActivityCoreExponent_sub_le_decay
#print axioms nat_card_mul_abs_dampedNormalizedTerm_le_bridge

end LatticeGauge
