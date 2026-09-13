/-
LatticeGauge/ActivityDampingLipschitz.lean — PEDRA 53,
Gate 53-B: CAPSTONE — TWO-PARAMETER (LIPSCHITZ) STABILITY OF THE
DAMPED FUNCTIONAL (architecture: GPT Astra; feasibility and
execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): for two damping
parameters θ, θ′ ∈ [0,1] the difference of the damped functional
F(θ) = activityDampedExpectation is, EXACTLY (53-B.1),

    F(θ) − F(θ′) = Σ_{T touching} θ′^t · W_T · (e^{E_T(θ)} − e^{E_T(θ′)})
                 + Σ_{T bridge}   (θ^t − θ′^t) · W_T · e^{E_T(θ)},

t = touchCount r T — the same bookkeeping as the 52-B ledger with
the Gibbs side replaced by a second damped functional (no
`DependsOnlyOn f s` is needed: both sides are the 52-B exponential
form). The two columns are estimated separately with the factor
|θ − θ′| in front (53-B.2, 53-B.3):

  * connector column (ALL touching cores): 0 ≤ θ′^t ≤ 1, the core
    weight against the Mayer majorant |W_T| ≤ Cf·Π M, and the 53-A
    exponential control |e^{E_T(θ)} − e^{E_T(θ′)}| ≤
    |θ − θ′|·e^{−n/2}·e^{m_T/2 + 3 b_T·(2/113)}, then the budget
    (λ, κ) = (1/2, 3):
      Σ_T |θ′^t·W_T·(e^{E_T(θ)} − e^{E_T(θ′)})| ≤ |θ − θ′|·Cf·e^{−n/2}·e^{8 D_s/113};
  * bridge column (the bridge cores of the ledger): |θ^t − θ′^t| ≤
    t·|θ − θ′| ≤ card T·|θ − θ′|, the 53-A damped bridge first moment
    card T·|W_T·e^{E_T(θ)}| ≤ e^{−n/2}·Cf·e^{b_T·(2/113)}·Π massTilt(7/8)
    (κ = 1: the damped exponent pays only the local barrier), and the
    budget (λ, κ) = (7/8, 1):
      Σ_{T bridge} |(θ^t − θ′^t)·W_T·e^{E_T(θ)}| ≤ |θ − θ′|·Cf·e^{−n/2}·e^{4 D_s/113}.

Ledger + triangle inequality + the two bounds give the two-term
estimate (53-B.4)
    |F(θ) − F(θ′)| ≤ |θ − θ′|·Cf·e^{−n/2}·(e^{8 D_s/113} + e^{4 D_s/113}),
and, since D_s ≥ 0, the Stone 53 CAPSTONE
    |F(θ) − F(θ′)| ≤ |θ − θ′|·2·Cf·e^{8 D_s/113}·e^{−n/2},
D_s = card (supportLinkFinset s): the SAME constant as the Stone 52
capstone, now as a Lipschitz constant in the damping parameter,
uniform in θ, θ′ and in the region r. The hypothesis 0 ≤ Cf is
DERIVED from |f| ≤ Cf at `trivialConfig N G` (52-E), not assumed.
Nothing is divided by |θ − θ′|.

Endpoints (53-B.5): θ = θ′ (difference 0, bound 0); θ′ = 1 with
`DependsOnlyOn f s` recovers the Stone 52 capstone with the same
constant (|θ − 1| = 1 − θ); θ′ = 0 gives the distance to the
activity-restricted functional of Stone 51 with the factor θ;
r = ∅ gives the exact identity F(θ) = F(θ′) for all real θ, θ′.

WHAT THIS IS: a Lipschitz estimate in the damping parameter for the
damped functional at fixed β, χ, f, s, r, n. WHAT THIS IS NOT: a
monotonicity statement, a derivative, or a statement about the
actual size of the deviation.

HARD HOLD (not here): any Disjoint s r, size restriction on r or
volume factor; Gibbs-measure, boundary-condition, modified-action
or switch-off interpretations; thermodynamic limit, continuum,
spatial mixing, mass gap. No project-local scientific axioms;
0 sorry.
-/
import Mathlib
import LatticeGauge.ActivityDampingLipschitzInfrastructure
import LatticeGauge.ActivityDampingStability

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## 53-B.1 — the exact two-parameter ledger -/

/-- **THE EXACT TWO-PARAMETER LEDGER**: for θ, θ′ ∈ [0,1],
      F(θ) − F(θ′)
        = Σ_{T touching} θ′^t · W_T · (e^{E_T(θ)} − e^{E_T(θ′)})
        + Σ_{T bridge}   (θ^t − θ′^t) · W_T · e^{E_T(θ)}.
    Finite algebra on the 52-B exponential form of both sides; on the
    allowed column both weights are 1, so the bridge column is
    supported on bridge cores only. No `DependsOnlyOn`, no
    measurability or bound on f. -/
theorem activityDampedExpectation_sub_eq_two_column_lipschitz_ledger
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (f : Config N G → ℝ) (s r : Set (Link N))
    {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    activityDampedExpectation μm β χ f s r θ
        - activityDampedExpectation μm β χ f s r θ'
      = (∑ T ∈ typedTouchingFamilies (N := N) s,
          θ' ^ touchCount r T
            * typedMarkedCoreWeight μm β χ f T
            * (Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
                - Real.exp (dampedActivityCoreExponent μm β χ T s r θ')))
        + ∑ T ∈ activityBridgeCores (N := N) s r,
          (θ ^ touchCount r T - θ' ^ touchCount r T)
            * typedMarkedCoreWeight μm β χ f T
            * Real.exp (dampedActivityCoreExponent μm β χ T s r θ) := by
  rw [activityDampedExpectation_eq_sum_core_mul_exp μm hβ mχ hχabs hsmall
      f s r h0 h1,
    activityDampedExpectation_eq_sum_core_mul_exp μm hβ mχ hχabs hsmall
      f s r h0' h1']
  -- the θ-weighted sum with the θ-exponent, rewritten with the
  -- θ′-weight plus the bridge correction (weights agree on allowed cores)
  have hsplit : (∑ T ∈ typedTouchingFamilies (N := N) s,
        θ ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (dampedActivityCoreExponent μm β χ T s r θ))
      = (∑ T ∈ typedTouchingFamilies (N := N) s,
          θ' ^ touchCount r T
            * typedMarkedCoreWeight μm β χ f T
            * Real.exp (dampedActivityCoreExponent μm β χ T s r θ))
        + ∑ T ∈ activityBridgeCores (N := N) s r,
          (θ ^ touchCount r T - θ' ^ touchCount r T)
            * typedMarkedCoreWeight μm β χ f T
            * Real.exp (dampedActivityCoreExponent μm β χ T s r θ) := by
    rw [sum_touchingFamilies_eq_activityAllowed_add_bridge s r
        (fun T => θ ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (dampedActivityCoreExponent μm β χ T s r θ)),
      sum_touchingFamilies_eq_activityAllowed_add_bridge s r
        (fun T => θ' ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (dampedActivityCoreExponent μm β χ T s r θ))]
    have hallowed : (∑ T ∈ activityAllowedCores (N := N) s r,
          θ ^ touchCount r T
            * typedMarkedCoreWeight μm β χ f T
            * Real.exp (dampedActivityCoreExponent μm β χ T s r θ))
        = ∑ T ∈ activityAllowedCores (N := N) s r,
            θ' ^ touchCount r T
              * typedMarkedCoreWeight μm β χ f T
              * Real.exp (dampedActivityCoreExponent μm β χ T s r θ) := by
      refine Finset.sum_congr rfl (fun T hT => ?_)
      rw [pow_touchCount_eq_one_of_mem_activityAllowedCores θ hT,
        pow_touchCount_eq_one_of_mem_activityAllowedCores θ' hT]
    rw [hallowed, add_assoc, ← Finset.sum_add_distrib, add_right_inj]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    ring
  rw [hsplit, add_sub_right_comm, ← Finset.sum_sub_distrib, add_left_inj]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  ring

/-! ## 53-B.2 — the connector column (κ = 3, tilt 1/2) -/

/-- **CONNECTOR-COLUMN TERM, κ = 3**: for every touching core T,
      |θ′^t·W_T·(e^{E_T(θ)} − e^{E_T(θ′)})|
        ≤ |θ − θ′|·e^{−n/2}·Cf·halfTiltCoreBudgetTerm β 3 s T. -/
theorem abs_lipschitzConnectorColumnTerm_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    |θ' ^ touchCount r T
        * typedMarkedCoreWeight μm β χ f T
        * (Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
            - Real.exp (dampedActivityCoreExponent μm β χ T s r θ'))|
      ≤ |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
          * halfTiltCoreBudgetTerm β 3 s T := by
  have hW := abs_typedMarkedCoreWeight_le_mayerCoreMajorant
    μm hβ mχ hχabs mf hCf0 hCf T
  have hE := abs_exp_dampedActivityCoreExponent_sub_le_decay
    μm hβ mχ hχabs hsmall hT hsep h0 h1 h0' h1'
  have hθ0 : 0 ≤ θ' ^ touchCount r T := dampedPow_nonneg h0' _
  have hθ1 : θ' ^ touchCount r T ≤ 1 := dampedPow_le_one h0' h1' _
  have hW0 : (0:ℝ) ≤ Cf * ∏ η ∈ T, mayerCoreMajorant β η :=
    le_trans (abs_nonneg _) hW
  have hre : θ' ^ touchCount r T * typedMarkedCoreWeight μm β χ f T
      * (Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
          - Real.exp (dampedActivityCoreExponent μm β χ T s r θ'))
      = θ' ^ touchCount r T
        * (typedMarkedCoreWeight μm β χ f T
            * (Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
                - Real.exp (dampedActivityCoreExponent μm β χ T s r θ'))) := by
    ring
  rw [hre, abs_mul, abs_mul, abs_of_nonneg hθ0]
  calc θ' ^ touchCount r T
        * (|typedMarkedCoreWeight μm β χ f T|
            * |Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
                - Real.exp (dampedActivityCoreExponent μm β χ T s r θ')|)
      ≤ 1 * (|typedMarkedCoreWeight μm β χ f T|
            * |Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
                - Real.exp (dampedActivityCoreExponent μm β χ T s r θ')|) :=
        mul_le_mul_of_nonneg_right hθ1
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = |typedMarkedCoreWeight μm β χ f T|
          * |Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
              - Real.exp (dampedActivityCoreExponent μm β χ T s r θ')| :=
        one_mul _
    _ ≤ (Cf * ∏ η ∈ T, mayerCoreMajorant β η)
          * (|θ - θ'| * Real.exp (-(n : ℝ) / 2)
            * Real.exp ((familyTotalCard T : ℝ) / 2
                + 3 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113))) :=
        mul_le_mul hW hE (abs_nonneg _) hW0
    _ = |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
          * halfTiltCoreBudgetTerm β 3 s T := by
        rw [halfTiltCoreBudgetTerm_eq]
        ring

/-- **CONNECTOR COLUMN, SUM OF ABSOLUTE VALUES** (budget (1/2, 3)):
      Σ_T |θ′^t·W_T·(e^{E_T(θ)} − e^{E_T(θ′)})|
        ≤ |θ − θ′|·Cf·e^{−n/2}·e^{4·D_s·(2/113)}  (= e^{8 D_s/113}). -/
theorem sum_abs_lipschitzConnectorColumn_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        |θ' ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
              - Real.exp (dampedActivityCoreExponent μm β χ T s r θ'))|)
      ≤ |θ - θ'| * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
  have hpre : (0:ℝ) ≤ |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) hCf0
  calc (∑ T ∈ typedTouchingFamilies (N := N) s,
        |θ' ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
              - Real.exp (dampedActivityCoreExponent μm β χ T s r θ'))|)
      ≤ ∑ T ∈ typedTouchingFamilies (N := N) s,
          |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
            * halfTiltCoreBudgetTerm β 3 s T :=
        Finset.sum_le_sum (fun T hT =>
          abs_lipschitzConnectorColumnTerm_le μm hβ mχ hχabs hsmall
            mf hCf0 hCf hT hsep h0 h1 h0' h1')
    _ = |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
          * ∑ T ∈ typedTouchingFamilies (N := N) s,
              halfTiltCoreBudgetTerm β 3 s T := by
        rw [Finset.mul_sum]
    _ ≤ |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
          * Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
        mul_le_mul_of_nonneg_left (sum_halfTilt_three_le hβ hsmall s) hpre
    _ = |θ - θ'| * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
        ring

/-- **CONNECTOR COLUMN, ABSOLUTE VALUE OF THE SUM**. -/
theorem abs_sum_lipschitzConnectorColumn_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    |∑ T ∈ typedTouchingFamilies (N := N) s,
        θ' ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
              - Real.exp (dampedActivityCoreExponent μm β χ T s r θ'))|
      ≤ |θ - θ'| * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
  le_trans (Finset.abs_sum_le_sum_abs _ _)
    (sum_abs_lipschitzConnectorColumn_le μm hβ mχ hχabs hsmall mf hCf0 hCf
      hsep h0 h1 h0' h1')

/-! ## 53-B.3 — the bridge column (κ = 1, tilt 7/8) -/

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **The bridge weight**: |θ^t − θ′^t| ≤ t·|θ − θ′| ≤ card T·|θ − θ′|,
    t = touchCount r T. -/
theorem abs_pow_touchCount_sub_le_card_mul_abs_sub (r : Set (Link N))
    (T : Finset (Polymer N)) {θ θ' : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    |θ ^ touchCount r T - θ' ^ touchCount r T|
      ≤ (T.card : ℝ) * |θ - θ'| :=
  le_trans (abs_pow_sub_pow_le_nat_mul_abs_sub h0 h1 h0' h1' _)
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (touchCount_le_card r T))
      (abs_nonneg _))

/-- **BRIDGE-COLUMN TERM, κ = 1**: for a bridge core T,
      |(θ^t − θ′^t)·W_T·e^{E_T(θ)}|
        ≤ |θ − θ′|·e^{−n/2}·Cf·(e^{1·b_T·(2/113)}·Π massTilt(7/8) M).
    The count is paid by card T·|θ − θ′|; card T·|W_T·e^{E_T(θ)}| is
    the 53-A damped bridge first moment (the damped exponent pays
    only the local barrier, κ = 1; the separation e^{−n/2} comes from
    the bridge geometry n ≤ m_T and the tilt 7/8). -/
theorem abs_lipschitzBridgeColumnTerm_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ activityBridgeCores (N := N) s r)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    |(θ ^ touchCount r T - θ' ^ touchCount r T)
        * typedMarkedCoreWeight μm β χ f T
        * Real.exp (dampedActivityCoreExponent μm β χ T s r θ)|
      ≤ |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) := by
  have hw := abs_pow_touchCount_sub_le_card_mul_abs_sub r T h0 h1 h0' h1'
  have hmom := nat_card_mul_abs_dampedNormalizedTerm_le_bridge
    μm hβ mχ hχabs hsmall mf hCf0 hCf hT hsep h0 h1
  rw [mul_assoc, abs_mul]
  calc |θ ^ touchCount r T - θ' ^ touchCount r T|
        * |typedMarkedCoreWeight μm β χ f T
            * Real.exp (dampedActivityCoreExponent μm β χ T s r θ)|
      ≤ ((T.card : ℝ) * |θ - θ'|)
        * |typedMarkedCoreWeight μm β χ f T
            * Real.exp (dampedActivityCoreExponent μm β χ T s r θ)| :=
        mul_le_mul_of_nonneg_right hw (abs_nonneg _)
    _ = |θ - θ'| * ((T.card : ℝ)
          * |typedMarkedCoreWeight μm β χ f T
              * Real.exp (dampedActivityCoreExponent μm β χ T s r θ)|) := by
        ring
    _ ≤ |θ - θ'| * (Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η)) :=
        mul_le_mul_of_nonneg_left hmom (abs_nonneg _)
    _ = |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) := by
        ring

/-- **BRIDGE COLUMN, SUM OF ABSOLUTE VALUES** (budget (7/8, 1)):
      Σ_{T bridge} |(θ^t − θ′^t)·W_T·e^{E_T(θ)}|
        ≤ |θ − θ′|·Cf·e^{−n/2}·e^{2·D_s·(2/113)}  (= e^{4 D_s/113}). -/
theorem sum_abs_lipschitzBridgeColumn_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    (∑ T ∈ activityBridgeCores (N := N) s r,
        |(θ ^ touchCount r T - θ' ^ touchCount r T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (dampedActivityCoreExponent μm β χ T s r θ)|)
      ≤ |θ - θ'| * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
  have hpre : (0:ℝ) ≤ |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) hCf0
  have hterm0 : ∀ T : Finset (Polymer N),
      (0:ℝ) ≤ |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
        * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) :=
    fun T => mul_nonneg hpre (sevenEighthsBudgetTerm_nonneg hβ s T)
  calc (∑ T ∈ activityBridgeCores (N := N) s r,
        |(θ ^ touchCount r T - θ' ^ touchCount r T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (dampedActivityCoreExponent μm β χ T s r θ)|)
      ≤ ∑ T ∈ activityBridgeCores (N := N) s r,
          |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
            * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
              * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) :=
        Finset.sum_le_sum (fun T hT =>
          abs_lipschitzBridgeColumnTerm_le μm hβ mχ hχabs hsmall
            mf hCf0 hCf hT hsep h0 h1 h0' h1')
    _ ≤ ∑ T ∈ typedTouchingFamilies (N := N) s,
          |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
            * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
              * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun T _ _ => hterm0 T)
    _ = |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
          * ∑ T ∈ typedTouchingFamilies (N := N) s,
              Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
                * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η := by
        rw [Finset.mul_sum]
    _ ≤ |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
          * Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
        mul_le_mul_of_nonneg_left (sum_sevenEighthsTilt_one_le hβ hsmall s) hpre
    _ = |θ - θ'| * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
        ring

/-- **BRIDGE COLUMN, ABSOLUTE VALUE OF THE SUM**. -/
theorem abs_sum_lipschitzBridgeColumn_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    |∑ T ∈ activityBridgeCores (N := N) s r,
        (θ ^ touchCount r T - θ' ^ touchCount r T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (dampedActivityCoreExponent μm β χ T s r θ)|
      ≤ |θ - θ'| * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
  le_trans (Finset.abs_sum_le_sum_abs _ _)
    (sum_abs_lipschitzBridgeColumn_le μm hβ mχ hχabs hsmall mf hCf0 hCf
      hsep h0 h1 h0' h1')

/-! ## 53-B.4 — the two-term estimate and the CAPSTONE -/

/-- **TWO-TERM LIPSCHITZ ESTIMATE**: ledger + triangle inequality +
    the two column bounds, constants kept separate:
      |F(θ) − F(θ′)| ≤ |θ − θ′|·Cf·e^{−n/2}·(e^{8 D_s/113} + e^{4 D_s/113}).
    Written with the constants `4·D_s·(2/113)` and `2·D_s·(2/113)`.
    No `DependsOnlyOn f s`; 0 ≤ Cf derived. -/
theorem abs_activityDampedExpectation_sub_activityDampedExpectation_le_two_terms
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)}
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    |activityDampedExpectation μm β χ f s r θ
        - activityDampedExpectation μm β χ f s r θ'|
      ≤ |θ - θ'| * Cf * Real.exp (-(n : ℝ) / 2)
          * (Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))) := by
  have hCf0 : 0 ≤ Cf := nonneg_of_abs_le_of_config hCf
  have hA := abs_sum_lipschitzConnectorColumn_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf hsep h0 h1 h0' h1'
  have hB := abs_sum_lipschitzBridgeColumn_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf hsep h0 h1 h0' h1'
  rw [activityDampedExpectation_sub_eq_two_column_lipschitz_ledger
    μm hβ mχ hχabs hsmall f s r h0 h1 h0' h1']
  refine le_trans (abs_add _ _) ?_
  have hsum := add_le_add hA hB
  calc _ ≤ _ := hsum
    _ = _ := by ring

/-- **CAPSTONE 53 — LIPSCHITZ STABILITY OF THE DAMPED FUNCTIONAL IN
    THE DAMPING PARAMETER**: for a local observable f (support s,
    bound Cf) and damping parameters θ, θ′ ∈ [0,1] on a region r at
    walk-barrier separation n from s,
      |F(θ) − F(θ′)| ≤ |θ − θ′|·2·Cf·e^{8 D_s/113}·e^{−n/2},
    the SAME constant as the Stone 52 capstone, uniform in θ, θ′, r.
    From the two-term estimate and e^{4 D_s/113} ≤ e^{8 D_s/113}
    (D_s ≥ 0). No `DependsOnlyOn f s`; no division by |θ − θ′|. -/
theorem abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)}
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    |activityDampedExpectation μm β χ f s r θ
        - activityDampedExpectation μm β χ f s r θ'|
      ≤ |θ - θ'| * (2 * Cf)
          * Real.exp (8 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) := by
  have hCf0 : 0 ≤ Cf := nonneg_of_abs_le_of_config hCf
  have h2 := abs_activityDampedExpectation_sub_activityDampedExpectation_le_two_terms
    μm hβ mχ hχabs hsmall mf hCf hsep h0 h1 h0' h1'
  have hD : (0:ℝ) ≤ ((supportLinkFinset (N := N) s).card : ℝ) :=
    Nat.cast_nonneg _
  have hmono : Real.exp
      (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
      ≤ Real.exp
        (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  have hpos : (0:ℝ) ≤ |θ - θ'| * Cf * Real.exp (-(n : ℝ) / 2) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hCf0) (Real.exp_pos _).le
  have h8 : Real.exp (8 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
      = Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
    congr 1
    ring
  rw [h8]
  refine le_trans h2 ?_
  calc |θ - θ'| * Cf * Real.exp (-(n : ℝ) / 2)
          * (Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)))
      ≤ |θ - θ'| * Cf * Real.exp (-(n : ℝ) / 2)
          * (Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hmono _) hpos
    _ = |θ - θ'| * (2 * Cf)
          * Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
          * Real.exp (-(n : ℝ) / 2) := by ring

/-! ## 53-B.5 — endpoints -/

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **θ = θ′**: the difference is 0 (no hypotheses). -/
theorem activityDampedExpectation_sub_self (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s r : Set (Link N)) (θ : ℝ) :
    activityDampedExpectation μm β χ f s r θ
        - activityDampedExpectation μm β χ f s r θ = 0 :=
  sub_self _

/-- **θ = θ′, through the capstone**: the bound itself is 0 there
    (nothing was divided by |θ − θ′|). -/
theorem lipschitz_bound_self {s : Set (Link N)} (Cf : ℝ) (n : ℕ) (θ : ℝ) :
    |θ - θ| * (2 * Cf)
        * Real.exp (8 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
        * Real.exp (-(n : ℝ) / 2) = 0 := by
  rw [sub_self, abs_zero, zero_mul, zero_mul, zero_mul]

/-- **θ′ = 1 recovers Stone 52**: with `DependsOnlyOn f s` the damped
    functional at 1 is the Gibbs expectation (52-A), |θ − 1| = 1 − θ,
    and the capstone at θ′ = 1 IS the Stone 52 capstone with the same
    constant (compare
    `abs_gibbsExpectation_sub_activityDampedExpectation_le_local_exp_decay`). -/
theorem abs_activityDampedExpectation_sub_gibbsExpectation_le_of_damping_one
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |activityDampedExpectation μm β χ f s r θ
        - gibbsExpectation (N := N) μm β χ f|
      ≤ (1 - θ) * (2 * Cf)
          * Real.exp (8 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) := by
  have h := abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay
    μm hβ mχ hχabs hsmall mf hCf hsep h0 h1 (zero_le_one : (0:ℝ) ≤ 1)
    (le_refl (1:ℝ))
  rw [activityDampedExpectation_one μm hβ mχ hχabs hf mf hCf r,
    abs_sub_comm θ 1, abs_of_nonneg (sub_nonneg.mpr h1)] at h
  exact h

/-- **The Stone 52 capstone re-derived from Stone 53** (same
    statement, same constant; only the order of the difference
    differs). -/
theorem abs_gibbsExpectation_sub_activityDampedExpectation_le_of_lipschitz
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |gibbsExpectation (N := N) μm β χ f
        - activityDampedExpectation μm β χ f s r θ|
      ≤ (1 - θ) * (2 * Cf)
          * Real.exp (8 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) := by
  rw [abs_sub_comm]
  exact abs_activityDampedExpectation_sub_gibbsExpectation_le_of_damping_one
    μm hβ mχ hχabs hsmall hf mf hCf hsep h0 h1

/-- **θ′ = 0**: the distance from the damped functional to the
    activity-restricted functional of Stone 51 carries the factor θ
    (|θ − 0| = θ); no `DependsOnlyOn f s`. -/
theorem abs_activityDampedExpectation_sub_activityRestrictedExpectation_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)}
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |activityDampedExpectation μm β χ f s r θ
        - activityRestrictedExpectation μm β χ f s r|
      ≤ θ * (2 * Cf)
          * Real.exp (8 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) := by
  have h := abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay
    μm hβ mχ hχabs hsmall mf hCf hsep h0 h1 (le_refl (0:ℝ))
    (zero_le_one : (0:ℝ) ≤ 1)
  rw [activityDampedExpectation_zero, sub_zero, abs_of_nonneg h0] at h
  exact h

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **r = ∅**: the damping is trivial and F(θ) = F(θ′) exactly, for
    ALL real θ, θ′ (no hypotheses: both sides are the undamped ratio). -/
theorem activityDampedExpectation_sub_activityDampedExpectation_empty_region
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ) (s : Set (Link N)) (θ θ' : ℝ) :
    activityDampedExpectation μm β χ f s (∅ : Set (Link N)) θ
        - activityDampedExpectation μm β χ f s (∅ : Set (Link N)) θ' = 0 := by
  unfold activityDampedExpectation
  rw [activityDampedMarkedGas_empty_region μm β χ f s θ,
    activityDampedMarkedGas_empty_region μm β χ f s θ',
    activityDampedPolymerGas_empty_region μm β χ θ,
    activityDampedPolymerGas_empty_region μm β χ θ', sub_self]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **r = ∅, column by column**: both ledger columns vanish termwise
    (every touchCount is 0, E_T(θ) = E_T(θ′) = the full exponent). -/
theorem two_column_lipschitz_ledger_empty_region (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s : Set (Link N)) (θ θ' : ℝ) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        θ' ^ touchCount (∅ : Set (Link N)) T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (dampedActivityCoreExponent μm β χ T s ∅ θ)
              - Real.exp (dampedActivityCoreExponent μm β χ T s ∅ θ')))
      + ∑ T ∈ activityBridgeCores (N := N) s (∅ : Set (Link N)),
        (θ ^ touchCount (∅ : Set (Link N)) T
            - θ' ^ touchCount (∅ : Set (Link N)) T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (dampedActivityCoreExponent μm β χ T s ∅ θ) = 0 := by
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro T _
    rw [touchCount_empty_region, pow_zero, pow_zero, sub_self, zero_mul, zero_mul]
  · intro T _
    rw [dampedActivityCoreExponent_empty_region μm β χ T s θ,
      dampedActivityCoreExponent_empty_region μm β χ T s θ', sub_self, mul_zero]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **θ = θ′, column by column**: both ledger columns vanish termwise. -/
theorem two_column_lipschitz_ledger_self (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s r : Set (Link N)) (θ : ℝ) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        θ ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
              - Real.exp (dampedActivityCoreExponent μm β χ T s r θ)))
      + ∑ T ∈ activityBridgeCores (N := N) s r,
        (θ ^ touchCount r T - θ ^ touchCount r T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (dampedActivityCoreExponent μm β χ T s r θ) = 0 := by
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro T _
    rw [sub_self, zero_mul, zero_mul]
  · intro T _
    rw [sub_self, mul_zero]

#print axioms activityDampedExpectation_sub_eq_two_column_lipschitz_ledger
#print axioms abs_lipschitzConnectorColumnTerm_le
#print axioms sum_abs_lipschitzConnectorColumn_le
#print axioms abs_sum_lipschitzConnectorColumn_le
#print axioms abs_pow_touchCount_sub_le_card_mul_abs_sub
#print axioms abs_lipschitzBridgeColumnTerm_le
#print axioms sum_abs_lipschitzBridgeColumn_le
#print axioms abs_sum_lipschitzBridgeColumn_le
#print axioms abs_activityDampedExpectation_sub_activityDampedExpectation_le_two_terms
#print axioms abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay
#print axioms activityDampedExpectation_sub_self
#print axioms lipschitz_bound_self
#print axioms abs_activityDampedExpectation_sub_gibbsExpectation_le_of_damping_one
#print axioms abs_gibbsExpectation_sub_activityDampedExpectation_le_of_lipschitz
#print axioms abs_activityDampedExpectation_sub_activityRestrictedExpectation_le
#print axioms activityDampedExpectation_sub_activityDampedExpectation_empty_region
#print axioms two_column_lipschitz_ledger_empty_region
#print axioms two_column_lipschitz_ledger_self

end LatticeGauge
