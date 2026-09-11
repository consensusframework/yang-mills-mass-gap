/-
LatticeGauge/ActivityDampingColumnBounds.lean — PEDRA 52,
Gate 52-D: THE TWO COLUMN ESTIMATES OF THE DAMPING LEDGER
(architecture: Sol/GPT-5.6; execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): the 52-B ledger is
exact,

    gibbs − damped = Σ_{T touching} θ^t·W_T·(e^{E_T(1)} − e^{E_T(θ)})
                   + Σ_{T bridge}   (1 − θ^t)·W_T·e^{E_T(1)},

t = touchCount r T. This gate estimates the two columns SEPARATELY,
each with the factor (1 − θ) in front, and does NOT combine them:

  * connector column (ALL touching cores, not only the region-
    allowed ones): the 52-C factorization e^{E_T(1)} − e^{E_T(θ)}
    = e^{E_T(1)}(1 − e^{C_{T,r}(θ)}), the normalization
    W_T·e^{E_T(1)} = N_f(s,T), the 52-C exponential control
    |1 − e^{C}| ≤ (1−θ)·e^{−n/2}·e^{m_T/2 + 2b_T}, 0 ≤ θ^t ≤ 1, and
    the budget (λ, κ) = (1/2, 3):
      Σ_T |θ^t·W_T·(e^{E_T(1)} − e^{E_T(θ)})| ≤ (1−θ)·Cf·e^{−n/2}·e^{8 D_s/113};
  * bridge column (the bridge cores of the ledger, exactly):
    0 ≤ 1 − θ^t ≤ t(1−θ) ≤ card T·(1−θ), the 52-A0 bridge first
    moment card T·|N_f(s,T)| ≤ e^{−n/2}·Cf·(e^{b_T}·Π massTilt(7/8))
    — where the separation e^{−n/2} is paid by the bridge geometry
    n ≤ m_T (`activityBridgeCore_familyTotalCard_ge`) inside that
    lemma — and the budget (λ, κ) = (7/8, 1):
      Σ_{T bridge} |(1 − θ^t)·W_T·e^{E_T(1)}| ≤ (1−θ)·Cf·e^{−n/2}·e^{4 D_s/113}.

Both sums of absolute values and both absolute values of sums are
provided. Endpoints: θ = 1 kills both columns termwise; θ = 0
reduces the connector column to the Stone 51 allowed column (the
bridge terms carry 0^t = 0) and the bridge column to the Stone 51
bridge column; r = ∅ kills both termwise. Nothing is divided by
(1 − θ): θ = 1 stays covered.

HARD HOLD (not here): the combination of the two columns into the
bound on |gibbs − damped|, the Stone 52 capstone and the
certification of its constant (52-E); any Disjoint s r, size
restriction on r or volume factor; the budget (7/8, 3); the factor
8/(3e); Gibbs-measure, boundary-condition, modified-action or
switch-off interpretations; thermodynamic limit, continuum, mass
gap. No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.ActivityDampingConnector

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## 52-D.1 — the connector column, termwise (κ = 3) -/

/-- **CONNECTOR-COLUMN TERM, κ = 3**: for every touching core T
    (region-allowed or bridge alike),
      |θ^t·W_T·(e^{E_T(1)} − e^{E_T(θ)})|
        ≤ (1 − θ)·e^{−n/2}·Cf·halfTiltCoreBudgetTerm β 3 s T.
    Route: 52-C factorization, normalization W_T·e^{E_T(1)} = N,
    |N| ≤ Cf·e^{b_T}·Π M, the 52-C exponential control (which
    carries (1−θ) and e^{−n/2}·e^{m_T/2}), and 0 ≤ θ^t ≤ 1. -/
theorem abs_dampingConnectorColumnTerm_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |θ ^ touchCount r T
        * typedMarkedCoreWeight μm β χ f T
        * (Real.exp (fullActivityCoreExponent μm β χ T s)
            - Real.exp (dampedActivityCoreExponent μm β χ T s r θ))|
      ≤ (1 - θ) * Real.exp (-(n : ℝ) / 2) * Cf
          * halfTiltCoreBudgetTerm β 3 s T := by
  -- the 52-C factorization of the exponential difference
  rw [exp_full_sub_exp_damped_eq_activityDampingConnector
    μm hβ mχ hχabs hsmall T s r h0 h1]
  -- normalization W_T·e^{E_T(1)} = N_f(s,T)
  have hbridge :=
    typedMarkedCoreWeight_mul_exp_full_eq_normalizedMarkedCoreTerm
      μm hβ mχ hχabs hsmall f s T
  have hN := abs_normalizedMarkedCoreTerm_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf s T
  -- the 52-C exponential control, repurchased form
  have hE := abs_one_sub_exp_activityDampingConnector_le_decay
    μm hβ mχ hχabs hsmall hT hsep h0 h1
  -- the damping weight is in [0, 1]
  have hθ0 : 0 ≤ θ ^ touchCount r T := dampedPow_nonneg h0 _
  have hθ1 : θ ^ touchCount r T ≤ 1 := dampedPow_le_one h0 h1 _
  have hM : (0:ℝ) ≤ ∏ η ∈ T, mayerCoreMajorant β η :=
    Finset.prod_nonneg (fun η _ => mayerCoreMajorant_nonneg hβ η)
  have hb1 : (0:ℝ) ≤ Cf * Real.exp
      (((barrierLinkFinset T s).card : ℝ) * (2/113))
      * ∏ η ∈ T, mayerCoreMajorant β η :=
    mul_nonneg (mul_nonneg hCf0 (Real.exp_pos _).le) hM
  have hE0 : (0:ℝ) ≤ (1 - θ) * Real.exp (-(n : ℝ) / 2)
      * Real.exp ((familyTotalCard T : ℝ) / 2
          + 2 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113)) :=
    mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) (Real.exp_pos _).le
  have hexp : Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
      * Real.exp ((familyTotalCard T : ℝ) / 2
          + 2 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
      = Real.exp ((familyTotalCard T : ℝ) / 2
          + 3 * ((barrierLinkFinset T s).card : ℝ) * (2/113)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  -- regroup: θ^t · (W·e^{E1}) · (1 − e^{C})
  have hre : θ ^ touchCount r T * typedMarkedCoreWeight μm β χ f T
      * (Real.exp (fullActivityCoreExponent μm β χ T s)
          * (1 - Real.exp (activityDampingConnector μm β χ T s r θ)))
      = θ ^ touchCount r T
        * ((typedMarkedCoreWeight μm β χ f T
              * Real.exp (fullActivityCoreExponent μm β χ T s))
            * (1 - Real.exp (activityDampingConnector μm β χ T s r θ))) := by
    ring
  rw [hre, hbridge, abs_mul, abs_mul, abs_of_nonneg hθ0]
  calc θ ^ touchCount r T
        * (|normalizedMarkedCoreTerm μm β χ f s T|
            * |1 - Real.exp (activityDampingConnector μm β χ T s r θ)|)
      ≤ 1 * (|normalizedMarkedCoreTerm μm β χ f s T|
            * |1 - Real.exp (activityDampingConnector μm β χ T s r θ)|) :=
        mul_le_mul_of_nonneg_right hθ1
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = |normalizedMarkedCoreTerm μm β χ f s T|
          * |1 - Real.exp (activityDampingConnector μm β χ T s r θ)| :=
        one_mul _
    _ ≤ (Cf * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, mayerCoreMajorant β η)
          * ((1 - θ) * Real.exp (-(n : ℝ) / 2)
            * Real.exp ((familyTotalCard T : ℝ) / 2
                + 2 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113))) :=
        mul_le_mul hN hE (abs_nonneg _) hb1
    _ = (1 - θ) * Real.exp (-(n : ℝ) / 2) * Cf
          * halfTiltCoreBudgetTerm β 3 s T := by
        rw [halfTiltCoreBudgetTerm_eq, ← hexp]
        ring

/-! ## 52-D.2 — the connector column, summed (budget (1/2, 3)) -/

/-- **CONNECTOR COLUMN, SUM OF ABSOLUTE VALUES**: over ALL touching
    cores,
      Σ_T |θ^t·W_T·(e^{E_T(1)} − e^{E_T(θ)})|
        ≤ (1 − θ)·Cf·e^{−n/2}·e^{4·D_s·(2/113)}  (= e^{8 D_s/113}). -/
theorem sum_abs_dampingConnectorColumn_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        |θ ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (fullActivityCoreExponent μm β χ T s)
              - Real.exp (dampedActivityCoreExponent μm β χ T s r θ))|)
      ≤ (1 - θ) * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
  have hpre : (0:ℝ) ≤ (1 - θ) * Real.exp (-(n : ℝ) / 2) * Cf :=
    mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) hCf0
  calc (∑ T ∈ typedTouchingFamilies (N := N) s,
        |θ ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (fullActivityCoreExponent μm β χ T s)
              - Real.exp (dampedActivityCoreExponent μm β χ T s r θ))|)
      ≤ ∑ T ∈ typedTouchingFamilies (N := N) s,
          (1 - θ) * Real.exp (-(n : ℝ) / 2) * Cf
            * halfTiltCoreBudgetTerm β 3 s T :=
        Finset.sum_le_sum (fun T hT =>
          abs_dampingConnectorColumnTerm_le μm hβ mχ hχabs hsmall
            mf hCf0 hCf hT hsep h0 h1)
    _ = (1 - θ) * Real.exp (-(n : ℝ) / 2) * Cf
          * ∑ T ∈ typedTouchingFamilies (N := N) s,
              halfTiltCoreBudgetTerm β 3 s T := by
        rw [Finset.mul_sum]
    _ ≤ (1 - θ) * Real.exp (-(n : ℝ) / 2) * Cf
          * Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
        mul_le_mul_of_nonneg_left (sum_halfTilt_three_le hβ hsmall s) hpre
    _ = (1 - θ) * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
        ring

/-- **CONNECTOR COLUMN, ABSOLUTE VALUE OF THE SUM** (for the
    capstone's consumption): |Σ_T …| ≤ (1 − θ)·Cf·e^{−n/2}·e^{8 D_s/113}. -/
theorem abs_sum_dampingConnectorColumn_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |∑ T ∈ typedTouchingFamilies (N := N) s,
        θ ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (fullActivityCoreExponent μm β χ T s)
              - Real.exp (dampedActivityCoreExponent μm β χ T s r θ))|
      ≤ (1 - θ) * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
  le_trans (Finset.abs_sum_le_sum_abs _ _)
    (sum_abs_dampingConnectorColumn_le μm hβ mχ hχabs hsmall mf hCf0 hCf hsep h0 h1)

/-! ## 52-D.3 — the bridge column, termwise (κ = 1) -/

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **The bridge weight**: 0 ≤ 1 − θ^t ≤ t·(1 − θ) ≤ card T·(1 − θ),
    t = touchCount r T (52-A0 count lemma + touchCount ≤ card). -/
theorem one_sub_pow_touchCount_le_card_mul_one_sub (r : Set (Link N))
    (T : Finset (Polymer N)) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    0 ≤ 1 - θ ^ touchCount r T
      ∧ 1 - θ ^ touchCount r T ≤ (touchCount r T : ℝ) * (1 - θ)
      ∧ (touchCount r T : ℝ) * (1 - θ) ≤ (T.card : ℝ) * (1 - θ) :=
  ⟨one_sub_dampedPow_nonneg h0 h1 _,
   one_sub_dampedPow_le_nat_mul_one_sub h0 h1 _,
   mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (touchCount_le_card r T))
     (by linarith)⟩

/-- **BRIDGE-COLUMN TERM, κ = 1**: for a bridge core T,
      |(1 − θ^t)·W_T·e^{E_T(1)}|
        ≤ (1 − θ)·e^{−n/2}·Cf·(e^{1·b_T·(2/113)}·Π massTilt(7/8) M).
    The count is paid by card T·(1−θ); card T·|N_f(s,T)| is the 52-A0
    bridge first moment, in which the separation e^{−n/2} comes from
    the bridge geometry n ≤ m_T (`activityBridgeCore_familyTotalCard_ge`)
    and the tilt 7/8. -/
theorem abs_dampingBridgeColumnTerm_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ activityBridgeCores (N := N) s r)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |(1 - θ ^ touchCount r T)
        * typedMarkedCoreWeight μm β χ f T
        * Real.exp (fullActivityCoreExponent μm β χ T s)|
      ≤ (1 - θ) * Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) := by
  obtain ⟨hw0, hw1, hw2⟩ :=
    one_sub_pow_touchCount_le_card_mul_one_sub r T h0 h1
  have hmom := nat_card_mul_abs_normalizedMarkedCoreTerm_le_budgetTerm
    μm hβ mχ hχabs hsmall mf hCf0 hCf hT hsep
  have hθ : (0:ℝ) ≤ 1 - θ := by linarith
  rw [mul_assoc, typedMarkedCoreWeight_mul_exp_full_eq_normalizedMarkedCoreTerm
      μm hβ mχ hχabs hsmall f s T,
    abs_mul, abs_of_nonneg hw0]
  calc (1 - θ ^ touchCount r T) * |normalizedMarkedCoreTerm μm β χ f s T|
      ≤ ((T.card : ℝ) * (1 - θ)) * |normalizedMarkedCoreTerm μm β χ f s T| :=
        mul_le_mul_of_nonneg_right (le_trans hw1 hw2) (abs_nonneg _)
    _ = (1 - θ) * ((T.card : ℝ) * |normalizedMarkedCoreTerm μm β χ f s T|) := by
        ring
    _ ≤ (1 - θ) * (Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η)) :=
        mul_le_mul_of_nonneg_left hmom hθ
    _ = (1 - θ) * Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) := by
        ring

/-! ## 52-D.4 — the bridge column, summed (budget (7/8, 1)) -/

/-- The (7/8, 1) budget summand is nonnegative. -/
theorem sevenEighthsBudgetTerm_nonneg {β : ℝ} (hβ : 0 ≤ β)
    (s : Set (Link N)) (T : Finset (Polymer N)) :
    (0:ℝ) ≤ Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
      * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η :=
  mul_nonneg (Real.exp_pos _).le
    (Finset.prod_nonneg (fun η _ =>
      massTiltActivity_nonneg (mayerCoreMajorant_nonneg hβ) η))

/-- **BRIDGE COLUMN, SUM OF ABSOLUTE VALUES**: over the bridge cores
    of the ledger,
      Σ_T |(1 − θ^t)·W_T·e^{E_T(1)}|
        ≤ (1 − θ)·Cf·e^{−n/2}·e^{2·D_s·(2/113)}  (= e^{4 D_s/113}).
    Termwise κ = 1 bound, inclusion of the bridge cores into the
    touching cores (nonnegative summands), budget (7/8, 1). -/
theorem sum_abs_dampingBridgeColumn_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    (∑ T ∈ activityBridgeCores (N := N) s r,
        |(1 - θ ^ touchCount r T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (fullActivityCoreExponent μm β χ T s)|)
      ≤ (1 - θ) * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
  have hpre : (0:ℝ) ≤ (1 - θ) * Real.exp (-(n : ℝ) / 2) * Cf :=
    mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le) hCf0
  have hterm0 : ∀ T : Finset (Polymer N),
      (0:ℝ) ≤ (1 - θ) * Real.exp (-(n : ℝ) / 2) * Cf
        * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) :=
    fun T => mul_nonneg hpre (sevenEighthsBudgetTerm_nonneg hβ s T)
  calc (∑ T ∈ activityBridgeCores (N := N) s r,
        |(1 - θ ^ touchCount r T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (fullActivityCoreExponent μm β χ T s)|)
      ≤ ∑ T ∈ activityBridgeCores (N := N) s r,
          (1 - θ) * Real.exp (-(n : ℝ) / 2) * Cf
            * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
              * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) :=
        Finset.sum_le_sum (fun T hT =>
          abs_dampingBridgeColumnTerm_le μm hβ mχ hχabs hsmall
            mf hCf0 hCf hT hsep h0 h1)
    _ ≤ ∑ T ∈ typedTouchingFamilies (N := N) s,
          (1 - θ) * Real.exp (-(n : ℝ) / 2) * Cf
            * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
              * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun T _ _ => hterm0 T)
    _ = (1 - θ) * Real.exp (-(n : ℝ) / 2) * Cf
          * ∑ T ∈ typedTouchingFamilies (N := N) s,
              Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
                * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η := by
        rw [Finset.mul_sum]
    _ ≤ (1 - θ) * Real.exp (-(n : ℝ) / 2) * Cf
          * Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
        mul_le_mul_of_nonneg_left (sum_sevenEighthsTilt_one_le hβ hsmall s) hpre
    _ = (1 - θ) * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
        ring

/-- **BRIDGE COLUMN, ABSOLUTE VALUE OF THE SUM**. -/
theorem abs_sum_dampingBridgeColumn_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    |∑ T ∈ activityBridgeCores (N := N) s r,
        (1 - θ ^ touchCount r T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (fullActivityCoreExponent μm β χ T s)|
      ≤ (1 - θ) * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
  le_trans (Finset.abs_sum_le_sum_abs _ _)
    (sum_abs_dampingBridgeColumn_le μm hβ mχ hχabs hsmall mf hCf0 hCf hsep h0 h1)

/-! ## 52-D.5 — the columns ARE the 52-B ledger columns (interface) -/

/-- The two estimated sums are literally the two columns of the 52-B
    ledger: restated capstone, no new content. -/
theorem ledger_columns_are_the_estimated_sums
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
            * Real.exp (fullActivityCoreExponent μm β χ T s) :=
  gibbsExpectation_sub_activityDampedExpectation_eq_two_column_ledger
    μm hβ mχ hχabs hsmall hf mf hCf r h0 h1

/-! ## 52-D.6 — endpoints of the two columns -/

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **θ = 1**: both column terms vanish (no division by 1 − θ). -/
theorem dampingConnectorColumnTerm_one (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (T : Finset (Polymer N)) (s r : Set (Link N)) :
    (1 : ℝ) ^ touchCount r T
        * typedMarkedCoreWeight μm β χ f T
        * (Real.exp (fullActivityCoreExponent μm β χ T s)
            - Real.exp (dampedActivityCoreExponent μm β χ T s r 1)) = 0 := by
  rw [dampedActivityCoreExponent_one, sub_self, mul_zero]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
theorem dampingBridgeColumnTerm_one (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (T : Finset (Polymer N)) (s r : Set (Link N)) :
    (1 - (1 : ℝ) ^ touchCount r T)
        * typedMarkedCoreWeight μm β χ f T
        * Real.exp (fullActivityCoreExponent μm β χ T s) = 0 := by
  rw [one_pow, sub_self, zero_mul, zero_mul]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **θ = 0, connector column**: the sum over all touching cores IS the
    Stone 51 allowed column (bridge terms carry 0^t = 0; on allowed
    cores the weight is 1 and E_T(0) is the regional exponent). -/
theorem sum_dampingConnectorColumn_zero (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s r : Set (Link N)) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        (0 : ℝ) ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (fullActivityCoreExponent μm β χ T s)
              - Real.exp (dampedActivityCoreExponent μm β χ T s r 0)))
      = ∑ T ∈ activityAllowedCores (N := N) s r,
          typedMarkedCoreWeight μm β χ f T
            * (Real.exp (fullActivityCoreExponent μm β χ T s)
                - Real.exp (regionActivityCoreExponent μm β χ T s r)) := by
  rw [sum_touchingFamilies_eq_activityAllowed_add_bridge s r]
  have hbridge0 : (∑ T ∈ activityBridgeCores (N := N) s r,
        (0 : ℝ) ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (fullActivityCoreExponent μm β χ T s)
              - Real.exp (dampedActivityCoreExponent μm β χ T s r 0))) = 0 := by
    refine Finset.sum_eq_zero (fun T hT => ?_)
    rw [zero_pow (Nat.pos_iff_ne_zero.mp
        (touchCount_pos_of_mem_activityBridgeCores hT)), zero_mul, zero_mul]
  rw [hbridge0, add_zero]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  rw [pow_touchCount_eq_one_of_mem_activityAllowedCores 0 hT, one_mul,
    dampedActivityCoreExponent_zero]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **θ = 0, bridge column**: the Stone 51 bridge column, termwise. -/
theorem sum_dampingBridgeColumn_zero (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s r : Set (Link N)) :
    (∑ T ∈ activityBridgeCores (N := N) s r,
        (1 - (0 : ℝ) ^ touchCount r T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (fullActivityCoreExponent μm β χ T s))
      = ∑ T ∈ activityBridgeCores (N := N) s r,
          typedMarkedCoreWeight μm β χ f T
            * Real.exp (fullActivityCoreExponent μm β χ T s) := by
  refine Finset.sum_congr rfl (fun T hT => ?_)
  rw [zero_pow (Nat.pos_iff_ne_zero.mp
      (touchCount_pos_of_mem_activityBridgeCores hT)), sub_zero, one_mul]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **r = ∅**: both column terms vanish (every count is 0, E_T(θ) is
    the full exponent). -/
theorem dampingConnectorColumnTerm_empty_region (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (T : Finset (Polymer N)) (s : Set (Link N)) (θ : ℝ) :
    θ ^ touchCount (∅ : Set (Link N)) T
        * typedMarkedCoreWeight μm β χ f T
        * (Real.exp (fullActivityCoreExponent μm β χ T s)
            - Real.exp (dampedActivityCoreExponent μm β χ T s ∅ θ)) = 0 := by
  rw [dampedActivityCoreExponent_empty_region, sub_self, mul_zero]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
theorem dampingBridgeColumnTerm_empty_region (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (T : Finset (Polymer N)) (s : Set (Link N)) (θ : ℝ) :
    (1 - θ ^ touchCount (∅ : Set (Link N)) T)
        * typedMarkedCoreWeight μm β χ f T
        * Real.exp (fullActivityCoreExponent μm β χ T s) = 0 := by
  rw [touchCount_empty_region, pow_zero, sub_self, zero_mul, zero_mul]

#print axioms abs_dampingConnectorColumnTerm_le
#print axioms sum_abs_dampingConnectorColumn_le
#print axioms abs_sum_dampingConnectorColumn_le
#print axioms one_sub_pow_touchCount_le_card_mul_one_sub
#print axioms abs_dampingBridgeColumnTerm_le
#print axioms sum_abs_dampingBridgeColumn_le
#print axioms abs_sum_dampingBridgeColumn_le
#print axioms ledger_columns_are_the_estimated_sums
#print axioms sum_dampingConnectorColumn_zero
#print axioms sum_dampingBridgeColumn_zero
#print axioms dampingConnectorColumnTerm_one
#print axioms dampingBridgeColumnTerm_one
#print axioms dampingConnectorColumnTerm_empty_region
#print axioms dampingBridgeColumnTerm_empty_region

end LatticeGauge
