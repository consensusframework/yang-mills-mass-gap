/-
LatticeGauge/ActivityDampingLipschitzRefined.lean — PEDRA 54,
Gate 54-A: QUANTITATIVE STRENGTHENING OF THE LIPSCHITZ STABILITY OF THE
DAMPED FUNCTIONAL — THE CONNECTOR COLUMN AT κ = 2 (architecture and
review: GPT Astra; execution: Fable).

ORIGIN OF THE PROPOSAL (recorded, not re-derived here): section E.3 of
the antecedents-and-originality research report on Stone 53 received by
the coordinator ("κ = 3 is not a demonstrated necessity"), followed by
the architectural review of GPT Astra. The report does not name the
researching model; no identity is invented here.

CONCEPTUAL RECORD (architect's precision, kept): Stone 53 controls the
connector column of the two-parameter ledger through the factorization
e^{E_T(θ)} − e^{E_T(θ′)} = e^{E_T(θ′)}·(e^{Δ} − 1), which costs THREE
barrier exponentials (κ = 3: one from e^{E_T(θ′)} and two from the
control |e^{Δ} − 1| ≤ d·e^{2q_T}) and lands on the budget (1/2, 3),
prefactor e^{8 D_s/113}. Since the exponents are REAL numbers bounded
above by q_T = card(barrierLinkFinset T s)·(2/113), the plain
mean-value bound of the exponential,
    |e^x − e^y| ≤ e^{q}·|x − y|      for x, y ≤ q,
applied to x = E_T(θ), y = E_T(θ′) (both ≤ q_T by 53-A), together with
the eroded two-parameter bound |E_T(θ) − E_T(θ′)| ≤ d·e^{−((n−m_T:ℕ))/2}·q_T
of 53-A and q_T ≤ e^{q_T}, gives
    |e^{E_T(θ)} − e^{E_T(θ′)}| ≤ d·e^{−n/2}·e^{m_T/2 + 2 q_T}     (κ = 2),
so the connector column closes with the budget (1/2, 2), admissible
because 1/2 + 2·(8/113) = 145/226 ≤ 1, and the prefactor e^{6 D_s/113}.
The bridge column of Stone 53 (κ = 1, tilt 7/8, prefactor e^{4 D_s/113})
is reused intact, as is the exact two-parameter ledger (bridge column
with a PLUS sign). Hence, for θ, θ′ ∈ [0, 1],
    |F(θ) − F(θ′)| ≤ |θ − θ′|·Cf·e^{−n/2}·(e^{6 D_s/113} + e^{4 D_s/113})
                  ≤ |θ − θ′|·2·Cf·e^{6 D_s/113}·e^{−n/2},
with F(θ) = activityDampedExpectation, under EXACTLY the hypotheses of
the Stone 53 capstone (no `DependsOnlyOn f s`; 0 ≤ Cf derived; no sign
condition on activities or exponents; nothing divided by |θ − θ′|). The
spatial rate 1/2 and the interval [0, 1] are unchanged. The Stone 53
capstone (prefactor e^{8 D_s/113}) is recovered from the refined one as a
corollary, since e^{6 D_s/113} ≤ e^{8 D_s/113}; no published module is
modified.

No optimality, sharpness or bibliographic priority is claimed for the
constant 6/113.

HARD HOLD (not here): any Disjoint s r, size restriction on r or volume
factor; monotonicity or differentiability in θ; Gibbs-measure,
boundary-condition or modified-action interpretations; thermodynamic
limit, continuum, mass gap. No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.ActivityDampingLipschitz
import LatticeGauge.CovarianceDecay

open MeasureTheory
open scoped Classical

namespace LatticeGauge

/-! ## 54-A.1 — the scalar mean-value bound of the exponential -/

section ScalarLemmas

/-- One-sided mean-value bound: for x, y ≤ q,
    e^x − e^y ≤ e^q·|x − y|. If x ≤ y the left side is ≤ 0; if y ≤ x,
    from (y − x) + 1 ≤ e^{y − x} (Mathlib `Real.add_one_le_exp`)
    multiplied by e^x: e^y ≥ e^x + e^x·(y − x), i.e.
    e^x − e^y ≤ e^x·(x − y) ≤ e^q·(x − y). Only x ≤ q is needed on this
    side; no sign condition on x, y. -/
theorem exp_sub_exp_le_exp_mul_abs_sub {x y q : ℝ} (hx : x ≤ q) :
    Real.exp x - Real.exp y ≤ Real.exp q * |x - y| := by
  rcases le_total x y with h | h
  · have h1 : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr h
    have h2 : (0:ℝ) ≤ Real.exp q * |x - y| :=
      mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
    linarith
  · have h1 := Real.add_one_le_exp (y - x)
    have h2 : Real.exp x * ((y - x) + 1) ≤ Real.exp x * Real.exp (y - x) :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    have h3 : Real.exp x * Real.exp (y - x) = Real.exp y := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h3] at h2
    have h4 : Real.exp x * (y - x) + Real.exp x ≤ Real.exp y := by
      have hr : Real.exp x * ((y - x) + 1)
          = Real.exp x * (y - x) + Real.exp x := by ring
      linarith
    have hxq : Real.exp x ≤ Real.exp q := Real.exp_le_exp.mpr hx
    have h5 : Real.exp x * (x - y) ≤ Real.exp q * (x - y) :=
      mul_le_mul_of_nonneg_right hxq (sub_nonneg.mpr h)
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hr2 : Real.exp x * (x - y) = -(Real.exp x * (y - x)) := by ring
    linarith

/-- **Two-sided mean-value bound**: for x, y ≤ q,
    |e^x − e^y| ≤ e^q·|x − y|. The Stone 53 route paid
    e^{q}·d·e^{2q} through e^{E(θ′)}·(e^{Δ} − 1); this bound pays e^{q}·|Δ|
    only, and introduces no exponential of |x − y|. -/
theorem abs_exp_sub_exp_le_exp_mul_abs_sub {x y q : ℝ}
    (hx : x ≤ q) (hy : y ≤ q) :
    |Real.exp x - Real.exp y| ≤ Real.exp q * |x - y| := by
  rw [abs_sub_le_iff]
  refine ⟨exp_sub_exp_le_exp_mul_abs_sub hx, ?_⟩
  have h := exp_sub_exp_le_exp_mul_abs_sub hy (y := x)
  rw [abs_sub_comm] at h
  exact h

/-- q ≤ e^q for every real q (from q + 1 ≤ e^q). -/
theorem le_exp_self (q : ℝ) : q ≤ Real.exp q := by
  have := Real.add_one_le_exp q
  linarith

end ScalarLemmas

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## 54-A.2 — refined exponential control of the exponent difference (κ = 2) -/

/-- **REFINED EXPONENTIAL CONTROL (two parameters, κ = 2)**:
      |e^{E_T(θ)} − e^{E_T(θ′)}|
        ≤ |θ − θ′|·e^{−n/2}·e^{m_T/2 + 2·b_T·(2/113)}.
    Route: both exponents are ≤ q_T = b_T·(2/113) (53-A); the mean-value
    bound gives e^{q_T}·|E_T(θ) − E_T(θ′)|; the exponent difference is
    the connector difference (53-A), eroded:
    |C_θ − C_θ′| ≤ |θ − θ′|·e^{−((n − m_T : ℕ))/2}·q_T; then q_T ≤ e^{q_T}
    and the repurchased erosion e^{−((n−m_T:ℕ))/2} ≤ e^{−n/2}·e^{m_T/2}
    (natural truncated subtraction: m_T > n gives the factor 1). -/
theorem abs_exp_dampedActivityCoreExponent_sub_le_decay_refined
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
            + 2 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
  set q : ℝ := ((barrierLinkFinset T s).card : ℝ) * (2 / 113) with hq
  -- both exponents are bounded above by q (53-A, κ = 1)
  have hx : dampedActivityCoreExponent μm β χ T s r θ ≤ q :=
    le_trans (le_abs_self _)
      (abs_dampedActivityCoreExponent_le_barrier μm hβ mχ hχabs hsmall T s r h0 h1)
  have hy : dampedActivityCoreExponent μm β χ T s r θ' ≤ q :=
    le_trans (le_abs_self _)
      (abs_dampedActivityCoreExponent_le_barrier μm hβ mχ hχabs hsmall T s r h0' h1')
  -- the eroded bound on the exponent difference (53-A)
  have hΔ : |dampedActivityCoreExponent μm β χ T s r θ
      - dampedActivityCoreExponent μm β χ T s r θ'|
      ≤ |θ - θ'| * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) * q := by
    rw [dampedActivityCoreExponent_sub_eq_activityDampingConnector_sub
      μm hβ mχ hχabs hsmall T s r h0 h1 h0' h1', hq]
    exact abs_activityDampingConnector_sub_le_eroded
      μm hβ mχ hχabs hsmall hT hsep h0 h1 h0' h1'
  have hq0 : (0:ℝ) ≤ q := mul_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hqexp : q ≤ Real.exp q := le_exp_self q
  have herode := exp_neg_nat_sub_half_le n (familyTotalCard T)
  have hd0 : (0:ℝ) ≤ |θ - θ'| := abs_nonneg _
  have he0 : (0:ℝ) ≤ Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) :=
    (Real.exp_pos _).le
  calc |Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
        - Real.exp (dampedActivityCoreExponent μm β χ T s r θ')|
      ≤ Real.exp q * |dampedActivityCoreExponent μm β χ T s r θ
          - dampedActivityCoreExponent μm β χ T s r θ'| :=
        abs_exp_sub_exp_le_exp_mul_abs_sub hx hy
    _ ≤ Real.exp q
          * (|θ - θ'| * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) * q) :=
        mul_le_mul_of_nonneg_left hΔ (Real.exp_pos _).le
    _ ≤ Real.exp q
          * (|θ - θ'| * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2)
              * Real.exp q) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hqexp (mul_nonneg hd0 he0)
    _ ≤ Real.exp q
          * (|θ - θ'| * (Real.exp (-(n : ℝ) / 2)
              * Real.exp ((familyTotalCard T : ℝ) / 2))
              * Real.exp q) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left herode hd0
    _ = |θ - θ'| * Real.exp (-(n : ℝ) / 2)
        * Real.exp ((familyTotalCard T : ℝ) / 2
            + 2 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
        rw [hq, Real.exp_add]
        have h2 : Real.exp (2 * (((barrierLinkFinset T s).card : ℝ) * (2 / 113)))
            = Real.exp (((barrierLinkFinset T s).card : ℝ) * (2 / 113))
              * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have h3 : Real.exp (2 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113))
            = Real.exp (2 * (((barrierLinkFinset T s).card : ℝ) * (2 / 113))) := by
          congr 1
          ring
        rw [h3, h2]
        ring

/-! ## 54-A.3 — the connector column at κ = 2 -/

/-- **REFINED CONNECTOR-COLUMN TERM, κ = 2**: for every touching core T,
      |θ′^t·W_T·(e^{E_T(θ)} − e^{E_T(θ′)})|
        ≤ |θ − θ′|·e^{−n/2}·Cf·halfTiltCoreBudgetTerm β 2 s T.
    0 ≤ θ′^t ≤ 1, |W_T| ≤ Cf·Π M (no exponential), and the refined
    exponential control. -/
theorem abs_refinedConnectorColumnTerm_le
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
          * halfTiltCoreBudgetTerm β 2 s T := by
  have hW := abs_typedMarkedCoreWeight_le_mayerCoreMajorant
    μm hβ mχ hχabs mf hCf0 hCf T
  have hE := abs_exp_dampedActivityCoreExponent_sub_le_decay_refined
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
                + 2 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113))) :=
        mul_le_mul hW hE (abs_nonneg _) hW0
    _ = |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
          * halfTiltCoreBudgetTerm β 2 s T := by
        rw [halfTiltCoreBudgetTerm_eq]
        ring

/-- **REFINED CONNECTOR COLUMN, SUM OF ABSOLUTE VALUES** (budget (1/2, 2)):
      Σ_T |θ′^t·W_T·(e^{E_T(θ)} − e^{E_T(θ′)})|
        ≤ |θ − θ′|·Cf·e^{−n/2}·e^{3·D_s·(2/113)}  (= e^{6 D_s/113}).
    The budget (1/2, 2) is admissible: 1/2 + 2·(8/113) = 145/226 ≤ 1
    (`sum_halfTilt_two_le`, through the generic `coreLocalBudget`). -/
theorem sum_abs_refinedConnectorColumn_le
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
          * Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
  have hpre : (0:ℝ) ≤ |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) hCf0
  calc (∑ T ∈ typedTouchingFamilies (N := N) s,
        |θ' ^ touchCount r T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (dampedActivityCoreExponent μm β χ T s r θ)
              - Real.exp (dampedActivityCoreExponent μm β χ T s r θ'))|)
      ≤ ∑ T ∈ typedTouchingFamilies (N := N) s,
          |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
            * halfTiltCoreBudgetTerm β 2 s T :=
        Finset.sum_le_sum (fun T hT =>
          abs_refinedConnectorColumnTerm_le μm hβ mχ hχabs hsmall
            mf hCf0 hCf hT hsep h0 h1 h0' h1')
    _ = |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
          * ∑ T ∈ typedTouchingFamilies (N := N) s,
              halfTiltCoreBudgetTerm β 2 s T := by
        rw [Finset.mul_sum]
    _ ≤ |θ - θ'| * Real.exp (-(n : ℝ) / 2) * Cf
          * Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
        mul_le_mul_of_nonneg_left (sum_halfTilt_two_le hβ hsmall s) hpre
    _ = |θ - θ'| * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
        ring

/-- **REFINED CONNECTOR COLUMN, ABSOLUTE VALUE OF THE SUM**. -/
theorem abs_sum_refinedConnectorColumn_le
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
          * Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
  le_trans (Finset.abs_sum_le_sum_abs _ _)
    (sum_abs_refinedConnectorColumn_le μm hβ mχ hχabs hsmall mf hCf0 hCf
      hsep h0 h1 h0' h1')

/-! ## 54-A.4 — the refined two-term estimate and the refined capstone -/

/-- **REFINED TWO-TERM ESTIMATE**: the Stone 53 ledger + triangle
    inequality + the refined connector column (κ = 2) + the Stone 53
    bridge column (κ = 1), constants kept separate:
      |F(θ) − F(θ′)| ≤ |θ − θ′|·Cf·e^{−n/2}·(e^{6 D_s/113} + e^{4 D_s/113}).
    Written with the constants `3·D_s·(2/113)` and `2·D_s·(2/113)`.
    No `DependsOnlyOn f s`; 0 ≤ Cf derived. -/
theorem abs_activityDampedExpectation_sub_activityDampedExpectation_le_two_terms_refined
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
          * (Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))) := by
  have hCf0 : 0 ≤ Cf := nonneg_of_abs_le_of_config hCf
  have hA := abs_sum_refinedConnectorColumn_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf hsep h0 h1 h0' h1'
  have hB := abs_sum_lipschitzBridgeColumn_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf hsep h0 h1 h0' h1'
  rw [activityDampedExpectation_sub_eq_two_column_lipschitz_ledger
    μm hβ mχ hχabs hsmall f s r h0 h1 h0' h1']
  refine le_trans (abs_add _ _) ?_
  have hsum := add_le_add hA hB
  calc _ ≤ _ := hsum
    _ = _ := by ring

/-- **REFINED CAPSTONE (Stone 54)** — LIPSCHITZ STABILITY OF THE DAMPED
    FUNCTIONAL IN THE DAMPING PARAMETER WITH THE PREFACTOR e^{6 D_s/113}:
    for θ, θ′ ∈ [0, 1],
      |F(θ) − F(θ′)| ≤ |θ − θ′|·2·Cf·e^{6 D_s/113}·e^{−n/2},
    under exactly the hypotheses of the Stone 53 capstone. From the refined
    two-term estimate and e^{4 D_s/113} ≤ e^{6 D_s/113} (D_s ≥ 0). -/
theorem abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay_refined
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
          * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) := by
  have hCf0 : 0 ≤ Cf := nonneg_of_abs_le_of_config hCf
  have h2 := abs_activityDampedExpectation_sub_activityDampedExpectation_le_two_terms_refined
    μm hβ mχ hχabs hsmall mf hCf hsep h0 h1 h0' h1'
  have hD : (0:ℝ) ≤ ((supportLinkFinset (N := N) s).card : ℝ) :=
    Nat.cast_nonneg _
  have hmono : Real.exp
      (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
      ≤ Real.exp
        (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  have hpos : (0:ℝ) ≤ |θ - θ'| * Cf * Real.exp (-(n : ℝ) / 2) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) hCf0) (Real.exp_pos _).le
  have h6 : Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
      = Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
    congr 1
    ring
  rw [h6]
  refine le_trans h2 ?_
  calc |θ - θ'| * Cf * Real.exp (-(n : ℝ) / 2)
          * (Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)))
      ≤ |θ - θ'| * Cf * Real.exp (-(n : ℝ) / 2)
          * (Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hmono _) hpos
    _ = |θ - θ'| * (2 * Cf)
          * Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
          * Real.exp (-(n : ℝ) / 2) := by ring

/-! ## 54-A.5 — comparison with the published Stone 53 constant -/

/-- The refined constant is at most the published one:
    2·Cf·e^{6 D_s/113}·e^{−n/2} ≤ 2·Cf·e^{8 D_s/113}·e^{−n/2} for 0 ≤ Cf
    (the two agree exactly when D_s = 0). -/
theorem refined_constant_le_published_constant
    {s : Set (Link N)} {Cf : ℝ} (hCf0 : 0 ≤ Cf) (n : ℕ) :
    (2 * Cf) * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
        * Real.exp (-(n : ℝ) / 2)
      ≤ (2 * Cf) * Real.exp (8 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
        * Real.exp (-(n : ℝ) / 2) := by
  have hD : (0:ℝ) ≤ ((supportLinkFinset (N := N) s).card : ℝ) := Nat.cast_nonneg _
  have hmono : Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
      ≤ Real.exp (8 * ((supportLinkFinset (N := N) s).card : ℝ) / 113) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left hmono (by linarith)

/-- **The Stone 53 capstone re-derived from the refined one** (same
    statement as `abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay`;
    a corollary, not a replacement — the published module is untouched). -/
theorem abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay_of_refined
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
  have h := abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay_refined
    μm hβ mχ hχabs hsmall mf hCf hsep h0 h1 h0' h1'
  have hc := refined_constant_le_published_constant (N := N) (s := s) hCf0 n
  calc _ ≤ _ := h
    _ = |θ - θ'| * ((2 * Cf)
          * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2)) := by ring
    _ ≤ |θ - θ'| * ((2 * Cf)
          * Real.exp (8 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hc (abs_nonneg _)
    _ = _ := by ring

/-! ## 54-A.6 — endpoints of the refined estimate -/

/-- **θ′ = 1 with `DependsOnlyOn f s`**: the refined estimate against the
    Gibbs expectation, |F(θ) − gibbs| ≤ (1 − θ)·2·Cf·e^{6 D_s/113}·e^{−n/2}
    (the Stone 52 statement with the smaller prefactor). -/
theorem abs_activityDampedExpectation_sub_gibbsExpectation_le_refined
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
          * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) := by
  have h := abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay_refined
    μm hβ mχ hχabs hsmall mf hCf hsep h0 h1 (zero_le_one : (0:ℝ) ≤ 1)
    (le_refl (1:ℝ))
  rw [activityDampedExpectation_one μm hβ mχ hχabs hf mf hCf r,
    abs_sub_comm θ 1, abs_of_nonneg (sub_nonneg.mpr h1)] at h
  exact h

/-- **θ′ = 0**: the refined distance to the activity-restricted functional
    of Stone 51, with the factor θ; no `DependsOnlyOn f s`. -/
theorem abs_activityDampedExpectation_sub_activityRestrictedExpectation_le_refined
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
          * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) := by
  have h := abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay_refined
    μm hβ mχ hχabs hsmall mf hCf hsep h0 h1 (le_refl (0:ℝ))
    (zero_le_one : (0:ℝ) ≤ 1)
  rw [activityDampedExpectation_zero, sub_zero, abs_of_nonneg h0] at h
  exact h

#print axioms exp_sub_exp_le_exp_mul_abs_sub
#print axioms abs_exp_sub_exp_le_exp_mul_abs_sub
#print axioms le_exp_self
#print axioms abs_exp_dampedActivityCoreExponent_sub_le_decay_refined
#print axioms abs_refinedConnectorColumnTerm_le
#print axioms sum_abs_refinedConnectorColumn_le
#print axioms abs_sum_refinedConnectorColumn_le
#print axioms abs_activityDampedExpectation_sub_activityDampedExpectation_le_two_terms_refined
#print axioms abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay_refined
#print axioms refined_constant_le_published_constant
#print axioms abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay_of_refined
#print axioms abs_activityDampedExpectation_sub_gibbsExpectation_le_refined
#print axioms abs_activityDampedExpectation_sub_activityRestrictedExpectation_le_refined

end LatticeGauge
