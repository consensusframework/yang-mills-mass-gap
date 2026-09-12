/-
LatticeGauge/ActivityDampingStability.lean — PEDRA 52,
Gate 52-E: CAPSTONE — STABILITY UNDER CONTINUOUS REMOTE ACTIVITY
DAMPING (architecture: Sol/GPT-5.6; execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): the 52-B ledger is
exact,
    gibbs − damped = Σ_{T touching} θ^t·W_T·(e^{E_T(1)} − e^{E_T(θ)})
                   + Σ_{T bridge}   (1 − θ^t)·W_T·e^{E_T(1)},
and 52-D bounds the absolute value of each column separately, with
the factor (1 − θ) in front:
    |column 1| ≤ (1−θ)·Cf·e^{−n/2}·e^{8 D_s/113}   (budget (1/2, 3)),
    |column 2| ≤ (1−θ)·Cf·e^{−n/2}·e^{4 D_s/113}   (budget (7/8, 1)).
This gate combines them: ledger + triangle inequality + the two
bounds give first the sharper estimate
    |gibbs − damped| ≤ (1−θ)·Cf·e^{−n/2}·(e^{8 D_s/113} + e^{4 D_s/113}),
and then, since D_s ≥ 0 gives e^{4 D_s/113} ≤ e^{8 D_s/113}, the
Stone 52 capstone
    |gibbs − damped| ≤ (1−θ)·2·Cf·e^{8 D_s/113}·e^{−n/2},
D_s = card (supportLinkFinset s). The redundant hypothesis 0 ≤ Cf
is DERIVED from |f| ≤ Cf at the configuration `trivialConfig N G`
(not assumed). Nothing is divided by (1 − θ): θ = 1 stays covered
(bound 0). Endpoints: θ = 0 recovers the Stone 51 capstone
`abs_gibbsExpectation_sub_activityRestrictedExpectation_le_local_exp_decay`
with the SAME constant 2·Cf·e^{8 D_s/113}·e^{−n/2}; θ = 1 and r = ∅
are the exact identities of 52-B (difference 0, weakest hypotheses
of those interfaces), and the bound at r = ∅ is also stated.

WHAT THIS IS: an estimate of the deviation of the damped functional
from the Gibbs expectation, in the walk-barrier separation n of the
support s from the damped region r. WHAT THIS IS NOT: a monotonicity
statement about the actual deviation, and not an estimate between
two arbitrary damping parameters θ, θ'.

HARD HOLD (not here): any Disjoint s r, size restriction on r or
volume factor; Gibbs-measure, boundary-condition, modified-action or
switch-off interpretations; thermodynamic limit, continuum, spatial
mixing, mass gap. No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.ActivityDampingColumnBounds

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## 52-E.1 — 0 ≤ Cf is derived, not assumed -/

omit [NeZero N] [Fintype (Site N)] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- A bound `∀ U, |f U| ≤ Cf` forces `0 ≤ Cf`, witnessed by the
    trivial configuration (Config N G is inhabited). -/
theorem nonneg_of_abs_le_of_config {f : Config N G → ℝ} {Cf : ℝ}
    (hCf : ∀ U, |f U| ≤ Cf) : 0 ≤ Cf :=
  le_trans (abs_nonneg _) (hCf (trivialConfig N G))

/-! ## 52-E.2 — the sharper two-term estimate -/

/-- **TWO-TERM STABILITY ESTIMATE**: ledger (52-B) + triangle
    inequality + the two column bounds (52-D), constants kept
    separate:
      |gibbs − damped| ≤ (1−θ)·Cf·e^{−n/2}·(e^{8 D_s/113} + e^{4 D_s/113}).
    Written with the 52-D constants `4·D_s·(2/113)` and `2·D_s·(2/113)`. -/
theorem abs_gibbsExpectation_sub_activityDampedExpectation_le_two_terms
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
      ≤ (1 - θ) * Cf * Real.exp (-(n : ℝ) / 2)
          * (Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))) := by
  have hCf0 : 0 ≤ Cf := nonneg_of_abs_le_of_config hCf
  have hA := abs_sum_dampingConnectorColumn_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf hsep h0 h1
  have hB := abs_sum_dampingBridgeColumn_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf hsep h0 h1
  rw [ledger_columns_are_the_estimated_sums μm hβ mχ hχabs hsmall hf mf hCf r h0 h1]
  refine le_trans (abs_add _ _) ?_
  have hsum := add_le_add hA hB
  calc _ ≤ _ := hsum
    _ = _ := by ring

/-! ## 52-E.3 — CAPSTONE -/

/-- **CAPSTONE 52 — LOCAL EXPONENTIAL STABILITY UNDER CONTINUOUS
    REMOTE ACTIVITY DAMPING**: for a local observable f (support s,
    bound Cf) and damping parameter 0 ≤ θ ≤ 1 on a region r at
    walk-barrier separation n from s,
      |gibbs(f) − damped(f, s, r, θ)|
        ≤ (1 − θ)·2·Cf·e^{8 D_s/113}·e^{−n/2}.
    From the two-term estimate and e^{4 D_s/113} ≤ e^{8 D_s/113}
    (D_s ≥ 0). No division by (1 − θ); at θ = 1 the bound is 0. -/
theorem abs_gibbsExpectation_sub_activityDampedExpectation_le_local_exp_decay
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
  have hCf0 : 0 ≤ Cf := nonneg_of_abs_le_of_config hCf
  have h2 := abs_gibbsExpectation_sub_activityDampedExpectation_le_two_terms
    μm hβ mχ hχabs hsmall hf mf hCf hsep h0 h1
  have hD : (0:ℝ) ≤ ((supportLinkFinset (N := N) s).card : ℝ) :=
    Nat.cast_nonneg _
  have hmono : Real.exp
      (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
      ≤ Real.exp
        (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  have hpos : (0:ℝ) ≤ (1 - θ) * Cf * Real.exp (-(n : ℝ) / 2) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr h1) hCf0) (Real.exp_pos _).le
  have h8 : Real.exp (8 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
      = Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
    congr 1
    ring
  rw [h8]
  refine le_trans h2 ?_
  calc (1 - θ) * Cf * Real.exp (-(n : ℝ) / 2)
          * (Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)))
      ≤ (1 - θ) * Cf * Real.exp (-(n : ℝ) / 2)
          * (Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hmono _) hpos
    _ = (1 - θ) * (2 * Cf)
          * Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
          * Real.exp (-(n : ℝ) / 2) := by ring

/-! ## 52-E.4 — endpoints -/

/-- **θ = 0 recovers Stone 51**: the capstone at θ = 0 IS the Stone 51
    estimate for the activity-restricted functional, with the same
    constant 2·Cf·e^{8 D_s/113}·e^{−n/2} (compare
    `abs_gibbsExpectation_sub_activityRestrictedExpectation_le_local_exp_decay`,
    whose hypotheses include the here-derived 0 ≤ Cf). -/
theorem abs_gibbsExpectation_sub_activityRestrictedExpectation_le_of_damping_zero
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n) :
    |gibbsExpectation (N := N) μm β χ f
        - activityRestrictedExpectation μm β χ f s r|
      ≤ 2 * Cf
        * Real.exp (8 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
        * Real.exp (-(n : ℝ) / 2) := by
  have h := abs_gibbsExpectation_sub_activityDampedExpectation_le_local_exp_decay
    μm hβ mχ hχabs hsmall hf mf hCf hsep (le_refl (0:ℝ)) zero_le_one
  rw [activityDampedExpectation_zero] at h
  calc _ ≤ _ := h
    _ = _ := by ring

/-- **θ = 1**: the difference is exactly 0 (52-B identity; hypotheses
    of the published representation only, no smallness, no
    separation). -/
theorem gibbsExpectation_sub_activityDampedExpectation_one_eq_zero
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (r : Set (Link N)) :
    gibbsExpectation (N := N) μm β χ f
        - activityDampedExpectation μm β χ f s r 1 = 0 :=
  gibbsExpectation_sub_activityDampedExpectation_one μm hβ mχ hχabs hf mf hCf r

/-- **θ = 1, through the capstone**: the bound itself is 0 at θ = 1
    (the capstone is applicable there; nothing was divided by 1 − θ). -/
theorem capstone_bound_one
    {s : Set (Link N)} (Cf : ℝ) (n : ℕ) :
    (1 - (1:ℝ)) * (2 * Cf)
        * Real.exp (8 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
        * Real.exp (-(n : ℝ) / 2) = 0 := by
  rw [sub_self, zero_mul, zero_mul, zero_mul]

/-- **r = ∅**: the difference is exactly 0 for every θ (52-B identity;
    hypotheses of the published representation only). -/
theorem gibbsExpectation_sub_activityDampedExpectation_empty_region_eq_zero
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf) (θ : ℝ) :
    gibbsExpectation (N := N) μm β χ f
        - activityDampedExpectation μm β χ f s (∅ : Set (Link N)) θ = 0 :=
  gibbsExpectation_sub_activityDampedExpectation_empty_region μm hβ mχ hχabs hf mf hCf θ

#print axioms nonneg_of_abs_le_of_config
#print axioms abs_gibbsExpectation_sub_activityDampedExpectation_le_two_terms
#print axioms abs_gibbsExpectation_sub_activityDampedExpectation_le_local_exp_decay
#print axioms abs_gibbsExpectation_sub_activityRestrictedExpectation_le_of_damping_zero
#print axioms gibbsExpectation_sub_activityDampedExpectation_one_eq_zero
#print axioms capstone_bound_one
#print axioms gibbsExpectation_sub_activityDampedExpectation_empty_region_eq_zero

end LatticeGauge
