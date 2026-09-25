/-
LatticeGauge/ActivityProfileDampingLocality.lean — PEDRA 56,
Gate 56-L: LOCALIZATION OF THE PROFILE STABILITY ESTIMATE ON THE REGION
WHERE THE EFFECTIVE FACTORS CHANGE, WITH A COMMON DAMPING BACKGROUND
(architecture: GPT Astra, FITA 56-A; feasibility and construction: Fable).

CONCEPTUAL RECORD (architect's precision, kept): Stone 55 damps the
activity of every polymer touching ONE region r by a profile a, and
measures the change of the normalized polymer functional F(a) when the
profile moves on that same region r, at walk separation n from the
observable support s. Stone 56 separates two regions:
  * R — the region of the damping, arbitrary, present in EVERY weight,
    activity and exponent (F_R(a) = profileExpectation μm β χ f s R a,
    b(η) = touchFactor R a η, b′(η) = touchFactor R a′ η);
  * r — the region that LOCALIZES the difference of the effective factors:
        hsame : ∀ η, ¬ typedTouchesSupport η r → b(η) = b′(η)
        hδ    : ∀ η, typedTouchesSupport η r → |b(η) − b′(η)| ≤ δ
        hsep  : WalkBarrierSeparated s r n.
A common damping background (b = b′, not necessarily 1) may exist outside
r — near s included. The background is PRESERVED in the products, the
coefficients and the functional (it is never removed); the cancellation
localizes the DIFFERENCE and the bound is uniform in that background:
    |F_R(a) − F_R(a′)| ≤ δ·Cf·e^{−n/2}·(e^{6 D_s/113} + e^{4 D_s/113})
                       ≤ δ·2·Cf·e^{6 D_s/113}·e^{−n/2},
the Stone 54/55 constant, rate and regime. NOT required: any separation
of s from R, r ⊆ R, a unit background outside r, δ ≤ 1, a sign condition
on activities or exponents, `DependsOnlyOn f s`; nothing is divided by δ
or by a factor of a profile; 0 ≤ Cf is derived from |f| ≤ Cf; no factor of
card R or card r enters the constant. Replacing R by r in the definition of
the functional would remove the background and change the object: this
gate keeps R everywhere and proves the localized cancellation directly.

The route is the Stone 55 route with the localization inserted at the
level of the effective factors:
  * families and tuples avoiding r have EQUAL weights (not weight 1); the
    telescoping lemma of 55-A applied to the effective factors gives
    |A_T − A′_T| ≤ touchCount r T·δ, |A_δ − A′_δ| ≤ tupleTouchCount r δ·δ ≤ k·δ
    (positions counted, repetitions included);
  * the localized difference coefficient D_k (weight A′_δ − A_δ on the
    tuples hitting the P-barrier and the r-barrier, Ursell, ∏ z, /k!) and
    its DIRECT identity with [c_k(restr z_a P) − c_k(z_a)] − [c_k(restr z_{a′} P)
    − c_k(z_{a′})], proved from the expansion, orientation A′ − A, with no
    hypothesis on the profiles beyond hsame; the domination
    |D_k| ≤ δ·k·A_k(|z|, P, regionAllowed r);
  * the series identity E^R_T(a) − E^R_T(a′) = Σ′ D_k (four cluster series
    summable by the KP transport with region R; no separation of s from R)
    and the eroded bound δ·e^{−((n − m_T : ℕ))/2}·b_T·(2/113) with the
    natural truncated subtraction, from the separation of s and r only;
  * the bilateral exponential control of Stone 54 at κ = 2, the exponents
    controlled with R arbitrary (55-A);
  * the ledger: the second profile's weight on the connector column, the
    weight difference with the PLUS sign and the first profile's exponent
    on the bridge column, supported on activityBridgeCores s r; on the
    r-allowed cores the correction vanishes by EQUALITY of the weights;
  * the connector column at budget (1/2, 2) and the bridge column at κ = 1,
    tilt 7/8, budget (7/8, 1), through a two-region interface of the profile
    bridge first moment (exponent with R, geometry with r; the published
    55-B interface, which ties both to one region, is not edited);
  * the two-term estimate and the capstone.
Interfaces: equality of all effective factors gives F_R(a) = F_R(a′)
exactly (an algebraic identity, no analytic hypothesis, real profiles);
r = ∅ under hsame is that case; r = R translates the Stone 55 hypotheses
into hsame and hδ, and the Stone 55 statement is recovered as an
APPLICATION of the localized capstone (direction 56 ⇒ 55; the published
Stone 55 capstone is not used in any proof here and remains untouched).

HARD HOLD (not here): any Disjoint s R, size restriction on R or r or a
volume factor; a minimal region r or a Euclidean distance; per-link
profiles; Gibbs identifications beyond the published ones (with a
non-unit common background the unit-profile identification does not
follow from the localization); monotonicity or differentiability in the
profile; Gibbs-measure, boundary-condition or modified-action
interpretations; thermodynamic limit, continuum, mass gap. No optimality,
sharpness or bibliographic priority is claimed. No project-local
scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.ActivityProfileDampingStability

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## 56-L.1 — localized weight identities and bounds (effective factors) -/

/-- **Cancellation outside r (families)**: a family avoiding r has EQUAL
    weights under the two profiles — not necessarily weight 1. Only `hsame`. -/
theorem profileWeight_eq_of_touchCount_zero_of_same (R r : Set (Link N))
    {a a' : Polymer N → ℝ}
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η)
    {Γ : Finset (Polymer N)} (h : touchCount r Γ = 0) :
    profileWeight R a Γ = profileWeight R a' Γ := by
  have hall := (touchCount_eq_zero_iff r Γ).mp h
  unfold profileWeight
  exact Finset.prod_congr rfl (fun η hη => hsame η (regionAllowed_iff.mp (hall η hη)))

/-- **Cancellation outside r (tuples)**: positions counted, repetitions included. -/
theorem tupleProfileWeight_eq_of_tupleTouchCount_zero_of_same (R r : Set (Link N))
    {a a' : Polymer N → ℝ}
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η)
    {k : ℕ} {δt : Fin k → Polymer N} (h : tupleTouchCount r δt = 0) :
    tupleProfileWeight R a δt = tupleProfileWeight R a' δt := by
  have hall := (tupleTouchCount_eq_zero_iff r δt).mp h
  unfold tupleProfileWeight
  exact Finset.prod_congr rfl (fun i _ => hsame (δt i) (regionAllowed_iff.mp (hall i)))

/-- **LOCALIZED FAMILY WEIGHT DIFFERENCE**: |A_Γ − A′_Γ| ≤ touchCount r Γ · δ.
    The telescoping lemma of 55-A on the effective factors (in [0,1]), the
    sum split by "touches r": the terms outside r vanish by `hsame`, the
    terms on r are ≤ δ by `hδ`. Uses the interval of the profiles and `hδ`. -/
theorem abs_profileWeight_sub_le_localized (R r : Set (Link N)) {a a' : Polymer N → ℝ} {δ : ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |touchFactor R a η - touchFactor R a' η| ≤ δ)
    (Γ : Finset (Polymer N)) :
    |profileWeight R a Γ - profileWeight R a' Γ| ≤ (touchCount r Γ : ℝ) * δ := by
  unfold profileWeight
  refine le_trans (abs_prod_sub_prod_le_sum_abs_sub Γ _ _
    (fun η _ => touchFactor_nonneg R h0 η) (fun η _ => touchFactor_le_one R h1 η)
    (fun η _ => touchFactor_nonneg R h0' η) (fun η _ => touchFactor_le_one R h1' η)) ?_
  unfold touchCount
  rw [← Finset.sum_filter_add_sum_filter_not Γ (fun η => typedTouchesSupport (N := N) η r)]
  have h2 : (∑ η ∈ Γ.filter (fun η => ¬ typedTouchesSupport (N := N) η r),
      |touchFactor R a η - touchFactor R a' η|) = 0 := by
    refine Finset.sum_eq_zero (fun η hη => ?_)
    rw [hsame η (Finset.mem_filter.mp hη).2, sub_self, abs_zero]
  rw [h2, add_zero]
  calc (∑ η ∈ Γ.filter (fun η => typedTouchesSupport (N := N) η r),
        |touchFactor R a η - touchFactor R a' η|)
      ≤ ∑ η ∈ Γ.filter (fun η => typedTouchesSupport (N := N) η r), δ :=
        Finset.sum_le_sum (fun η hη => hδ η (Finset.mem_filter.mp hη).2)
    _ = ((Γ.filter (fun η => typedTouchesSupport (N := N) η r)).card : ℝ) * δ := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **LOCALIZED TUPLE WEIGHT DIFFERENCE** (positions counted, repetitions included):
    |A_δ − A′_δ| ≤ tupleTouchCount r δ · δ. -/
theorem abs_tupleProfileWeight_sub_le_localized (R r : Set (Link N)) {a a' : Polymer N → ℝ}
    {δ : ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |touchFactor R a η - touchFactor R a' η| ≤ δ)
    {k : ℕ} (δt : Fin k → Polymer N) :
    |tupleProfileWeight R a δt - tupleProfileWeight R a' δt|
      ≤ (tupleTouchCount r δt : ℝ) * δ := by
  unfold tupleProfileWeight
  refine le_trans (abs_prod_sub_prod_le_sum_abs_sub Finset.univ _ _
    (fun i _ => touchFactor_nonneg R h0 (δt i)) (fun i _ => touchFactor_le_one R h1 (δt i))
    (fun i _ => touchFactor_nonneg R h0' (δt i))
    (fun i _ => touchFactor_le_one R h1' (δt i))) ?_
  unfold tupleTouchCount
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin k => typedTouchesSupport (N := N) (δt i) r)]
  have h2 : (∑ i ∈ Finset.univ.filter
      (fun i : Fin k => ¬ typedTouchesSupport (N := N) (δt i) r),
      |touchFactor R a (δt i) - touchFactor R a' (δt i)|) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [hsame (δt i) (Finset.mem_filter.mp hi).2, sub_self, abs_zero]
  rw [h2, add_zero]
  calc (∑ i ∈ Finset.univ.filter (fun i : Fin k => typedTouchesSupport (N := N) (δt i) r),
        |touchFactor R a (δt i) - touchFactor R a' (δt i)|)
      ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin k => typedTouchesSupport (N := N) (δt i) r), δ :=
        Finset.sum_le_sum (fun i hi => hδ (δt i) (Finset.mem_filter.mp hi).2)
    _ = ((Finset.univ.filter
          (fun i : Fin k => typedTouchesSupport (N := N) (δt i) r)).card : ℝ) * δ := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- tupleTouchCount ≤ k transports the localized tuple bound to k·δ (0 ≤ δ). -/
theorem abs_tupleProfileWeight_sub_le_k_localized (R r : Set (Link N)) {a a' : Polymer N → ℝ}
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |touchFactor R a η - touchFactor R a' η| ≤ δ)
    {k : ℕ} (δt : Fin k → Polymer N) :
    |tupleProfileWeight R a δt - tupleProfileWeight R a' δt| ≤ (k : ℝ) * δ :=
  le_trans (abs_tupleProfileWeight_sub_le_localized R r h0 h1 h0' h1' hsame hδ δt)
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (tupleTouchCount_le r δt)) hδ0)

/-- The localized family weight difference against card T: |A_T − A′_T| ≤ card T·δ. -/
theorem abs_profileWeight_sub_le_card_localized (R r : Set (Link N)) {a a' : Polymer N → ℝ}
    {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |touchFactor R a η - touchFactor R a' η| ≤ δ)
    (T : Finset (Polymer N)) :
    |profileWeight R a T - profileWeight R a' T| ≤ (T.card : ℝ) * δ :=
  le_trans (abs_profileWeight_sub_le_localized R r h0 h1 h0' h1' hsame hδ T)
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (touchCount_le_card r T)) hδ0)

/-! ## 56-L.2 — the localized difference coefficient (orientation A′ − A) -/

/-- **The localized difference coefficient** D_k: the tuple sum over tuples
    hitting BOTH barriers (P-forbidden somewhere and r-touching somewhere),
    each weighted by A′_δ − A_δ (weights computed with R; positions counted,
    repetitions included), times the Ursell factor and the product of the
    ORIGINAL activities; divided by k! outside the sum. -/
noncomputable def kpLocalizedDiffCoeff (k : ℕ) (z : Polymer N → ℝ) (P : Polymer N → Prop)
    (r R : Set (Link N)) (a a' : Polymer N → ℝ) : ℝ :=
  (∑ δ : Fin k → Polymer N,
      if TupleHitsBothForbidden P (regionAllowed (N := N) r) δ then
        (tupleProfileWeight R a' δ - tupleProfileWeight R a δ)
          * (((ursellCoeff (N := N) (fun i => (δ i).val) : ℤ) : ℝ) * ∏ i : Fin k, z (δ i))
      else 0)
    / ((Nat.factorial k : ℕ) : ℝ)

/-- **THE LOCALIZED DIFFERENCE IDENTITY (coefficients)**: for every activity
    z, predicate P and order k,
      [c_k(restr(z_a, P)) − c_k(z_a)] − [c_k(restr(z_{a′}, P)) − c_k(z_{a′})] = D_k,
    z_a = profileDampedActivity z R a. Proved DIRECTLY from the expansion: a
    P-allowed tuple cancels between restricted and unrestricted; a tuple
    avoiding r has A_δ = A′_δ by `hsame` (the regional filter enters only
    through `TupleAllowed (regionAllowed r) δ → tupleTouchCount r δ = 0`, no
    converse); the remaining tuples carry A′_δ − A_δ, the orientation coming
    from "restricted minus unrestricted". No hypothesis on the profiles
    beyond `hsame` (no interval); the common background stays inside A_δ, A′_δ. -/
theorem kpLocalizedDiff_inclusion_exclusion (k : ℕ) (z : Polymer N → ℝ) (P : Polymer N → Prop)
    (r R : Set (Link N)) {a a' : Polymer N → ℝ}
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η) :
    (kpSignedUnrootedCoeff (N := N) k (restrictedActivity (profileDampedActivity z R a) P)
        - kpSignedUnrootedCoeff (N := N) k (profileDampedActivity z R a))
      - (kpSignedUnrootedCoeff (N := N) k (restrictedActivity (profileDampedActivity z R a') P)
        - kpSignedUnrootedCoeff (N := N) k (profileDampedActivity z R a'))
      = kpLocalizedDiffCoeff k z P r R a a' := by
  unfold kpSignedUnrootedCoeff kpLocalizedDiffCoeff
  rw [div_sub_div_same, div_sub_div_same, div_sub_div_same]
  congr 1
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  rw [prod_restrictedActivity_eq, prod_restrictedActivity_eq,
    prod_profileDampedActivity_tuple z R a, prod_profileDampedActivity_tuple z R a']
  by_cases hP : TupleAllowed P δ
  · rw [if_pos hP, if_pos hP, if_neg (fun h => h.1 hP)]
    ring
  · by_cases hQ : TupleAllowed (regionAllowed (N := N) r) δ
    · have hc : tupleTouchCount r δ = 0 :=
        (tupleAllowed_regionAllowed_iff_tupleTouchCount_eq_zero r δ).mp hQ
      rw [if_neg hP, if_neg hP, if_neg (fun h => h.2 hQ),
        tupleProfileWeight_eq_of_tupleTouchCount_zero_of_same R r hsame hc]
      ring
    · rw [if_neg hP, if_neg hP, if_pos ⟨hP, hQ⟩]
      ring

/-- **Order k = 0**: the empty tuple is allowed everywhere, so it hits no
    barrier — the coefficient vanishes (the weight is never evaluated). -/
theorem kpLocalizedDiffCoeff_order_zero (z : Polymer N → ℝ) (P : Polymer N → Prop)
    (r R : Set (Link N)) (a a' : Polymer N → ℝ) :
    kpLocalizedDiffCoeff (N := N) 0 z P r R a a' = 0 := by
  unfold kpLocalizedDiffCoeff
  rw [Finset.univ_unique, Finset.sum_singleton]
  have hP : TupleAllowed P (default : Fin 0 → Polymer N) := fun i => Fin.elim0 i
  rw [if_neg (fun h => h.1 hP), zero_div]

/-- **LOCALIZED DOMINATION**: |D_k| ≤ δ·k·A_k(|z|, P, regionAllowed r), the
    weight difference paid by the localized tuple bound (≤ k·δ), the rest by
    the positive connector coefficient of the ORIGINAL |z|. -/
theorem abs_kpLocalizedDiffCoeff_le (k : ℕ) (z : Polymer N → ℝ) (P : Polymer N → Prop)
    (r R : Set (Link N)) {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |touchFactor R a η - touchFactor R a' η| ≤ δ) :
    |kpLocalizedDiffCoeff (N := N) k z P r R a a'|
      ≤ δ * (k : ℝ)
          * kpAbsConnectorUnrootedCoeff k (fun η => |z η|) P (regionAllowed (N := N) r) := by
  unfold kpLocalizedDiffCoeff kpAbsConnectorUnrootedCoeff
  rw [← mul_div_assoc, abs_div, Nat.abs_cast]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun δt _ => ?_))
  by_cases h : TupleHitsBothForbidden P (regionAllowed (N := N) r) δt
  · rw [if_pos h, if_pos h, abs_mul, abs_mul,
      Finset.abs_prod, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    have hw : |tupleProfileWeight R a' δt - tupleProfileWeight R a δt| ≤ δ * (k : ℝ) := by
      rw [abs_sub_comm]
      calc |tupleProfileWeight R a δt - tupleProfileWeight R a' δt|
          ≤ (k : ℝ) * δ :=
            abs_tupleProfileWeight_sub_le_k_localized R r hδ0 h0 h1 h0' h1' hsame hδ δt
        _ = δ * (k : ℝ) := mul_comm _ _
    have hrest : 0 ≤ (((ursellCoeff (N := N) (fun i => (δt i).val)).natAbs : ℕ) : ℝ)
        * ∏ i : Fin k, |z (δt i)| :=
      mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => abs_nonneg _))
    calc |tupleProfileWeight R a' δt - tupleProfileWeight R a δt|
          * ((((ursellCoeff (N := N) (fun i => (δt i).val)).natAbs : ℕ) : ℝ)
              * ∏ i : Fin k, |z (δt i)|)
        ≤ (δ * (k : ℝ))
          * ((((ursellCoeff (N := N) (fun i => (δt i).val)).natAbs : ℕ) : ℝ)
              * ∏ i : Fin k, |z (δt i)|) :=
          mul_le_mul_of_nonneg_right hw hrest
      _ = δ * (k : ℝ)
          * ((((ursellCoeff (N := N) (fun i => (δt i).val)).natAbs : ℕ) : ℝ)
              * ∏ i : Fin k, |z (δt i)|) := by ring
  · rw [if_neg h, if_neg h, abs_zero, mul_zero]

/-! ## 56-L.3 — translation of the Stone 55 hypotheses (r = R) -/

/-- **r = R**: the Stone 55 hypothesis |a − a′| ≤ δ on the polymers touching
    R gives `hsame` (both effective factors are 1 outside R) and the effective
    majorant on R. A translation of hypotheses, not a bound. -/
theorem localized_hypotheses_of_profile_hypotheses (R : Set (Link N)) {a a' : Polymer N → ℝ}
    {δ : ℝ} (hδ : ∀ η, typedTouchesSupport (N := N) η R → |a η - a' η| ≤ δ) :
    (∀ η, ¬ typedTouchesSupport (N := N) η R → touchFactor R a η = touchFactor R a' η)
    ∧ (∀ η, typedTouchesSupport (N := N) η R → |touchFactor R a η - touchFactor R a' η| ≤ δ) := by
  constructor
  · intro η h
    unfold touchFactor
    rw [if_neg h, if_neg h]
  · intro η h
    unfold touchFactor
    rw [if_pos h, if_pos h]
    exact hδ η h

/-! ## 56-L.4 — the localized series, the exponent difference and the erosion -/

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **The localized connector difference** Σ′ D_k, with the polymer weight as
    activity and the core-relative barrier P = remoteAllowed T s. -/
noncomputable def localizedConnectorDiff (β : ℝ) (χ : G → ℝ) (T : Finset (Polymer N))
    (s r R : Set (Link N)) (a a' : Polymer N → ℝ) : ℝ :=
  ∑' k, kpLocalizedDiffCoeff (N := N) k
    (fun η => polymerWeight (N := N) μm β χ η.val) (remoteAllowed (N := N) T s) r R a a'

/-- **SERIES IDENTITY**: E^R_T(a) − E^R_T(a′) = Σ′ D_k. The four cluster
    series are summable by the KP transport with region R (the profiles in
    [0,1]; no separation of s from R); the termwise identity is 56-L.2. Uses
    the KP regime and the intervals; not `mf`, `hCf`, `hsep` or `hδ`. -/
theorem profileCoreExponent_sub_eq_localizedConnectorDiff
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r R : Set (Link N))
    {a a' : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1)
    (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η) :
    profileCoreExponent μm β χ T s R a - profileCoreExponent μm β χ T s R a'
      = localizedConnectorDiff μm β χ T s r R a a' := by
  have ha : ∀ γ : Polymer N, 0 ≤ ((γ.val.card : ℕ) : ℝ) := fun γ => Nat.cast_nonneg _
  have hKP := abstractKP_of_beta_le_one_div_40000 (N := N) μm hβ mχ hχabs hsmall
  have hKPa := abstractKP_profileDampedActivity R h0 h1 hKP
  have hKPa' := abstractKP_profileDampedActivity R h0' h1' hKP
  have hSPa : Summable (fun n => kpSignedUnrootedCoeff (N := N) n
      (restrictedActivity
        (profileDampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) R a)
        (remoteAllowed (N := N) T s))) :=
    summable_kpSignedUnrootedCoeff ha
      (abstractKP_restrictedActivity (remoteAllowed (N := N) T s) hKPa)
  have hS0a : Summable (fun n => kpSignedUnrootedCoeff (N := N) n
      (profileDampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) R a)) :=
    summable_kpSignedUnrootedCoeff ha hKPa
  have hSPa' : Summable (fun n => kpSignedUnrootedCoeff (N := N) n
      (restrictedActivity
        (profileDampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) R a')
        (remoteAllowed (N := N) T s))) :=
    summable_kpSignedUnrootedCoeff ha
      (abstractKP_restrictedActivity (remoteAllowed (N := N) T s) hKPa')
  have hS0a' : Summable (fun n => kpSignedUnrootedCoeff (N := N) n
      (profileDampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) R a')) :=
    summable_kpSignedUnrootedCoeff ha hKPa'
  unfold profileCoreExponent localizedConnectorDiff
  rw [← tsum_sub hSPa hS0a, ← tsum_sub hSPa' hS0a', ← tsum_sub (hSPa.sub hS0a) (hSPa'.sub hS0a')]
  exact tsum_congr (fun k =>
    kpLocalizedDiff_inclusion_exclusion k _ (remoteAllowed (N := N) T s) r R hsame)

/-- **ERODED LOCALIZED BOUND**: |Σ′ D_k| ≤ δ·e^{−((n − m_T : ℕ))/2}·b_T·(2/113),
    natural truncated subtraction, from the separation of s and r only (the
    barrier regions of T at s and of ∅ at r keep separation n − m_T), the
    localized domination and the 52-A0 first moment. No 8/(3e). -/
theorem abs_localizedConnectorDiff_le_eroded
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {T : Finset (Polymer N)} {s r : Set (Link N)} (R : Set (Link N)) {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |touchFactor R a η - touchFactor R a' η| ≤ δ) :
    |localizedConnectorDiff μm β χ T s r R a a'|
      ≤ δ * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2)
        * (((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
  have hero := walkBarrierSeparated_barrierRegions_sub_familyMass
    hT (empty_mem_typedTouchingFamilies r) hsep
  have hzero : familyTotalCard (∅ : Finset (Polymer N)) = 0 := by
    unfold familyTotalCard
    exact Finset.sum_empty
  rw [hzero, Nat.add_zero] at hero
  have hmaj := summable_nat_mul_kpAbsConnector_polymerWeight μm hβ mχ hχabs hsmall hero
  have hmom := tsum_nat_mul_kpAbsConnector_polymerWeight_le_local_P μm hβ mχ hχabs hsmall hero
  rw [← regionAllowed_eq_remoteAllowed_empty] at hmaj hmom
  have hdom : ∀ k : ℕ,
      |kpLocalizedDiffCoeff (N := N) k (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s) r R a a'|
      ≤ δ * ((k : ℝ)
          * kpAbsConnectorUnrootedCoeff k
              (fun η => |polymerWeight (N := N) μm β χ η.val|)
              (remoteAllowed (N := N) T s) (regionAllowed (N := N) r)) := by
    intro k
    have := abs_kpLocalizedDiffCoeff_le k (fun η => polymerWeight (N := N) μm β χ η.val)
      (remoteAllowed (N := N) T s) r R hδ0 h0 h1 h0' h1' hsame hδ
    rw [mul_assoc] at this
    exact this
  have hsumabs : Summable (fun k : ℕ =>
      |kpLocalizedDiffCoeff (N := N) k (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s) r R a a'|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hdom (Summable.mul_left δ hmaj)
  unfold localizedConnectorDiff
  have h1' : ‖∑' k : ℕ, kpLocalizedDiffCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val) (remoteAllowed (N := N) T s) r R a a'‖
      ≤ ∑' k : ℕ, ‖kpLocalizedDiffCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val) (remoteAllowed (N := N) T s) r R a a'‖ := by
    refine norm_tsum_le_tsum_norm ?_
    simpa [Real.norm_eq_abs] using hsumabs
  simp only [Real.norm_eq_abs] at h1'
  have h2 := tsum_le_tsum hdom hsumabs (Summable.mul_left δ hmaj)
  rw [tsum_mul_left] at h2
  have h3 : δ * (∑' k : ℕ, (k : ℝ)
        * kpAbsConnectorUnrootedCoeff k
            (fun η => |polymerWeight (N := N) μm β χ η.val|)
            (remoteAllowed (N := N) T s) (regionAllowed (N := N) r))
      ≤ δ * (Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2)
          * (((barrierLinkFinset T s).card : ℝ) * (2 / 113))) :=
    mul_le_mul_of_nonneg_left hmom hδ0
  calc _ ≤ _ := h1'
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ = δ * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2)
          * (((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by ring

/-! ## 56-L.5 — the bilateral exponential control (κ = 2, exponents with R) -/

/-- **EXPONENTIAL CONTROL (two profiles, localized, κ = 2)**:
      |e^{E^R_T(a)} − e^{E^R_T(a′)}| ≤ δ·e^{−n/2}·e^{m_T/2 + 2·b_T·(2/113)}.
    Both exponents are ≤ q_T = b_T·(2/113) with R arbitrary (55-A); the scalar
    bound of Stone 54; the eroded localized bound; q_T ≤ e^{q_T}; the
    repurchased erosion. No δ ≤ 1, no sign condition. -/
theorem abs_exp_profileCoreExponent_sub_le_decay_localized
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {T : Finset (Polymer N)} {s r : Set (Link N)} (R : Set (Link N)) {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |touchFactor R a η - touchFactor R a' η| ≤ δ) :
    |Real.exp (profileCoreExponent μm β χ T s R a)
        - Real.exp (profileCoreExponent μm β χ T s R a')|
      ≤ δ * Real.exp (-(n : ℝ) / 2)
        * Real.exp ((familyTotalCard T : ℝ) / 2
            + 2 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
  set q : ℝ := ((barrierLinkFinset T s).card : ℝ) * (2 / 113) with hq
  have hx : profileCoreExponent μm β χ T s R a ≤ q :=
    le_trans (le_abs_self _)
      (abs_profileCoreExponent_le_barrier μm hβ mχ hχabs hsmall T s R h0 h1)
  have hy : profileCoreExponent μm β χ T s R a' ≤ q :=
    le_trans (le_abs_self _)
      (abs_profileCoreExponent_le_barrier μm hβ mχ hχabs hsmall T s R h0' h1')
  have hΔ : |profileCoreExponent μm β χ T s R a - profileCoreExponent μm β χ T s R a'|
      ≤ δ * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) * q := by
    rw [profileCoreExponent_sub_eq_localizedConnectorDiff
      μm hβ mχ hχabs hsmall T s r R h0 h1 h0' h1' hsame, hq]
    exact abs_localizedConnectorDiff_le_eroded
      μm hβ mχ hχabs hsmall R hT hsep hδ0 h0 h1 h0' h1' hsame hδ
  have hqexp : q ≤ Real.exp q := le_exp_self q
  have herode := exp_neg_nat_sub_half_le n (familyTotalCard T)
  have he0 : (0:ℝ) ≤ Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) :=
    (Real.exp_pos _).le
  calc |Real.exp (profileCoreExponent μm β χ T s R a)
        - Real.exp (profileCoreExponent μm β χ T s R a')|
      ≤ Real.exp q * |profileCoreExponent μm β χ T s R a
          - profileCoreExponent μm β χ T s R a'| :=
        abs_exp_sub_exp_le_exp_mul_abs_sub hx hy
    _ ≤ Real.exp q
          * (δ * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) * q) :=
        mul_le_mul_of_nonneg_left hΔ (Real.exp_pos _).le
    _ ≤ Real.exp q
          * (δ * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2)
              * Real.exp q) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hqexp (mul_nonneg hδ0 he0)
    _ ≤ Real.exp q
          * (δ * (Real.exp (-(n : ℝ) / 2)
              * Real.exp ((familyTotalCard T : ℝ) / 2))
              * Real.exp q) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left herode hδ0
    _ = δ * Real.exp (-(n : ℝ) / 2)
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

/-! ## 56-L.6 — the localized ledger -/

/-- **THE LOCALIZED TWO-PROFILE LEDGER**: weights and exponents with R, the
    touching cores split by r:
      F_R(a) − F_R(a′)
        = Σ_{T touching} A′_T · W_T · (e^{E^R_T(a)} − e^{E^R_T(a′)})
        + Σ_{T ∈ activityBridgeCores s r} (A_T − A′_T) · W_T · e^{E^R_T(a)}.
    The second profile's weight on the connector column; the weight
    difference with the PLUS sign and the first profile's exponent on the
    bridge column; on the r-allowed cores the correction vanishes by EQUALITY
    of the weights (`hsame`), which need not be 1. Finite algebra on the
    exponential form of both sides: uses the KP regime and the intervals
    (for the exponential representation) and `hsame`; not `mf`, `hCf`,
    `hsep` or `hδ`. -/
theorem profileExpectation_sub_eq_two_column_ledger_localized
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    (f : Config N G → ℝ) (s r R : Set (Link N))
    {a a' : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1)
    (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η) :
    profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'
      = (∑ T ∈ typedTouchingFamilies (N := N) s,
          profileWeight R a' T * typedMarkedCoreWeight μm β χ f T
            * (Real.exp (profileCoreExponent μm β χ T s R a)
                - Real.exp (profileCoreExponent μm β χ T s R a')))
        + ∑ T ∈ activityBridgeCores (N := N) s r,
          (profileWeight R a T - profileWeight R a' T) * typedMarkedCoreWeight μm β χ f T
            * Real.exp (profileCoreExponent μm β χ T s R a) := by
  rw [profileExpectation_eq_sum_core_mul_exp μm hβ mχ hχabs hsmall f s R h0 h1,
    profileExpectation_eq_sum_core_mul_exp μm hβ mχ hχabs hsmall f s R h0' h1']
  have hsplit : (∑ T ∈ typedTouchingFamilies (N := N) s,
        profileWeight R a T * typedMarkedCoreWeight μm β χ f T
          * Real.exp (profileCoreExponent μm β χ T s R a))
      = (∑ T ∈ typedTouchingFamilies (N := N) s,
          profileWeight R a' T * typedMarkedCoreWeight μm β χ f T
            * Real.exp (profileCoreExponent μm β χ T s R a))
        + ∑ T ∈ activityBridgeCores (N := N) s r,
          (profileWeight R a T - profileWeight R a' T) * typedMarkedCoreWeight μm β χ f T
            * Real.exp (profileCoreExponent μm β χ T s R a) := by
    rw [sum_touchingFamilies_eq_activityAllowed_add_bridge s r
        (fun T => profileWeight R a T * typedMarkedCoreWeight μm β χ f T
          * Real.exp (profileCoreExponent μm β χ T s R a)),
      sum_touchingFamilies_eq_activityAllowed_add_bridge s r
        (fun T => profileWeight R a' T * typedMarkedCoreWeight μm β χ f T
          * Real.exp (profileCoreExponent μm β χ T s R a))]
    have hallowed : (∑ T ∈ activityAllowedCores (N := N) s r,
          profileWeight R a T * typedMarkedCoreWeight μm β χ f T
            * Real.exp (profileCoreExponent μm β χ T s R a))
        = ∑ T ∈ activityAllowedCores (N := N) s r,
            profileWeight R a' T * typedMarkedCoreWeight μm β χ f T
              * Real.exp (profileCoreExponent μm β χ T s R a) := by
      refine Finset.sum_congr rfl (fun T hT => ?_)
      rw [profileWeight_eq_of_touchCount_zero_of_same R r hsame
        ((touchCount_eq_zero_iff r T).mpr (mem_activityAllowedCores.mp hT).2)]
    rw [hallowed, add_assoc, ← Finset.sum_add_distrib, add_right_inj]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    ring
  rw [hsplit, add_sub_right_comm, ← Finset.sum_sub_distrib, add_left_inj]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  ring

/-! ## 56-L.7 — the connector column at κ = 2, budget (1/2, 2) -/

/-- **LOCALIZED CONNECTOR COLUMN**: |Σ_T A′_T·W_T·(e^{E^R_T(a)} − e^{E^R_T(a′)})|
    ≤ δ·Cf·e^{−n/2}·e^{3·D_s·(2/113)} (= e^{6 D_s/113}). 0 ≤ A′_T ≤ 1 (with
    R), the Mayer majorant |W_T| ≤ Cf·Π M, the κ = 2 control, the generic
    budget (1/2, 2) (`sum_halfTilt_two_le`). -/
theorem abs_sum_localizedConnectorColumn_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} (R : Set (Link N)) {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |touchFactor R a η - touchFactor R a' η| ≤ δ) :
    |∑ T ∈ typedTouchingFamilies (N := N) s,
        profileWeight R a' T * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (profileCoreExponent μm β χ T s R a)
              - Real.exp (profileCoreExponent μm β χ T s R a'))|
      ≤ δ * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
  have hpre : (0:ℝ) ≤ δ * Real.exp (-(n : ℝ) / 2) * Cf :=
    mul_nonneg (mul_nonneg hδ0 (Real.exp_pos _).le) hCf0
  have hterm : ∀ T ∈ typedTouchingFamilies (N := N) s,
      |profileWeight R a' T * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (profileCoreExponent μm β χ T s R a)
              - Real.exp (profileCoreExponent μm β χ T s R a'))|
        ≤ δ * Real.exp (-(n : ℝ) / 2) * Cf * halfTiltCoreBudgetTerm β 2 s T := by
    intro T hT
    have hW := abs_typedMarkedCoreWeight_le_mayerCoreMajorant μm hβ mχ hχabs mf hCf0 hCf T
    have hE := abs_exp_profileCoreExponent_sub_le_decay_localized
      μm hβ mχ hχabs hsmall R hT hsep hδ0 h0 h1 h0' h1' hsame hδ
    have hA0 : 0 ≤ profileWeight R a' T := profileWeight_nonneg R h0' T
    have hA1 : profileWeight R a' T ≤ 1 := profileWeight_le_one R h0' h1' T
    have hW0 : (0:ℝ) ≤ Cf * ∏ η ∈ T, mayerCoreMajorant β η := le_trans (abs_nonneg _) hW
    rw [mul_assoc, abs_mul, abs_mul, abs_of_nonneg hA0]
    calc profileWeight R a' T
          * (|typedMarkedCoreWeight μm β χ f T|
              * |Real.exp (profileCoreExponent μm β χ T s R a)
                  - Real.exp (profileCoreExponent μm β χ T s R a')|)
        ≤ 1 * (|typedMarkedCoreWeight μm β χ f T|
              * |Real.exp (profileCoreExponent μm β χ T s R a)
                  - Real.exp (profileCoreExponent μm β χ T s R a')|) :=
          mul_le_mul_of_nonneg_right hA1 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |typedMarkedCoreWeight μm β χ f T|
            * |Real.exp (profileCoreExponent μm β χ T s R a)
                - Real.exp (profileCoreExponent μm β χ T s R a')| := one_mul _
      _ ≤ (Cf * ∏ η ∈ T, mayerCoreMajorant β η)
            * (δ * Real.exp (-(n : ℝ) / 2)
              * Real.exp ((familyTotalCard T : ℝ) / 2
                  + 2 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113))) :=
          mul_le_mul hW hE (abs_nonneg _) hW0
      _ = δ * Real.exp (-(n : ℝ) / 2) * Cf * halfTiltCoreBudgetTerm β 2 s T := by
          rw [halfTiltCoreBudgetTerm_eq]
          ring
  calc |∑ T ∈ typedTouchingFamilies (N := N) s,
        profileWeight R a' T * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (profileCoreExponent μm β χ T s R a)
              - Real.exp (profileCoreExponent μm β χ T s R a'))|
      ≤ ∑ T ∈ typedTouchingFamilies (N := N) s,
          |profileWeight R a' T * typedMarkedCoreWeight μm β χ f T
            * (Real.exp (profileCoreExponent μm β χ T s R a)
                - Real.exp (profileCoreExponent μm β χ T s R a'))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ typedTouchingFamilies (N := N) s,
          δ * Real.exp (-(n : ℝ) / 2) * Cf * halfTiltCoreBudgetTerm β 2 s T :=
        Finset.sum_le_sum hterm
    _ = δ * Real.exp (-(n : ℝ) / 2) * Cf
          * ∑ T ∈ typedTouchingFamilies (N := N) s, halfTiltCoreBudgetTerm β 2 s T := by
        rw [Finset.mul_sum]
    _ ≤ δ * Real.exp (-(n : ℝ) / 2) * Cf
          * Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
        mul_le_mul_of_nonneg_left (sum_halfTilt_two_le hβ hsmall s) hpre
    _ = δ * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by ring

/-! ## 56-L.8 — the bridge column at κ = 1, tilt 7/8, budget (7/8, 1) -/

/-- **PROFILE BRIDGE FIRST MOMENT, TWO REGIONS**: the exponent with R, the
    bridge geometry with r:
      card T·|W_T·e^{E^R_T(a)}| ≤ e^{−n/2}·Cf·(e^{1·b_T·(2/113)}·Π massTilt(7/8) M)
    for T ∈ activityBridgeCores s r under WalkBarrierSeparated s r n. The
    published 55-B interface ties both regions to r and is not edited. -/
theorem nat_card_mul_abs_profileNormalizedTerm_le_bridge_two_regions
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {T : Finset (Polymer N)} {s r : Set (Link N)} (R : Set (Link N)) {n : ℕ}
    (hT : T ∈ activityBridgeCores (N := N) s r)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {a : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) :
    (T.card : ℝ) * |typedMarkedCoreWeight μm β χ f T
        * Real.exp (profileCoreExponent μm β χ T s R a)|
      ≤ Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) := by
  have hn : n ≤ familyTotalCard T := activityBridgeCore_familyTotalCard_ge hT hsep
  have hnR : (n : ℝ) ≤ (familyTotalCard T : ℝ) := Nat.cast_le.mpr hn
  have hcard : (T.card : ℝ) ≤ (familyTotalCard T : ℝ) :=
    Nat.cast_le.mpr (familyCard_le_familyTotalCard T)
  have habs := nat_le_exp_three_eighths (familyTotalCard T)
  have hM : (0 : ℝ) ≤ ∏ η ∈ T, mayerCoreMajorant β η :=
    Finset.prod_nonneg (fun η _ => mayerCoreMajorant_nonneg hβ η)
  have hN := abs_typedMarkedCoreWeight_mul_exp_profile_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf T s R h0 h1
  have hb0 : (0 : ℝ) ≤ Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113)) :=
    (Real.exp_pos _).le
  have hpay : (1 : ℝ) ≤ Real.exp (-(n : ℝ) / 2) * Real.exp ((familyTotalCard T : ℝ) / 2) := by
    rw [← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hprod := prod_family_massTiltActivity (N := N) (7/8) (mayerCoreMajorant β) T
  have hL0 : (0:ℝ) ≤ Cf * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
      * ∏ η ∈ T, mayerCoreMajorant β η :=
    mul_nonneg (mul_nonneg hCf0 hb0) hM
  calc (T.card : ℝ) * |typedMarkedCoreWeight μm β χ f T
        * Real.exp (profileCoreExponent μm β χ T s R a)|
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

/-- **LOCALIZED BRIDGE COLUMN** (budget (7/8, 1)):
      |Σ_{T ∈ activityBridgeCores s r} (A_T − A′_T)·W_T·e^{E^R_T(a)}|
        ≤ δ·Cf·e^{−n/2}·e^{2·D_s·(2/113)}  (= e^{4 D_s/113}).
    The weight difference by card T·δ (56-L.1), the two-region first moment,
    the sum extended to the touching families (non-negative terms) and the
    generic budget `sum_sevenEighthsTilt_one_le`. -/
theorem abs_sum_localizedBridgeColumn_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} (R : Set (Link N)) {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |touchFactor R a η - touchFactor R a' η| ≤ δ) :
    |∑ T ∈ activityBridgeCores (N := N) s r,
        (profileWeight R a T - profileWeight R a' T) * typedMarkedCoreWeight μm β χ f T
          * Real.exp (profileCoreExponent μm β χ T s R a)|
      ≤ δ * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
  have hpre : (0:ℝ) ≤ δ * Real.exp (-(n : ℝ) / 2) * Cf :=
    mul_nonneg (mul_nonneg hδ0 (Real.exp_pos _).le) hCf0
  have hterm0 : ∀ T : Finset (Polymer N),
      (0:ℝ) ≤ δ * Real.exp (-(n : ℝ) / 2) * Cf
        * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) :=
    fun T => mul_nonneg hpre (sevenEighthsBudgetTerm_nonneg hβ s T)
  have hterm : ∀ T ∈ activityBridgeCores (N := N) s r,
      |(profileWeight R a T - profileWeight R a' T) * typedMarkedCoreWeight μm β χ f T
          * Real.exp (profileCoreExponent μm β χ T s R a)|
        ≤ δ * Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) := by
    intro T hT
    have hw := abs_profileWeight_sub_le_card_localized R r hδ0 h0 h1 h0' h1' hsame hδ T
    have hmom := nat_card_mul_abs_profileNormalizedTerm_le_bridge_two_regions
      μm hβ mχ hχabs hsmall mf hCf0 hCf R hT hsep h0 h1
    rw [mul_assoc, abs_mul]
    calc |profileWeight R a T - profileWeight R a' T|
          * |typedMarkedCoreWeight μm β χ f T * Real.exp (profileCoreExponent μm β χ T s R a)|
        ≤ ((T.card : ℝ) * δ)
          * |typedMarkedCoreWeight μm β χ f T * Real.exp (profileCoreExponent μm β χ T s R a)| :=
          mul_le_mul_of_nonneg_right hw (abs_nonneg _)
      _ = δ * ((T.card : ℝ)
            * |typedMarkedCoreWeight μm β χ f T
                * Real.exp (profileCoreExponent μm β χ T s R a)|) := by ring
      _ ≤ δ * (Real.exp (-(n : ℝ) / 2) * Cf
            * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
              * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η)) :=
          mul_le_mul_of_nonneg_left hmom hδ0
      _ = δ * Real.exp (-(n : ℝ) / 2) * Cf
            * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
              * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) := by ring
  calc |∑ T ∈ activityBridgeCores (N := N) s r,
        (profileWeight R a T - profileWeight R a' T) * typedMarkedCoreWeight μm β χ f T
          * Real.exp (profileCoreExponent μm β χ T s R a)|
      ≤ ∑ T ∈ activityBridgeCores (N := N) s r,
          |(profileWeight R a T - profileWeight R a' T) * typedMarkedCoreWeight μm β χ f T
            * Real.exp (profileCoreExponent μm β χ T s R a)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ activityBridgeCores (N := N) s r,
          δ * Real.exp (-(n : ℝ) / 2) * Cf
            * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
              * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ T ∈ typedTouchingFamilies (N := N) s,
          δ * Real.exp (-(n : ℝ) / 2) * Cf
            * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
              * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun T _ _ => hterm0 T)
    _ = δ * Real.exp (-(n : ℝ) / 2) * Cf
          * ∑ T ∈ typedTouchingFamilies (N := N) s,
              Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
                * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η := by
        rw [Finset.mul_sum]
    _ ≤ δ * Real.exp (-(n : ℝ) / 2) * Cf
          * Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
        mul_le_mul_of_nonneg_left (sum_sevenEighthsTilt_one_le hβ hsmall s) hpre
    _ = δ * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by ring

/-! ## 56-L.9 — the two-term estimate and CAPSTONE 56 -/

/-- **TWO-TERM LOCALIZED ESTIMATE**: ledger + triangle inequality + the two
    columns, constants kept separate:
      |F_R(a) − F_R(a′)| ≤ δ·Cf·e^{−n/2}·(e^{6 D_s/113} + e^{4 D_s/113}),
    written with `3·D_s·(2/113)` and `2·D_s·(2/113)`. No `DependsOnlyOn f s`;
    0 ≤ Cf derived; nothing divided by δ; no δ ≤ 1; no separation of s from R. -/
theorem abs_profileExpectation_sub_profileExpectation_le_two_terms_localized
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |touchFactor R a η - touchFactor R a' η| ≤ δ) :
    |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      ≤ δ * Cf * Real.exp (-(n : ℝ) / 2)
          * (Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))) := by
  have hCf0 : 0 ≤ Cf := nonneg_of_abs_le_of_config hCf
  have hA := abs_sum_localizedConnectorColumn_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf R hsep hδ0 h0 h1 h0' h1' hsame hδ
  have hB := abs_sum_localizedBridgeColumn_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf R hsep hδ0 h0 h1 h0' h1' hsame hδ
  rw [profileExpectation_sub_eq_two_column_ledger_localized
    μm hβ mχ hχabs hsmall f s r R h0 h1 h0' h1' hsame]
  refine le_trans (abs_add _ _) ?_
  have hsum := add_le_add hA hB
  calc _ ≤ _ := hsum
    _ = _ := by ring

/-- **CAPSTONE 56 — LOCALIZED STABILITY OF THE PROFILE-DAMPED FUNCTIONAL
    WITH A COMMON DAMPING BACKGROUND**: for profiles a, a′ in [0,1] whose
    effective factors (with respect to the damping region R) agree outside
    the change region r and differ by at most δ on r, at walk separation n of
    s from r,
      |F_R(a) − F_R(a′)| ≤ δ·2·Cf·e^{6 D_s/113}·e^{−n/2},
    the Stone 54/55 constant, rate and regime. No separation of s from R, no
    r ⊆ R, no unit background outside r, no δ ≤ 1, no `DependsOnlyOn f s`,
    no sign condition; 0 ≤ Cf derived; nothing divided by δ. From the
    two-term estimate and e^{4 D_s/113} ≤ e^{6 D_s/113} (D_s ≥ 0). -/
theorem abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_localized
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |touchFactor R a η - touchFactor R a' η| ≤ δ) :
    |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      ≤ δ * (2 * Cf)
          * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) := by
  have hCf0 : 0 ≤ Cf := nonneg_of_abs_le_of_config hCf
  have h2 := abs_profileExpectation_sub_profileExpectation_le_two_terms_localized
    μm hβ mχ hχabs hsmall R mf hCf hsep hδ0 h0 h1 h0' h1' hsame hδ
  have hD : (0:ℝ) ≤ ((supportLinkFinset (N := N) s).card : ℝ) := Nat.cast_nonneg _
  have hmono : Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
      ≤ Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hK : (0:ℝ) ≤ δ * Cf * Real.exp (-(n : ℝ) / 2) :=
    mul_nonneg (mul_nonneg hδ0 hCf0) (Real.exp_pos _).le
  have h3 : Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
      = Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113) := by
    congr 1; ring
  calc |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      ≤ δ * Cf * Real.exp (-(n : ℝ) / 2)
          * (Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))) := h2
    _ ≤ δ * Cf * Real.exp (-(n : ℝ) / 2)
          * (Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hmono _) hK
    _ = δ * (2 * Cf) * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) := by rw [← h3]; ring

/-! ## 56-L.10 — interfaces: exact identities and the recovery of Stone 55 -/

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Equal effective factors ⇒ equal functionals, EXACTLY**: for arbitrary
    real profiles, if touchFactor R a = touchFactor R a′ pointwise then
    F_R(a) = F_R(a′). An identity of definitions (the damped activities and
    all family weights coincide): no KP regime, no separation, no bound on f. -/
theorem profileExpectation_eq_of_touchFactor_eq (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s R : Set (Link N)) {a a' : Polymer N → ℝ}
    (hb : ∀ η, touchFactor R a η = touchFactor R a' η) :
    profileExpectation μm β χ f s R a = profileExpectation μm β χ f s R a' := by
  have hz : ∀ z : Polymer N → ℝ, profileDampedActivity z R a = profileDampedActivity z R a' := by
    intro z
    funext η
    have h := hb η
    unfold touchFactor at h
    unfold profileDampedActivity
    split_ifs with ht
    · rw [if_pos ht, if_pos ht] at h
      rw [h]
    · rfl
  have hw : ∀ Γ : Finset (Polymer N), profileWeight R a Γ = profileWeight R a' Γ := by
    intro Γ
    unfold profileWeight
    exact Finset.prod_congr rfl (fun η _ => hb η)
  unfold profileExpectation profileMarkedGas profilePolymerGas
  rw [hz]
  congr 1
  exact Finset.sum_congr rfl (fun Γ _ => by rw [hw])

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Empty change region**: r = ∅ makes `hsame` the equality of all effective
    factors (no polymer touches ∅), hence F_R(a) = F_R(a′) exactly, for
    arbitrary real profiles. Distinct from R = ∅, where every effective factor
    is 1 (55-A). -/
theorem profileExpectation_eq_of_same_empty_region (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s R : Set (Link N)) {a a' : Polymer N → ℝ}
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η (∅ : Set (Link N))
      → touchFactor R a η = touchFactor R a' η) :
    profileExpectation μm β χ f s R a = profileExpectation μm β χ f s R a' :=
  profileExpectation_eq_of_touchFactor_eq μm β χ f s R
    (fun η => hsame η (not_blockTouchesSupport_empty η.val))

/-- **The Stone 55 statement recovered (r = R)**: under the Stone 55
    hypotheses (|a − a′| ≤ δ on the polymers touching r) the localized capstone
    applied with R := r gives the Stone 55 bound. Direction 56 ⇒ 55: the
    published Stone 55 capstone is not used; the statement is rederived. -/
theorem abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_of_localized
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)}
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ) :
    |profileExpectation μm β χ f s r a - profileExpectation μm β χ f s r a'|
      ≤ δ * (2 * Cf) * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) :=
  abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_localized
    μm hβ mχ hχabs hsmall r mf hCf hsep hδ0 h0 h1 h0' h1'
    (localized_hypotheses_of_profile_hypotheses r hδ).1
    (localized_hypotheses_of_profile_hypotheses r hδ).2

#print axioms profileWeight_eq_of_touchCount_zero_of_same
#print axioms tupleProfileWeight_eq_of_tupleTouchCount_zero_of_same
#print axioms abs_profileWeight_sub_le_localized
#print axioms abs_tupleProfileWeight_sub_le_localized
#print axioms abs_tupleProfileWeight_sub_le_k_localized
#print axioms abs_profileWeight_sub_le_card_localized
#print axioms kpLocalizedDiff_inclusion_exclusion
#print axioms kpLocalizedDiffCoeff_order_zero
#print axioms abs_kpLocalizedDiffCoeff_le
#print axioms localized_hypotheses_of_profile_hypotheses
#print axioms profileCoreExponent_sub_eq_localizedConnectorDiff
#print axioms abs_localizedConnectorDiff_le_eroded
#print axioms abs_exp_profileCoreExponent_sub_le_decay_localized
#print axioms profileExpectation_sub_eq_two_column_ledger_localized
#print axioms abs_sum_localizedConnectorColumn_le
#print axioms nat_card_mul_abs_profileNormalizedTerm_le_bridge_two_regions
#print axioms abs_sum_localizedBridgeColumn_le
#print axioms abs_profileExpectation_sub_profileExpectation_le_two_terms_localized
#print axioms abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_localized
#print axioms profileExpectation_eq_of_touchFactor_eq
#print axioms profileExpectation_eq_of_same_empty_region
#print axioms abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_of_localized

end LatticeGauge
