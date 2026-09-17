/-
LatticeGauge/ActivityProfileDampingStability.lean — PEDRA 55,
Gate 55-B: CAPSTONE — STABILITY OF THE PROFILE-DAMPED FUNCTIONAL UNDER A
UNIFORM MAJORANT OF THE PROFILE DIFFERENCE
(architecture and review: GPT Astra; feasibility and execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): for two profiles a, a′
in [0,1] and a majorant 0 ≤ δ with |a(γ) − a′(γ)| ≤ δ on every polymer
touching r, the profile functional F(a) = profileExpectation satisfies
    |F(a) − F(a′)| ≤ δ·Cf·e^{−n/2}·(e^{6 D_s/113} + e^{4 D_s/113})
                  ≤ δ·2·Cf·e^{6 D_s/113}·e^{−n/2},
D_s = card (supportLinkFinset s), n the walk-barrier separation of s and
r — the Stone 54 constant, rate and regime, with δ in the place of
|θ − θ′|. The route is the Stone 54 route with the count bounds of 55-A
in the place of the power lemma:
  * the profile connector coefficient (weight 1 − A_δ on the tuples
    hitting both barriers), its coefficient-level inclusion–exclusion,
    the two-profile domination |c_k(a) − c_k(a′)| ≤ δ·k·A_k (tuple
    positions, repetitions counted), summability from the 52-A0 first
    moment, and the series identities E_T(a) − E_T(full) = C(a),
    E_T(a) − E_T(a′) = C(a) − C(a′) (orientation of 51-C/52-C kept);
  * the eroded two-profile bound |C(a) − C(a′)| ≤ δ·e^{−((n−m_T:ℕ))/2}·q_T
    (natural truncated subtraction, no 8/(3e));
  * the bilateral exponential control of Stone 54 with κ = 2:
    |e^{E_T(a)} − e^{E_T(a′)}| ≤ δ·e^{−n/2}·e^{m_T/2 + 2 q_T}, both
    exponents ≤ q_T by 55-A; no δ ≤ 1 is needed anywhere;
  * the connector column at budget (1/2, 2) (0 ≤ A′_T ≤ 1, Mayer
    majorant, `sum_halfTilt_two_le`), prefactor e^{6 D_s/113};
  * the bridge column at κ = 1, tilt 7/8, budget (7/8, 1):
    |A_T − A′_T| ≤ card T·δ and the profile bridge first moment,
    prefactor e^{4 D_s/113};
  * the two-term estimate and the capstone; the constant-profile
    specialization (δ = |θ − θ′|) gives back the Stone 54 capstone as an
    APPLICATION of the new one; equal profiles (δ = 0) give the bound 0;
    the corollaries against the zero profile (Stone 51 functional, no
    `DependsOnlyOn`) and the unit profile (Gibbs, with `DependsOnlyOn`).
Nothing is divided by δ; 0 ≤ Cf is derived from |f| ≤ Cf; no sign
condition on activities or exponents is introduced.

No optimality, sharpness or bibliographic priority is claimed.

HARD HOLD (not here): any Disjoint s r, size restriction on r or volume
factor; per-link profiles; monotonicity or differentiability in the
profile; Gibbs-measure, boundary-condition or modified-action
interpretations; thermodynamic limit, continuum, mass gap. No
project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.ActivityProfileDamping

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## 55-B.1 — the profile connector coefficient -/

/-- **The profile connector coefficient**: the tuple sum over tuples
    hitting BOTH barriers (P-forbidden somewhere and r-touching
    somewhere), each weighted by 1 − A_δ (positions counted, repetitions
    included), times the Ursell factor and the product of the ORIGINAL
    activities; divided by k! outside the sum, exactly as in
    `kpDampedConnectorUnrootedCoeff`. -/
noncomputable def kpProfileConnectorUnrootedCoeff (k : ℕ) (z : Polymer N → ℝ)
    (P : Polymer N → Prop) (r : Set (Link N)) (a : Polymer N → ℝ) : ℝ :=
  (∑ δ : Fin k → Polymer N,
      if TupleHitsBothForbidden P (regionAllowed (N := N) r) δ then
        (1 - tupleProfileWeight r a δ)
          * (((ursellCoeff (N := N) (fun i => (δ i).val) : ℤ) : ℝ) * ∏ i : Fin k, z (δ i))
      else 0)
    / ((Nat.factorial k : ℕ) : ℝ)

/-- **Constant profile**: the Stone 52 damped connector coefficient. -/
theorem kpProfileConnectorUnrootedCoeff_const (k : ℕ) (z : Polymer N → ℝ)
    (P : Polymer N → Prop) (r : Set (Link N)) (θ : ℝ) :
    kpProfileConnectorUnrootedCoeff k z P r (fun _ => θ)
      = kpDampedConnectorUnrootedCoeff k z P r θ := by
  unfold kpProfileConnectorUnrootedCoeff kpDampedConnectorUnrootedCoeff
  congr 1
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  rw [tupleProfileWeight_const]

/-- **Unit profile**: the weight 1 − 1 vanishes, the coefficient is 0. -/
theorem kpProfileConnectorUnrootedCoeff_unit (k : ℕ) (z : Polymer N → ℝ)
    (P : Polymer N → Prop) (r : Set (Link N)) :
    kpProfileConnectorUnrootedCoeff (N := N) k z P r (fun _ => 1) = 0 := by
  rw [kpProfileConnectorUnrootedCoeff_const]
  exact kpDampedConnectorUnrootedCoeff_one k z P r

/-- **PROFILE INCLUSION–EXCLUSION (coefficients)**: the four-term
    combination of the Stone 49 coefficients of the profile-damped and
    the original activity, restricted or not by P, IS the profile
    connector coefficient. The regional filter enters only through
    `TupleAllowed (regionAllowed r) δ → tupleTouchCount r δ = 0 → A_δ = 1
    → weight 0`; no converse is used. No hypothesis on a. -/
theorem kpProfileConnector_inclusion_exclusion (k : ℕ) (z : Polymer N → ℝ)
    (P : Polymer N → Prop) (r : Set (Link N)) (a : Polymer N → ℝ) :
    kpSignedUnrootedCoeff (N := N) k (restrictedActivity (profileDampedActivity z r a) P)
      - kpSignedUnrootedCoeff (N := N) k (profileDampedActivity z r a)
      - kpSignedUnrootedCoeff (N := N) k (restrictedActivity z P)
      + kpSignedUnrootedCoeff (N := N) k z
      = kpProfileConnectorUnrootedCoeff k z P r a := by
  unfold kpSignedUnrootedCoeff kpProfileConnectorUnrootedCoeff
  rw [div_sub_div_same, div_sub_div_same, div_add_div_same]
  congr 1
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  rw [prod_restrictedActivity_eq, prod_restrictedActivity_eq, prod_profileDampedActivity_tuple]
  by_cases hP : TupleAllowed P δ
  · rw [if_pos hP, if_pos hP, if_neg (fun h => h.1 hP)]
    ring
  · by_cases hQ : TupleAllowed (regionAllowed (N := N) r) δ
    · have hc : tupleTouchCount r δ = 0 :=
        (tupleAllowed_regionAllowed_iff_tupleTouchCount_eq_zero r δ).mp hQ
      rw [if_neg hP, if_neg hP, if_neg (fun h => h.2 hQ),
        tupleProfileWeight_eq_one_of_tupleTouchCount_zero r a hc]
      ring
    · rw [if_neg hP, if_neg hP, if_pos ⟨hP, hQ⟩]
      ring

/-! ## 55-B.2 — domination of the profile connector coefficients -/

/-- **DOMINATION (two profiles)**: |c_k(a) − c_k(a′)| ≤ δ·k·A_k(|z|), where
    the weights differ by A′_δ − A_δ on every tuple hitting both barriers,
    |A_δ − A′_δ| ≤ tupleTouchCount·δ ≤ k·δ (55-A). -/
theorem abs_kpProfileConnectorUnrootedCoeff_sub_le (k : ℕ) (z : Polymer N → ℝ)
    (P : Polymer N → Prop) (r : Set (Link N)) {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ) :
    |kpProfileConnectorUnrootedCoeff (N := N) k z P r a
        - kpProfileConnectorUnrootedCoeff (N := N) k z P r a'|
      ≤ δ * (k : ℝ)
          * kpAbsConnectorUnrootedCoeff k (fun η => |z η|) P (regionAllowed (N := N) r) := by
  unfold kpProfileConnectorUnrootedCoeff kpAbsConnectorUnrootedCoeff
  rw [div_sub_div_same, ← mul_div_assoc, abs_div, Nat.abs_cast]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun δt _ => ?_))
  by_cases h : TupleHitsBothForbidden P (regionAllowed (N := N) r) δt
  · rw [if_pos h, if_pos h, if_pos h, ← sub_mul, abs_mul, abs_mul,
      Finset.abs_prod, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
    have hw : |(1 - tupleProfileWeight r a δt) - (1 - tupleProfileWeight r a' δt)|
        ≤ δ * (k : ℝ) := by
      rw [show (1 - tupleProfileWeight r a δt) - (1 - tupleProfileWeight r a' δt)
          = -(tupleProfileWeight r a δt - tupleProfileWeight r a' δt) from by ring, abs_neg]
      calc |tupleProfileWeight r a δt - tupleProfileWeight r a' δt|
          ≤ (k : ℝ) * δ := abs_tupleProfileWeight_sub_le_k r hδ0 h0 h1 h0' h1' hδ δt
        _ = δ * (k : ℝ) := mul_comm _ _
    have hrest : 0 ≤ (((ursellCoeff (N := N) (fun i => (δt i).val)).natAbs : ℕ) : ℝ)
        * ∏ i : Fin k, |z (δt i)| :=
      mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => abs_nonneg _))
    calc |(1 - tupleProfileWeight r a δt) - (1 - tupleProfileWeight r a' δt)|
          * ((((ursellCoeff (N := N) (fun i => (δt i).val)).natAbs : ℕ) : ℝ)
              * ∏ i : Fin k, |z (δt i)|)
        ≤ (δ * (k : ℝ))
          * ((((ursellCoeff (N := N) (fun i => (δt i).val)).natAbs : ℕ) : ℝ)
              * ∏ i : Fin k, |z (δt i)|) :=
          mul_le_mul_of_nonneg_right hw hrest
      _ = δ * (k : ℝ)
          * ((((ursellCoeff (N := N) (fun i => (δt i).val)).natAbs : ℕ) : ℝ)
              * ∏ i : Fin k, |z (δt i)|) := by ring
  · rw [if_neg h, if_neg h, if_neg h, sub_zero, abs_zero, mul_zero]

/-- **DOMINATION (one profile, against the unit profile)**:
    |c_k(a)| ≤ 1·k·A_k(|z|), since c_k(1) = 0 and |a − 1| ≤ 1 on [0,1]. -/
theorem abs_kpProfileConnectorUnrootedCoeff_le (k : ℕ) (z : Polymer N → ℝ)
    (P : Polymer N → Prop) (r : Set (Link N)) {a : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) :
    |kpProfileConnectorUnrootedCoeff (N := N) k z P r a|
      ≤ 1 * (k : ℝ)
          * kpAbsConnectorUnrootedCoeff k (fun η => |z η|) P (regionAllowed (N := N) r) := by
  have := abs_kpProfileConnectorUnrootedCoeff_sub_le k z P r (a := a) (a' := fun _ => 1)
    (δ := 1) zero_le_one h0 h1 (fun _ => zero_le_one) (fun _ => le_rfl)
    (fun η _ => by
      show |a η - 1| ≤ 1
      rw [abs_le]
      constructor <;> linarith [h0 η, h1 η])
  rwa [kpProfileConnectorUnrootedCoeff_unit, sub_zero] at this

/-! ## 55-B.3 — the profile connector series -/

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **The profile connector** C_{T,r}(a): the series of the profile
    connector coefficients of the polymer weight between the core-relative
    barrier (remote-allowed for T at s) and the regional barrier r. -/
noncomputable def profileConnector (β : ℝ) (χ : G → ℝ) (T : Finset (Polymer N))
    (s r : Set (Link N)) (a : Polymer N → ℝ) : ℝ :=
  ∑' k, kpProfileConnectorUnrootedCoeff (N := N) k
    (fun η => polymerWeight (N := N) μm β χ η.val) (remoteAllowed (N := N) T s) r a

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Constant profile**: the Stone 52 damped connector. -/
theorem profileConnector_const (β : ℝ) (χ : G → ℝ) (T : Finset (Polymer N))
    (s r : Set (Link N)) (θ : ℝ) :
    profileConnector μm β χ T s r (fun _ => θ) = activityDampingConnector μm β χ T s r θ := by
  unfold profileConnector activityDampingConnector
  exact tsum_congr (fun k => kpProfileConnectorUnrootedCoeff_const k _ _ r θ)

/-- **Summability of the profile connector series**, under the separation
    of the two barrier regions (the 52-A0 first moment is the majorant). -/
theorem summable_kpProfileConnectorUnrootedCoeff
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {q : ℕ}
    (hwsep : WalkBarrierSeparated (N := N) (barrierRegion (N := N) T s)
      (barrierRegion (N := N) (∅ : Finset (Polymer N)) r) q)
    {a : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) :
    Summable (fun k : ℕ =>
      |kpProfileConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val) (remoteAllowed (N := N) T s) r a|) := by
  have hmaj := summable_nat_mul_kpAbsConnector_polymerWeight μm hβ mχ hχabs hsmall hwsep
  rw [← regionAllowed_eq_remoteAllowed_empty] at hmaj
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_)
    (Summable.mul_left 1 hmaj)
  have := abs_kpProfileConnectorUnrootedCoeff_le k
    (fun η => polymerWeight (N := N) μm β χ η.val) (remoteAllowed (N := N) T s) r h0 h1
  rw [mul_assoc] at this
  exact this

/-- **PROFILE INCLUSION–EXCLUSION (series)**: E_T(a) − E_T(full) = C_{T,r}(a).
    All four cluster series are summable by KP (the profile ones through
    the 55-A transport); orientation identical to Stone 51-C/52-C. -/
theorem profileCoreExponent_sub_full_eq_profileConnector
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r : Set (Link N))
    {a : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) :
    profileCoreExponent μm β χ T s r a - fullActivityCoreExponent μm β χ T s
      = profileConnector μm β χ T s r a := by
  have ha : ∀ γ : Polymer N, 0 ≤ ((γ.val.card : ℕ) : ℝ) := fun γ => Nat.cast_nonneg _
  have hKP := abstractKP_of_beta_le_one_div_40000 (N := N) μm hβ mχ hχabs hsmall
  have hKPa := abstractKP_profileDampedActivity r h0 h1 hKP
  have hSPa : Summable (fun n => kpSignedUnrootedCoeff (N := N) n
      (restrictedActivity
        (profileDampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) r a)
        (remoteAllowed (N := N) T s))) :=
    summable_kpSignedUnrootedCoeff ha
      (abstractKP_restrictedActivity (remoteAllowed (N := N) T s) hKPa)
  have hS0a : Summable (fun n => kpSignedUnrootedCoeff (N := N) n
      (profileDampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) r a)) :=
    summable_kpSignedUnrootedCoeff ha hKPa
  have hSP : Summable (fun n => kpSignedUnrootedCoeff (N := N) n
      (restrictedActivity (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s))) :=
    summable_kpSignedUnrootedCoeff ha
      (abstractKP_restrictedActivity (remoteAllowed (N := N) T s) hKP)
  have hS0 : Summable (fun n => kpSignedUnrootedCoeff (N := N) n
      (fun η => polymerWeight (N := N) μm β χ η.val)) :=
    summable_kpSignedUnrootedCoeff ha hKP
  unfold profileCoreExponent fullActivityCoreExponent profileConnector
  have hlin : ∀ a b c d : ℝ, (a - b) - (c - d) = a - b - c + d := by
    intro a b c d; ring
  rw [hlin, ← tsum_sub hSPa hS0a, ← tsum_sub (hSPa.sub hS0a) hSP,
    ← tsum_add ((hSPa.sub hS0a).sub hSP) hS0]
  exact tsum_congr (fun k =>
    kpProfileConnector_inclusion_exclusion k _ (remoteAllowed (N := N) T s) r a)

/-- E_T(a) − E_T(a′) = C_{T,r}(a) − C_{T,r}(a′). -/
theorem profileCoreExponent_sub_eq_profileConnector_sub
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r : Set (Link N))
    {a a' : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1)
    (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1) :
    profileCoreExponent μm β χ T s r a - profileCoreExponent μm β χ T s r a'
      = profileConnector μm β χ T s r a - profileConnector μm β χ T s r a' := by
  have e1 := profileCoreExponent_sub_full_eq_profileConnector μm hβ mχ hχabs hsmall T s r h0 h1
  have e2 := profileCoreExponent_sub_full_eq_profileConnector μm hβ mχ hχabs hsmall T s r
    h0' h1'
  linarith

/-! ## 55-B.4 — the eroded two-profile connector difference -/

/-- **ERODED TWO-PROFILE BOUND**:
      |C_{T,r}(a) − C_{T,r}(a′)| ≤ δ·e^{−((n − m_T : ℕ))/2}·q′,
    q′ = card(barrierLinkFinset T s)·(2/113), natural truncated
    subtraction. Route: 51-D erosion, the summability of both series, the
    two-profile domination and the 52-A0 first moment Σ k·A_k ≤ e^{−q/2}·q′
    (no 8/(3e)). Mirror of `abs_activityDampingConnector_sub_le_eroded`. -/
theorem abs_profileConnector_sub_le_eroded
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ) :
    |profileConnector μm β χ T s r a - profileConnector μm β χ T s r a'|
      ≤ δ * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2)
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
  -- summability of both profile series
  have hSa : Summable (fun k : ℕ =>
      kpProfileConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s) r a) :=
    Summable.of_norm (by
      simpa [Real.norm_eq_abs] using
        summable_kpProfileConnectorUnrootedCoeff μm hβ mχ hχabs hsmall hero h0 h1)
  have hSa' : Summable (fun k : ℕ =>
      kpProfileConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s) r a') :=
    Summable.of_norm (by
      simpa [Real.norm_eq_abs] using
        summable_kpProfileConnectorUnrootedCoeff μm hβ mχ hχabs hsmall hero h0' h1')
  -- termwise domination of the difference
  have hdom : ∀ k : ℕ,
      |kpProfileConnectorUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s) r a
        - kpProfileConnectorUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s) r a'|
      ≤ δ * ((k : ℝ)
          * kpAbsConnectorUnrootedCoeff k
              (fun η => |polymerWeight (N := N) μm β χ η.val|)
              (remoteAllowed (N := N) T s) (regionAllowed (N := N) r)) := by
    intro k
    have := abs_kpProfileConnectorUnrootedCoeff_sub_le k
      (fun η => polymerWeight (N := N) μm β χ η.val)
      (remoteAllowed (N := N) T s) r hδ0 h0 h1 h0' h1' hδ
    rw [mul_assoc] at this
    exact this
  have hsumabs : Summable (fun k : ℕ =>
      |kpProfileConnectorUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s) r a
        - kpProfileConnectorUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s) r a'|) :=
    Summable.of_nonneg_of_le (fun k => abs_nonneg _) hdom
      (Summable.mul_left δ hmaj)
  unfold profileConnector
  rw [← tsum_sub hSa hSa']
  have h1' : ‖∑' k : ℕ, (kpProfileConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s) r a
      - kpProfileConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s) r a')‖
      ≤ ∑' k : ℕ, ‖kpProfileConnectorUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s) r a
        - kpProfileConnectorUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s) r a'‖ := by
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

/-! ## 55-B.5 — the bilateral exponential control (κ = 2) -/

/-- **EXPONENTIAL CONTROL (two profiles, κ = 2)**:
      |e^{E_T(a)} − e^{E_T(a′)}| ≤ δ·e^{−n/2}·e^{m_T/2 + 2·b_T·(2/113)}.
    Route (Stone 54): both exponents are ≤ q_T = b_T·(2/113) (55-A); the
    scalar bound |e^x − e^y| ≤ e^{q}·|x − y|; the eroded two-profile bound;
    q_T ≤ e^{q_T}; the repurchased erosion. No δ ≤ 1 is needed. -/
theorem abs_exp_profileCoreExponent_sub_le_decay_refined
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ) :
    |Real.exp (profileCoreExponent μm β χ T s r a)
        - Real.exp (profileCoreExponent μm β χ T s r a')|
      ≤ δ * Real.exp (-(n : ℝ) / 2)
        * Real.exp ((familyTotalCard T : ℝ) / 2
            + 2 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
  set q : ℝ := ((barrierLinkFinset T s).card : ℝ) * (2 / 113) with hq
  have hx : profileCoreExponent μm β χ T s r a ≤ q :=
    le_trans (le_abs_self _)
      (abs_profileCoreExponent_le_barrier μm hβ mχ hχabs hsmall T s r h0 h1)
  have hy : profileCoreExponent μm β χ T s r a' ≤ q :=
    le_trans (le_abs_self _)
      (abs_profileCoreExponent_le_barrier μm hβ mχ hχabs hsmall T s r h0' h1')
  have hΔ : |profileCoreExponent μm β χ T s r a - profileCoreExponent μm β χ T s r a'|
      ≤ δ * Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) * q := by
    rw [profileCoreExponent_sub_eq_profileConnector_sub
      μm hβ mχ hχabs hsmall T s r h0 h1 h0' h1', hq]
    exact abs_profileConnector_sub_le_eroded
      μm hβ mχ hχabs hsmall hT hsep hδ0 h0 h1 h0' h1' hδ
  have hq0 : (0:ℝ) ≤ q := mul_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hqexp : q ≤ Real.exp q := le_exp_self q
  have herode := exp_neg_nat_sub_half_le n (familyTotalCard T)
  have he0 : (0:ℝ) ≤ Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) :=
    (Real.exp_pos _).le
  calc |Real.exp (profileCoreExponent μm β χ T s r a)
        - Real.exp (profileCoreExponent μm β χ T s r a')|
      ≤ Real.exp q * |profileCoreExponent μm β χ T s r a
          - profileCoreExponent μm β χ T s r a'| :=
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

/-! ## 55-B.6 — the connector column at κ = 2, budget (1/2, 2) -/

/-- **CONNECTOR-COLUMN TERM, κ = 2**: for every touching core T,
      |A′_T·W_T·(e^{E_T(a)} − e^{E_T(a′)})|
        ≤ δ·e^{−n/2}·Cf·halfTiltCoreBudgetTerm β 2 s T.
    0 ≤ A′_T ≤ 1, |W_T| ≤ Cf·Π M (no exponential), the exponential control. -/
theorem abs_profileConnectorColumnTerm_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ) :
    |profileWeight r a' T
        * typedMarkedCoreWeight μm β χ f T
        * (Real.exp (profileCoreExponent μm β χ T s r a)
            - Real.exp (profileCoreExponent μm β χ T s r a'))|
      ≤ δ * Real.exp (-(n : ℝ) / 2) * Cf
          * halfTiltCoreBudgetTerm β 2 s T := by
  have hW := abs_typedMarkedCoreWeight_le_mayerCoreMajorant
    μm hβ mχ hχabs mf hCf0 hCf T
  have hE := abs_exp_profileCoreExponent_sub_le_decay_refined
    μm hβ mχ hχabs hsmall hT hsep hδ0 h0 h1 h0' h1' hδ
  have hA0 : 0 ≤ profileWeight r a' T := profileWeight_nonneg r h0' T
  have hA1 : profileWeight r a' T ≤ 1 := profileWeight_le_one r h0' h1' T
  have hW0 : (0:ℝ) ≤ Cf * ∏ η ∈ T, mayerCoreMajorant β η :=
    le_trans (abs_nonneg _) hW
  have hre : profileWeight r a' T * typedMarkedCoreWeight μm β χ f T
      * (Real.exp (profileCoreExponent μm β χ T s r a)
          - Real.exp (profileCoreExponent μm β χ T s r a'))
      = profileWeight r a' T
        * (typedMarkedCoreWeight μm β χ f T
            * (Real.exp (profileCoreExponent μm β χ T s r a)
                - Real.exp (profileCoreExponent μm β χ T s r a'))) := by
    ring
  rw [hre, abs_mul, abs_mul, abs_of_nonneg hA0]
  calc profileWeight r a' T
        * (|typedMarkedCoreWeight μm β χ f T|
            * |Real.exp (profileCoreExponent μm β χ T s r a)
                - Real.exp (profileCoreExponent μm β χ T s r a')|)
      ≤ 1 * (|typedMarkedCoreWeight μm β χ f T|
            * |Real.exp (profileCoreExponent μm β χ T s r a)
                - Real.exp (profileCoreExponent μm β χ T s r a')|) :=
        mul_le_mul_of_nonneg_right hA1
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = |typedMarkedCoreWeight μm β χ f T|
          * |Real.exp (profileCoreExponent μm β χ T s r a)
              - Real.exp (profileCoreExponent μm β χ T s r a')| :=
        one_mul _
    _ ≤ (Cf * ∏ η ∈ T, mayerCoreMajorant β η)
          * (δ * Real.exp (-(n : ℝ) / 2)
            * Real.exp ((familyTotalCard T : ℝ) / 2
                + 2 * ((barrierLinkFinset T s).card : ℝ) * (2 / 113))) :=
        mul_le_mul hW hE (abs_nonneg _) hW0
    _ = δ * Real.exp (-(n : ℝ) / 2) * Cf
          * halfTiltCoreBudgetTerm β 2 s T := by
        rw [halfTiltCoreBudgetTerm_eq]
        ring

/-- **CONNECTOR COLUMN, SUM OF ABSOLUTE VALUES** (budget (1/2, 2)):
      Σ_T |A′_T·W_T·(e^{E_T(a)} − e^{E_T(a′)})|
        ≤ δ·Cf·e^{−n/2}·e^{3·D_s·(2/113)}  (= e^{6 D_s/113}). -/
theorem sum_abs_profileConnectorColumn_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        |profileWeight r a' T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (profileCoreExponent μm β χ T s r a)
              - Real.exp (profileCoreExponent μm β χ T s r a'))|)
      ≤ δ * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
  have hpre : (0:ℝ) ≤ δ * Real.exp (-(n : ℝ) / 2) * Cf :=
    mul_nonneg (mul_nonneg hδ0 (Real.exp_pos _).le) hCf0
  calc (∑ T ∈ typedTouchingFamilies (N := N) s,
        |profileWeight r a' T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (profileCoreExponent μm β χ T s r a)
              - Real.exp (profileCoreExponent μm β χ T s r a'))|)
      ≤ ∑ T ∈ typedTouchingFamilies (N := N) s,
          δ * Real.exp (-(n : ℝ) / 2) * Cf
            * halfTiltCoreBudgetTerm β 2 s T :=
        Finset.sum_le_sum (fun T hT =>
          abs_profileConnectorColumnTerm_le μm hβ mχ hχabs hsmall
            mf hCf0 hCf hT hsep hδ0 h0 h1 h0' h1' hδ)
    _ = δ * Real.exp (-(n : ℝ) / 2) * Cf
          * ∑ T ∈ typedTouchingFamilies (N := N) s,
              halfTiltCoreBudgetTerm β 2 s T := by
        rw [Finset.mul_sum]
    _ ≤ δ * Real.exp (-(n : ℝ) / 2) * Cf
          * Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
        mul_le_mul_of_nonneg_left (sum_halfTilt_two_le hβ hsmall s) hpre
    _ = δ * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
        ring

/-- **CONNECTOR COLUMN, ABSOLUTE VALUE OF THE SUM**. -/
theorem abs_sum_profileConnectorColumn_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ) :
    |∑ T ∈ typedTouchingFamilies (N := N) s,
        profileWeight r a' T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (profileCoreExponent μm β χ T s r a)
              - Real.exp (profileCoreExponent μm β χ T s r a'))|
      ≤ δ * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
  le_trans (Finset.abs_sum_le_sum_abs _ _)
    (sum_abs_profileConnectorColumn_le μm hβ mχ hχabs hsmall mf hCf0 hCf
      hsep hδ0 h0 h1 h0' h1' hδ)

/-! ## 55-B.7 — the bridge column at κ = 1, tilt 7/8, budget (7/8, 1) -/

/-- **Profile normalized term**: |W_T·e^{E_T(a)}| ≤ Cf·e^{b_T·(2/113)}·Π M
    (the core weight against the Mayer majorant times the profile exponent
    bound — ONE barrier exponential). -/
theorem abs_typedMarkedCoreWeight_mul_exp_profile_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    (T : Finset (Polymer N)) (s r : Set (Link N))
    {a : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) :
    |typedMarkedCoreWeight μm β χ f T
        * Real.exp (profileCoreExponent μm β χ T s r a)|
      ≤ Cf * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T, mayerCoreMajorant β η := by
  have hW := abs_typedMarkedCoreWeight_le_mayerCoreMajorant
    μm hβ mχ hχabs mf hCf0 hCf T
  have hE := exp_profileCoreExponent_le_exp_barrier
    μm hβ mχ hχabs hsmall T s r h0 h1
  have hL0 : (0:ℝ) ≤ Cf * ∏ η ∈ T, mayerCoreMajorant β η :=
    le_trans (abs_nonneg _) hW
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |typedMarkedCoreWeight μm β χ f T|
        * Real.exp (profileCoreExponent μm β χ T s r a)
      ≤ (Cf * ∏ η ∈ T, mayerCoreMajorant β η)
          * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113)) :=
        mul_le_mul hW hE (Real.exp_pos _).le hL0
    _ = Cf * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T, mayerCoreMajorant β η := by ring

/-- **PROFILE FIRST MOMENT OF A BRIDGE CORE** (κ = 1, tilt 7/8):
      card T·|W_T·e^{E_T(a)}| ≤ e^{−n/2}·Cf·(e^{1·b_T·(2/113)}·Π massTilt(7/8) M).
    card T ≤ m_T ≤ e^{3 m_T/8} and n ≤ m_T (bridge geometry) pay e^{−n/2}·e^{m_T/2}. -/
theorem nat_card_mul_abs_profileNormalizedTerm_le_bridge
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ activityBridgeCores (N := N) s r)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {a : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) :
    (T.card : ℝ) * |typedMarkedCoreWeight μm β χ f T
        * Real.exp (profileCoreExponent μm β χ T s r a)|
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
  have hN := abs_typedMarkedCoreWeight_mul_exp_profile_le
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
        * Real.exp (profileCoreExponent μm β χ T s r a)|
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

/-- **BRIDGE-COLUMN TERM, κ = 1**: for a bridge core T,
      |(A_T − A′_T)·W_T·e^{E_T(a)}|
        ≤ δ·e^{−n/2}·Cf·(e^{1·b_T·(2/113)}·Π massTilt(7/8) M).
    The weight difference is paid by card T·δ (55-A); card T·|W_T·e^{E_T(a)}|
    is the profile bridge first moment. -/
theorem abs_profileBridgeColumnTerm_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ activityBridgeCores (N := N) s r)
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ) :
    |(profileWeight r a T - profileWeight r a' T)
        * typedMarkedCoreWeight μm β χ f T
        * Real.exp (profileCoreExponent μm β χ T s r a)|
      ≤ δ * Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) := by
  have hw := abs_profileWeight_sub_le_card r hδ0 h0 h1 h0' h1' hδ T
  have hmom := nat_card_mul_abs_profileNormalizedTerm_le_bridge
    μm hβ mχ hχabs hsmall mf hCf0 hCf hT hsep h0 h1
  rw [mul_assoc, abs_mul]
  calc |profileWeight r a T - profileWeight r a' T|
        * |typedMarkedCoreWeight μm β χ f T
            * Real.exp (profileCoreExponent μm β χ T s r a)|
      ≤ ((T.card : ℝ) * δ)
        * |typedMarkedCoreWeight μm β χ f T
            * Real.exp (profileCoreExponent μm β χ T s r a)| :=
        mul_le_mul_of_nonneg_right hw (abs_nonneg _)
    _ = δ * ((T.card : ℝ)
          * |typedMarkedCoreWeight μm β χ f T
              * Real.exp (profileCoreExponent μm β χ T s r a)|) := by
        ring
    _ ≤ δ * (Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η)) :=
        mul_le_mul_of_nonneg_left hmom hδ0
    _ = δ * Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) := by
        ring

/-- **BRIDGE COLUMN, SUM OF ABSOLUTE VALUES** (budget (7/8, 1)):
      Σ_{T bridge} |(A_T − A′_T)·W_T·e^{E_T(a)}|
        ≤ δ·Cf·e^{−n/2}·e^{2·D_s·(2/113)}  (= e^{4 D_s/113}). -/
theorem sum_abs_profileBridgeColumn_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ) :
    (∑ T ∈ activityBridgeCores (N := N) s r,
        |(profileWeight r a T - profileWeight r a' T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (profileCoreExponent μm β χ T s r a)|)
      ≤ δ * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
  have hpre : (0:ℝ) ≤ δ * Real.exp (-(n : ℝ) / 2) * Cf :=
    mul_nonneg (mul_nonneg hδ0 (Real.exp_pos _).le) hCf0
  have hterm0 : ∀ T : Finset (Polymer N),
      (0:ℝ) ≤ δ * Real.exp (-(n : ℝ) / 2) * Cf
        * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) :=
    fun T => mul_nonneg hpre (sevenEighthsBudgetTerm_nonneg hβ s T)
  calc (∑ T ∈ activityBridgeCores (N := N) s r,
        |(profileWeight r a T - profileWeight r a' T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (profileCoreExponent μm β χ T s r a)|)
      ≤ ∑ T ∈ activityBridgeCores (N := N) s r,
          δ * Real.exp (-(n : ℝ) / 2) * Cf
            * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
              * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) :=
        Finset.sum_le_sum (fun T hT =>
          abs_profileBridgeColumnTerm_le μm hβ mχ hχabs hsmall
            mf hCf0 hCf hT hsep hδ0 h0 h1 h0' h1' hδ)
    _ ≤ ∑ T ∈ typedTouchingFamilies (N := N) s,
          δ * Real.exp (-(n : ℝ) / 2) * Cf
            * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
              * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun T _ _ => hterm0 T)
    _ = δ * Real.exp (-(n : ℝ) / 2) * Cf
          * ∑ T ∈ typedTouchingFamilies (N := N) s,
              Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
                * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η := by
        rw [Finset.mul_sum]
    _ ≤ δ * Real.exp (-(n : ℝ) / 2) * Cf
          * Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
        mul_le_mul_of_nonneg_left (sum_sevenEighthsTilt_one_le hβ hsmall s) hpre
    _ = δ * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
        ring

/-- **BRIDGE COLUMN, ABSOLUTE VALUE OF THE SUM**. -/
theorem abs_sum_profileBridgeColumn_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ) :
    |∑ T ∈ activityBridgeCores (N := N) s r,
        (profileWeight r a T - profileWeight r a' T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (profileCoreExponent μm β χ T s r a)|
      ≤ δ * Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) :=
  le_trans (Finset.abs_sum_le_sum_abs _ _)
    (sum_abs_profileBridgeColumn_le μm hβ mχ hχabs hsmall mf hCf0 hCf
      hsep hδ0 h0 h1 h0' h1' hδ)

/-! ## 55-B.8 — the two-term estimate and the CAPSTONE -/

/-- **TWO-TERM PROFILE ESTIMATE**: ledger + triangle inequality + the two
    column bounds, constants kept separate:
      |F(a) − F(a′)| ≤ δ·Cf·e^{−n/2}·(e^{6 D_s/113} + e^{4 D_s/113}).
    Written with the constants `3·D_s·(2/113)` and `2·D_s·(2/113)`.
    No `DependsOnlyOn f s`; 0 ≤ Cf derived; nothing divided by δ. -/
theorem abs_profileExpectation_sub_profileExpectation_le_two_terms
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)}
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ) :
    |profileExpectation μm β χ f s r a - profileExpectation μm β χ f s r a'|
      ≤ δ * Cf * Real.exp (-(n : ℝ) / 2)
          * (Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))) := by
  have hCf0 : 0 ≤ Cf := nonneg_of_abs_le_of_config hCf
  have hA := abs_sum_profileConnectorColumn_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf hsep hδ0 h0 h1 h0' h1' hδ
  have hB := abs_sum_profileBridgeColumn_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf hsep hδ0 h0 h1 h0' h1' hδ
  rw [profileExpectation_sub_eq_two_column_ledger
    μm hβ mχ hχabs hsmall f s r h0 h1 h0' h1']
  refine le_trans (abs_add _ _) ?_
  have hsum := add_le_add hA hB
  calc _ ≤ _ := hsum
    _ = _ := by ring

/-- **CAPSTONE 55 — STABILITY OF THE PROFILE-DAMPED FUNCTIONAL UNDER A
    UNIFORM MAJORANT OF THE PROFILE DIFFERENCE**: for profiles a, a′ in
    [0,1] with |a − a′| ≤ δ on the polymers touching r,
      |F(a) − F(a′)| ≤ δ·2·Cf·e^{6 D_s/113}·e^{−n/2},
    the Stone 54 constant, rate and regime. From the two-term estimate and
    e^{4 D_s/113} ≤ e^{6 D_s/113} (D_s ≥ 0). No `DependsOnlyOn f s`; no
    division by δ; no δ ≤ 1. -/
theorem abs_profileExpectation_sub_profileExpectation_le_local_exp_decay
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)}
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ) :
    |profileExpectation μm β χ f s r a - profileExpectation μm β χ f s r a'|
      ≤ δ * (2 * Cf)
          * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) := by
  have hCf0 : 0 ≤ Cf := nonneg_of_abs_le_of_config hCf
  have h2 := abs_profileExpectation_sub_profileExpectation_le_two_terms
    μm hβ mχ hχabs hsmall mf hCf hsep hδ0 h0 h1 h0' h1' hδ
  have hD : (0:ℝ) ≤ ((supportLinkFinset (N := N) s).card : ℝ) :=
    Nat.cast_nonneg _
  have hmono : Real.exp
      (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
      ≤ Real.exp
        (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
    refine Real.exp_le_exp.mpr ?_
    linarith
  have hpos : (0:ℝ) ≤ δ * Cf * Real.exp (-(n : ℝ) / 2) :=
    mul_nonneg (mul_nonneg hδ0 hCf0) (Real.exp_pos _).le
  have h6 : Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
      = Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
    congr 1
    ring
  rw [h6]
  refine le_trans h2 ?_
  calc δ * Cf * Real.exp (-(n : ℝ) / 2)
          * (Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)))
      ≤ δ * Cf * Real.exp (-(n : ℝ) / 2)
          * (Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hmono _) hpos
    _ = δ * (2 * Cf)
          * Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
          * Real.exp (-(n : ℝ) / 2) := by ring

/-! ## 55-B.9 — endpoints and the recovery of Stone 54 -/

/-- **Equal profiles through the capstone**: with δ = 0 the bound itself
    is 0 (nothing was divided by δ). -/
theorem profile_bound_self {s : Set (Link N)} (Cf : ℝ) (n : ℕ) :
    (0:ℝ) * (2 * Cf)
        * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
        * Real.exp (-(n : ℝ) / 2) = 0 := by
  ring

/-- **Constant profiles recover Stone 54** — an APPLICATION of the new
    capstone to a ≡ θ, a′ ≡ θ′, δ = |θ − θ′|, then the constant-profile
    identity `profileExpectation_const`; same statement and constant as
    `abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay_refined`
    (a corollary, not a replacement — the Stone 54 module is untouched). -/
theorem abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay_of_profile
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)}
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n)
    {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) :
    |activityDampedExpectation μm β χ f s r θ
        - activityDampedExpectation μm β χ f s r θ'|
      ≤ |θ - θ'| * (2 * Cf)
          * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) := by
  have h := abs_profileExpectation_sub_profileExpectation_le_local_exp_decay
    μm hβ mχ hχabs hsmall mf hCf hsep (a := fun _ => θ) (a' := fun _ => θ')
    (δ := |θ - θ'|) (abs_nonneg _) (fun _ => h0) (fun _ => h1) (fun _ => h0') (fun _ => h1')
    (fun _ _ => le_rfl)
  rwa [profileExpectation_const, profileExpectation_const] at h

/-- **Against the unit profile (Gibbs)**, with `DependsOnlyOn f s`: for a
    profile a in [0,1] with 1 − a ≤ δ on the polymers touching r,
      |F(a) − gibbs| ≤ δ·2·Cf·e^{6 D_s/113}·e^{−n/2}. -/
theorem abs_profileExpectation_sub_gibbsExpectation_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n)
    {a : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → 1 - a η ≤ δ) :
    |profileExpectation μm β χ f s r a - gibbsExpectation (N := N) μm β χ f|
      ≤ δ * (2 * Cf)
          * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) := by
  have h := abs_profileExpectation_sub_profileExpectation_le_local_exp_decay
    μm hβ mχ hχabs hsmall mf hCf hsep (a := a) (a' := fun _ => 1) (δ := δ) hδ0 h0 h1
    (fun _ => zero_le_one) (fun _ => le_rfl)
    (fun η hη => by
      show |a η - 1| ≤ δ
      rw [abs_sub_comm, abs_of_nonneg (by linarith [h1 η])]
      exact hδ η hη)
  rwa [profileExpectation_one μm hβ mχ hχabs hf mf hCf r] at h

/-- **Against the zero profile (Stone 51)**, no `DependsOnlyOn f s`: for a
    profile a in [0,1] with a ≤ δ on the polymers touching r,
      |F(a) − activityRestrictedExpectation| ≤ δ·2·Cf·e^{6 D_s/113}·e^{−n/2}. -/
theorem abs_profileExpectation_sub_activityRestrictedExpectation_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)}
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n)
    {a : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → a η ≤ δ) :
    |profileExpectation μm β χ f s r a - activityRestrictedExpectation μm β χ f s r|
      ≤ δ * (2 * Cf)
          * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) := by
  have h := abs_profileExpectation_sub_profileExpectation_le_local_exp_decay
    μm hβ mχ hχabs hsmall mf hCf hsep (a := a) (a' := fun _ => 0) (δ := δ) hδ0 h0 h1
    (fun _ => le_rfl) (fun _ => zero_le_one)
    (fun η hη => by
      show |a η - 0| ≤ δ
      rw [sub_zero, abs_of_nonneg (h0 η)]
      exact hδ η hη)
  rwa [profileExpectation_zero] at h

#print axioms kpProfileConnectorUnrootedCoeff_const
#print axioms kpProfileConnectorUnrootedCoeff_unit
#print axioms kpProfileConnector_inclusion_exclusion
#print axioms abs_kpProfileConnectorUnrootedCoeff_sub_le
#print axioms abs_kpProfileConnectorUnrootedCoeff_le
#print axioms profileConnector_const
#print axioms summable_kpProfileConnectorUnrootedCoeff
#print axioms profileCoreExponent_sub_full_eq_profileConnector
#print axioms profileCoreExponent_sub_eq_profileConnector_sub
#print axioms abs_profileConnector_sub_le_eroded
#print axioms abs_exp_profileCoreExponent_sub_le_decay_refined
#print axioms abs_profileConnectorColumnTerm_le
#print axioms sum_abs_profileConnectorColumn_le
#print axioms abs_sum_profileConnectorColumn_le
#print axioms abs_typedMarkedCoreWeight_mul_exp_profile_le
#print axioms nat_card_mul_abs_profileNormalizedTerm_le_bridge
#print axioms abs_profileBridgeColumnTerm_le
#print axioms sum_abs_profileBridgeColumn_le
#print axioms abs_sum_profileBridgeColumn_le
#print axioms abs_profileExpectation_sub_profileExpectation_le_two_terms
#print axioms abs_profileExpectation_sub_profileExpectation_le_local_exp_decay
#print axioms profile_bound_self
#print axioms abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay_of_profile
#print axioms abs_profileExpectation_sub_gibbsExpectation_le
#print axioms abs_profileExpectation_sub_activityRestrictedExpectation_le

end LatticeGauge
