/-
LatticeGauge/ActivityRestrictionLedger.lean — PEDRA 51,
Gate 51-B: THE EXACT TWO-COLUMN LEDGER
(architecture: Sol/GPT-5.6; execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): the difference
between the original Gibbs expectation and the normalized
activity-restricted polymer functional of 51-A is written as an
EXACT finite identity in ℝ, separated into exactly two columns:

  * region-allowed cores — cores of the touching families all of
    whose members avoid the remote region r — contribute the core
    weight times the DIFFERENCE of two exponentials (the full
    cluster exponent and the region-restricted cluster exponent);
  * bridge cores — cores containing some polymer that touches r —
    contribute their full term integrally.

Ingredients: the exact partition of the touching cores into
allowed + bridge (finite complement, no new geometry); the
composition law for nested activity restrictions
(P after Q = P ∧ Q); two transparent exponent abbreviations; the
regional gas ratio as an exponential (KP inherited by
monotonicity from the region-restricted base activity; the ratio
identity comes from the exponential representation — no
denominator cancelled, no nonvanishing assumed); the exponential
form of the restricted functional; the allowed + bridge split of
the published expectation; and the ledger itself by finite
algebra.

No estimate enters. Exact two-column ledger for the difference
between the original Gibbs expectation and the normalized
activity-restricted polymer functional.

HARD HOLD (not here): connector cluster sums, inclusion–exclusion,
identification of the exponent difference with a connector,
Real.exp_sub between the two exponents, absolute values or
inequalities, barrier regions, walk separation, distance, bridge
mass, tilt, erosion, constants, exponential bounds, thermodynamic
limit, infinite volume, continuum, mass gap. No project-local
scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.ActivityRestrictedObservableGas

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## 51-B.1 — the exact partition of the touching cores -/

/-- The region-allowed cores: touching cores of s all of whose
    members are r-allowed. -/
noncomputable def activityAllowedCores (s r : Set (Link N)) :
    Finset (Finset (Polymer N)) :=
  (typedTouchingFamilies (N := N) s).filter
    (fun T => ∀ η ∈ T, regionAllowed (N := N) r η)

/-- The bridge cores: the exact complement inside the touching
    cores of s — cores for which NOT every member is r-allowed. -/
noncomputable def activityBridgeCores (s r : Set (Link N)) :
    Finset (Finset (Polymer N)) :=
  (typedTouchingFamilies (N := N) s).filter
    (fun T => ¬ ∀ η ∈ T, regionAllowed (N := N) r η)

theorem mem_activityAllowedCores {s r : Set (Link N)}
    {T : Finset (Polymer N)} :
    T ∈ activityAllowedCores (N := N) s r
      ↔ T ∈ typedTouchingFamilies (N := N) s
        ∧ ∀ η ∈ T, regionAllowed (N := N) r η :=
  Finset.mem_filter

theorem mem_activityBridgeCores {s r : Set (Link N)}
    {T : Finset (Polymer N)} :
    T ∈ activityBridgeCores (N := N) s r
      ↔ T ∈ typedTouchingFamilies (N := N) s
        ∧ ¬ ∀ η ∈ T, regionAllowed (N := N) r η :=
  Finset.mem_filter

/-- **Semantic reading of the bridge cores**: a touching core is a
    bridge core iff some member touches the remote region r
    (`regionAllowed_iff` plus classical logic; no new geometric
    concept). -/
theorem mem_activityBridgeCores_iff_exists_touches
    {s r : Set (Link N)} {T : Finset (Polymer N)} :
    T ∈ activityBridgeCores (N := N) s r
      ↔ T ∈ typedTouchingFamilies (N := N) s
        ∧ ∃ η ∈ T, typedTouchesSupport (N := N) η r := by
  rw [mem_activityBridgeCores]
  constructor
  · rintro ⟨hT, hnot⟩
    refine ⟨hT, ?_⟩
    by_contra hcon
    apply hnot
    intro η hη
    rw [regionAllowed_iff]
    exact fun ht => hcon ⟨η, hη, ht⟩
  · rintro ⟨hT, η, hη, ht⟩
    refine ⟨hT, fun hall => ?_⟩
    exact (regionAllowed_iff.mp (hall η hη)) ht

theorem activityAllowed_union_bridge (s r : Set (Link N)) :
    activityAllowedCores (N := N) s r
        ∪ activityBridgeCores (N := N) s r
      = typedTouchingFamilies (N := N) s := by
  unfold activityAllowedCores activityBridgeCores
  ext T
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    by_cases hall : ∀ η ∈ T, regionAllowed (N := N) r η
    · exact Or.inl ⟨h, hall⟩
    · exact Or.inr ⟨h, hall⟩

theorem activityAllowed_disjoint_bridge (s r : Set (Link N)) :
    Disjoint (activityAllowedCores (N := N) s r)
      (activityBridgeCores (N := N) s r) := by
  rw [Finset.disjoint_left]
  intro T hA hB
  exact (mem_activityBridgeCores.mp hB).2
    (mem_activityAllowedCores.mp hA).2

/-- Generic split of any additive sum over the touching cores of s
    into region-allowed + bridge. -/
theorem sum_touchingFamilies_eq_activityAllowed_add_bridge
    {M : Type*} [AddCommMonoid M] (s r : Set (Link N))
    (F : Finset (Polymer N) → M) :
    (∑ T ∈ typedTouchingFamilies (N := N) s, F T)
      = (∑ T ∈ activityAllowedCores (N := N) s r, F T)
        + ∑ T ∈ activityBridgeCores (N := N) s r, F T := by
  rw [← activityAllowed_union_bridge s r,
    Finset.sum_union (activityAllowed_disjoint_bridge s r)]

/-! ## 51-B.2 — composition of nested activity restrictions -/

/-- **Composition law**: restricting first by Q and then by P is
    the single restriction by P ∧ Q. Pure extensionality and case
    analysis on the two predicates. -/
theorem restrictedActivity_comp
    (z : Polymer N → ℝ)
    (P Q : Polymer N → Prop) :
    restrictedActivity (restrictedActivity z Q) P
      = restrictedActivity z (fun η => P η ∧ Q η) := by
  funext η
  simp only [restrictedActivity]
  by_cases hP : P η
  · by_cases hQ : Q η
    · rw [if_pos hP, if_pos hQ, if_pos (And.intro hP hQ)]
    · rw [if_pos hP, if_neg hQ,
        if_neg (fun h : P η ∧ Q η => hQ h.2)]
  · rw [if_neg hP, if_neg (fun h : P η ∧ Q η => hP h.1)]

/-- **Specialization**: the region restriction followed by the
    core-relative restriction is the single restriction by
    `remoteRegionAllowed` (definitionally the conjunction). -/
theorem restrictedActivity_regionAllowed_remoteAllowed
    (z : Polymer N → ℝ) (T : Finset (Polymer N))
    (s r : Set (Link N)) :
    restrictedActivity
        (restrictedActivity z (regionAllowed (N := N) r))
        (remoteAllowed T s)
      = restrictedActivity z (remoteRegionAllowed (N := N) T s r) :=
  restrictedActivity_comp z (remoteAllowed T s) (regionAllowed (N := N) r)

/-! ## 51-B.3 — two transparent exponents -/

/-- The full core exponent: cluster sum of the activity restricted
    to the remote-allowed polymers of the core T, minus the vacuum
    cluster sum. Transparent abbreviation of the exponent already
    present in the published expectation theorem. -/
noncomputable def fullActivityCoreExponent (β : ℝ) (χ : G → ℝ)
    (T : Finset (Polymer N)) (s : Set (Link N)) : ℝ :=
  (∑' n, kpSignedUnrootedCoeff n
      (restrictedActivity
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed T s)))
    - ∑' n, kpSignedUnrootedCoeff (N := N) n
        (fun η => polymerWeight (N := N) μm β χ η.val)

/-- The regional core exponent: cluster sum of the activity
    restricted to the remote-AND-region-allowed polymers, minus
    the cluster sum of the region-restricted activity. No
    interpretation of the difference with the full exponent is
    attached here. -/
noncomputable def regionActivityCoreExponent (β : ℝ) (χ : G → ℝ)
    (T : Finset (Polymer N)) (s r : Set (Link N)) : ℝ :=
  (∑' n, kpSignedUnrootedCoeff n
      (restrictedActivity
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteRegionAllowed (N := N) T s r)))
    - ∑' n, kpSignedUnrootedCoeff n
        (restrictedActivity
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (regionAllowed (N := N) r))

/-! ## 51-B.4 — the regional gas ratio as an exponential -/

/-- **Regional gas ratio**: with the region-restricted activity as
    base, KP is inherited by monotonicity, the published ratio
    identity applies, and the nested restriction composes. No
    denominator is cancelled; nonvanishing is never assumed. -/
theorem regionActivityGas_ratio_eq_exp
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r : Set (Link N)) :
    typedPolymerGas (N := N)
        (restrictedActivity
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteRegionAllowed (N := N) T s r))
      / typedPolymerGas (N := N)
          (restrictedActivity
            (fun η => polymerWeight (N := N) μm β χ η.val)
            (regionAllowed (N := N) r))
      = Real.exp (regionActivityCoreExponent μm β χ T s r) := by
  have hKP :=
    abstractKP_restrictedActivity (regionAllowed (N := N) r)
      (abstractKP_of_beta_le_one_div_40000 μm hβ mχ hχabs hsmall)
  have h := typedPolymerGas_ratio_eq_exp_sub
    (fun γ => Nat.cast_nonneg _) hKP (remoteAllowed T s)
  rw [restrictedActivity_regionAllowed_remoteAllowed] at h
  unfold regionActivityCoreExponent
  exact h

/-! ## 51-B.5 — exponential form of the restricted functional -/

/-- **Exponential form of the activity-restricted functional**:
    the 51-A finite regrouping, divided termwise by the restricted
    gas, with each ratio an exponential of the regional exponent.
    No `DependsOnlyOn`, measurability or bound on f is needed: this
    side is the polymer functional of 51-A. -/
theorem activityRestrictedExpectation_eq_sum_core_mul_exp
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (f : Config N G → ℝ) (s r : Set (Link N)) :
    activityRestrictedExpectation μm β χ f s r
      = ∑ T ∈ activityAllowedCores (N := N) s r,
          typedMarkedCoreWeight μm β χ f T
            * Real.exp (regionActivityCoreExponent μm β χ T s r) := by
  unfold activityRestrictedExpectation activityRestrictedPolymerGas
    activityAllowedCores
  rw [activityRestrictedMarkedGas_eq_sum_core_mul_restricted
      μm β χ f s r,
    Finset.sum_div]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [mul_div_assoc]
  congr 1
  exact regionActivityGas_ratio_eq_exp μm hβ mχ hχabs hsmall T s r

/-! ## 51-B.6 — the original expectation, allowed + bridge -/

/-- **Allowed + bridge split of the published expectation**: the
    A3 capstone summed over the two exact columns of cores. The
    hypotheses are exactly those of the published theorem. -/
theorem gibbsExpectation_eq_activityAllowed_add_bridge
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (r : Set (Link N)) :
    gibbsExpectation (N := N) μm β χ f
      = (∑ T ∈ activityAllowedCores (N := N) s r,
          typedMarkedCoreWeight μm β χ f T
            * Real.exp (fullActivityCoreExponent μm β χ T s))
        + ∑ T ∈ activityBridgeCores (N := N) s r,
          typedMarkedCoreWeight μm β χ f T
            * Real.exp (fullActivityCoreExponent μm β χ T s) := by
  rw [gibbsExpectation_eq_sum_core_mul_exp μm hβ mχ hχabs hsmall
    hf mf hCf]
  unfold fullActivityCoreExponent
  exact sum_touchingFamilies_eq_activityAllowed_add_bridge s r
    (fun T => typedMarkedCoreWeight μm β χ f T
      * Real.exp
          ((∑' n, kpSignedUnrootedCoeff n
              (restrictedActivity
                (fun η => polymerWeight (N := N) μm β χ η.val)
                (remoteAllowed T s)))
            - ∑' n, kpSignedUnrootedCoeff (N := N) n
                (fun η => polymerWeight (N := N) μm β χ η.val)))

/-! ## 51-B.7 — CAPSTONE: the two-column ledger -/

/-- **CAPSTONE 51-B — THE EXACT TWO-COLUMN LEDGER**: the difference
    between the original Gibbs expectation and the normalized
    activity-restricted polymer functional is, exactly,
      (allowed column) core weight × (exp full − exp regional)
    + (bridge column)  core weight × exp full.
    Exactly two columns; no third term; finite algebra only. -/
theorem gibbsExpectation_sub_activityRestrictedExpectation_eq_two_column_ledger
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
  rw [gibbsExpectation_eq_activityAllowed_add_bridge μm hβ mχ hχabs
      hsmall hf mf hCf r,
    activityRestrictedExpectation_eq_sum_core_mul_exp μm hβ mχ hχabs
      hsmall f s r,
    add_sub_right_comm, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun T _ => ?_)
  exact (mul_sub _ _ _).symm

#print axioms restrictedActivity_comp
#print axioms activityRestrictedExpectation_eq_sum_core_mul_exp
#print axioms gibbsExpectation_sub_activityRestrictedExpectation_eq_two_column_ledger

end LatticeGauge
