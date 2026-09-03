/-
LatticeGauge/ActivityRestrictionColumnBounds.lean — PEDRA 51,
Gate 51-D: UNILATERAL CONNECTOR CONTROL AND THE TWO COLUMN BOUNDS
(architecture: Sol/GPT-5.6; execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): the exact
connector + bridge ledger of 51-C is turned into TWO SEPARATE
quantitative bounds, each decaying like exp(−n/2) under
WalkBarrierSeparated s r n, with prefactors depending ONLY on the
support s — never on the size of the remote region r.

Frozen quantitative ledger (per core T; report abbreviations):
  b_T = card(barrierLinkFinset T s)·(2/113),  m_T = familyTotalCard T,
  E_n = exp(−n/2),  D_s = card(supportLinkFinset s).

  * CONNECTOR COLUMN (allowed cores): the activity-restriction
    connector is the Stone-50 core connector with the EMPTY core on
    the remote side; its signed value obeys the UNILATERAL A12 tail
    (only the s-side barrier is charged), eroded by the mass of T
    alone: |C| ≤ exp(−(n−m_T)/2)·b_T. Hence
    |1 − e^C| ≤ E_n·exp(m_T/2 + 2 b_T), and the normalized weight
    costs exp(b_T): per core, E_n·Cf·halfTiltCoreBudgetTerm β 3 s T
    (κ = 3), summed by the A17 budget at κ+1 = 4: exp(8 D_s/113).
  * BRIDGE COLUMN: the geometric toll of 51-C pays exp(−n/2)
    through the half tilt; the normalized weight costs exp(b_T):
    per core, E_n·Cf·halfTiltCoreBudgetTerm β 1 s T (κ = 1), summed
    at κ+1 = 2: exp(4 D_s/113).

No hypothesis |C| ≤ 1 is assumed; the symmetric (two-sided)
Stone-50 exponential control is NOT used, because it charges the
remote side.

HARD HOLD (not here): the inequality for the full expectation
difference, the combination of the two columns, the constant 2,
the Stone-51 capstone, two Gibbs measures, modified action,
boundary conditions, weak/strong spatial mixing, thermodynamic
limit, infinite volume, continuum, mass gap, Clay. No
project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.ActivityRestrictionConnectorGeometry
import LatticeGauge.CovarianceNormalizedColumns

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## 51-D.1 — the empty core and the Stone-50 connector dress -/

/-- The empty core is a touching core of any region: compatibility
    and touching are vacuous over ∅. -/
theorem empty_mem_typedTouchingFamilies (r : Set (Link N)) :
    (∅ : Finset (Polymer N)) ∈ typedTouchingFamilies (N := N) r := by
  unfold typedTouchingFamilies
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · refine mem_typedCompatiblePolymerFamilies.mpr ?_
    intro η hη
    exact absurd hη (Finset.not_mem_empty η)
  · intro η hη
    exact absurd hη (Finset.not_mem_empty η)

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- The activity-restriction connector IS the Stone-50 core
    connector between T (at s) and the EMPTY core (at r):
    51-C's empty-core form, then definitional. -/
theorem activityRestrictionConnector_eq_coreConnectorSum_empty
    (β : ℝ) (χ : G → ℝ)
    (T : Finset (Polymer N))
    (s r : Set (Link N)) :
    activityRestrictionConnector μm β χ T s r
      = coreConnectorSum μm β χ T
          (∅ : Finset (Polymer N)) s r :=
  activityRestrictionConnector_eq_emptyCore μm β χ T s r

/-! ## 51-D.2 — the unilateral signed connector tail -/

/-- **UNILATERAL TAIL**: the signed core connector is bounded by
    the A12 tail charged on the s-side barrier ONLY (no minimum, no
    remote-side count). Route: open the two definitions, concrete
    KP, summability, `norm_tsum_le_tsum_norm`, then the local A12
    bound on the P side. -/
theorem abs_coreConnectorSum_le_local_P
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {q : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') q) :
    |coreConnectorSum μm β χ T T' s s'|
      ≤ Real.exp (-(q : ℝ) / 2)
          * (((barrierLinkFinset T s).card : ℝ) * (2/113)) := by
  unfold coreConnectorSum connectorClusterSum
  have hKP := abstractKP_of_beta_le_one_div_40000
    (N := N) μm hβ mχ hχabs hsmall
  have ha : ∀ γ : Polymer N, 0 ≤ ((γ.val.card : ℕ) : ℝ) :=
    fun γ => Nat.cast_nonneg _
  have hsum := summable_abs_kpConnectorUnrootedCoeff
    ha hKP (remoteAllowed (N := N) T s)
    (remoteAllowed (N := N) T' s')
  have h1 : ‖∑' k : ℕ, kpConnectorUnrootedCoeff (N := N) k
      (fun η => polymerWeight (N := N) μm β χ η.val)
      (remoteAllowed (N := N) T s)
      (remoteAllowed (N := N) T' s')‖
      ≤ ∑' k : ℕ, ‖kpConnectorUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s)
          (remoteAllowed (N := N) T' s')‖ := by
    refine norm_tsum_le_tsum_norm ?_
    simpa [Real.norm_eq_abs] using hsum
  simp only [Real.norm_eq_abs] at h1
  exact h1.trans (tsum_abs_kpConnector_le_local_P
    μm hβ mχ hχabs hsmall hwsep)

/-! ## 51-D.3 — unilateral erosion of the activity connector -/

/-- **UNILATERAL EROSION**: the separation of s and r at scale n
    erodes, on the barrier regions, only by the mass of T (the
    remote core is empty, of mass 0); the tail is charged on the
    s-side barrier only. -/
theorem abs_activityRestrictionConnector_le_eroded
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hsep : WalkBarrierSeparated (N := N) s r n) :
    |activityRestrictionConnector μm β χ T s r|
      ≤ Real.exp
          (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2)
        * (((barrierLinkFinset T s).card : ℝ) * (2/113)) := by
  have hero := walkBarrierSeparated_barrierRegions_sub_familyMass
    hT (empty_mem_typedTouchingFamilies r) hsep
  have hzero : familyTotalCard (∅ : Finset (Polymer N)) = 0 := by
    unfold familyTotalCard
    exact Finset.sum_empty
  rw [hzero, Nat.add_zero] at hero
  rw [activityRestrictionConnector_eq_coreConnectorSum_empty]
  exact abs_coreConnectorSum_le_local_P μm hβ mχ hχabs hsmall hero

/-! ## 51-D.4 — the unilateral exponential, no remote region -/

/-- **UNILATERAL EXPONENTIAL CONTROL**: |1 − e^C| ≤ E_n·exp(m_T/2
    + 2 b_T). The decay factor d = exp(−(n−m_T)/2) ≤ 1, the linear
    size q = b_T, the exponential cost B = 2 b_T; the erosion is
    repurchased at half mass. No |C| ≤ 1 assumed; nothing of r. -/
theorem abs_one_sub_exp_activityRestrictionConnector_le_eroded
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hsep : WalkBarrierSeparated (N := N) s r n) :
    |1 - Real.exp
        (activityRestrictionConnector μm β χ T s r)|
      ≤ Real.exp (-(n : ℝ) / 2)
        * Real.exp
            ((familyTotalCard T : ℝ) / 2
              + 2 * ((barrierLinkFinset T s).card : ℝ)
                  * (2/113)) := by
  have hC := abs_activityRestrictionConnector_le_eroded
    μm hβ mχ hχabs hsmall hT hsep
  have hd0 : (0:ℝ) ≤ Real.exp
      (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) :=
    (Real.exp_pos _).le
  have hd1 : Real.exp
      (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2) ≤ 1 := by
    rw [← Real.exp_zero]
    refine Real.exp_le_exp.mpr ?_
    have h0 : (0:ℝ) ≤ (((n - familyTotalCard T : ℕ)) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hq0 : (0:ℝ) ≤ ((barrierLinkFinset T s).card : ℝ) * (2/113) :=
    mul_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hmain := abs_exp_sub_one_le_decay_exp hd0 hd1 hq0 hC
    (le_refl (2 * (((barrierLinkFinset T s).card : ℝ) * (2/113))))
  have herode := exp_neg_nat_sub_half_le n (familyTotalCard T)
  rw [abs_sub_comm]
  calc |Real.exp (activityRestrictionConnector μm β χ T s r) - 1|
      ≤ Real.exp (-(((n - familyTotalCard T : ℕ)) : ℝ) / 2)
          * Real.exp
              (2 * (((barrierLinkFinset T s).card : ℝ) * (2/113))) :=
        hmain
    _ ≤ (Real.exp (-(n : ℝ) / 2)
          * Real.exp ((familyTotalCard T : ℝ) / 2))
          * Real.exp
              (2 * (((barrierLinkFinset T s).card : ℝ) * (2/113))) :=
        mul_le_mul_of_nonneg_right herode (Real.exp_pos _).le
    _ = Real.exp (-(n : ℝ) / 2)
        * Real.exp
            ((familyTotalCard T : ℝ) / 2
              + 2 * ((barrierLinkFinset T s).card : ℝ)
                  * (2/113)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-! ## 51-D.5 — the bridge to the normalized term -/

/-- **NORMALIZED BRIDGE**: core weight × e^{E_T} IS the Stone-50
    normalized term N_f(s,T) — the ratio identity read backwards
    through concrete KP. No denominator cancelled by hand. -/
theorem typedMarkedCoreWeight_mul_exp_full_eq_normalizedMarkedCoreTerm
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (f : Config N G → ℝ) (s : Set (Link N))
    (T : Finset (Polymer N)) :
    typedMarkedCoreWeight μm β χ f T
        * Real.exp (fullActivityCoreExponent μm β χ T s)
      = normalizedMarkedCoreTerm μm β χ f s T := by
  rw [normalizedMarkedCoreTerm_eq, coreRestrictedGas_def,
    typedPolymerGas_ratio_eq_exp_sub
      (fun γ => Nat.cast_nonneg _)
      (abstractKP_of_beta_le_one_div_40000 μm hβ mχ hχabs hsmall)
      (remoteAllowed (N := N) T s)]
  rfl

/-! ## 51-D.6 — pointwise bounds of the two columns -/

/-- **ALLOWED-CORE TERM, κ = 3**: normalized weight exp(b_T) ×
    unilateral exponential control exp(m_T/2 + 2 b_T) =
    exp(m_T/2 + 3 b_T): the half-tilt budget term at κ = 3. -/
theorem abs_activityAllowedCoreTerm_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ activityAllowedCores (N := N) s r)
    (hsep : WalkBarrierSeparated (N := N) s r n) :
    |typedMarkedCoreWeight μm β χ f T
        * (Real.exp (fullActivityCoreExponent μm β χ T s)
          * (1 - Real.exp
              (activityRestrictionConnector μm β χ T s r)))|
      ≤ Real.exp (-(n : ℝ) / 2) * Cf
          * halfTiltCoreBudgetTerm β 3 s T := by
  have hbridge :=
    typedMarkedCoreWeight_mul_exp_full_eq_normalizedMarkedCoreTerm
      μm hβ mχ hχabs hsmall f s T
  have hN := abs_normalizedMarkedCoreTerm_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf s T
  have hE := abs_one_sub_exp_activityRestrictionConnector_le_eroded
    μm hβ mχ hχabs hsmall (mem_activityAllowedCores.mp hT).1 hsep
  have hM : (0:ℝ) ≤ ∏ η ∈ T, mayerCoreMajorant β η :=
    Finset.prod_nonneg (fun η _ => mayerCoreMajorant_nonneg hβ η)
  have hb1 : (0:ℝ) ≤ Cf * Real.exp
      (((barrierLinkFinset T s).card : ℝ) * (2/113))
      * ∏ η ∈ T, mayerCoreMajorant β η :=
    mul_nonneg (mul_nonneg hCf0 (Real.exp_pos _).le) hM
  have hexp : Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
      * Real.exp ((familyTotalCard T : ℝ) / 2
          + 2 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
      = Real.exp ((familyTotalCard T : ℝ) / 2
          + 3 * ((barrierLinkFinset T s).card : ℝ) * (2/113)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, hbridge, abs_mul]
  calc |normalizedMarkedCoreTerm μm β χ f s T|
      * |1 - Real.exp (activityRestrictionConnector μm β χ T s r)|
      ≤ (Cf * Real.exp
            (((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T, mayerCoreMajorant β η)
        * (Real.exp (-(n : ℝ) / 2)
          * Real.exp ((familyTotalCard T : ℝ) / 2
              + 2 * ((barrierLinkFinset T s).card : ℝ)
                  * (2/113))) :=
        mul_le_mul hN hE (abs_nonneg _) hb1
    _ = Real.exp (-(n : ℝ) / 2) * Cf
          * halfTiltCoreBudgetTerm β 3 s T := by
        rw [halfTiltCoreBudgetTerm_eq, ← hexp]
        ring

/-- **BRIDGE-CORE TERM, κ = 1**: the geometric toll of 51-C pays
    exp(−n/2) through the half tilt (lam = 1/2); the normalized
    weight costs exp(b_T): the half-tilt budget term at κ = 1. -/
theorem abs_activityBridgeCoreTerm_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ activityBridgeCores (N := N) s r)
    (hsep : WalkBarrierSeparated (N := N) s r n) :
    |typedMarkedCoreWeight μm β χ f T
        * Real.exp (fullActivityCoreExponent μm β χ T s)|
      ≤ Real.exp (-(n : ℝ) / 2) * Cf
          * halfTiltCoreBudgetTerm β 1 s T := by
  have hne := activityBridgeCore_nonempty hT
  have hW := abs_coreWeight_le_exp_neg_tilt μm (lam := 1/2)
    (by norm_num) hβ mχ hχabs mf hCf0 hCf hne hsep
  have h := abs_normalizedMarkedCoreTerm_le_of_abs_le
    μm hβ mχ hχabs hsmall (s := s) hW
  rw [typedMarkedCoreWeight_mul_exp_full_eq_normalizedMarkedCoreTerm
    μm hβ mχ hχabs hsmall f s T]
  calc |normalizedMarkedCoreTerm μm β χ f s T|
      ≤ (Real.exp (-(1/2 : ℝ) * (n : ℝ))
          * (Cf * ∏ η ∈ T,
              massTiltActivity (1/2) (mayerCoreMajorant β) η))
        * Real.exp
            (((barrierLinkFinset T s).card : ℝ) * (2/113)) := h
    _ = Real.exp (-(n : ℝ) / 2) * Cf
          * halfTiltCoreBudgetTerm β 1 s T := by
        unfold halfTiltCoreBudgetTerm
        rw [one_mul,
          show -(1/2 : ℝ) * (n : ℝ) = -(n : ℝ) / 2 from by ring]
        ring

/-! ## 51-D.7 — the numerical budgets (A17 consumed; no recount) -/

/-- **κ = 3 budget**: 1/2 + 3·(8/113) = 161/226 ≤ 1; the sum of
    half-tilt budget terms at κ = 3 is at most exp(4·D_s·(2/113)). -/
theorem sum_halfTilt_three_le
    {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (s : Set (Link N)) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        halfTiltCoreBudgetTerm β 3 s T)
      ≤ Real.exp
          (4 * ((supportLinkFinset (N := N) s).card : ℝ)
            * (2/113)) := by
  have h := coreLocalBudget (lam := 1/2) (κ := 3)
    (by norm_num) (by norm_num) (by norm_num) hβ hsmall s
  calc (∑ T ∈ typedTouchingFamilies (N := N) s,
      halfTiltCoreBudgetTerm β 3 s T)
      ≤ Real.exp (((3:ℝ) + 1)
          * ((supportLinkFinset (N := N) s).card : ℝ)
          * (2/113)) := h
    _ = Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ)
          * (2/113)) := by
        rw [show ((3:ℝ) + 1) = 4 from by norm_num]

/-- **κ = 1 budget** (the generic A17 budget at κ = 1; named apart
    from the Stone-50 decay module, which is not imported). -/
theorem sum_halfTilt_one_le_bridgeColumn
    {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (s : Set (Link N)) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        halfTiltCoreBudgetTerm β 1 s T)
      ≤ Real.exp
          (2 * ((supportLinkFinset (N := N) s).card : ℝ)
            * (2/113)) := by
  have h := coreLocalBudget (lam := 1/2) (κ := 1)
    (by norm_num) (by norm_num) (by norm_num) hβ hsmall s
  calc (∑ T ∈ typedTouchingFamilies (N := N) s,
      halfTiltCoreBudgetTerm β 1 s T)
      ≤ Real.exp (((1:ℝ) + 1)
          * ((supportLinkFinset (N := N) s).card : ℝ)
          * (2/113)) := h
    _ = Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ)
          * (2/113)) := by
        rw [show ((1:ℝ) + 1) = 2 from by norm_num]

/-! ## 51-D.8 — CAPSTONES: the two column sums, separately -/

/-- **ALLOWED COLUMN SUM**: |Σ_allowed| ≤ E_n·Cf·exp(8 D_s/113).
    Triangle inequality, pointwise κ = 3 bound, inclusion into the
    touching cores (terms nonnegative), κ = 3 budget. -/
theorem abs_activityAllowedColumn_sum_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n) :
    |∑ T ∈ activityAllowedCores (N := N) s r,
        typedMarkedCoreWeight μm β χ f T
          * (Real.exp (fullActivityCoreExponent μm β χ T s)
            * (1 - Real.exp
                (activityRestrictionConnector μm β χ T s r)))|
      ≤ Real.exp (-(n : ℝ) / 2) * Cf
          * Real.exp
              (4 * ((supportLinkFinset (N := N) s).card : ℝ)
                * (2/113)) := by
  have hterm0 : ∀ T : Finset (Polymer N),
      (0:ℝ) ≤ Real.exp (-(n : ℝ) / 2) * Cf
        * halfTiltCoreBudgetTerm β 3 s T :=
    fun T => mul_nonneg (mul_nonneg (Real.exp_pos _).le hCf0)
      (halfTiltCoreBudgetTerm_nonneg hβ 3 s T)
  calc |∑ T ∈ activityAllowedCores (N := N) s r,
      typedMarkedCoreWeight μm β χ f T
        * (Real.exp (fullActivityCoreExponent μm β χ T s)
          * (1 - Real.exp
              (activityRestrictionConnector μm β χ T s r)))|
      ≤ ∑ T ∈ activityAllowedCores (N := N) s r,
          |typedMarkedCoreWeight μm β χ f T
            * (Real.exp (fullActivityCoreExponent μm β χ T s)
              * (1 - Real.exp
                  (activityRestrictionConnector μm β χ T s r)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ activityAllowedCores (N := N) s r,
          Real.exp (-(n : ℝ) / 2) * Cf
            * halfTiltCoreBudgetTerm β 3 s T :=
        Finset.sum_le_sum (fun T hT =>
          abs_activityAllowedCoreTerm_le μm hβ mχ hχabs hsmall
            mf hCf0 hCf hT hsep)
    _ ≤ ∑ T ∈ typedTouchingFamilies (N := N) s,
          Real.exp (-(n : ℝ) / 2) * Cf
            * halfTiltCoreBudgetTerm β 3 s T :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
          (fun T _ _ => hterm0 T)
    _ = Real.exp (-(n : ℝ) / 2) * Cf
        * ∑ T ∈ typedTouchingFamilies (N := N) s,
            halfTiltCoreBudgetTerm β 3 s T := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(n : ℝ) / 2) * Cf
        * Real.exp
            (4 * ((supportLinkFinset (N := N) s).card : ℝ)
              * (2/113)) :=
        mul_le_mul_of_nonneg_left
          (sum_halfTilt_three_le hβ hsmall s)
          (mul_nonneg (Real.exp_pos _).le hCf0)

/-- **BRIDGE COLUMN SUM**: |Σ_bridge| ≤ E_n·Cf·exp(4 D_s/113).
    Triangle inequality, pointwise κ = 1 bound, inclusion into the
    touching cores, κ = 1 budget. -/
theorem abs_activityBridgeColumn_sum_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {s r : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s r n) :
    |∑ T ∈ activityBridgeCores (N := N) s r,
        typedMarkedCoreWeight μm β χ f T
          * Real.exp (fullActivityCoreExponent μm β χ T s)|
      ≤ Real.exp (-(n : ℝ) / 2) * Cf
          * Real.exp
              (2 * ((supportLinkFinset (N := N) s).card : ℝ)
                * (2/113)) := by
  have hterm0 : ∀ T : Finset (Polymer N),
      (0:ℝ) ≤ Real.exp (-(n : ℝ) / 2) * Cf
        * halfTiltCoreBudgetTerm β 1 s T :=
    fun T => mul_nonneg (mul_nonneg (Real.exp_pos _).le hCf0)
      (halfTiltCoreBudgetTerm_nonneg hβ 1 s T)
  calc |∑ T ∈ activityBridgeCores (N := N) s r,
      typedMarkedCoreWeight μm β χ f T
        * Real.exp (fullActivityCoreExponent μm β χ T s)|
      ≤ ∑ T ∈ activityBridgeCores (N := N) s r,
          |typedMarkedCoreWeight μm β χ f T
            * Real.exp (fullActivityCoreExponent μm β χ T s)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ T ∈ activityBridgeCores (N := N) s r,
          Real.exp (-(n : ℝ) / 2) * Cf
            * halfTiltCoreBudgetTerm β 1 s T :=
        Finset.sum_le_sum (fun T hT =>
          abs_activityBridgeCoreTerm_le μm hβ mχ hχabs hsmall
            mf hCf0 hCf hT hsep)
    _ ≤ ∑ T ∈ typedTouchingFamilies (N := N) s,
          Real.exp (-(n : ℝ) / 2) * Cf
            * halfTiltCoreBudgetTerm β 1 s T :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
          (fun T _ _ => hterm0 T)
    _ = Real.exp (-(n : ℝ) / 2) * Cf
        * ∑ T ∈ typedTouchingFamilies (N := N) s,
            halfTiltCoreBudgetTerm β 1 s T := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(n : ℝ) / 2) * Cf
        * Real.exp
            (2 * ((supportLinkFinset (N := N) s).card : ℝ)
              * (2/113)) :=
        mul_le_mul_of_nonneg_left
          (sum_halfTilt_one_le_bridgeColumn hβ hsmall s)
          (mul_nonneg (Real.exp_pos _).le hCf0)

#print axioms abs_one_sub_exp_activityRestrictionConnector_le_eroded
#print axioms abs_activityAllowedColumn_sum_le
#print axioms abs_activityBridgeColumn_sum_le

end LatticeGauge
