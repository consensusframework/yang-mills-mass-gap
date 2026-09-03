/-
LatticeGauge/ActivityRestrictionConnectorGeometry.lean — PEDRA 51,
Gate 51-C: THE CONNECTOR IDENTIFICATION AND THE BRIDGE GEOMETRY
(architecture: Sol/GPT-5.6; execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): the two-column
ledger of 51-B is turned into a usable scientific structure, still
without any estimate:

  * the ORIENTED difference of the two core exponents of an
    allowed core is EXACTLY the connector cluster sum between the
    core-relative barrier (remoteAllowed T s) and the regional
    suppression (regionAllowed r):
        E^r_T − E_T = C_{T,r},
    with E_T = S_P − S_0, E^r_T = S_{P∧Q} − S_Q and
    C_{T,r} = S_0 − S_P − S_Q + S_{P∧Q} (cluster-sum
    inclusion–exclusion, consumed); the sign is not inverted;
  * hence the exponential column factors exactly:
        e^{E_T} − e^{E^r_T} = e^{E_T}(1 − e^{C_{T,r}});
  * every bridge core contains a polymer touching BOTH s and r
    (the witness of 51-B's semantic reading, inserted into the
    bridgeCore of the covariance wiring — no silent choice);
  * hence, under WalkBarrierSeparated s r n, the geometric mass
    toll n ≤ familyTotalCard T (purely geometric: no β, χ, μm,
    activity, tilt or exponential);
  * CAPSTONE: the 51-B ledger rewritten as the exact
    connector + bridge ledger.

The connector defined here is a connector of clusters between two
barriers. It is NOT a covariance, a linear response, a derivative,
a modified Gibbs measure or a boundary condition.

HARD HOLD (not here): any bound on the connector, tsum_abs, local
connector bounds, 2/113, the 1/2 tilt rate, massTiltActivity,
coreLocalBudget, separation erosion, bounds on |exp C − 1|,
majorized sums, constants, decay conclusions, weak/strong spatial
mixing, thermodynamic limit, infinite volume, continuum, mass gap.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.ActivityRestrictionLedger
import LatticeGauge.ConnectorClusters
import LatticeGauge.CovarianceBridgeMass

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## 51-C.1 — the regional predicate as an empty-core barrier -/

/-- **Extensional empty-core bridge**: the regional predicate IS
    the core-relative predicate of the empty core (funext + propext
    over the 51-A pointwise bridge; the semantics of `remoteAllowed`
    is not reproved). -/
theorem regionAllowed_eq_remoteAllowed_empty (r : Set (Link N)) :
    regionAllowed (N := N) r
      = remoteAllowed (N := N) (∅ : Finset (Polymer N)) r := by
  funext η
  exact propext (regionAllowed_iff_remoteAllowed_empty r η)

/-! ## 51-C.2 — the connector of the activity restriction -/

/-- The connector cluster sum between the core-relative barrier
    (remote-allowed for T at s) and the regional suppression
    (r-allowed). A connector of clusters between two barriers —
    nothing more is claimed. -/
noncomputable def activityRestrictionConnector
    (β : ℝ) (χ : G → ℝ)
    (T : Finset (Polymer N))
    (s r : Set (Link N)) : ℝ :=
  connectorClusterSum (N := N)
    (fun η => polymerWeight (N := N) μm β χ η.val)
    (remoteAllowed (N := N) T s)
    (regionAllowed (N := N) r)

/-! ## 51-C.3 — the empty-core form -/

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- The connector in the two-barrier dress demanded by the
    double-barrier machinery: the regional barrier is the empty
    core's barrier. Coefficients are not opened. -/
theorem activityRestrictionConnector_eq_emptyCore
    (β : ℝ) (χ : G → ℝ) (T : Finset (Polymer N))
    (s r : Set (Link N)) :
    activityRestrictionConnector μm β χ T s r
      = connectorClusterSum (N := N)
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s)
          (remoteAllowed (N := N)
            (∅ : Finset (Polymer N)) r) := by
  unfold activityRestrictionConnector
  rw [regionAllowed_eq_remoteAllowed_empty]

/-! ## 51-C.4 — the oriented exponent identity -/

/-- **ORIENTED IDENTITY**: regional exponent minus full exponent
    IS the connector. Route: concrete KP → cluster-sum
    inclusion–exclusion → composition of the nested restriction
    (51-B) → exact algebra. The cross-ratio theorem is not used. -/
theorem regionActivityCoreExponent_sub_full_eq_activityRestrictionConnector
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r : Set (Link N)) :
    regionActivityCoreExponent μm β χ T s r
        - fullActivityCoreExponent μm β χ T s
      = activityRestrictionConnector μm β χ T s r := by
  have hIE := clusterSum_inclusion_exclusion
    (fun γ => Nat.cast_nonneg _)
    (abstractKP_of_beta_le_one_div_40000 μm hβ mχ hχabs hsmall)
    (remoteAllowed (N := N) T s) (regionAllowed (N := N) r)
  have hcomp :
      restrictedActivity
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (fun η => remoteAllowed (N := N) T s η
            ∧ regionAllowed (N := N) r η)
        = restrictedActivity
            (fun η => polymerWeight (N := N) μm β χ η.val)
            (remoteRegionAllowed (N := N) T s r) :=
    (restrictedActivity_comp
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s)
        (regionAllowed (N := N) r)).symm.trans
      (restrictedActivity_regionAllowed_remoteAllowed
        (fun η => polymerWeight (N := N) μm β χ η.val) T s r)
  rw [hcomp] at hIE
  unfold regionActivityCoreExponent fullActivityCoreExponent
    activityRestrictionConnector
  rw [← hIE]
  ring

/-! ## 51-C.5 — exact factorization of the exponential column -/

/-- **EXACT FACTORIZATION**: e^{E_T} − e^{E^r_T}
    = e^{E_T}(1 − e^{C_{T,r}}). Oriented identity + `Real.exp_add`;
    exact algebra only, no absolute value, no inequality. -/
theorem exp_full_sub_exp_region_eq_activityRestrictionConnector
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r : Set (Link N)) :
    Real.exp (fullActivityCoreExponent μm β χ T s)
        - Real.exp (regionActivityCoreExponent μm β χ T s r)
      = Real.exp (fullActivityCoreExponent μm β χ T s)
          * (1 - Real.exp
              (activityRestrictionConnector μm β χ T s r)) := by
  have hC :=
    regionActivityCoreExponent_sub_full_eq_activityRestrictionConnector
      μm hβ mχ hχabs hsmall T s r
  have hregion : regionActivityCoreExponent μm β χ T s r
      = fullActivityCoreExponent μm β χ T s
        + activityRestrictionConnector μm β χ T s r := by
    rw [← hC]
    ring
  rw [hregion, Real.exp_add]
  ring

/-! ## 51-C.6 — the geometric witness of the bridge column -/

/-- **BRIDGE WITNESS**: a bridge core has a member touching BOTH s
    (every member of a touching core touches s) and r (the 51-B
    semantic reading); that same member lies in `bridgeCore T s r`.
    No silent choice, no extra disjointness hypothesis. -/
theorem activityBridgeCore_nonempty
    {s r : Set (Link N)}
    {T : Finset (Polymer N)}
    (hT : T ∈ activityBridgeCores (N := N) s r) :
    (bridgeCore T s r).Nonempty := by
  obtain ⟨hTfam, η, hη, hr⟩ :=
    mem_activityBridgeCores_iff_exists_touches.mp hT
  have hs : typedTouchesSupport (N := N) η s :=
    (Finset.mem_filter.mp hTfam).2 η hη
  exact ⟨η, mem_bridgeCore.mpr ⟨hη, hs, hr⟩⟩

/-! ## 51-C.7 — the geometric mass toll -/

/-- **GEOMETRIC MASS TOLL**: under walk-barrier separation of s
    and r at scale n, every bridge core carries total mass at least
    n. Purely geometric — consumed from the A14 bridge-mass lemmas
    (`bridgeCore_sum_card_ge`, `bridgeCore_sum_le_familyTotalCard`),
    the two constituents of `bridge_n_le_familyTotalCard`. -/
theorem activityBridgeCore_familyTotalCard_ge
    {s r : Set (Link N)}
    {T : Finset (Polymer N)}
    {n : ℕ}
    (hT : T ∈ activityBridgeCores (N := N) s r)
    (hsep : WalkBarrierSeparated (N := N) s r n) :
    n ≤ familyTotalCard T :=
  le_trans
    (bridgeCore_sum_card_ge (activityBridgeCore_nonempty hT) hsep)
    (bridgeCore_sum_le_familyTotalCard T s r)

/-! ## 51-C.8 — CAPSTONE: the connector + bridge ledger -/

/-- **CAPSTONE 51-C — THE EXACT CONNECTOR + BRIDGE LEDGER**: the
    51-B two-column ledger with the allowed column factored through
    the connector, termwise; the bridge column preserved integrally.
    Exactly two columns; no estimate. -/
theorem gibbsExpectation_sub_activityRestrictedExpectation_eq_connector_bridge_ledger
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
            * (Real.exp
                (fullActivityCoreExponent μm β χ T s)
              * (1 - Real.exp
                  (activityRestrictionConnector
                    μm β χ T s r))))
        + ∑ T ∈ activityBridgeCores (N := N) s r,
          typedMarkedCoreWeight μm β χ f T
            * Real.exp
                (fullActivityCoreExponent μm β χ T s) := by
  rw [gibbsExpectation_sub_activityRestrictedExpectation_eq_two_column_ledger
    μm hβ mχ hχabs hsmall hf mf hCf r]
  congr 1
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [exp_full_sub_exp_region_eq_activityRestrictionConnector
    μm hβ mχ hχabs hsmall T s r]

#print axioms regionActivityCoreExponent_sub_full_eq_activityRestrictionConnector
#print axioms activityBridgeCore_familyTotalCard_ge
#print axioms gibbsExpectation_sub_activityRestrictedExpectation_eq_connector_bridge_ledger

end LatticeGauge
