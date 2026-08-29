/-
LatticeGauge/KPConnectorEnvelopeLocalization.lean — PEDRA 50,
Gate 50-A12: ENVELOPE LOCALIZATION — EVERY BARRIER LINK PAYS
2/113 (architecture: Sol; execution: Fable).

The concrete forbidden-root envelope of A11 becomes a LOCAL
geometric prefactor: every forbidden root touches the barrier
(A6), so the roots are covered by the barrier links; each link
carries at most the Stone-45/46 rooted geometric sum, whose
scalar under β ≤ 1/40000 is at most 2/113 (visible arithmetic:
10000·q ≤ 2; no optimality claimed for 2/113). Combined with
A11:
  Σ'ₖ |connectorₖ(w_β)| ≤ e^{-n/2} · card(barrier links) · 2/113,
in the P and Q versions and the symmetric min capstone.
Overcounting roots that touch several links is deliberate and
legitimate by nonnegativity. This is still a CONNECTOR TAIL —
NOT covariance, NOT correlation decay, NOT clustering.

NOT here (hard hold): no covariance, no Z[fg]·Z − Z[f]·Z[g]
wiring, no sum over the cores T/T', no typedMarkedCoreWeight
estimate, no bound on the number of touching cores, no
improvement of β or of the rate 1/2, no polymer recount, no
doubled walks or geometric series redone, no SimpleGraph.dist,
no volume-uniformity claim without a barrier hypothesis, no
thermodynamic limit, no continuum, no mass gap, no Clay claim.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.KPConnectorTiltSpecialization

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## A12.1 — the barrier as an exact Finset of links -/

noncomputable def barrierLinkFinset (T : Finset (Polymer N))
    (s : Set (Link N)) : Finset (Link N) :=
  Finset.univ.filter (fun ℓ => ℓ ∈ barrierRegion (N := N) T s)

theorem mem_barrierLinkFinset {T : Finset (Polymer N)}
    {s : Set (Link N)} {ℓ : Link N} :
    ℓ ∈ barrierLinkFinset T s ↔ ℓ ∈ barrierRegion (N := N) T s := by
  unfold barrierLinkFinset
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-! ## A12.2 — forbidden roots and per-link roots (typed) -/

noncomputable def forbiddenRootFinset (T : Finset (Polymer N))
    (s : Set (Link N)) : Finset (Polymer N) :=
  Finset.univ.filter (fun η => ¬ remoteAllowed (N := N) T s η)

theorem mem_forbiddenRootFinset {T : Finset (Polymer N)}
    {s : Set (Link N)} {η : Polymer N} :
    η ∈ forbiddenRootFinset T s
      ↔ ¬ remoteAllowed (N := N) T s η := by
  unfold forbiddenRootFinset
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

noncomputable def typedPolymersUsingLink (ℓ : Link N) :
    Finset (Polymer N) :=
  Finset.univ.filter
    (fun η => ℓ ∈ blockLinkSupport (N := N) η.val)

theorem mem_typedPolymersUsingLink {ℓ : Link N} {η : Polymer N} :
    η ∈ typedPolymersUsingLink ℓ
      ↔ ℓ ∈ blockLinkSupport (N := N) η.val := by
  unfold typedPolymersUsingLink
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- **GEOMETRIC LOCALIZATION CAPSTONE**: every forbidden root is
    covered by the barrier links (A6's contact theorem consumed —
    not_remoteAllowed_iff never reopened by hand). -/
theorem forbiddenRootFinset_subset_linkCover
    (T : Finset (Polymer N)) (s : Set (Link N)) :
    forbiddenRootFinset T s
      ⊆ (barrierLinkFinset T s).biUnion typedPolymersUsingLink := by
  intro η hη
  have hmeet := forbidden_meets_barrierRegion
    (mem_forbiddenRootFinset.mp hη)
  rw [Set.not_disjoint_iff] at hmeet
  obtain ⟨ℓ, hℓη, hℓbar⟩ := hmeet
  rw [Finset.mem_biUnion]
  exact ⟨ℓ, mem_barrierLinkFinset.mpr hℓbar,
    mem_typedPolymersUsingLink.mpr hℓη⟩

/-! ## A12.3 — the typed ↔ raw bridge per link (the canonical
    subtype route of 47c-C0; no new equivalence built) -/

theorem typed_link_sum_eq_raw (β : ℝ) (χ : G → ℝ) (ℓ : Link N) :
    (∑ η ∈ typedPolymersUsingLink ℓ,
        |polymerWeight (N := N) μm β χ η.val|
          * Real.exp ((η.val.card : ℕ) : ℝ))
      = ∑ D ∈ polymersUsingLink ℓ,
          kpActivityWeight μm β χ 1 D := by
  have hfe : (allPlaquettePolymers N).filter
      (fun D => ℓ ∈ blockLinkSupport (N := N) D)
      = polymersUsingLink (N := N) ℓ := by
    unfold polymersUsingLink
    exact Finset.filter_congr
      (fun D _ => Iff.symm mem_blockLinkFinset)
  calc (∑ η ∈ typedPolymersUsingLink ℓ,
      |polymerWeight (N := N) μm β χ η.val|
        * Real.exp ((η.val.card : ℕ) : ℝ))
      = ∑ η : Polymer N,
          if ℓ ∈ blockLinkSupport (N := N) η.val then
            |polymerWeight (N := N) μm β χ η.val|
              * Real.exp ((η.val.card : ℕ) : ℝ)
          else 0 :=
        Finset.sum_filter _ _
    _ = ∑ D ∈ allPlaquettePolymers N,
          if ℓ ∈ blockLinkSupport (N := N) D then
            |polymerWeight (N := N) μm β χ D|
              * Real.exp ((D.card : ℕ) : ℝ)
          else 0 :=
        (Finset.sum_subtype (allPlaquettePolymers N)
          (fun _ => Iff.rfl)
          (fun D => if ℓ ∈ blockLinkSupport (N := N) D then
            |polymerWeight (N := N) μm β χ D|
              * Real.exp ((D.card : ℕ) : ℝ)
          else 0)).symm
    _ = ∑ D ∈ (allPlaquettePolymers N).filter
          (fun D => ℓ ∈ blockLinkSupport (N := N) D),
          |polymerWeight (N := N) μm β χ D|
            * Real.exp ((D.card : ℕ) : ℝ) :=
        (Finset.sum_filter _ _).symm
    _ = ∑ D ∈ polymersUsingLink ℓ,
          kpActivityWeight μm β χ 1 D := by
        rw [hfe]
        refine Finset.sum_congr rfl (fun D _ => ?_)
        unfold kpActivityWeight
        rw [one_mul]

/-! ## A12.4 — the uniform price of one link (visible
    arithmetic: 10000·q ≤ 2; no optimality claimed) -/

theorem kpPerLinkScalar_le_two_div_113 {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000) :
    16 * kpQ β 1 / (1 - kpR β 1) ≤ 2 / 113 := by
  have hq := kpQ_le_one_div_5000 hβ hsmall
  have hq0 := kpQ_nonneg hβ 1
  have hrle := kpR_le_512_div_625 hβ hsmall
  have hpos : 0 < 1 - kpR β 1 := by linarith
  rw [div_le_iff₀ hpos]
  unfold kpR
  have h10000 : 10000 * kpQ β 1 ≤ 2 := by linarith
  linarith

/-- **Each link pays at most 2/113** (Stone 45/46 consumed
    through rootedLink_kp_sum_geometric_bound; nothing redone). -/
theorem typed_link_sum_le_two_div_113
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) (ℓ : Link N) :
    (∑ η ∈ typedPolymersUsingLink ℓ,
        |polymerWeight (N := N) μm β χ η.val|
          * Real.exp ((η.val.card : ℕ) : ℝ))
      ≤ 2 / 113 := by
  rw [typed_link_sum_eq_raw μm β χ ℓ]
  exact (rootedLink_kp_sum_geometric_bound μm hβ mχ hχabs
    (kpR_lt_one_of_small_beta hβ hsmall) ℓ).trans
    (kpPerLinkScalar_le_two_div_113 hβ hsmall)

/-! ## A12.5 — localization of the envelope (deliberate,
    legitimate overcounting by nonnegativity) -/

theorem kpForbiddenRootEnvelope_le_barrierLinkCount
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s : Set (Link N)) :
    (∑ γ₀ : Polymer N,
        if remoteAllowed (N := N) T s γ₀ then 0
        else |polymerWeight (N := N) μm β χ γ₀.val|
          * Real.exp ((γ₀.val.card : ℕ) : ℝ))
      ≤ ((barrierLinkFinset T s).card : ℝ) * (2 / 113) := by
  have h1 : (∑ γ₀ : Polymer N,
      if remoteAllowed (N := N) T s γ₀ then 0
      else |polymerWeight (N := N) μm β χ γ₀.val|
        * Real.exp ((γ₀.val.card : ℕ) : ℝ))
      = ∑ η ∈ forbiddenRootFinset T s,
          |polymerWeight (N := N) μm β χ η.val|
            * Real.exp ((η.val.card : ℕ) : ℝ) := by
    unfold forbiddenRootFinset
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun γ₀ _ => ?_)
    by_cases h : remoteAllowed (N := N) T s γ₀
    · rw [if_pos h, if_neg (not_not_intro h)]
    · rw [if_neg h, if_pos h]
  calc (∑ γ₀ : Polymer N,
      if remoteAllowed (N := N) T s γ₀ then 0
      else |polymerWeight (N := N) μm β χ γ₀.val|
        * Real.exp ((γ₀.val.card : ℕ) : ℝ))
      = ∑ η ∈ forbiddenRootFinset T s,
          |polymerWeight (N := N) μm β χ η.val|
            * Real.exp ((η.val.card : ℕ) : ℝ) := h1
    _ ≤ ∑ ℓ ∈ barrierLinkFinset T s,
          ∑ η ∈ typedPolymersUsingLink ℓ,
            |polymerWeight (N := N) μm β χ η.val|
              * Real.exp ((η.val.card : ℕ) : ℝ) :=
        sum_le_sum_over_cover
          (forbiddenRootFinset_subset_linkCover T s)
          (fun η _ => mul_nonneg (abs_nonneg _)
            (Real.exp_pos _).le)
    _ ≤ (barrierLinkFinset T s).card • ((2 : ℝ) / 113) :=
        Finset.sum_le_card_nsmul _ _ _
          (fun ℓ _ => typed_link_sum_le_two_div_113
            μm hβ mχ hχabs hsmall ℓ)
    _ = ((barrierLinkFinset T s).card : ℝ) * (2 / 113) :=
        nsmul_eq_mul _ _

/-! ## A12.6 — the LOCAL tails (A11 + A12.5, nothing else) -/

/-- **Local tail, P side**. -/
theorem tsum_abs_kpConnector_le_local_P
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    (∑' k : ℕ, |kpConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s)
        (remoteAllowed (N := N) T' s')|)
      ≤ Real.exp (-(n : ℝ)/2)
          * (((barrierLinkFinset T s).card : ℝ) * (2 / 113)) :=
  le_trans
    (tsum_abs_kpConnector_polymerWeight_le_exp_neg_half
      μm hβ mχ hχabs hsmall hwsep)
    (mul_le_mul_of_nonneg_left
      (kpForbiddenRootEnvelope_le_barrierLinkCount
        μm hβ mχ hχabs hsmall T s)
      (Real.exp_pos _).le)

/-- **Local tail, Q side**. -/
theorem tsum_abs_kpConnector_le_local_Q
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    (∑' k : ℕ, |kpConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s)
        (remoteAllowed (N := N) T' s')|)
      ≤ Real.exp (-(n : ℝ)/2)
          * (((barrierLinkFinset T' s').card : ℝ) * (2 / 113)) :=
  le_trans
    (tsum_abs_kpConnector_polymerWeight_le_exp_neg_half_Q
      μm hβ mχ hχabs hsmall hwsep)
    (mul_le_mul_of_nonneg_left
      (kpForbiddenRootEnvelope_le_barrierLinkCount
        μm hβ mχ hχabs hsmall T' s')
      (Real.exp_pos _).le)

/-! ## A12.7 — the symmetric capstone (min from the two proved
    inequalities only; the envelope analysis is not duplicated) -/

/-- **CAPSTONE 50-A12**: the connector tail pays e^{-n/2} times
    the SMALLER barrier, at 2/113 per link. -/
theorem tsum_abs_kpConnector_le_local_min
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    (∑' k : ℕ, |kpConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s)
        (remoteAllowed (N := N) T' s')|)
      ≤ Real.exp (-(n : ℝ)/2)
          * ((min (barrierLinkFinset T s).card
              (barrierLinkFinset T' s').card : ℕ) : ℝ)
          * (2 / 113) := by
  rcases le_total (barrierLinkFinset T s).card
    (barrierLinkFinset T' s').card with hle | hle
  · rw [min_eq_left hle]
    refine le_trans (tsum_abs_kpConnector_le_local_P
      μm hβ mχ hχabs hsmall hwsep) (le_of_eq ?_)
    ring
  · rw [min_eq_right hle]
    refine le_trans (tsum_abs_kpConnector_le_local_Q
      μm hβ mχ hχabs hsmall hwsep) (le_of_eq ?_)
    ring

#print axioms forbiddenRootFinset_subset_linkCover
#print axioms kpForbiddenRootEnvelope_le_barrierLinkCount
#print axioms tsum_abs_kpConnector_le_local_P
#print axioms tsum_abs_kpConnector_le_local_min

end LatticeGauge
