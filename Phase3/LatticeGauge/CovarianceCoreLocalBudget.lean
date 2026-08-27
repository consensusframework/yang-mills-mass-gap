/-
LatticeGauge/CovarianceCoreLocalBudget.lean — PEDRA 50, Gate
50-A17: THE LOCAL BUDGET OF THE CORES (architecture: Sol;
execution: Fable).

The sum over ALL cores touching a support stays controlled by
the LOCAL size of that support, even after including a mass tilt
lam, the exponential of the VARIABLE barrier, and the cost of
the core's own polymers. The lattice volume never appears on the
right-hand side; no cardinality of Finset.univ survives in any
bound. RULINGS honoured: the weight is the PURE Mayer majorant
(2β)^card·e^{α·card} — the physical 45/46 theorem is NEVER
applied to it; the strictly necessary TWIN is built explicitly
from the published geometry (size slices, 16·64^{2m} count,
kpQ/kpR, finite geometric sum) — doubled walks and the polymer
count are consumed, not reopened. Generic budget:
  0 ≤ lam, 0 ≤ κ, lam + κ·(8/113) ≤ 1  ⟹
  Σ_T exp(κ·|barrier(T,s)|·2/113)·Π massTilt(lam)(mayer)
    ≤ exp((κ+1)·|supportLinks(s)|·2/113),
with the visible origin: |barrier(T,s)| ≤ |s|_links + 4·mass(T)
and lam·mass + κ·(8/113)·mass ≤ mass. Numeric corollary at
lam = 1/2, κ = 1 (1/2 + 8/113 < 1). No |connectorSum| ≤ 1
hypothesis anywhere.

NOT here (hard hold): no polymerWeight in the main capstone, no
physical KP applied to the Mayer majorant, no observables f/g,
no covariance/numerator, no connector, no exp(C) − 1, no A18
pairing, no dependence on N on the right side except through the
given local support, no thermodynamic limit, no continuum, no
mass gap, no Clay claim. A0–A16 stay frozen; 45/46 not
refactored.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.CovarianceRestrictedGasLocalization

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## A17.1 — the support as an exact Finset (barrierLinkFinset
    with the empty core, reused — no duplication) -/

noncomputable def supportLinkFinset (s : Set (Link N)) :
    Finset (Link N) :=
  barrierLinkFinset (∅ : Finset (Polymer N)) s

theorem mem_supportLinkFinset {s : Set (Link N)} {ℓ : Link N} :
    ℓ ∈ supportLinkFinset s ↔ ℓ ∈ s := by
  unfold supportLinkFinset
  rw [mem_barrierLinkFinset]
  unfold barrierRegion
  constructor
  · rintro (h | h)
    · exact h
    · obtain ⟨t, ht, -⟩ := h
      exact absurd ht (Finset.not_mem_empty t)
  · exact fun h => Or.inl h

/-! ## A17.2 — the pure-Mayer per-link twin (geometry and count
    of 45/46 consumed; the PHYSICAL slice theorem never applied) -/

theorem massTilt_one_mayer_eq (β : ℝ) (η : Polymer N) :
    massTiltActivity 1 (mayerCoreMajorant β) η
      = (2*β) ^ (η.val).card
          * Real.exp (((η.val).card : ℕ) : ℝ) := by
  unfold massTiltActivity mayerCoreMajorant
  rw [one_mul]
  ring

/-- Generic typed ↔ raw bridge for any per-block weight (the
    A12 subtype route with an arbitrary F). -/
theorem typed_link_sum_eq_raw_fn (ℓ : Link N)
    (F : Finset (Site N × Dir × Dir) → ℝ) :
    (∑ η ∈ typedPolymersUsingLink (N := N) ℓ, F η.val)
      = ∑ D ∈ polymersUsingLink (N := N) ℓ, F D := by
  have hfe : (allPlaquettePolymers N).filter
      (fun D => ℓ ∈ blockLinkSupport (N := N) D)
      = polymersUsingLink (N := N) ℓ := by
    unfold polymersUsingLink
    exact Finset.filter_congr
      (fun D _ => Iff.symm mem_blockLinkFinset)
  calc (∑ η ∈ typedPolymersUsingLink (N := N) ℓ, F η.val)
      = ∑ η : Polymer N,
          if ℓ ∈ blockLinkSupport (N := N) η.val then F η.val
          else 0 :=
        Finset.sum_filter _ _
    _ = ∑ D ∈ allPlaquettePolymers N,
          if ℓ ∈ blockLinkSupport (N := N) D then F D else 0 :=
        (Finset.sum_subtype (allPlaquettePolymers N)
          (fun _ => Iff.rfl)
          (fun D => if ℓ ∈ blockLinkSupport (N := N) D then F D
            else 0)).symm
    _ = ∑ D ∈ (allPlaquettePolymers N).filter
          (fun D => ℓ ∈ blockLinkSupport (N := N) D), F D :=
        (Finset.sum_filter _ _).symm
    _ = ∑ D ∈ polymersUsingLink (N := N) ℓ, F D := by rw [hfe]

/-- Generic size decomposition (the published partition of the
    rooted-link polymers, for any weight). -/
theorem rootedLink_sum_decompose_fn (ℓ : Link N)
    (F : Finset (Site N × Dir × Dir) → ℝ) :
    (∑ D ∈ polymersUsingLink (N := N) ℓ, F D)
      = ∑ m ∈ Finset.range (admissiblePlaquettes N).card,
          ∑ D ∈ rootedLinkPolymersOfSize ℓ m, F D := by
  rw [polymersUsingLink_eq_biUnion ℓ]
  exact Finset.sum_biUnion
    (rootedLinkPolymersOfSize_pairwiseDisjoint ℓ)

/-- The slice normalization for the PURE Mayer weight at α = 1:
    count bound × constant slice weight = 16·q·r^m exactly. -/
theorem mayer_slice_norm (β : ℝ) (m : ℕ) :
    ((16 * 64 ^ (2*m) : ℕ) : ℝ)
        * ((2*β) ^ (m+1) * Real.exp (((m+1 : ℕ)) : ℝ))
      = 16 * kpQ β 1 * kpR β 1 ^ m := by
  have hexp : Real.exp (((m+1 : ℕ)) : ℝ) = Real.exp 1 ^ (m+1) := by
    rw [← Real.exp_nat_mul, mul_one]
  have hmerge : (2*β) ^ (m+1) * Real.exp 1 ^ (m+1)
      = (2*β*Real.exp 1) ^ (m+1) := (mul_pow _ _ _).symm
  have hcast : ((16 * 64 ^ (2*m) : ℕ) : ℝ) = 16 * (4096:ℝ) ^ m := by
    push_cast
    rw [pow_mul]
    norm_num
  unfold kpR kpQ
  rw [hcast, hexp, hmerge]
  generalize (2*β*Real.exp 1 : ℝ) = q
  rw [pow_succ, mul_pow]
  ring

/-- The pure-Mayer slice bound (the weight is CONSTANT on the
    slice; the 45b count enters as a pure cardinality). -/
theorem mayer_slice_le {β : ℝ} (hβ : 0 ≤ β) (ℓ : Link N) (m : ℕ) :
    (∑ D ∈ rootedLinkPolymersOfSize (N := N) ℓ m,
        (2*β) ^ D.card * Real.exp ((D.card : ℕ) : ℝ))
      ≤ 16 * kpQ β 1 * kpR β 1 ^ m := by
  have hconst : ∀ D ∈ rootedLinkPolymersOfSize (N := N) ℓ m,
      (2*β) ^ D.card * Real.exp ((D.card : ℕ) : ℝ)
        = (2*β) ^ (m+1) * Real.exp (((m+1 : ℕ)) : ℝ) := by
    intro D hD
    rw [(mem_rootedLinkPolymersOfSize.mp hD).2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hw : (0:ℝ) ≤ (2*β) ^ (m+1) * Real.exp (((m+1 : ℕ)) : ℝ) :=
    mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le
  have hcard : (((rootedLinkPolymersOfSize (N := N) ℓ m).card : ℕ) : ℝ)
      ≤ ((16 * 64 ^ (2*m) : ℕ) : ℝ) :=
    Nat.cast_le.mpr (rootedLinkPolymersOfSize_card_le ℓ m)
  calc (((rootedLinkPolymersOfSize (N := N) ℓ m).card : ℕ) : ℝ)
        * ((2*β) ^ (m+1) * Real.exp (((m+1 : ℕ)) : ℝ))
      ≤ ((16 * 64 ^ (2*m) : ℕ) : ℝ)
          * ((2*β) ^ (m+1) * Real.exp (((m+1 : ℕ)) : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard hw
    _ = 16 * kpQ β 1 * kpR β 1 ^ m := mayer_slice_norm β m

/-- **A17.2 CAPSTONE (per link, α = 1)** — measure-free: no μm,
    no χ, no group anywhere. -/
theorem mayer_link_sum_le_two_div_113 {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000) (ℓ : Link N) :
    (∑ η ∈ typedPolymersUsingLink (N := N) ℓ,
        massTiltActivity 1 (mayerCoreMajorant β) η)
      ≤ 2 / 113 := by
  have heq : (∑ η ∈ typedPolymersUsingLink (N := N) ℓ,
      massTiltActivity 1 (mayerCoreMajorant β) η)
      = ∑ D ∈ polymersUsingLink (N := N) ℓ,
          (2*β) ^ D.card * Real.exp ((D.card : ℕ) : ℝ) := by
    rw [Finset.sum_congr rfl
      (fun η _ => massTilt_one_mayer_eq β η)]
    exact typed_link_sum_eq_raw_fn ℓ
      (fun D => (2*β) ^ D.card * Real.exp ((D.card : ℕ) : ℝ))
  rw [heq, rootedLink_sum_decompose_fn ℓ
    (fun D => (2*β) ^ D.card * Real.exp ((D.card : ℕ) : ℝ))]
  have hq0 := kpQ_nonneg hβ 1
  have hr0 := kpR_nonneg hβ 1
  have hr1 := kpR_lt_one_of_small_beta hβ hsmall
  calc (∑ m ∈ Finset.range (admissiblePlaquettes N).card,
      ∑ D ∈ rootedLinkPolymersOfSize ℓ m,
        (2*β) ^ D.card * Real.exp ((D.card : ℕ) : ℝ))
      ≤ ∑ m ∈ Finset.range (admissiblePlaquettes N).card,
          16 * kpQ β 1 * kpR β 1 ^ m :=
        Finset.sum_le_sum (fun m _ => mayer_slice_le hβ ℓ m)
    _ = 16 * kpQ β 1
          * ∑ m ∈ Finset.range (admissiblePlaquettes N).card,
              kpR β 1 ^ m := by
        rw [Finset.mul_sum]
    _ ≤ 16 * kpQ β 1 * (1 / (1 - kpR β 1)) :=
        mul_le_mul_of_nonneg_left
          (geom_sum_le_inv_one_sub hr0 hr1 _)
          (by linarith)
    _ = 16 * kpQ β 1 / (1 - kpR β 1) := by rw [mul_one_div]
    _ ≤ 2 / 113 := kpPerLinkScalar_le_two_div_113 hβ hsmall

/-! ## A17.3 — the polymers touching the support -/

noncomputable def typedTouchingPolymers (s : Set (Link N)) :
    Finset (Polymer N) :=
  Finset.univ.filter
    (fun η => typedTouchesSupport (N := N) η s)

theorem mem_typedTouchingPolymers {s : Set (Link N)}
    {η : Polymer N} :
    η ∈ typedTouchingPolymers s
      ↔ typedTouchesSupport (N := N) η s := by
  unfold typedTouchingPolymers
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem typedTouchingPolymers_subset_linkCover
    (s : Set (Link N)) :
    typedTouchingPolymers s
      ⊆ (supportLinkFinset s).biUnion typedPolymersUsingLink := by
  intro η hη
  have h' : ¬ Disjoint (blockLinkSupport (N := N) η.val) s :=
    mem_typedTouchingPolymers.mp hη
  rw [Set.not_disjoint_iff] at h'
  obtain ⟨ℓ, hℓη, hℓs⟩ := h'
  rw [Finset.mem_biUnion]
  exact ⟨ℓ, mem_supportLinkFinset.mpr hℓs,
    mem_typedPolymersUsingLink.mpr hℓη⟩

theorem sum_touching_massTilt_le {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000) (s : Set (Link N)) :
    (∑ η ∈ typedTouchingPolymers s,
        massTiltActivity 1 (mayerCoreMajorant β) η)
      ≤ ((supportLinkFinset s).card : ℝ) * (2 / 113) := by
  calc (∑ η ∈ typedTouchingPolymers s,
      massTiltActivity 1 (mayerCoreMajorant β) η)
      ≤ ∑ ℓ ∈ supportLinkFinset s,
          ∑ η ∈ typedPolymersUsingLink ℓ,
            massTiltActivity 1 (mayerCoreMajorant β) η :=
        sum_le_sum_over_cover
          (typedTouchingPolymers_subset_linkCover s)
          (fun η _ => massTiltActivity_nonneg
            (mayerCoreMajorant_nonneg hβ) η)
    _ ≤ (supportLinkFinset s).card • ((2 : ℝ) / 113) :=
        Finset.sum_le_card_nsmul _ _ _
          (fun ℓ _ => mayer_link_sum_le_two_div_113 hβ hsmall ℓ)
    _ = ((supportLinkFinset s).card : ℝ) * (2 / 113) :=
        nsmul_eq_mul _ _

/-! ## A17.4 — the sum of core families (compatibility forgotten
    ONLY as a majorant; powerset + prod_one_add + 1 + x ≤ e^x;
    the number of families never appears as a bare cardinality) -/

theorem sum_touchingFamilies_prod_le {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000) (s : Set (Link N)) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        ∏ η ∈ T, massTiltActivity 1 (mayerCoreMajorant β) η)
      ≤ Real.exp
          (((supportLinkFinset s).card : ℝ) * (2 / 113)) := by
  have ha : ∀ η : Polymer N,
      0 ≤ massTiltActivity 1 (mayerCoreMajorant β) η :=
    massTiltActivity_nonneg (mayerCoreMajorant_nonneg hβ)
  have hsub : typedTouchingFamilies (N := N) s
      ⊆ (typedTouchingPolymers s).powerset := by
    intro T hT
    rw [Finset.mem_powerset]
    intro η hη
    exact mem_typedTouchingPolymers.mpr
      ((Finset.mem_filter.mp hT).2 η hη)
  calc (∑ T ∈ typedTouchingFamilies (N := N) s,
      ∏ η ∈ T, massTiltActivity 1 (mayerCoreMajorant β) η)
      ≤ ∑ T ∈ (typedTouchingPolymers s).powerset,
          ∏ η ∈ T, massTiltActivity 1 (mayerCoreMajorant β) η :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun T _ _ => Finset.prod_nonneg (fun η _ => ha η))
    _ = ∏ η ∈ typedTouchingPolymers s,
          (1 + massTiltActivity 1 (mayerCoreMajorant β) η) :=
        (Finset.prod_one_add _).symm
    _ ≤ ∏ η ∈ typedTouchingPolymers s,
          Real.exp (massTiltActivity 1 (mayerCoreMajorant β) η) :=
        Finset.prod_le_prod
          (fun η _ => by linarith [ha η])
          (fun η _ => by
            have := Real.add_one_le_exp
              (massTiltActivity 1 (mayerCoreMajorant β) η)
            linarith)
    _ = Real.exp (∑ η ∈ typedTouchingPolymers s,
          massTiltActivity 1 (mayerCoreMajorant β) η) :=
        (Real.exp_sum _ _).symm
    _ ≤ Real.exp
          (((supportLinkFinset s).card : ℝ) * (2 / 113)) :=
        Real.exp_le_exp.mpr (sum_touching_massTilt_le hβ hsmall s)

/-! ## A17.5 — the barrier cardinality is support + mass -/

theorem barrierLinkFinset_card_le_support_add_mass
    (T : Finset (Polymer N)) (s : Set (Link N)) :
    (barrierLinkFinset T s).card
      ≤ (supportLinkFinset s).card + 4 * familyTotalCard T := by
  have hsub : barrierLinkFinset T s
      ⊆ supportLinkFinset s
        ∪ T.biUnion (fun η => blockLinkFinset (N := N) η.val) := by
    intro ℓ hℓ
    have h := mem_barrierLinkFinset.mp hℓ
    rw [Finset.mem_union]
    rcases h with h | h
    · exact Or.inl (mem_supportLinkFinset.mpr h)
    · obtain ⟨t, htT, hℓt⟩ := h
      exact Or.inr (Finset.mem_biUnion.mpr
        ⟨t, htT, mem_blockLinkFinset.mpr hℓt⟩)
  calc (barrierLinkFinset T s).card
      ≤ (supportLinkFinset s
          ∪ T.biUnion (fun η => blockLinkFinset (N := N) η.val)).card :=
        Finset.card_le_card hsub
    _ ≤ (supportLinkFinset s).card
          + (T.biUnion (fun η => blockLinkFinset (N := N) η.val)).card :=
        Finset.card_union_le _ _
    _ ≤ (supportLinkFinset s).card
          + ∑ η ∈ T, (blockLinkFinset (N := N) η.val).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ (supportLinkFinset s).card + ∑ η ∈ T, 4 * (η.val).card :=
        Nat.add_le_add_left
          (Finset.sum_le_sum
            (fun η _ => blockLinkFinset_card_le η.val)) _
    _ = (supportLinkFinset s).card + 4 * familyTotalCard T := by
        rw [← Finset.mul_sum]
        rfl

/-! ## A17.6 — THE GENERIC BUDGET -/

/-- **CAPSTONE 50-A17**: under 0 ≤ lam, 0 ≤ κ and the budget
    lam + κ·(8/113) ≤ 1, the tilted core sum with the variable
    barrier exponential is controlled by the LOCAL support:
    the visible origin is |barrier| ≤ |s| + 4·mass and
    lam·mass + κ·(8/113)·mass ≤ mass, after which everything is
    dominated by the α = 1 tilt closed in A17.4. -/
theorem coreLocalBudget {lam κ : ℝ} (hlam : 0 ≤ lam)
    (hκ : 0 ≤ κ) (hbudget : lam + κ * (8/113) ≤ 1)
    {β : ℝ} (hβ : 0 ≤ β) (hsmall : β ≤ (1 : ℝ) / 40000)
    (s : Set (Link N)) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        Real.exp (κ * ((barrierLinkFinset T s).card : ℝ)
            * (2/113))
          * ∏ η ∈ T,
              massTiltActivity lam (mayerCoreMajorant β) η)
      ≤ Real.exp ((κ + 1)
          * ((supportLinkFinset s).card : ℝ) * (2/113)) := by
  have hterm : ∀ T ∈ typedTouchingFamilies (N := N) s,
      Real.exp (κ * ((barrierLinkFinset T s).card : ℝ) * (2/113))
        * ∏ η ∈ T, massTiltActivity lam (mayerCoreMajorant β) η
      ≤ Real.exp (κ * ((supportLinkFinset s).card : ℝ) * (2/113))
        * ∏ η ∈ T, massTiltActivity 1 (mayerCoreMajorant β) η := by
    intro T _
    rw [prod_family_massTiltActivity lam (mayerCoreMajorant β) T,
      prod_family_massTiltActivity 1 (mayerCoreMajorant β) T]
    have hM : (0:ℝ) ≤ (familyTotalCard T : ℝ) := Nat.cast_nonneg _
    have hprod : (0:ℝ) ≤ ∏ η ∈ T, mayerCoreMajorant β η :=
      Finset.prod_nonneg
        (fun η _ => mayerCoreMajorant_nonneg hβ η)
    have hB : ((barrierLinkFinset T s).card : ℝ)
        ≤ ((supportLinkFinset s).card : ℝ)
          + 4 * (familyTotalCard T : ℝ) := by
      exact_mod_cast
        barrierLinkFinset_card_le_support_add_mass T s
    have hexp : Real.exp (κ * ((barrierLinkFinset T s).card : ℝ)
          * (2/113))
        * Real.exp (lam * (familyTotalCard T : ℝ))
        ≤ Real.exp (κ * ((supportLinkFinset s).card : ℝ)
            * (2/113))
          * Real.exp (1 * (familyTotalCard T : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [mul_le_mul_of_nonneg_left hB hκ,
        mul_le_mul_of_nonneg_right hbudget hM]
    calc Real.exp (κ * ((barrierLinkFinset T s).card : ℝ)
          * (2/113))
        * (Real.exp (lam * (familyTotalCard T : ℝ))
          * ∏ η ∈ T, mayerCoreMajorant β η)
        = Real.exp (κ * ((barrierLinkFinset T s).card : ℝ)
            * (2/113))
          * Real.exp (lam * (familyTotalCard T : ℝ))
          * ∏ η ∈ T, mayerCoreMajorant β η := by ring
      _ ≤ Real.exp (κ * ((supportLinkFinset s).card : ℝ)
            * (2/113))
          * Real.exp (1 * (familyTotalCard T : ℝ))
          * ∏ η ∈ T, mayerCoreMajorant β η :=
          mul_le_mul_of_nonneg_right hexp hprod
      _ = Real.exp (κ * ((supportLinkFinset s).card : ℝ)
            * (2/113))
          * (Real.exp (1 * (familyTotalCard T : ℝ))
            * ∏ η ∈ T, mayerCoreMajorant β η) := by ring
  calc (∑ T ∈ typedTouchingFamilies (N := N) s,
      Real.exp (κ * ((barrierLinkFinset T s).card : ℝ) * (2/113))
        * ∏ η ∈ T, massTiltActivity lam (mayerCoreMajorant β) η)
      ≤ ∑ T ∈ typedTouchingFamilies (N := N) s,
          Real.exp (κ * ((supportLinkFinset s).card : ℝ)
              * (2/113))
            * ∏ η ∈ T,
                massTiltActivity 1 (mayerCoreMajorant β) η :=
        Finset.sum_le_sum hterm
    _ = Real.exp (κ * ((supportLinkFinset s).card : ℝ) * (2/113))
          * ∑ T ∈ typedTouchingFamilies (N := N) s,
              ∏ η ∈ T,
                massTiltActivity 1 (mayerCoreMajorant β) η := by
        rw [← Finset.mul_sum]
    _ ≤ Real.exp (κ * ((supportLinkFinset s).card : ℝ) * (2/113))
          * Real.exp
              (((supportLinkFinset s).card : ℝ) * (2/113)) :=
        mul_le_mul_of_nonneg_left
          (sum_touchingFamilies_prod_le hβ hsmall s)
          (Real.exp_pos _).le
    _ = Real.exp ((κ + 1)
          * ((supportLinkFinset s).card : ℝ) * (2/113)) := by
        rw [← Real.exp_add,
          show κ * ((supportLinkFinset s).card : ℝ) * (2/113)
              + ((supportLinkFinset s).card : ℝ) * (2/113)
            = (κ + 1) * ((supportLinkFinset s).card : ℝ)
                * (2/113) from by ring]

/-! ## Numeric corollary (bridge regime: lam = 1/2, κ = 1;
    1/2 + 8/113 = 129/226 < 1) -/

theorem coreLocalBudget_bridge {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000) (s : Set (Link N)) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T,
              massTiltActivity (1/2) (mayerCoreMajorant β) η)
      ≤ Real.exp
          (2 * ((supportLinkFinset s).card : ℝ) * (2/113)) := by
  have h := coreLocalBudget (lam := 1/2) (κ := 1)
    (by norm_num) (by norm_num) (by norm_num) hβ hsmall s
  simpa [one_mul, show (1:ℝ) + 1 = 2 from by norm_num] using h

#print axioms sum_touchingFamilies_prod_le
#print axioms coreLocalBudget

end LatticeGauge
