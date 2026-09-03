/-
LatticeGauge/ActivityRestrictedObservableGas.lean — PEDRA 51,
Gate 51-A: THE HONEST WHOLE-FAMILY RESTRICTION
(architecture: Sol/GPT-5.6; execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): the restriction
must hit the WHOLE family before any fibering — core and remote
part alike. Restricting only the remote gas would let a core
polymer that touches the forbidden region r slip through the
turnstile inside the coat. This gate builds:

  * regionAllowed r — the allowed predicate for a remote region,
    with its empty-core bridge to remoteAllowed;
  * activityRestrictedPolymerGas — the gas of the r-restricted
    activity (purely polymeric; NOT the partition function of a
    new physical theory);
  * activityRestrictedMarkedGas — the marked numerator summed
    ONLY over families all of whose members are r-allowed;
  * activityRestrictedExpectation — their quotient, a normalized
    polymer functional (no Gibbs-measure reading is claimed);
  * TRUE normalization at f = 1, s = ∅: numerator = denominator
    AND denominator > 0 by the restricted KP exponential
    representation (nonvanishing as OUTPUT, never a premise);
  * CAPSTONE: the filtered finite regrouping by touching cores —
    the A3a method redone WITH the r-filter carried through core
    and remote part.

HARD HOLD (not here): connector clusters, inclusion–exclusion,
walk separation, family mass, barrier erosion, mass tilt, decay
bounds, covariance, constants, Gibbs-measure or boundary-
condition interpretations, spatial mixing language, thermodynamic
limit, continuum, mass gap. No project-local scientific axioms;
0 sorry.
-/
import Mathlib
import LatticeGauge.RestrictedGas

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## 51-A.1 — the allowed predicate for a remote region -/

/-- A polymer is allowed relative to a remote region r iff it does
    not touch r. No compatibility clause: this is a pure region
    predicate, not a core-relative one. -/
def regionAllowed (r : Set (Link N)) (η : Polymer N) : Prop :=
  ¬ typedTouchesSupport (N := N) η r

theorem regionAllowed_iff {r : Set (Link N)} {η : Polymer N} :
    regionAllowed (N := N) r η
      ↔ ¬ typedTouchesSupport (N := N) η r :=
  Iff.rfl

/-- Elaboration-only name for the conjunction governing a remote
    polymer in the restricted marked-gas capstone. This definition
    adds no mathematical content and is definitionally transparent. -/
def remoteRegionAllowed
    (T : Finset (Polymer N))
    (s r : Set (Link N))
    (η : Polymer N) : Prop :=
  remoteAllowed T s η ∧ regionAllowed (N := N) r η

theorem remoteRegionAllowed_iff
    {T : Finset (Polymer N)}
    {s r : Set (Link N)}
    {η : Polymer N} :
    remoteRegionAllowed (N := N) T s r η
      ↔ remoteAllowed T s η
        ∧ regionAllowed (N := N) r η :=
  Iff.rfl

/-- **Empty-core bridge**: relative to the empty core, the
    core-relative predicate collapses to the pure region
    predicate (the compatibility clause quantifies over ∅). -/
theorem regionAllowed_iff_remoteAllowed_empty
    (r : Set (Link N)) (η : Polymer N) :
    regionAllowed (N := N) r η
      ↔ remoteAllowed (∅ : Finset (Polymer N)) r η := by
  unfold regionAllowed remoteAllowed
  exact ⟨fun h => ⟨h, fun t ht =>
      absurd ht (Finset.not_mem_empty t)⟩,
    And.left⟩

/-- The compatible families all of whose members are r-allowed. -/
noncomputable def regionAllowedFamilies (r : Set (Link N)) :
    Finset (Finset (Polymer N)) :=
  (typedCompatiblePolymerFamilies N).filter
    (fun Γ => ∀ η ∈ Γ, regionAllowed (N := N) r η)

theorem mem_regionAllowedFamilies {r : Set (Link N)}
    {Γ : Finset (Polymer N)} :
    Γ ∈ regionAllowedFamilies (N := N) r
      ↔ TypedCompatible (N := N) Γ
        ∧ ∀ η ∈ Γ, regionAllowed (N := N) r η := by
  unfold regionAllowedFamilies
  rw [Finset.mem_filter, mem_typedCompatiblePolymerFamilies]

/-! ## 51-A.2 — the r-restricted polymer gas -/

/-- The typed polymer gas of the activity restricted by
    `regionAllowed r`: activities of polymers touching r are
    absorbed as zeros. A purely polymeric object. -/
noncomputable def activityRestrictedPolymerGas
    (β : ℝ) (χ : G → ℝ) (r : Set (Link N)) : ℝ :=
  typedPolymerGas (N := N)
    (restrictedActivity
      (fun η => polymerWeight (N := N) μm β χ η.val)
      (regionAllowed (N := N) r))

/-! ## 51-A.3 — the marked gas with the WHOLE family restricted -/

/-- The marked numerator restricted at the level of the WHOLE
    family: only families all of whose members are r-allowed
    contribute — core and remote part alike. -/
noncomputable def activityRestrictedMarkedGas
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s : Set (Link N)) (r : Set (Link N)) : ℝ :=
  ∑ Γ ∈ regionAllowedFamilies (N := N) r,
    markedRawFamilyWeight μm β χ f s (rawFamily Γ)

/-! ## 51-A.4 — the normalized polymer functional -/

/-- The activity-restricted expectation: a NORMALIZED POLYMER
    FUNCTIONAL, quotient of the restricted marked gas by the
    restricted gas. No identification with a Gibbs measure, a
    boundary condition or a physical switch-off is claimed at
    this gate. -/
noncomputable def activityRestrictedExpectation
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s : Set (Link N)) (r : Set (Link N)) : ℝ :=
  activityRestrictedMarkedGas μm β χ f s r
    / activityRestrictedPolymerGas μm β χ r

/-! ## 51-A.5 — normalization of the numerator at f = 1, s = ∅ -/

/-- With f = 1 and empty support, the restricted marked gas IS
    the restricted polymer gas: each family weight collapses to
    the product of ordinary weights, and the filtered sum is the
    zero-absorption form of the restricted gas. -/
theorem activityRestrictedMarkedGas_one_empty
    (β : ℝ) (χ : G → ℝ) (r : Set (Link N)) :
    activityRestrictedMarkedGas μm β χ (fun _ => 1)
        (∅ : Set (Link N)) r
      = activityRestrictedPolymerGas μm β χ r := by
  unfold activityRestrictedMarkedGas
    activityRestrictedPolymerGas regionAllowedFamilies
  rw [typedPolymerGas_restricted_eq_sum_allowed]
  refine Finset.sum_congr rfl (fun Γ _ => ?_)
  rw [markedRawFamilyWeight_one_empty]
  unfold rawFamily
  exact Finset.prod_image
    (fun a _ b _ h => Subtype.val_injective h)

/-! ## 51-A.6 — positivity of the denominator (KP as output) -/

/-- Under the published physical hypotheses the restricted gas is
    POSITIVE: the restricted activity inherits KP by monotonicity
    and the gas is an exponential. Nonvanishing is an OUTPUT of
    the expansion, never a premise. -/
theorem activityRestrictedPolymerGas_pos
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) (r : Set (Link N)) :
    0 < activityRestrictedPolymerGas μm β χ r := by
  unfold activityRestrictedPolymerGas
  rw [typedPolymerGas_restricted_eq_exp
    (fun γ => Nat.cast_nonneg _)
    (abstractKP_of_beta_le_one_div_40000 μm hβ mχ hχabs hsmall)
    (regionAllowed (N := N) r)]
  exact Real.exp_pos _

/-! ## 51-A.7 — true normalization of the functional -/

/-- **TRUE NORMALIZATION**: at f = 1 and empty support the
    functional equals 1 — numerator = denominator (51-A.5) AND
    the denominator is nonzero by positivity (51-A.6); only then
    is the quotient cancelled. -/
theorem activityRestrictedExpectation_one_empty
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) (r : Set (Link N)) :
    activityRestrictedExpectation μm β χ (fun _ => 1)
        (∅ : Set (Link N)) r = 1 := by
  unfold activityRestrictedExpectation
  rw [activityRestrictedMarkedGas_one_empty]
  exact div_self (ne_of_gt
    (activityRestrictedPolymerGas_pos μm hβ mχ hχabs hsmall r))

/-! ## 51-A.8 — CAPSTONE: the filtered regrouping by cores -/

/-- **CAPSTONE 51-A — THE FILTERED FINITE REGROUPING**: the
    restricted marked gas fibers over its touching cores, the
    r-filter carried honestly through BOTH parts: only cores all
    of whose members are r-allowed appear, and each fiber
    contributes the core weight times the gas of the activity
    restricted by the CONJUNCTION (remote-allowed for T at s) ∧
    (r-allowed). The A3a method is redone with the filter; the
    old theorem is not cited as if it carried the filter. -/
theorem activityRestrictedMarkedGas_eq_sum_core_mul_restricted'
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s : Set (Link N)) (r : Set (Link N)) :
    activityRestrictedMarkedGas μm β χ f s r
      = ∑ T ∈ (typedTouchingFamilies (N := N) s).filter
            (fun T => ∀ η ∈ T, regionAllowed (N := N) r η),
          typedMarkedCoreWeight μm β χ f T
            * typedPolymerGas (N := N)
                (restrictedActivity
                  (fun η => polymerWeight (N := N) μm β χ η.val)
                  (remoteRegionAllowed (N := N) T s r)) := by
  classical
  unfold activityRestrictedMarkedGas
  -- D2: fiber into the simple codomain first; impose the regional
  -- filter only after the fibers have been formed.
  have hmaps : ∀ Γ ∈ regionAllowedFamilies (N := N) r,
      Γ.filter (fun η => typedTouchesSupport (N := N) η s)
        ∈ typedTouchingFamilies (N := N) s := by
    intro Γ hΓ
    obtain ⟨hΓcompat, _⟩ := mem_regionAllowedFamilies.mp hΓ
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_typedCompatiblePolymerFamilies.mpr
        (typedCompatible_mono (Finset.filter_subset _ _)
          hΓcompat)
    · intro η hη
      exact (Finset.mem_filter.mp hη).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun Γ => markedRawFamilyWeight μm β χ f s (rawFamily Γ))]
  calc
    ∑ T ∈ typedTouchingFamilies (N := N) s,
        ∑ Γ ∈ (regionAllowedFamilies (N := N) r).filter
          (fun Γ => Γ.filter
            (fun η => typedTouchesSupport (N := N) η s) = T),
          markedRawFamilyWeight μm β χ f s (rawFamily Γ)
      = ∑ T ∈ (typedTouchingFamilies (N := N) s).filter
          (fun T => ∀ η ∈ T, regionAllowed (N := N) r η),
          ∑ Γ ∈ (regionAllowedFamilies (N := N) r).filter
            (fun Γ => Γ.filter
              (fun η => typedTouchesSupport (N := N) η s) = T),
            markedRawFamilyWeight μm β χ f s (rawFamily Γ) := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro T hT hTnot
        have hTregion : ¬ ∀ η ∈ T, regionAllowed (N := N) r η := by
          intro h
          exact hTnot (Finset.mem_filter.mpr ⟨hT, h⟩)
        have hfiber_empty :
            (regionAllowedFamilies (N := N) r).filter
              (fun Γ => Γ.filter
                (fun η => typedTouchesSupport (N := N) η s) = T)
              = ∅ := by
          apply Finset.eq_empty_iff_forall_not_mem.mpr
          intro Γ hΓ
          simp only [Finset.mem_filter] at hΓ
          obtain ⟨_, hΓregion⟩ := mem_regionAllowedFamilies.mp hΓ.1
          apply hTregion
          intro η hη
          have hηfilter : η ∈ Γ.filter
              (fun θ => typedTouchesSupport (N := N) θ s) :=
            hΓ.2.symm ▸ hη
          exact hΓregion η (Finset.mem_filter.mp hηfilter).1
        simp [hfiber_empty]
    _ = ∑ T ∈ (typedTouchingFamilies (N := N) s).filter
          (fun T => ∀ η ∈ T, regionAllowed (N := N) r η),
          typedMarkedCoreWeight μm β χ f T
            * typedPolymerGas (N := N)
                (restrictedActivity
                  (fun η => polymerWeight (N := N) μm β χ η.val)
                  (remoteRegionAllowed (N := N) T s r)) := by
      refine Finset.sum_congr rfl (fun T hT => ?_)
      obtain ⟨hTtouchfam, hTregion⟩ := Finset.mem_filter.mp hT
      obtain ⟨hTcompatmem, hTtouch⟩ :=
        Finset.mem_filter.mp hTtouchfam
      have hTtyped : TypedCompatible (N := N) T :=
        mem_typedCompatiblePolymerFamilies.mp hTcompatmem
      have hsummand : ∀ Γ ∈ (regionAllowedFamilies (N := N) r).filter
          (fun Γ => Γ.filter
            (fun η => typedTouchesSupport (N := N) η s) = T),
          markedRawFamilyWeight μm β χ f s (rawFamily Γ)
            = typedMarkedCoreWeight μm β χ f T
                * ∏ η ∈ Γ.filter
                    (fun η => ¬ typedTouchesSupport (N := N) η s),
                    polymerWeight (N := N) μm β χ η.val := by
        intro Γ hΓ
        simp only [Finset.mem_filter] at hΓ
        rw [markedRawFamilyWeight_rawFamily, hΓ.2]
        rfl
      rw [Finset.sum_congr rfl hsummand, ← Finset.mul_sum]
      congr 1
      rw [typedPolymerGas_restricted_eq_sum_allowed]
      refine Finset.sum_bij
        (fun Γ _ => Γ.filter
          (fun η => ¬ typedTouchesSupport (N := N) η s))
        ?_ ?_ ?_ ?_
      · intro Γ hΓ
        simp only [Finset.mem_filter] at hΓ
        obtain ⟨hΓdom, hΓfib⟩ := hΓ
        obtain ⟨hΓcompat, hΓregion⟩ :=
          mem_regionAllowedFamilies.mp hΓdom
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · exact mem_typedCompatiblePolymerFamilies.mpr
            (typedCompatible_mono (Finset.filter_subset _ _)
              hΓcompat)
        · intro η hη
          obtain ⟨hηΓ, hηnot⟩ := Finset.mem_filter.mp hη
          apply remoteRegionAllowed_iff.mpr
          refine ⟨⟨hηnot, ?_⟩, hΓregion η hηΓ⟩
          intro t ht
          have htfil : t ∈ Γ.filter
              (fun θ => typedTouchesSupport (N := N) θ s) :=
            hΓfib.symm ▸ ht
          have htΓ : t ∈ Γ := (Finset.mem_filter.mp htfil).1
          have hne : η ≠ t := by
            rintro rfl
            exact hηnot (Finset.mem_filter.mp htfil).2
          exact hΓcompat η hηΓ t htΓ hne
      · intro Γ₁ h₁ Γ₂ h₂ heq
        have heq' : Γ₁.filter
            (fun η => ¬ typedTouchesSupport (N := N) η s)
          = Γ₂.filter
            (fun η => ¬ typedTouchesSupport (N := N) η s) := heq
        simp only [Finset.mem_filter] at h₁ h₂
        have hf₁ := h₁.2
        have hf₂ := h₂.2
        calc Γ₁ = Γ₁.filter
              (fun η => typedTouchesSupport (N := N) η s)
            ∪ Γ₁.filter
              (fun η => ¬ typedTouchesSupport (N := N) η s) :=
              (Finset.filter_union_filter_neg_eq _ _).symm
          _ = T ∪ Γ₂.filter
              (fun η => ¬ typedTouchesSupport (N := N) η s) := by
              rw [hf₁, heq']
          _ = Γ₂.filter
              (fun η => typedTouchesSupport (N := N) η s)
            ∪ Γ₂.filter
              (fun η => ¬ typedTouchesSupport (N := N) η s) := by
              rw [hf₂]
          _ = Γ₂ := Finset.filter_union_filter_neg_eq _ _
      · intro R hR
        obtain ⟨hRtypedmem, hRallowed⟩ := Finset.mem_filter.mp hR
        have hRtyped : TypedCompatible (N := N) R :=
          mem_typedCompatiblePolymerFamilies.mp hRtypedmem
        have hTfilter : T.filter
            (fun η => typedTouchesSupport (N := N) η s) = T :=
          Finset.filter_true_of_mem hTtouch
        have hRparts : ∀ η ∈ R,
            remoteAllowed T s η ∧ regionAllowed (N := N) r η :=
          fun η hη => remoteRegionAllowed_iff.mp (hRallowed η hη)
        have hRfilter : R.filter
            (fun η => typedTouchesSupport (N := N) η s) = ∅ :=
          Finset.filter_false_of_mem
            (fun η hη => (hRparts η hη).1.1)
        have hTnot : T.filter
            (fun η => ¬ typedTouchesSupport (N := N) η s) = ∅ :=
          Finset.filter_false_of_mem
            (fun η hη h => h (hTtouch η hη))
        have hRnot : R.filter
            (fun η => ¬ typedTouchesSupport (N := N) η s) = R :=
          Finset.filter_true_of_mem
            (fun η hη => (hRparts η hη).1.1)
        refine ⟨T ∪ R, ?_, ?_⟩
        · simp only [Finset.mem_filter]
          refine ⟨mem_regionAllowedFamilies.mpr ⟨?_, ?_⟩, ?_⟩
          · intro η hη θ hθ hne
            rcases Finset.mem_union.mp hη with hηT | hηR
            · rcases Finset.mem_union.mp hθ with hθT | hθR
              · exact hTtyped η hηT θ hθT hne
              · exact plaquetteCompatible_symm
                  ((hRparts θ hθR).1.2 η hηT)
            · rcases Finset.mem_union.mp hθ with hθT | hθR
              · exact (hRparts η hηR).1.2 θ hθT
              · exact hRtyped η hηR θ hθR hne
          · intro η hη
            rcases Finset.mem_union.mp hη with hηT | hηR
            · exact hTregion η hηT
            · exact (hRparts η hηR).2
          · show (T ∪ R).filter
                (fun η => typedTouchesSupport (N := N) η s) = T
            rw [Finset.filter_union, hTfilter, hRfilter,
              Finset.union_empty]
        · show (T ∪ R).filter
              (fun η => ¬ typedTouchesSupport (N := N) η s) = R
          rw [Finset.filter_union, hTnot, hRnot,
            Finset.empty_union]
      · intro Γ _
        rfl

theorem activityRestrictedMarkedGas_eq_sum_core_mul_restricted
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s : Set (Link N)) (r : Set (Link N)) :
    activityRestrictedMarkedGas μm β χ f s r
      = ∑ T ∈ (typedTouchingFamilies (N := N) s).filter
            (fun T => ∀ η ∈ T, regionAllowed (N := N) r η),
          typedMarkedCoreWeight μm β χ f T
            * typedPolymerGas (N := N)
                (restrictedActivity
                  (fun η => polymerWeight (N := N) μm β χ η.val)
                  (fun η => remoteAllowed T s η
                    ∧ regionAllowed (N := N) r η)) := by
  simpa only [remoteRegionAllowed] using
    activityRestrictedMarkedGas_eq_sum_core_mul_restricted'
      (μm := μm) β χ f s r

#print axioms activityRestrictedExpectation_one_empty
#print axioms activityRestrictedMarkedGas_eq_sum_core_mul_restricted'
#print axioms activityRestrictedMarkedGas_eq_sum_core_mul_restricted

end LatticeGauge
