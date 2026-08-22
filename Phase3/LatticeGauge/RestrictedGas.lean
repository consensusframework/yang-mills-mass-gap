/-
LatticeGauge/RestrictedGas.lean — PEDRA 50, Gate 50-A3 (analytic
half): RESTRICTED ACTIVITIES, KP MONOTONICITY, AND THE GAS RATIO
AS AN EXPONENTIAL OF A CLUSTER DIFFERENCE
(architecture: Sol/GPT-5.6; execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): A3 performs the
first legitimate GLOBAL cancellation — the vacuum clusters common
to the restricted and the full gas cancel in the EXPONENT of the
gas ratio. A3 does NOT yet formalize the combinatorial support
localization ("difference ≠ 0 only if the cluster touches the
excluded region" — next gate), and much less "cluster connects
supp f to supp g" (two insertions/covariance — later). We do not
name the road sign two kilometres early.

Content: typedTouchesSupport; restrictedActivity z P (activity
kept on the ALLOWED predicate P, zeroed elsewhere — constraints
absorbed as zeros, no new set machinery); the pointwise bound
|restricted| ≤ |z|; KP MONOTONICITY (a smaller absolute activity
inherits the Kotecký–Preiss hypothesis — stone 46 NOT redone);
the restricted concrete specialization for 0 ≤ β ≤ 1/40000; the
restricted gas as an exponential (the 49C-V identity for GENERIC
activity, consumed); and the RATIO identity
  gas(restricted)/gas(full) = exp(C_restricted − C_full)
by Real.exp_sub — no division simplified, no nonvanishing
hypothesis anywhere.

HARD HOLD (not here): distance, SimpleGraph.dist, q^d,
exponential decay, second insertion g, covariance, connector
clusters between two supports, thermodynamic limit, continuum,
mass gap. No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.KPInduction
import LatticeGauge.KPSpecialization
import LatticeGauge.KPClusterExpansion
import LatticeGauge.ObservableGas

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## A3.1 — typed support touching and restricted activities -/

/-- A typed polymer touches an observable support iff its raw
    shadow does. -/
def typedTouchesSupport (η : Polymer N) (s : Set (Link N)) :
    Prop :=
  blockTouchesSupport (N := N) η.val s

/-- Activity restricted to an ALLOWED predicate: kept on P,
    zeroed elsewhere — hard constraints absorbed as zeros. -/
noncomputable def restrictedActivity (z : Polymer N → ℝ)
    (P : Polymer N → Prop) : Polymer N → ℝ :=
  fun η => if P η then z η else 0

theorem abs_restrictedActivity_le (z : Polymer N → ℝ)
    (P : Polymer N → Prop) (η : Polymer N) :
    |restrictedActivity z P η| ≤ |z η| := by
  unfold restrictedActivity
  split_ifs
  · exact le_rfl
  · simp

/-! ## A3.2 — KP monotonicity: smaller absolute activity inherits
    the smallness hypothesis (stone 46 not redone) -/

theorem abstractKP_mono {ρ ρ' a : Polymer N → ℝ}
    (hle : ∀ η, ρ' η ≤ ρ η) (h0 : ∀ η, 0 ≤ ρ' η)
    (hKP : AbstractKPHypothesis (N := N) ρ a) :
    AbstractKPHypothesis (N := N) ρ' a := by
  intro γ₀
  refine le_trans (Finset.sum_le_sum ?_) (hKP γ₀)
  intro η _
  have hind : (0 : ℝ) ≤ (incompatibilityIndicator γ₀ η : ℝ) := by
    positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hle η) hind)
    (Real.exp_pos _).le

/-- Restriction preserves the abstract KP hypothesis. -/
theorem abstractKP_restrictedActivity {z a : Polymer N → ℝ}
    (P : Polymer N → Prop)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a) :
    AbstractKPHypothesis (N := N)
      (fun η => |restrictedActivity z P η|) a :=
  abstractKP_mono (fun η => abs_restrictedActivity_le z P η)
    (fun η => abs_nonneg _) hKP

/-- Concrete: for 0 ≤ β ≤ 1/40000, EVERY restriction of the
    polymer weight satisfies KP (stone 46/47 consumed through the
    49 specialization; monotonicity does the rest). -/
theorem abstractKP_restricted_polymerWeight {β : ℝ} (hβ : 0 ≤ β)
    {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) (P : Polymer N → Prop) :
    AbstractKPHypothesis (N := N)
      (fun η => |restrictedActivity
        (fun η => polymerWeight (N := N) μm β χ η.val) P η|)
      (fun η => ((η.val.card : ℕ) : ℝ)) :=
  abstractKP_restrictedActivity P
    (abstractKP_of_beta_le_one_div_40000 μm hβ mχ hχabs hsmall)

/-! ## A3.3 — the restricted gas as an exponential and THE RATIO
    AS exp OF A CLUSTER DIFFERENCE -/

/-- The restricted gas is an exponential of its own cluster sum
    (the generic-activity 49C-V identity consumed). -/
theorem typedPolymerGas_restricted_eq_exp {z a : Polymer N → ℝ}
    (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a)
    (P : Polymer N → Prop) :
    typedPolymerGas (N := N) (restrictedActivity z P)
      = Real.exp (∑' n, kpSignedUnrootedCoeff n
          (restrictedActivity z P)) :=
  typedPolymerGas_eq_exp_tsum_of_KP ha
    (abstractKP_restrictedActivity P hKP)

/-- **CAPSTONE (analytic half of A3)**: the gas ratio is the
    exponential of the cluster DIFFERENCE — the vacuum clusters
    common to both gases cancel in the exponent. Division is
    rewritten by Real.exp_sub; nothing is assumed nonzero. -/
theorem typedPolymerGas_ratio_eq_exp_sub {z a : Polymer N → ℝ}
    (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a)
    (P : Polymer N → Prop) :
    typedPolymerGas (N := N) (restrictedActivity z P)
        / typedPolymerGas (N := N) z
      = Real.exp
          ((∑' n, kpSignedUnrootedCoeff n
              (restrictedActivity z P))
            - ∑' n, kpSignedUnrootedCoeff (N := N) n z) := by
  rw [typedPolymerGas_eq_exp_tsum_of_KP ha hKP,
    typedPolymerGas_restricted_eq_exp ha hKP P,
    ← Real.exp_sub]

/-! ## A3.4 — the finite regrouping: fibering the marked gas by
    its touching core (all finite, all exact) -/

theorem typedCompatible_mono {T Γ : Finset (Polymer N)}
    (hsub : T ⊆ Γ) (h : TypedCompatible (N := N) Γ) :
    TypedCompatible (N := N) T :=
  fun η hη θ hθ hne => h η (hsub hη) θ (hsub hθ) hne

noncomputable def typedTouchingFamilies (s : Set (Link N)) :
    Finset (Finset (Polymer N)) :=
  (typedCompatiblePolymerFamilies N).filter
    (fun T => ∀ η ∈ T, typedTouchesSupport (N := N) η s)

/-- A remote polymer is ALLOWED relative to a core T: it does not
    touch the support and is compatible with every core member. -/
def remoteAllowed (T : Finset (Polymer N)) (s : Set (Link N))
    (η : Polymer N) : Prop :=
  ¬ typedTouchesSupport (N := N) η s
    ∧ ∀ t ∈ T, PlaquetteCompatible (N := N) η.val t.val

/-- The core weight: the observable integrates jointly with its
    touching polymers. -/
noncomputable def typedMarkedCoreWeight (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (T : Finset (Polymer N)) : ℝ :=
  ∫ U : Config N G,
    f U * ∏ η ∈ T, blockActivity β χ η.val U
    ∂(configMeasure μm N)

/-- **Zero absorption**: the restricted gas IS the sum over
    families all of whose members are allowed — forbidden members
    kill their family through a zero factor. -/
theorem typedPolymerGas_restricted_eq_sum_allowed
    (z : Polymer N → ℝ) (P : Polymer N → Prop) :
    typedPolymerGas (N := N) (restrictedActivity z P)
      = ∑ Γ ∈ (typedCompatiblePolymerFamilies N).filter
          (fun Γ => ∀ η ∈ Γ, P η),
          ∏ η ∈ Γ, z η := by
  unfold typedPolymerGas
  rw [← Finset.sum_filter_add_sum_filter_not
    (typedCompatiblePolymerFamilies N) (fun Γ => ∀ η ∈ Γ, P η)]
  have h2 : (∑ Γ ∈ (typedCompatiblePolymerFamilies N).filter
      (fun Γ => ¬ ∀ η ∈ Γ, P η),
      ∏ η ∈ Γ, restrictedActivity z P η) = 0 := by
    refine Finset.sum_eq_zero (fun Γ hΓ => ?_)
    obtain ⟨η, hη, hPη⟩ := by
      have h := (Finset.mem_filter.mp hΓ).2
      push_neg at h
      exact h
    refine Finset.prod_eq_zero hη ?_
    unfold restrictedActivity
    exact if_neg hPη
  have h1 : ∀ Γ ∈ (typedCompatiblePolymerFamilies N).filter
      (fun Γ => ∀ η ∈ Γ, P η),
      (∏ η ∈ Γ, restrictedActivity z P η) = ∏ η ∈ Γ, z η := by
    intro Γ hΓ
    refine Finset.prod_congr rfl (fun η hη => ?_)
    unfold restrictedActivity
    exact if_pos ((Finset.mem_filter.mp hΓ).2 η hη)
  rw [Finset.sum_congr rfl h1, h2, add_zero]

/-- The A2 marked weight in typed-native form (filter/image
    commutation + injective products). -/
theorem markedRawFamilyWeight_rawFamily (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s : Set (Link N))
    (Γ : Finset (Polymer N)) :
    markedRawFamilyWeight μm β χ f s (rawFamily Γ)
      = (∫ U : Config N G,
          f U * ∏ η ∈ Γ.filter
            (fun η => typedTouchesSupport (N := N) η s),
            blockActivity β χ η.val U ∂(configMeasure μm N))
        * ∏ η ∈ Γ.filter
            (fun η => ¬ typedTouchesSupport (N := N) η s),
            polymerWeight (N := N) μm β χ η.val := by
  unfold markedRawFamilyWeight touchingFamily remoteFamily
    rawFamily typedTouchesSupport
  rw [Finset.filter_image, Finset.filter_image]
  congr 1
  · congr 1
    funext U
    exact Finset.prod_image
      (fun a _ b _ h => Subtype.val_injective h)
  · exact Finset.prod_image
      (fun a _ b _ h => Subtype.val_injective h)

/-- **CAPSTONE A3a — THE FINITE REGROUPING**: the typed marked
    gas fibers over its touching cores; each fiber contributes
    the core weight times the T-restricted gas (constraints
    absorbed as zeros). All finite, all exact — nothing
    cancelled yet. -/
theorem typedMarkedPolymerGas_eq_sum_core_mul_restricted
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s : Set (Link N)) :
    typedMarkedPolymerGas μm β χ f s
      = ∑ T ∈ typedTouchingFamilies (N := N) s,
          typedMarkedCoreWeight μm β χ f T
            * typedPolymerGas (N := N)
                (restrictedActivity
                  (fun η => polymerWeight (N := N) μm β χ η.val)
                  (remoteAllowed T s)) := by
  classical
  unfold typedMarkedPolymerGas
  rw [Finset.sum_congr rfl
    (fun Γ _ => markedRawFamilyWeight_rawFamily μm β χ f s Γ)]
  have hmaps : ∀ Γ ∈ typedCompatiblePolymerFamilies N,
      Γ.filter (fun η => typedTouchesSupport (N := N) η s)
        ∈ typedTouchingFamilies (N := N) s := by
    intro Γ hΓ
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_typedCompatiblePolymerFamilies.mpr
        (typedCompatible_mono (Finset.filter_subset _ _)
          (mem_typedCompatiblePolymerFamilies.mp hΓ))
    · intro η hη
      exact (Finset.mem_filter.mp hη).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun Γ : Finset (Polymer N) =>
      (∫ U : Config N G,
        f U * ∏ η ∈ Γ.filter
          (fun η => typedTouchesSupport (N := N) η s),
          blockActivity β χ η.val U ∂(configMeasure μm N))
        * ∏ η ∈ Γ.filter
            (fun η => ¬ typedTouchesSupport (N := N) η s),
            polymerWeight (N := N) μm β χ η.val)]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  obtain ⟨hTtyped, hTtouch⟩ := Finset.mem_filter.mp hT
  -- inside the fiber the core is constant
  have hfib : ∀ Γ ∈ (typedCompatiblePolymerFamilies N).filter
      (fun Γ => Γ.filter
        (fun η => typedTouchesSupport (N := N) η s) = T),
      ((∫ U : Config N G,
        f U * ∏ η ∈ Γ.filter
          (fun η => typedTouchesSupport (N := N) η s),
          blockActivity β χ η.val U ∂(configMeasure μm N))
        * ∏ η ∈ Γ.filter
            (fun η => ¬ typedTouchesSupport (N := N) η s),
            polymerWeight (N := N) μm β χ η.val)
      = typedMarkedCoreWeight μm β χ f T
          * ∏ η ∈ Γ.filter
              (fun η => ¬ typedTouchesSupport (N := N) η s),
              polymerWeight (N := N) μm β χ η.val := by
    intro Γ hΓ
    rw [(Finset.mem_filter.mp hΓ).2]
    rfl
  rw [Finset.sum_congr rfl hfib, ← Finset.mul_sum]
  congr 1
  -- the fiber ↔ allowed remote families bijection
  rw [typedPolymerGas_restricted_eq_sum_allowed]
  refine Finset.sum_bij
    (fun Γ _ => Γ.filter
      (fun η => ¬ typedTouchesSupport (N := N) η s))
    ?_ ?_ ?_ ?_
  · intro Γ hΓ
    obtain ⟨hΓtyped, hΓfib⟩ := Finset.mem_filter.mp hΓ
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_typedCompatiblePolymerFamilies.mpr
        (typedCompatible_mono (Finset.filter_subset _ _)
          (mem_typedCompatiblePolymerFamilies.mp hΓtyped))
    · intro η hη
      obtain ⟨hηΓ, hηnot⟩ := Finset.mem_filter.mp hη
      refine ⟨hηnot, ?_⟩
      intro t ht
      have htΓ : t ∈ Γ := by
        have := hΓfib ▸ ht
        exact (Finset.mem_filter.mp this).1
      have hne : η ≠ t := by
        rintro rfl
        exact hηnot (Finset.mem_filter.mp (hΓfib ▸ ht)).2
      exact mem_typedCompatiblePolymerFamilies.mp hΓtyped
        η hηΓ t htΓ hne
  · intro Γ₁ h₁ Γ₂ h₂ heq
    have heq' : Γ₁.filter
        (fun η => ¬ typedTouchesSupport (N := N) η s)
      = Γ₂.filter
        (fun η => ¬ typedTouchesSupport (N := N) η s) := heq
    have hf₁ := (Finset.mem_filter.mp h₁).2
    have hf₂ := (Finset.mem_filter.mp h₂).2
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
    obtain ⟨hRtyped, hRallowed⟩ := Finset.mem_filter.mp hR
    have hTfilter : T.filter
        (fun η => typedTouchesSupport (N := N) η s) = T :=
      Finset.filter_true_of_mem hTtouch
    have hRfilter : R.filter
        (fun η => typedTouchesSupport (N := N) η s) = ∅ :=
      Finset.filter_false_of_mem
        (fun η hη => (hRallowed η hη).1)
    have hTnot : T.filter
        (fun η => ¬ typedTouchesSupport (N := N) η s) = ∅ :=
      Finset.filter_false_of_mem
        (fun η hη h => h (hTtouch η hη))
    have hRnot : R.filter
        (fun η => ¬ typedTouchesSupport (N := N) η s) = R :=
      Finset.filter_true_of_mem
        (fun η hη => (hRallowed η hη).1)
    refine ⟨T ∪ R, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · refine mem_typedCompatiblePolymerFamilies.mpr ?_
      intro η hη θ hθ hne
      rcases Finset.mem_union.mp hη with hηT | hηR
      · rcases Finset.mem_union.mp hθ with hθT | hθR
        · exact mem_typedCompatiblePolymerFamilies.mp hTtyped
            η hηT θ hθT hne
        · exact plaquetteCompatible_symm
            ((hRallowed θ hθR).2 η hηT)
      · rcases Finset.mem_union.mp hθ with hθT | hθR
        · exact (hRallowed η hηR).2 θ hθT
        · exact mem_typedCompatiblePolymerFamilies.mp hRtyped
            η hηR θ hθR hne
    · rw [Finset.filter_union, hTfilter, hRfilter,
        Finset.union_empty]
    · rw [Finset.filter_union, hTnot, hRnot,
        Finset.empty_union]
  · intro Γ _
    rfl

/-! ## A3.5 — the expectation cluster-ratio capstone -/

/-- **CAPSTONE A3**: the Gibbs expectation as a finite sum of
    core weights times exponentials of cluster DIFFERENCES — the
    vacuum clusters common to the restricted and full gases
    cancel in each exponent. The difference is NOT yet localized
    (next gate); no second insertion, no covariance. -/
theorem gibbsExpectation_eq_sum_core_mul_exp {β : ℝ}
    (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf) :
    gibbsExpectation (N := N) μm β χ f
      = ∑ T ∈ typedTouchingFamilies (N := N) s,
          typedMarkedCoreWeight μm β χ f T
            * Real.exp
                ((∑' n, kpSignedUnrootedCoeff n
                    (restrictedActivity
                      (fun η => polymerWeight (N := N) μm β χ
                        η.val)
                      (remoteAllowed T s)))
                  - ∑' n, kpSignedUnrootedCoeff (N := N) n
                      (fun η => polymerWeight (N := N) μm β χ
                        η.val)) := by
  rw [gibbsExpectation_eq_markedGas_div_gas μm hβ mχ hχabs
      hf mf hCf,
    typedMarkedPolymerGas_eq_sum_core_mul_restricted μm β χ f s,
    Finset.sum_div]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [mul_div_assoc,
    typedPolymerGas_ratio_eq_exp_sub
      (fun γ => Nat.cast_nonneg _)
      (abstractKP_of_beta_le_one_div_40000 μm hβ mχ hχabs
        hsmall)
      (remoteAllowed T s)]

end LatticeGauge
