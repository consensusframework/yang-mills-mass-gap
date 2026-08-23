/-
LatticeGauge/CovarianceMayerWiring.lean — PEDRA 50, Gate 50-A13:
THE DOUBLY MARKED ATOM AND THE BRIDGE FAMILIES (architecture:
Sol; execution: Fable).

The exact algebra of the covariance at the level of NUMERATORS,
and the decomposition of a compatible family by how its polymers
touch the two supports: leftOnly / rightOnly / bridge /
remoteBoth — an exact partition, no quotients, no ordered cores,
no representatives. For a BRIDGE-FREE family the doubly marked
integral factorizes exactly:
  ∫ f·g·Π_Γ = (core weight of f on leftOnly)
              · (core weight of g on rightOnly)
              · Π_remote polymerWeight,
through the A1 collective machine and the β=0 split — never
reproved. Bridge families are NOT eliminated and NOT estimated
here; they are the registered witness for the next gate.

NOT here (hard hold): no regrouping of the total sum by T/T', no
elimination or estimate of bridgeCore, no ConnectorClusters, no
A12 tail, no exp(connector) − 1, no sum of typedMarkedCoreWeight,
no mass tilt of cores, no covariance bound, no correlation
decay/clustering, no SimpleGraph.dist, no thermodynamic limit,
no continuum, no mass gap, no Clay claim. A12 stays frozen.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.RestrictedGas
import LatticeGauge.KPPartitionExp
import LatticeGauge.KPConnectorEnvelopeLocalization

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## A13.1 — the covariance numerator identity (Z ≠ 0 as the
    OUTPUT of the cluster expansion; no Mayer expansion here) -/

theorem gibbsCovariance_eq_observableNumerator_cross
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (f g : Config N G → ℝ) :
    gibbsCovariance (N := N) μm β χ f g
      = (observableNumerator μm β χ (fun U => f U * g U)
            * realZ (N := N) μm β χ
          - observableNumerator μm β χ f
            * observableNumerator μm β χ g)
        / (realZ (N := N) μm β χ) ^ 2 := by
  have hZ : realZ (N := N) μm β χ ≠ 0 :=
    realZ_ne_zero_of_clusterExpansion μm hβ mχ hχabs hsmall
  unfold gibbsCovariance
  rw [gibbsExpectation_eq_observableNumerator_div,
    gibbsExpectation_eq_observableNumerator_div,
    gibbsExpectation_eq_observableNumerator_div]
  field_simp
  ring

/-! ## A13.2 — the four colors of a family -/

noncomputable def leftOnlyCore (Γ : Finset (Polymer N))
    (s s' : Set (Link N)) : Finset (Polymer N) :=
  Γ.filter (fun η => typedTouchesSupport (N := N) η s
    ∧ ¬ typedTouchesSupport (N := N) η s')

noncomputable def rightOnlyCore (Γ : Finset (Polymer N))
    (s s' : Set (Link N)) : Finset (Polymer N) :=
  Γ.filter (fun η => ¬ typedTouchesSupport (N := N) η s
    ∧ typedTouchesSupport (N := N) η s')

noncomputable def bridgeCore (Γ : Finset (Polymer N))
    (s s' : Set (Link N)) : Finset (Polymer N) :=
  Γ.filter (fun η => typedTouchesSupport (N := N) η s
    ∧ typedTouchesSupport (N := N) η s')

noncomputable def remoteBothCore (Γ : Finset (Polymer N))
    (s s' : Set (Link N)) : Finset (Polymer N) :=
  Γ.filter (fun η => ¬ typedTouchesSupport (N := N) η s
    ∧ ¬ typedTouchesSupport (N := N) η s')

theorem mem_leftOnlyCore {Γ : Finset (Polymer N)}
    {s s' : Set (Link N)} {η : Polymer N} :
    η ∈ leftOnlyCore Γ s s'
      ↔ η ∈ Γ ∧ (typedTouchesSupport (N := N) η s
        ∧ ¬ typedTouchesSupport (N := N) η s') :=
  Finset.mem_filter

theorem mem_rightOnlyCore {Γ : Finset (Polymer N)}
    {s s' : Set (Link N)} {η : Polymer N} :
    η ∈ rightOnlyCore Γ s s'
      ↔ η ∈ Γ ∧ (¬ typedTouchesSupport (N := N) η s
        ∧ typedTouchesSupport (N := N) η s') :=
  Finset.mem_filter

theorem mem_bridgeCore {Γ : Finset (Polymer N)}
    {s s' : Set (Link N)} {η : Polymer N} :
    η ∈ bridgeCore Γ s s'
      ↔ η ∈ Γ ∧ (typedTouchesSupport (N := N) η s
        ∧ typedTouchesSupport (N := N) η s') :=
  Finset.mem_filter

theorem mem_remoteBothCore {Γ : Finset (Polymer N)}
    {s s' : Set (Link N)} {η : Polymer N} :
    η ∈ remoteBothCore Γ s s'
      ↔ η ∈ Γ ∧ (¬ typedTouchesSupport (N := N) η s
        ∧ ¬ typedTouchesSupport (N := N) η s') :=
  Finset.mem_filter

/-- **The exact partition** — every member wears exactly one of
    the four colors. -/
theorem core_partition (Γ : Finset (Polymer N))
    (s s' : Set (Link N)) :
    leftOnlyCore Γ s s' ∪ rightOnlyCore Γ s s'
      ∪ bridgeCore Γ s s' ∪ remoteBothCore Γ s s' = Γ := by
  ext η
  simp only [Finset.mem_union, mem_leftOnlyCore, mem_rightOnlyCore,
    mem_bridgeCore, mem_remoteBothCore]
  by_cases h1 : typedTouchesSupport (N := N) η s <;>
    by_cases h2 : typedTouchesSupport (N := N) η s' <;> tauto

/-! The disjunctions actually consumed by the factorization. -/

theorem disjoint_leftOnly_rightOnly (Γ : Finset (Polymer N))
    (s s' : Set (Link N)) :
    Disjoint (leftOnlyCore Γ s s') (rightOnlyCore Γ s s') := by
  rw [Finset.disjoint_left]
  intro η h1 h2
  exact (mem_rightOnlyCore.mp h2).2.1 (mem_leftOnlyCore.mp h1).2.1

theorem disjoint_leftOnly_remoteBoth (Γ : Finset (Polymer N))
    (s s' : Set (Link N)) :
    Disjoint (leftOnlyCore Γ s s') (remoteBothCore Γ s s') := by
  rw [Finset.disjoint_left]
  intro η h1 h2
  exact (mem_remoteBothCore.mp h2).2.1 (mem_leftOnlyCore.mp h1).2.1

theorem disjoint_rightOnly_remoteBoth (Γ : Finset (Polymer N))
    (s s' : Set (Link N)) :
    Disjoint (rightOnlyCore Γ s s') (remoteBothCore Γ s s') := by
  rw [Finset.disjoint_left]
  intro η h1 h2
  exact (mem_remoteBothCore.mp h2).2.2 (mem_rightOnlyCore.mp h1).2.2

/-! ## A13.3 — the supports of the two sides -/

/-- The smallest missing support lemma: a set disjoint from every
    member support is disjoint from the family support. -/
theorem disjoint_familySupport_of_forall {A : Set (Link N)}
    {T : Finset (Polymer N)}
    (h : ∀ η ∈ T,
      Disjoint (blockLinkSupport (N := N) η.val) A) :
    Disjoint A (familySupport
      (fun η : Polymer N => blockLinkSupport (N := N) η.val) T) := by
  rw [Set.disjoint_right]
  intro ℓ hℓ hℓA
  obtain ⟨η, hηT, hℓη⟩ := hℓ
  exact Set.disjoint_left.mp (h η hηT) hℓη hℓA

theorem disjoint_familySupport_familySupport
    {T T' : Finset (Polymer N)}
    (h : ∀ η ∈ T, ∀ θ ∈ T',
      Disjoint (blockLinkSupport (N := N) η.val)
        (blockLinkSupport (N := N) θ.val)) :
    Disjoint
      (familySupport (fun η : Polymer N =>
        blockLinkSupport (N := N) η.val) T)
      (familySupport (fun η : Polymer N =>
        blockLinkSupport (N := N) η.val) T') := by
  rw [Set.disjoint_left]
  intro ℓ hℓ hℓ'
  obtain ⟨η, hηT, hℓη⟩ := hℓ
  obtain ⟨θ, hθT', hℓθ⟩ := hℓ'
  exact Set.disjoint_left.mp (h η hηT θ hθT') hℓη hℓθ

/-- **The two augmented supports are disjoint.** Consumed
    motives, all explicit: s ⊥ s'; leftOnly does not touch s';
    rightOnly does not touch s; distinct family members are
    PlaquetteCompatible. (bridgeCore = ∅ is NOT needed here: the
    definition of leftOnly already excludes touching s'.) -/
theorem disjoint_augmented_supports {Γ : Finset (Polymer N)}
    {s s' : Set (Link N)} (hss' : Disjoint s s')
    (hΓ : TypedCompatible Γ) :
    Disjoint
      (s ∪ familySupport (fun η : Polymer N =>
        blockLinkSupport (N := N) η.val) (leftOnlyCore Γ s s'))
      (s' ∪ familySupport (fun η : Polymer N =>
        blockLinkSupport (N := N) η.val) (rightOnlyCore Γ s s')) := by
  rw [Set.disjoint_union_left]
  constructor
  · rw [Set.disjoint_union_right]
    refine ⟨hss', ?_⟩
    exact disjoint_familySupport_of_forall (fun η hη =>
      not_blockTouchesSupport_iff.mp
        (mem_rightOnlyCore.mp hη).2.1)
  · rw [Set.disjoint_union_right]
    constructor
    · exact (disjoint_familySupport_of_forall (fun η hη =>
        not_blockTouchesSupport_iff.mp
          (mem_leftOnlyCore.mp hη).2.2)).symm
    · refine disjoint_familySupport_familySupport
        (fun η hη θ hθ => ?_)
      have hne : η ≠ θ := fun he =>
        (mem_rightOnlyCore.mp hθ).2.1
          (he ▸ (mem_leftOnlyCore.mp hη).2.1)
      exact hΓ η (mem_leftOnlyCore.mp hη).1
        θ (mem_rightOnlyCore.mp hθ).1 hne

/-- A remote member is disjoint from the LEFT augmented support. -/
theorem remoteBoth_disjoint_left_augmented
    {Γ : Finset (Polymer N)} {s s' : Set (Link N)}
    (hΓ : TypedCompatible Γ) {η : Polymer N}
    (hη : η ∈ remoteBothCore Γ s s') :
    Disjoint (blockLinkSupport (N := N) η.val)
      (s ∪ familySupport (fun θ : Polymer N =>
        blockLinkSupport (N := N) θ.val) (leftOnlyCore Γ s s')) := by
  rw [Set.disjoint_union_right]
  refine ⟨not_blockTouchesSupport_iff.mp
    (mem_remoteBothCore.mp hη).2.1, ?_⟩
  refine disjoint_familySupport_of_forall (fun θ hθ => ?_)
  have hne : θ ≠ η := fun he =>
    (mem_remoteBothCore.mp hη).2.1
      (he ▸ (mem_leftOnlyCore.mp hθ).2.1)
  exact hΓ θ (mem_leftOnlyCore.mp hθ).1
    η (mem_remoteBothCore.mp hη).1 hne

/-- A remote member is disjoint from the RIGHT augmented support. -/
theorem remoteBoth_disjoint_right_augmented
    {Γ : Finset (Polymer N)} {s s' : Set (Link N)}
    (hΓ : TypedCompatible Γ) {η : Polymer N}
    (hη : η ∈ remoteBothCore Γ s s') :
    Disjoint (blockLinkSupport (N := N) η.val)
      (s' ∪ familySupport (fun θ : Polymer N =>
        blockLinkSupport (N := N) θ.val) (rightOnlyCore Γ s s')) := by
  rw [Set.disjoint_union_right]
  refine ⟨not_blockTouchesSupport_iff.mp
    (mem_remoteBothCore.mp hη).2.2, ?_⟩
  refine disjoint_familySupport_of_forall (fun θ hθ => ?_)
  have hne : θ ≠ η := fun he =>
    (mem_remoteBothCore.mp hη).2.2
      (he ▸ (mem_rightOnlyCore.mp hθ).2.2)
  exact hΓ θ (mem_rightOnlyCore.mp hθ).1
    η (mem_remoteBothCore.mp hη).1 hne

/-- Distinct remote members have disjoint supports. -/
theorem remoteBoth_pairwise_disjoint
    {Γ : Finset (Polymer N)} {s s' : Set (Link N)}
    (hΓ : TypedCompatible Γ) {η θ : Polymer N}
    (hη : η ∈ remoteBothCore Γ s s')
    (hθ : θ ∈ remoteBothCore Γ s s') (hne : η ≠ θ) :
    Disjoint (blockLinkSupport (N := N) η.val)
      (blockLinkSupport (N := N) θ.val) :=
  hΓ η (mem_remoteBothCore.mp hη).1
    θ (mem_remoteBothCore.mp hθ).1 hne

/-! ## A13.4 — the doubly marked atom -/

noncomputable def twoMarkedFamilyIntegral (β : ℝ) (χ : G → ℝ)
    (f g : Config N G → ℝ) (Γ : Finset (Polymer N)) : ℝ :=
  ∫ U : Config N G,
    f U * g U * ∏ η ∈ Γ, blockActivity β χ η.val U
    ∂(configMeasure μm N)

/-- **CAPSTONE 50-A13**: for a compatible BRIDGE-FREE family the
    doubly marked integral factorizes exactly — each observable
    keeps its touching polymers, the remote ones leave with their
    polymer weights (A1 collective machine + β=0 split consumed;
    independence never reproved). -/
theorem twoMarkedFamilyIntegral_factorizes {β : ℝ}
    {χ : G → ℝ} (mχ : Measurable χ)
    {s s' : Set (Link N)} (hss' : Disjoint s s')
    {f g : Config N G → ℝ}
    (hf : DependsOnlyOn f s) (mf : Measurable f)
    (hg : DependsOnlyOn g s') (mg : Measurable g)
    {Γ : Finset (Polymer N)} (hΓ : TypedCompatible Γ)
    (hbridge : bridgeCore Γ s s' = ∅) :
    twoMarkedFamilyIntegral μm β χ f g Γ
      = typedMarkedCoreWeight μm β χ f (leftOnlyCore Γ s s')
        * typedMarkedCoreWeight μm β χ g (rightOnlyCore Γ s s')
        * ∏ η ∈ remoteBothCore Γ s s',
            polymerWeight (N := N) μm β χ η.val := by
  have hLR := disjoint_leftOnly_rightOnly Γ s s'
  have hLRM : Disjoint
      (leftOnlyCore Γ s s' ∪ rightOnlyCore Γ s s')
      (remoteBothCore Γ s s') :=
    Finset.disjoint_union_left.mpr
      ⟨disjoint_leftOnly_remoteBoth Γ s s',
        disjoint_rightOnly_remoteBoth Γ s s'⟩
  have hpart : leftOnlyCore Γ s s' ∪ rightOnlyCore Γ s s'
      ∪ remoteBothCore Γ s s' = Γ := by
    have h := core_partition Γ s s'
    rw [hbridge, Finset.union_empty] at h
    exact h
  have hfL : DependsOnlyOn
      (fun U : Config N G => f U * ∏ η ∈ leftOnlyCore Γ s s',
        blockActivity β χ η.val U)
      (s ∪ familySupport (fun η : Polymer N =>
        blockLinkSupport (N := N) η.val) (leftOnlyCore Γ s s')) :=
    dependsOnlyOn_mul_union hf
      (dependsOnlyOn_finsetProd _ _ _
        (fun η _ => blockActivity_dependsOnlyOn β χ η.val))
  have hgR : DependsOnlyOn
      (fun U : Config N G => g U * ∏ η ∈ rightOnlyCore Γ s s',
        blockActivity β χ η.val U)
      (s' ∪ familySupport (fun η : Polymer N =>
        blockLinkSupport (N := N) η.val) (rightOnlyCore Γ s s')) :=
    dependsOnlyOn_mul_union hg
      (dependsOnlyOn_finsetProd _ _ _
        (fun η _ => blockActivity_dependsOnlyOn β χ η.val))
  have mfL : Measurable
      (fun U : Config N G => f U * ∏ η ∈ leftOnlyCore Γ s s',
        blockActivity β χ η.val U) :=
    mf.mul (Finset.measurable_prod _
      (fun η _ => measurable_blockActivity β mχ η.val))
  have mgR : Measurable
      (fun U : Config N G => g U * ∏ η ∈ rightOnlyCore Γ s s',
        blockActivity β χ η.val U) :=
    mg.mul (Finset.measurable_prod _
      (fun η _ => measurable_blockActivity β mχ η.val))
  have hgR' : DependsOnlyOn
      (fun U : Config N G => g U * ∏ η ∈ rightOnlyCore Γ s s',
        blockActivity β χ η.val U)
      (s ∪ familySupport (fun η : Polymer N =>
        blockLinkSupport (N := N) η.val) (leftOnlyCore Γ s s'))ᶜ :=
    dependsOnlyOn_mono hgR
      (fun x hx => Set.disjoint_right.mp
        (disjoint_augmented_supports hss' hΓ) hx)
  have hprodM : (∏ C ∈ rawFamily (remoteBothCore Γ s s'),
      ∫ U : Config N G, blockActivity β χ C U
        ∂(configMeasure μm N))
      = ∏ η ∈ remoteBothCore Γ s s',
          polymerWeight (N := N) μm β χ η.val := by
    rw [show (∏ C ∈ rawFamily (remoteBothCore Γ s s'),
        ∫ U : Config N G, blockActivity β χ C U
          ∂(configMeasure μm N))
        = ∏ η ∈ remoteBothCore Γ s s',
            ∫ U : Config N G, blockActivity β χ η.val U
              ∂(configMeasure μm N) from
      Finset.prod_image (fun η _ θ _ h => Subtype.val_injective h)]
    exact Finset.prod_congr rfl
      (fun η _ => (polymerWeight_eq_integral μm β χ η.val).symm)
  calc twoMarkedFamilyIntegral μm β χ f g Γ
      = ∫ U : Config N G,
          ((f U * ∏ η ∈ leftOnlyCore Γ s s',
              blockActivity β χ η.val U)
            * (g U * ∏ η ∈ rightOnlyCore Γ s s',
                blockActivity β χ η.val U))
            * ∏ C ∈ rawFamily (remoteBothCore Γ s s'),
                blockActivity β χ C U
          ∂(configMeasure μm N) := by
        unfold twoMarkedFamilyIntegral
        congr 1
        funext U
        calc f U * g U * ∏ η ∈ Γ, blockActivity β χ η.val U
            = f U * g U * ∏ η ∈ (leftOnlyCore Γ s s'
                ∪ rightOnlyCore Γ s s' ∪ remoteBothCore Γ s s'),
                blockActivity β χ η.val U := by rw [hpart]
          _ = f U * g U
                * ((∏ η ∈ leftOnlyCore Γ s s',
                    blockActivity β χ η.val U)
                  * (∏ η ∈ rightOnlyCore Γ s s',
                      blockActivity β χ η.val U)
                  * ∏ η ∈ remoteBothCore Γ s s',
                      blockActivity β χ η.val U) := by
              rw [Finset.prod_union hLRM, Finset.prod_union hLR]
          _ = ((f U * ∏ η ∈ leftOnlyCore Γ s s',
                  blockActivity β χ η.val U)
                * (g U * ∏ η ∈ rightOnlyCore Γ s s',
                    blockActivity β χ η.val U))
                * ∏ η ∈ remoteBothCore Γ s s',
                    blockActivity β χ η.val U := by ring
          _ = ((f U * ∏ η ∈ leftOnlyCore Γ s s',
                  blockActivity β χ η.val U)
                * (g U * ∏ η ∈ rightOnlyCore Γ s s',
                    blockActivity β χ η.val U))
                * ∏ C ∈ rawFamily (remoteBothCore Γ s s'),
                    blockActivity β χ C U := by
              rw [show (∏ C ∈ rawFamily (remoteBothCore Γ s s'),
                  blockActivity β χ C U)
                  = ∏ η ∈ remoteBothCore Γ s s',
                      blockActivity β χ η.val U from
                Finset.prod_image
                  (fun η _ θ _ h => Subtype.val_injective h)]
    _ = (∫ U : Config N G,
          (f U * ∏ η ∈ leftOnlyCore Γ s s',
              blockActivity β χ η.val U)
            * (g U * ∏ η ∈ rightOnlyCore Γ s s',
                blockActivity β χ η.val U)
          ∂(configMeasure μm N))
        * ∏ C ∈ rawFamily (remoteBothCore Γ s s'),
            ∫ U : Config N G, blockActivity β χ C U
              ∂(configMeasure μm N) := by
        refine integral_mul_prod_blockActivity_of_disjoint μm β mχ
          (dependsOnlyOn_mul_union hfL hgR) (mfL.mul mgR)
          (rawFamily (remoteBothCore Γ s s')) ?_ ?_
        · intro C hC
          obtain ⟨η, hηM, rfl⟩ := Finset.mem_image.mp hC
          rw [Set.disjoint_union_right]
          exact ⟨remoteBoth_disjoint_left_augmented hΓ hηM,
            remoteBoth_disjoint_right_augmented hΓ hηM⟩
        · intro C hC D hD hCD
          obtain ⟨η, hηM, rfl⟩ := Finset.mem_image.mp hC
          obtain ⟨θ, hθM, rfl⟩ := Finset.mem_image.mp hD
          exact remoteBoth_pairwise_disjoint hΓ hηM hθM
            (fun he => hCD (congrArg Subtype.val he))
    _ = ((∫ U : Config N G,
          f U * ∏ η ∈ leftOnlyCore Γ s s',
              blockActivity β χ η.val U
          ∂(configMeasure μm N))
        * ∫ U : Config N G,
            g U * ∏ η ∈ rightOnlyCore Γ s s',
                blockActivity β χ η.val U
            ∂(configMeasure μm N))
        * ∏ C ∈ rawFamily (remoteBothCore Γ s s'),
            ∫ U : Config N G, blockActivity β χ C U
              ∂(configMeasure μm N) := by
        rw [integral_mul_of_disjoint_support (N := N) μm
          (s ∪ familySupport (fun η : Polymer N =>
            blockLinkSupport (N := N) η.val)
            (leftOnlyCore Γ s s'))
          hfL hgR' mfL mgR]
    _ = typedMarkedCoreWeight μm β χ f (leftOnlyCore Γ s s')
        * typedMarkedCoreWeight μm β χ g (rightOnlyCore Γ s s')
        * ∏ η ∈ remoteBothCore Γ s s',
            polymerWeight (N := N) μm β χ η.val := by
        rw [hprodM]
        rfl

#print axioms gibbsCovariance_eq_observableNumerator_cross
#print axioms twoMarkedFamilyIntegral_factorizes

end LatticeGauge
