/-
LatticeGauge/MutualIndependenceBeta0.lean — Phase 3, twenty-ninth
stone.

MUTUAL INDEPENDENCE OF LINK-DISJOINT FAMILIES AT β = 0 (architecture:
Sol/GPT-5.6; execution: Fable). Strictly stronger than pairwise
independence: EVERY finite subfamily satisfies the intersection-
product law, certified through Mathlib's official iIndepFun. Route:
the economical Finset induction — the head event against the
indicator of the tail intersection, using ONLY the binary
measure-level independence of stone 28. No n-ary split, no indexed
pushforward, no new Measure.pi engineering, no indicator integrals.
Mathlib then gives block-vs-block independence for free
(iIndepFun.indepFun_finset) — the measure-level generalization of
stone 27's one-vs-block. LIMITS: mutual independence under the β = 0
product state; pairwise link-disjoint supports; paths may share
vertices and repeat their own links; no joint tuple pushforward law
yet (stone 30); no statement for β > 0; no distance decay; no mass
gap; no area law; no confinement; no nontrivial cluster expansion.
Credit: stone 28 (binary measure-level independence), stone 29
(finite-intersection induction and mutual-independence API). NO
axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.WilsonLoop
import LatticeGauge.Beta0
import LatticeGauge.WilsonExpectation
import LatticeGauge.WilsonDisjointBeta0
import LatticeGauge.FiniteSupportFactorizationBeta0
import LatticeGauge.JointLawBeta0
import LatticeGauge.UnitaryChar
import LatticeGauge.HaarUnitary

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

section Events

variable {ι : Type*} [DecidableEq ι]

/-- **A1. The event of a finite subfamily**: every observable lands in
    its prescribed set. -/
def familyEvent (s : Finset ι) (f : ι → Config N G → ℝ)
    (sets : ι → Set ℝ) : Set (Config N G) :=
  ⋂ i ∈ s, f i ⁻¹' sets i

/-- **A2. The real-valued indicator of the family event.** -/
noncomputable def familyEventIndicator (s : Finset ι) (f : ι → Config N G → ℝ)
    (sets : ι → Set ℝ) : Config N G → ℝ :=
  (familyEvent s f sets).indicator (fun _ => (1 : ℝ))

section MeasurableG

variable [MeasurableSpace G]

/-- **B1. The family event is measurable.** -/
theorem measurableSet_familyEvent (s : Finset ι)
    (f : ι → Config N G → ℝ) (sets : ι → Set ℝ)
    (mf : ∀ i ∈ s, Measurable (f i))
    (msets : ∀ i ∈ s, MeasurableSet (sets i)) :
    MeasurableSet (familyEvent s f sets) := by
  classical
  revert mf msets
  induction s using Finset.induction_on with
  | empty =>
    intro _ _
    simp [familyEvent]
  | @insert a t ha ih =>
    intro mf msets
    have hhead : MeasurableSet (f a ⁻¹' sets a) :=
      (mf a (by simp)) (msets a (by simp))
    have htail : MeasurableSet (familyEvent t f sets) :=
      ih (fun i hi => mf i (Finset.mem_insert_of_mem hi))
        (fun i hi => msets i (Finset.mem_insert_of_mem hi))
    simpa [familyEvent, Set.biInter_insert] using hhead.inter htail

/-- **B2. The family-event indicator is measurable.** -/
theorem measurable_familyEventIndicator (s : Finset ι)
    (f : ι → Config N G → ℝ) (sets : ι → Set ℝ)
    (mf : ∀ i ∈ s, Measurable (f i))
    (msets : ∀ i ∈ s, MeasurableSet (sets i)) :
    Measurable (familyEventIndicator s f sets) :=
  measurable_const.indicator
    (measurableSet_familyEvent s f sets mf msets)

end MeasurableG

/-- **C. The preimage of {1} under the indicator is the event.** -/
theorem familyEventIndicator_preimage_one (s : Finset ι)
    (f : ι → Config N G → ℝ) (sets : ι → Set ℝ) :
    familyEventIndicator s f sets ⁻¹' ({1} : Set ℝ)
      = familyEvent s f sets := by
  ext U
  by_cases hU : U ∈ familyEvent s f sets
  · simp [familyEventIndicator, hU]
  · simp [familyEventIndicator, hU]

/-- **D. The indicator depends only on the union of the supports.** -/
theorem dependsOnlyOn_familyEventIndicator [NeZero N] (s : Finset ι)
    (f : ι → Config N G → ℝ) (sets : ι → Set ℝ)
    (supp : ι → Set (Link N))
    (hf : ∀ i ∈ s, DependsOnlyOn (f i) (supp i)) :
    DependsOnlyOn (familyEventIndicator s f sets)
      (familySupport supp s) := by
  classical
  intro U V hUV
  have hmem : U ∈ familyEvent s f sets ↔ V ∈ familyEvent s f sets := by
    simp only [familyEvent, Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h i hi
      have hfi : f i U = f i V :=
        hf i hi U V (by
          intro ℓ hℓ
          exact hUV ℓ ⟨i, hi, hℓ⟩)
      simpa [hfi] using h i hi
    · intro h i hi
      have hfi : f i U = f i V :=
        hf i hi U V (by
          intro ℓ hℓ
          exact hUV ℓ ⟨i, hi, hℓ⟩)
      simpa [hfi] using h i hi
  by_cases hU : U ∈ familyEvent s f sets
  · have hV := hmem.mp hU
    simp [familyEventIndicator, hU, hV]
  · have hV : V ∉ familyEvent s f sets := by
      intro hv
      exact hU (hmem.mpr hv)
    simp [familyEventIndicator, hU, hV]

/-- **E. Head support is disjoint from the tail family support.** -/
theorem disjoint_familySupport_of_pairwise [NeZero N]
    {a : ι} {t : Finset ι} (ha : a ∉ t)
    (supp : ι → Set (Link N))
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j → Disjoint (supp i) (supp j)) :
    Disjoint (supp a) (familySupport supp t) := by
  refine Set.disjoint_left.2 ?_
  intro ℓ hℓa hℓt
  rcases hℓt with ⟨j, hj, hℓj⟩
  have haj : a ≠ j := by
    intro h
    apply ha
    simpa [h] using hj
  exact Set.disjoint_left.1 (hdisj haj) hℓa hℓj

end Events

section Measure

variable [MeasurableSpace G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **F. MAIN THEOREM (pedra 29): MUTUAL INDEPENDENCE.** A family of
    observables with pairwise link-disjoint supports is mutually
    independent under the β = 0 product state: every finite subfamily
    satisfies the intersection-product law. Route: Finset induction
    lifting the BINARY independence of stone 28 (head vs tail-event
    indicator). -/
theorem iIndepFun_of_pairwise_disjoint_support [NeZero N]
    {ι : Type*} [DecidableEq ι]
    (f : ι → Config N G → ℝ) (supp : ι → Set (Link N))
    (hf : ∀ i, DependsOnlyOn (f i) (supp i))
    (mf : ∀ i, Measurable (f i))
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j → Disjoint (supp i) (supp j)) :
    ProbabilityTheory.iIndepFun (fun _ : ι => borel ℝ) f
      (configMeasure μm N) := by
  classical
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s sets msets
  revert msets
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp
  | @insert a t ha ih =>
    intro msets
    have hEa : MeasurableSet (sets a) := msets a (by simp)
    have hEt : MeasurableSet (familyEvent t f sets) :=
      measurableSet_familyEvent t f sets (fun i _ => mf i)
        (fun i hi => msets i (Finset.mem_insert_of_mem hi))
    have mI : Measurable (familyEventIndicator t f sets) :=
      measurable_const.indicator hEt
    have hI : DependsOnlyOn (familyEventIndicator t f sets)
        (familySupport supp t) :=
      dependsOnlyOn_familyEventIndicator t f sets supp
        (fun i _ => hf i)
    have hsep : Disjoint (supp a) (familySupport supp t) :=
      disjoint_familySupport_of_pairwise ha supp hdisj
    have hind : ProbabilityTheory.IndepFun (f a)
        (familyEventIndicator t f sets) (configMeasure μm N) :=
      indepFun_of_disjoint_support (N := N) μm (hf a) hI (mf a) mI hsep
    have hpair := hind.measure_inter_preimage_eq_mul (sets a)
      ({1} : Set ℝ) hEa (measurableSet_singleton 1)
    rw [familyEventIndicator_preimage_one] at hpair
    unfold familyEvent at hpair
    rw [Finset.set_biInter_insert, hpair,
      ih (fun i hi => msets i (Finset.mem_insert_of_mem hi)),
      Finset.prod_insert ha]

/-- **G. BLOCK-VS-BLOCK independence at the measure level** — the
    measure-level generalization of stone 27's one-vs-block. NOT a
    new notion: the official corollary of Mathlib's iIndepFun API. -/
theorem indepFun_blocks_of_pairwise_disjoint_support [NeZero N]
    {ι : Type*} [DecidableEq ι]
    (f : ι → Config N G → ℝ) (supp : ι → Set (Link N))
    (hf : ∀ i, DependsOnlyOn (f i) (supp i))
    (mf : ∀ i, Measurable (f i))
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j → Disjoint (supp i) (supp j))
    (S T : Finset ι) (hST : Disjoint S T) :
    ProbabilityTheory.IndepFun
      (fun U (i : S) => f i U)
      (fun U (i : T) => f i U)
      (configMeasure μm N) := by
  have hmut := iIndepFun_of_pairwise_disjoint_support (N := N) μm
    f supp hf mf hdisj
  exact hmut.indepFun_finset S T hST mf

end Measure

/-! ## Wilson observables -/

section Wilson

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]
variable {χ : G → ℝ}

/-- **H. Families of pairwise link-disjoint Wilson paths are MUTUALLY
    independent at β = 0.** The index type ι may be arbitrary: mutual
    independence already quantifies over all finite subfamilies. -/
theorem iIndepFun_wilsonPaths_of_pairwise_disjoint [NeZero N]
    {ι : Type*} [DecidableEq ι] (mχ : Measurable χ)
    (x : ι → Site N) (p : ι → List Step)
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j →
      Disjoint (pathLinkSet (N := N) (x i) (p i))
        (pathLinkSet (N := N) (x j) (p j))) :
    ProbabilityTheory.iIndepFun (fun _ : ι => borel ℝ)
      (fun i U => wilsonLoop χ U (x i) (p i))
      (configMeasure μm N) :=
  iIndepFun_of_pairwise_disjoint_support (N := N) μm
    (fun i U => wilsonLoop χ U (x i) (p i))
    (fun i => pathLinkSet (N := N) (x i) (p i))
    (fun i => wilsonPath_dependsOnlyOn_pathLinkSet χ (x i) (p i))
    (fun i => measurable_wilsonLoop mχ (x i) (p i))
    hdisj

/-- **I1. Physical wrapper: families of closed, pairwise link-disjoint
    Wilson LOOPS are mutually independent at β = 0.** -/
theorem iIndepFun_wilsonLoops_of_pairwise_disjoint [NeZero N]
    {ι : Type*} [DecidableEq ι] (mχ : Measurable χ)
    (x : ι → Site N) (p : ι → List Step)
    (_hclosed : ∀ i, IsClosed (x i) (p i))
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j →
      Disjoint (pathLinkSet (N := N) (x i) (p i))
        (pathLinkSet (N := N) (x j) (p j))) :
    ProbabilityTheory.iIndepFun (fun _ : ι => borel ℝ)
      (fun i U => wilsonLoop χ U (x i) (p i))
      (configMeasure μm N) :=
  iIndepFun_wilsonPaths_of_pairwise_disjoint μm mχ x p hdisj

end Wilson

/-- **I2. UNCONDITIONAL on U(n): families of closed, pairwise
    link-disjoint Wilson loops are mutually independent at β = 0** —
    only structural conditions remain. -/
theorem iIndepFun_unitaryWilsonLoops_of_pairwise_disjoint
    (n : ℕ) [NeZero n] {N : ℕ} [NeZero N]
    {ι : Type*} [DecidableEq ι]
    (x : ι → Site N) (p : ι → List Step)
    (_hclosed : ∀ i, IsClosed (x i) (p i))
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j →
      Disjoint (pathLinkSet (N := N) (x i) (p i))
        (pathLinkSet (N := N) (x j) (p j))) :
    ProbabilityTheory.iIndepFun (fun _ : ι => borel ℝ)
      (fun i U => wilsonLoop (uChar n) U (x i) (p i))
      (configMeasure (haarU n) N) :=
  iIndepFun_wilsonPaths_of_pairwise_disjoint (haarU n)
    (measurable_uChar n) x p hdisj

end LatticeGauge
