/-
LatticeGauge/JointTupleLawBeta0.lean — Phase 3, thirtieth stone.

FINITE JOINT TUPLE PUSHFORWARD LAW (architecture: Sol/GPT-5.6;
execution: Fable). ARCHITECTURAL PROMOTION: the main theorem is
purely probabilistic — for ANY finite family of mutually independent
real random variables, the law of the tuple equals the finite product
of the marginal laws — mirroring the Mathlib-internal pattern of
measurePreserving_pi (Measure.pi_eq + map_apply + measurable
rectangles), with the intersection law supplied here by iIndepFun
instead of pre-built coordinates. Only afterwards specialized to
disjoint supports, Wilson paths, closed loops and U(n). This turns
"all events factorize" (stone 29) into the concrete statement that
the whole random vector has exactly the product distribution.
CONSISTENCY NOTES (documented, not separately proved, per the
architect's instruction): for ι = Fin 1 the tuple law collapses to
the single marginal; for ι = Fin 2, composing with the measurable
equivalence (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ conceptually recovers the binary
joint law of stone 28 — the Prod-equivalence bookkeeping is not
formalized here to avoid opening a new elaboration front.
LIMITS: finite index type only; exact joint pushforward law, stronger
than all finite moment factorizations; derived from stone 29;
pairwise link-disjoint supports; paths may share vertices and repeat
their own links; no infinite joint products; no statement for β > 0;
no distance decay; no mass gap; no area law; no confinement; no
cluster expansion. Credit: stone 28 (binary joint law), stone 29
(mutual independence), stone 30 (finite joint tuple law). NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.WilsonLoop
import LatticeGauge.Beta0
import LatticeGauge.WilsonExpectation
import LatticeGauge.WilsonDisjointBeta0
import LatticeGauge.FiniteSupportFactorizationBeta0
import LatticeGauge.JointLawBeta0
import LatticeGauge.MutualIndependenceBeta0
import LatticeGauge.UnitaryChar
import LatticeGauge.HaarUnitary

open MeasureTheory

namespace LatticeGauge

section GenericJointTuple

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **A. GENERIC JOINT TUPLE LAW**: the pushforward of the tuple of a
    mutually independent finite family of real random variables is the
    finite product of the marginal pushforwards. Purely probabilistic —
    no lattice content. -/
theorem map_jointTuple_eq_pi_marginals
    (f : ι → Ω → ℝ) (mf : ∀ i, Measurable (f i))
    (hmut : ProbabilityTheory.iIndepFun (fun _ : ι => borel ℝ) f μ) :
    Measure.map (fun ω i => f i ω) μ
      = Measure.pi (fun i => Measure.map (f i) μ) := by
  classical
  haveI : ∀ i, IsProbabilityMeasure (Measure.map (f i) μ) :=
    fun i => isProbabilityMeasure_map (mf i).aemeasurable
  have mtuple : Measurable (fun ω (i : ι) => f i ω) :=
    measurable_pi_iff.mpr mf
  refine (Measure.pi_eq ?_).symm
  intro sets hsets
  have hcyl : MeasurableSet (Set.pi Set.univ sets) :=
    MeasurableSet.univ_pi hsets
  have hpre : (fun ω (i : ι) => f i ω) ⁻¹' Set.pi Set.univ sets
      = ⋂ i ∈ (Finset.univ : Finset ι), f i ⁻¹' sets i := by
    ext ω
    simp [Set.mem_pi]
  have hrect := hmut.measure_inter_preimage_eq_mul
    (Finset.univ : Finset ι) (sets := sets) (fun i _ => hsets i)
  rw [Measure.map_apply mtuple hcyl, hpre, hrect]
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [Measure.map_apply (mf i) (hsets i)]

/-- **B. MeasurePreserving form** — the main API for future
    composition. -/
theorem measurePreserving_jointTuple
    (f : ι → Ω → ℝ) (mf : ∀ i, Measurable (f i))
    (hmut : ProbabilityTheory.iIndepFun (fun _ : ι => borel ℝ) f μ) :
    MeasurePreserving (fun ω i => f i ω) μ
      (Measure.pi fun i => Measure.map (f i) μ) :=
  ⟨measurable_pi_iff.mpr mf,
    map_jointTuple_eq_pi_marginals μ f mf hmut⟩

end GenericJointTuple

variable {N : ℕ} {G : Type*} [Group G]

section Measure

variable [MeasurableSpace G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **C1. Joint tuple law for observables with pairwise disjoint
    supports at β = 0.** -/
theorem map_jointTuple_eq_pi_marginals_of_disjoint_support [NeZero N]
    {ι : Type*} [Fintype ι]
    (f : ι → Config N G → ℝ) (supp : ι → Set (Link N))
    (hf : ∀ i, DependsOnlyOn (f i) (supp i))
    (mf : ∀ i, Measurable (f i))
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j → Disjoint (supp i) (supp j)) :
    Measure.map (fun U i => f i U) (configMeasure μm N)
      = Measure.pi
          (fun i => Measure.map (f i) (configMeasure μm N)) := by
  classical
  have hmut := iIndepFun_of_pairwise_disjoint_support (N := N) μm
    f supp hf mf hdisj
  exact map_jointTuple_eq_pi_marginals (configMeasure μm N) f mf hmut

/-- **C2. MeasurePreserving form for disjoint supports.** -/
theorem measurePreserving_jointTuple_of_disjoint_support [NeZero N]
    {ι : Type*} [Fintype ι]
    (f : ι → Config N G → ℝ) (supp : ι → Set (Link N))
    (hf : ∀ i, DependsOnlyOn (f i) (supp i))
    (mf : ∀ i, Measurable (f i))
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j → Disjoint (supp i) (supp j)) :
    MeasurePreserving (fun U i => f i U) (configMeasure μm N)
      (Measure.pi
        fun i => Measure.map (f i) (configMeasure μm N)) := by
  classical
  have hmut := iIndepFun_of_pairwise_disjoint_support (N := N) μm
    f supp hf mf hdisj
  exact measurePreserving_jointTuple (configMeasure μm N) f mf hmut

end Measure

/-! ## Wilson observables -/

section Wilson

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]
variable {χ : G → ℝ}

/-- **D. Joint tuple law for pairwise link-disjoint Wilson paths at
    β = 0**: the random vector of Wilson observables has exactly the
    product distribution of its marginals. -/
theorem map_jointTuple_wilsonPaths_eq_pi_marginals [NeZero N]
    {ι : Type*} [Fintype ι] (mχ : Measurable χ)
    (x : ι → Site N) (p : ι → List Step)
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j →
      Disjoint (pathLinkSet (N := N) (x i) (p i))
        (pathLinkSet (N := N) (x j) (p j))) :
    Measure.map (fun U i => wilsonLoop χ U (x i) (p i))
        (configMeasure μm N)
      = Measure.pi
          (fun i => Measure.map
            (fun U => wilsonLoop χ U (x i) (p i))
            (configMeasure μm N)) :=
  map_jointTuple_eq_pi_marginals_of_disjoint_support (N := N) μm
    (fun i U => wilsonLoop χ U (x i) (p i))
    (fun i => pathLinkSet (N := N) (x i) (p i))
    (fun i => wilsonPath_dependsOnlyOn_pathLinkSet χ (x i) (p i))
    (fun i => measurable_wilsonLoop mχ (x i) (p i))
    hdisj

/-- **E1. Physical wrapper: joint tuple law for closed, pairwise
    link-disjoint Wilson LOOPS at β = 0.** -/
theorem map_jointTuple_wilsonLoops_eq_pi_marginals [NeZero N]
    {ι : Type*} [Fintype ι] (mχ : Measurable χ)
    (x : ι → Site N) (p : ι → List Step)
    (_hclosed : ∀ i, IsClosed (x i) (p i))
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j →
      Disjoint (pathLinkSet (N := N) (x i) (p i))
        (pathLinkSet (N := N) (x j) (p j))) :
    Measure.map (fun U i => wilsonLoop χ U (x i) (p i))
        (configMeasure μm N)
      = Measure.pi
          (fun i => Measure.map
            (fun U => wilsonLoop χ U (x i) (p i))
            (configMeasure μm N)) :=
  map_jointTuple_wilsonPaths_eq_pi_marginals μm mχ x p hdisj

/-- **E2. Physical wrapper: MeasurePreserving form for closed
    loops.** -/
theorem measurePreserving_jointTuple_wilsonLoops [NeZero N]
    {ι : Type*} [Fintype ι] (mχ : Measurable χ)
    (x : ι → Site N) (p : ι → List Step)
    (_hclosed : ∀ i, IsClosed (x i) (p i))
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j →
      Disjoint (pathLinkSet (N := N) (x i) (p i))
        (pathLinkSet (N := N) (x j) (p j))) :
    MeasurePreserving (fun U i => wilsonLoop χ U (x i) (p i))
      (configMeasure μm N)
      (Measure.pi
        fun i => Measure.map
          (fun U => wilsonLoop χ U (x i) (p i))
          (configMeasure μm N)) :=
  measurePreserving_jointTuple_of_disjoint_support (N := N) μm
    (fun i U => wilsonLoop χ U (x i) (p i))
    (fun i => pathLinkSet (N := N) (x i) (p i))
    (fun i => wilsonPath_dependsOnlyOn_pathLinkSet χ (x i) (p i))
    (fun i => measurable_wilsonLoop mχ (x i) (p i))
    hdisj

end Wilson

/-! ## Concrete corollaries on U(n) with Haar measure -/

/-- **F1. UNCONDITIONAL on U(n): the random vector of closed,
    pairwise link-disjoint Wilson loops has exactly the product
    distribution at β = 0** — only structural conditions remain. -/
theorem map_jointTuple_unitaryWilsonLoops_eq_pi_marginals
    (n : ℕ) [NeZero n] {N : ℕ} [NeZero N]
    {ι : Type*} [Fintype ι]
    (x : ι → Site N) (p : ι → List Step)
    (_hclosed : ∀ i, IsClosed (x i) (p i))
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j →
      Disjoint (pathLinkSet (N := N) (x i) (p i))
        (pathLinkSet (N := N) (x j) (p j))) :
    Measure.map (fun U i => wilsonLoop (uChar n) U (x i) (p i))
        (configMeasure (haarU n) N)
      = Measure.pi
          (fun i => Measure.map
            (fun U => wilsonLoop (uChar n) U (x i) (p i))
            (configMeasure (haarU n) N)) :=
  map_jointTuple_wilsonPaths_eq_pi_marginals (haarU n)
    (measurable_uChar n) x p hdisj

/-- **F2. UNCONDITIONAL on U(n): MeasurePreserving form.** -/
theorem measurePreserving_jointTuple_unitaryWilsonLoops
    (n : ℕ) [NeZero n] {N : ℕ} [NeZero N]
    {ι : Type*} [Fintype ι]
    (x : ι → Site N) (p : ι → List Step)
    (_hclosed : ∀ i, IsClosed (x i) (p i))
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j →
      Disjoint (pathLinkSet (N := N) (x i) (p i))
        (pathLinkSet (N := N) (x j) (p j))) :
    MeasurePreserving
      (fun U i => wilsonLoop (uChar n) U (x i) (p i))
      (configMeasure (haarU n) N)
      (Measure.pi
        fun i => Measure.map
          (fun U => wilsonLoop (uChar n) U (x i) (p i))
          (configMeasure (haarU n) N)) :=
  measurePreserving_jointTuple_wilsonLoops (haarU n)
    (measurable_uChar n) x p _hclosed hdisj

end LatticeGauge
