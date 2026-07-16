/-
LatticeGauge/ComposedTupleLawBeta0.lean — Phase 3, thirty-first stone.

COORDINATE-WISE POST-COMPOSITION PRESERVES THE JOINT TUPLE LAW
(architecture: Sol/GPT-5.6, route A; execution: Fable). For any finite
family of mutually independent real random variables and any family of
measurable transformations gᵢ : ℝ → ℝ, the law of the transformed
tuple is the finite product of the transformed marginal laws:
map (fun ω i => gᵢ(fᵢ ω)) μ = pi (fun i => map gᵢ (map fᵢ μ)).
Consequence: EVERY derived statistic of link-disjoint Wilson loops
(powers, test functions, indicators, ...) inherits the product law at
β = 0. Independence of the composed family comes from Mathlib's
iIndepFun.comp (signature verified in the v4.15 source); the tuple law
comes from stone 30; marginals are normalized by Measure.map_map.
API NOTE (executor): both Mathlib names used here were verified in the
pinned source today — iIndepFun.comp (Probability/Independence/Basic,
line 566) and Measure.map_map (Measure/MeasureSpace, line 1291).
DELIBERATE RESTRICTIONS (architect): simple types only — no dependent
codomains, no block subtypes, no Finset-indexed families. LIMITS:
finite index type; exact laws at β = 0; pairwise link-disjoint
supports for the lattice corollaries; no claim about cluster
expansion, thermodynamics, mass gap, entanglement or continuum limit.
Credit: stone 29 (mutual independence), stone 30 (joint tuple law),
stone 31 (post-composition stability). NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.WilsonLoop
import LatticeGauge.Beta0
import LatticeGauge.WilsonExpectation
import LatticeGauge.WilsonDisjointBeta0
import LatticeGauge.MutualIndependenceBeta0
import LatticeGauge.JointTupleLawBeta0
import LatticeGauge.UnitaryChar
import LatticeGauge.HaarUnitary

open MeasureTheory

namespace LatticeGauge

section GenericComposedTuple

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **A. GENERIC: post-composition preserves the joint tuple law.**
    The transformed tuple of a mutually independent family has the
    product distribution of the transformed marginals. -/
theorem map_jointTuple_comp_eq_pi_marginals
    (f : ι → Ω → ℝ) (g : ι → ℝ → ℝ)
    (mf : ∀ i, Measurable (f i)) (mg : ∀ i, Measurable (g i))
    (hmut : ProbabilityTheory.iIndepFun (fun _ : ι => borel ℝ) f μ) :
    Measure.map (fun ω i => g i (f i ω)) μ
      = Measure.pi
          (fun i => Measure.map (g i) (Measure.map (f i) μ)) := by
  have hcomp : ProbabilityTheory.iIndepFun (fun _ : ι => borel ℝ)
      (fun i => g i ∘ f i) μ := hmut.comp g mg
  have h := map_jointTuple_eq_pi_marginals μ (fun i => g i ∘ f i)
    (fun i => (mg i).comp (mf i)) hcomp
  calc Measure.map (fun ω i => g i (f i ω)) μ
      = Measure.pi (fun i => Measure.map (g i ∘ f i) μ) := h
    _ = Measure.pi
          (fun i => Measure.map (g i) (Measure.map (f i) μ)) := by
        congr 1
        funext i
        exact (Measure.map_map (mg i) (mf i)).symm

/-- **B. MeasurePreserving form of the composed tuple law.** -/
theorem measurePreserving_jointTuple_comp
    (f : ι → Ω → ℝ) (g : ι → ℝ → ℝ)
    (mf : ∀ i, Measurable (f i)) (mg : ∀ i, Measurable (g i))
    (hmut : ProbabilityTheory.iIndepFun (fun _ : ι => borel ℝ) f μ) :
    MeasurePreserving (fun ω i => g i (f i ω)) μ
      (Measure.pi
        fun i => Measure.map (g i) (Measure.map (f i) μ)) :=
  ⟨measurable_pi_iff.mpr fun i => (mg i).comp (mf i),
    map_jointTuple_comp_eq_pi_marginals μ f g mf mg hmut⟩

end GenericComposedTuple

variable {N : ℕ} {G : Type*} [Group G]

section Measure

variable [MeasurableSpace G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **C. Composed tuple law for observables with pairwise disjoint
    supports at β = 0.** -/
theorem map_jointTuple_comp_eq_pi_marginals_of_disjoint_support
    [NeZero N] {ι : Type*} [Fintype ι]
    (f : ι → Config N G → ℝ) (supp : ι → Set (Link N))
    (g : ι → ℝ → ℝ)
    (hf : ∀ i, DependsOnlyOn (f i) (supp i))
    (mf : ∀ i, Measurable (f i)) (mg : ∀ i, Measurable (g i))
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j → Disjoint (supp i) (supp j)) :
    Measure.map (fun U i => g i (f i U)) (configMeasure μm N)
      = Measure.pi
          (fun i => Measure.map (g i)
            (Measure.map (f i) (configMeasure μm N))) := by
  classical
  exact map_jointTuple_comp_eq_pi_marginals (configMeasure μm N)
    f g mf mg
    (iIndepFun_of_pairwise_disjoint_support (N := N) μm f supp
      hf mf hdisj)

end Measure

/-! ## Wilson observables -/

section Wilson

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]
variable {χ : G → ℝ}

/-- **D. Derived statistics of link-disjoint Wilson paths inherit the
    product law at β = 0**: any measurable transformations applied
    coordinate-wise. -/
theorem map_jointTuple_comp_wilsonPaths_eq_pi_marginals [NeZero N]
    {ι : Type*} [Fintype ι] (mχ : Measurable χ)
    (x : ι → Site N) (p : ι → List Step) (g : ι → ℝ → ℝ)
    (mg : ∀ i, Measurable (g i))
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j →
      Disjoint (pathLinkSet (N := N) (x i) (p i))
        (pathLinkSet (N := N) (x j) (p j))) :
    Measure.map (fun U i => g i (wilsonLoop χ U (x i) (p i)))
        (configMeasure μm N)
      = Measure.pi
          (fun i => Measure.map (g i)
            (Measure.map (fun U => wilsonLoop χ U (x i) (p i))
              (configMeasure μm N))) :=
  map_jointTuple_comp_eq_pi_marginals_of_disjoint_support (N := N) μm
    (fun i U => wilsonLoop χ U (x i) (p i))
    (fun i => pathLinkSet (N := N) (x i) (p i)) g
    (fun i => wilsonPath_dependsOnlyOn_pathLinkSet χ (x i) (p i))
    (fun i => measurable_wilsonLoop mχ (x i) (p i)) mg hdisj

/-- **E. Physical wrapper: derived statistics of closed, pairwise
    link-disjoint Wilson LOOPS inherit the product law at β = 0.** -/
theorem map_jointTuple_comp_wilsonLoops_eq_pi_marginals [NeZero N]
    {ι : Type*} [Fintype ι] (mχ : Measurable χ)
    (x : ι → Site N) (p : ι → List Step) (g : ι → ℝ → ℝ)
    (mg : ∀ i, Measurable (g i))
    (_hclosed : ∀ i, IsClosed (x i) (p i))
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j →
      Disjoint (pathLinkSet (N := N) (x i) (p i))
        (pathLinkSet (N := N) (x j) (p j))) :
    Measure.map (fun U i => g i (wilsonLoop χ U (x i) (p i)))
        (configMeasure μm N)
      = Measure.pi
          (fun i => Measure.map (g i)
            (Measure.map (fun U => wilsonLoop χ U (x i) (p i))
              (configMeasure μm N))) :=
  map_jointTuple_comp_wilsonPaths_eq_pi_marginals μm mχ x p g mg hdisj

end Wilson

/-- **F. UNCONDITIONAL on U(n): derived statistics of closed, pairwise
    link-disjoint Wilson loops have the product law at β = 0** — only
    structural conditions and measurability of the transformations
    remain. -/
theorem map_jointTuple_comp_unitaryWilsonLoops_eq_pi_marginals
    (n : ℕ) [NeZero n] {N : ℕ} [NeZero N]
    {ι : Type*} [Fintype ι]
    (x : ι → Site N) (p : ι → List Step) (g : ι → ℝ → ℝ)
    (mg : ∀ i, Measurable (g i))
    (_hclosed : ∀ i, IsClosed (x i) (p i))
    (hdisj : ∀ ⦃i j : ι⦄, i ≠ j →
      Disjoint (pathLinkSet (N := N) (x i) (p i))
        (pathLinkSet (N := N) (x j) (p j))) :
    Measure.map
        (fun U i => g i (wilsonLoop (uChar n) U (x i) (p i)))
        (configMeasure (haarU n) N)
      = Measure.pi
          (fun i => Measure.map (g i)
            (Measure.map
              (fun U => wilsonLoop (uChar n) U (x i) (p i))
              (configMeasure (haarU n) N))) :=
  map_jointTuple_comp_wilsonPaths_eq_pi_marginals (haarU n)
    (measurable_uChar n) x p g mg hdisj

end LatticeGauge
