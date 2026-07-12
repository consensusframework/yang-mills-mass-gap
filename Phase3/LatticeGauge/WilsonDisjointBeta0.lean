/-
LatticeGauge/WilsonDisjointBeta0.lean — Phase 3, twenty-fifth stone.

EXACT FACTORIZATION OF LINK-DISJOINT WILSON OBSERVABLES AT β = 0
(architecture: Sol/GPT-5.6; execution: Fable). The probabilistic
factorization theorem was proved in stone 11 (Beta0.lean); the novelty
here is the GEOMETRIC API for Wilson observables: the support of a
path is the set of visited links (pathLinkSet), each Wilson path
depends only on its support, and support monotonicity transports the
second observable to the complement. Valid for empty paths and paths
that revisit their own links — the ONLY separation required is between
the two supports. LIMITS: exact independence of the product state at
β = 0; link-disjoint (not necessarily vertex-disjoint); NOT distance
decay; NOT a mass gap; NOT an area law; NOT confinement; no claim for
β > 0; no nontrivial cluster expansion. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.WilsonLoop
import LatticeGauge.Beta0
import LatticeGauge.HolonomyHaar
import LatticeGauge.WilsonExpectation
import LatticeGauge.UnitaryChar
import LatticeGauge.HaarUnitary

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

/-- **A. The support of a lattice path**: the set of link variables it
    visits, regardless of traversal orientation (stepLink already
    canonicalizes backward steps through shiftBack). Two paths may
    share vertices; disjointness means no shared LINKS. -/
def pathLinkSet [NeZero N] (x : Site N) (p : List Step) :
    Set (Link N) :=
  {ℓ | ℓ ∈ pathLinks x p}

/-- **B. Support monotonicity** for DependsOnlyOn. -/
theorem dependsOnlyOn_mono [NeZero N]
    {f : Config N G → ℝ} {s t : Set (Link N)}
    (hf : DependsOnlyOn f s) (hst : s ⊆ t) :
    DependsOnlyOn f t := by
  intro U V hUV
  apply hf
  intro ℓ hℓ
  exact hUV ℓ (hst hℓ)

/-- **C. A Wilson path depends only on its visited links.** -/
theorem wilsonPath_dependsOnlyOn_pathLinkSet [NeZero N]
    (χ : G → ℝ) (x : Site N) (p : List Step) :
    DependsOnlyOn (fun U : Config N G => wilsonLoop χ U x p)
      (pathLinkSet x p) := by
  intro U V hUV
  unfold wilsonLoop
  congr 1
  apply holonomy_congr_on_pathLinks p x U V
  intro ℓ hℓ
  exact hUV ℓ (by simpa [pathLinkSet] using hℓ)

section Measure

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]
variable {χ : G → ℝ}

/-- **D. FACTORIZATION OF TWO LINK-DISJOINT WILSON PATHS AT β = 0:**
    ⟨W₁ · W₂⟩₀ = ⟨W₁⟩₀ · ⟨W₂⟩₀. No Nodup, no nonemptiness, no Haar
    invariance — only disjointness of the two supports. -/
theorem gibbsExpectation_mul_wilsonPaths_zero_of_disjoint
    [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ)
    (x₁ x₂ : Site N) (p₁ p₂ : List Step)
    (hdisj : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂)) :
    gibbsExpectation (N := N) μm 0 χ
        (fun U => wilsonLoop χ U x₁ p₁ * wilsonLoop χ U x₂ p₂)
      = gibbsExpectation (N := N) μm 0 χ
          (fun U => wilsonLoop χ U x₁ p₁)
        * gibbsExpectation (N := N) μm 0 χ
            (fun U => wilsonLoop χ U x₂ p₂) := by
  classical
  have hW₁ := wilsonPath_dependsOnlyOn_pathLinkSet
    (N := N) (G := G) χ x₁ p₁
  have hW₂ := wilsonPath_dependsOnlyOn_pathLinkSet
    (N := N) (G := G) χ x₂ p₂
  have hs₂c : pathLinkSet (N := N) x₂ p₂
      ⊆ (pathLinkSet (N := N) x₁ p₁)ᶜ := by
    intro ℓ hℓ₂
    exact Set.mem_compl_iff.mpr fun hℓ₁ =>
      Set.disjoint_left.1 hdisj hℓ₁ hℓ₂
  have hW₂c : DependsOnlyOn
      (fun U : Config N G => wilsonLoop χ U x₂ p₂)
      (pathLinkSet (N := N) x₁ p₁)ᶜ :=
    dependsOnlyOn_mono hW₂ hs₂c
  rw [gibbsExpectation_zero (N := N) μm χ,
    gibbsExpectation_zero (N := N) μm χ,
    gibbsExpectation_zero (N := N) μm χ]
  exact integral_mul_of_disjoint_support (N := N) μm
    (pathLinkSet (N := N) x₁ p₁) hW₁ hW₂c
    (measurable_wilsonLoop mχ x₁ p₁)
    (measurable_wilsonLoop mχ x₂ p₂)

/-- **E. Vanishing truncated correlation of link-disjoint Wilson paths
    at β = 0.** -/
theorem truncatedCorrelation_wilsonPaths_zero_of_disjoint
    [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ)
    (x₁ x₂ : Site N) (p₁ p₂ : List Step)
    (hdisj : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂)) :
    truncatedCorrelation (N := N) μm 0 χ
      (fun U => wilsonLoop χ U x₁ p₁)
      (fun U => wilsonLoop χ U x₂ p₂) = 0 := by
  classical
  have hW₁ := wilsonPath_dependsOnlyOn_pathLinkSet
    (N := N) (G := G) χ x₁ p₁
  have hW₂ := wilsonPath_dependsOnlyOn_pathLinkSet
    (N := N) (G := G) χ x₂ p₂
  have hs₂c : pathLinkSet (N := N) x₂ p₂
      ⊆ (pathLinkSet (N := N) x₁ p₁)ᶜ := by
    intro ℓ hℓ₂
    exact Set.mem_compl_iff.mpr fun hℓ₁ =>
      Set.disjoint_left.1 hdisj hℓ₁ hℓ₂
  have hW₂c : DependsOnlyOn
      (fun U : Config N G => wilsonLoop χ U x₂ p₂)
      (pathLinkSet (N := N) x₁ p₁)ᶜ :=
    dependsOnlyOn_mono hW₂ hs₂c
  exact truncatedCorrelation_zero_beta_zero (N := N) μm χ
    (pathLinkSet (N := N) x₁ p₁) hW₁ hW₂c
    (measurable_wilsonLoop mχ x₁ p₁)
    (measurable_wilsonLoop mχ x₂ p₂)

/-- **F1. Physical wrapper: factorization of two closed, link-disjoint
    Wilson LOOPS at β = 0.** The closedness hypotheses certify both
    observables are the gauge-invariant physical loops; the
    factorization itself uses only support disjointness. -/
theorem gibbsExpectation_mul_wilsonLoops_zero_of_disjoint
    [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ)
    (x₁ x₂ : Site N) (p₁ p₂ : List Step)
    (_hp₁ : IsClosed x₁ p₁) (_hp₂ : IsClosed x₂ p₂)
    (hdisj : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂)) :
    gibbsExpectation (N := N) μm 0 χ
        (fun U => wilsonLoop χ U x₁ p₁ * wilsonLoop χ U x₂ p₂)
      = gibbsExpectation (N := N) μm 0 χ
          (fun U => wilsonLoop χ U x₁ p₁)
        * gibbsExpectation (N := N) μm 0 χ
            (fun U => wilsonLoop χ U x₂ p₂) :=
  gibbsExpectation_mul_wilsonPaths_zero_of_disjoint μm mχ x₁ x₂ p₁ p₂ hdisj

/-- **F2. Physical wrapper: vanishing truncated correlation of two
    closed, link-disjoint Wilson loops at β = 0.** -/
theorem truncatedCorrelation_wilsonLoops_zero_of_disjoint
    [NeZero N] [Fintype (Site N)]
    (mχ : Measurable χ)
    (x₁ x₂ : Site N) (p₁ p₂ : List Step)
    (_hp₁ : IsClosed x₁ p₁) (_hp₂ : IsClosed x₂ p₂)
    (hdisj : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂)) :
    truncatedCorrelation (N := N) μm 0 χ
      (fun U => wilsonLoop χ U x₁ p₁)
      (fun U => wilsonLoop χ U x₂ p₂) = 0 :=
  truncatedCorrelation_wilsonPaths_zero_of_disjoint μm mχ x₁ x₂ p₁ p₂ hdisj

end Measure

/-! ## Concrete corollaries on U(n) with Haar measure -/

/-- **G1. UNCONDITIONAL on U(n): factorization of two closed,
    link-disjoint Wilson loops at β = 0** — only structural conditions:
    NeZero N, NeZero n, closed paths, disjoint supports. -/
theorem gibbsExpectation_mul_unitaryWilsonLoops_zero_of_disjoint
    (n : ℕ) [NeZero n] {N : ℕ} [NeZero N] [Fintype (Site N)]
    (x₁ x₂ : Site N) (p₁ p₂ : List Step)
    (_hp₁ : IsClosed x₁ p₁) (_hp₂ : IsClosed x₂ p₂)
    (hdisj : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂)) :
    gibbsExpectation (N := N) (haarU n) 0 (uChar n)
        (fun U => wilsonLoop (uChar n) U x₁ p₁
          * wilsonLoop (uChar n) U x₂ p₂)
      = gibbsExpectation (N := N) (haarU n) 0 (uChar n)
          (fun U => wilsonLoop (uChar n) U x₁ p₁)
        * gibbsExpectation (N := N) (haarU n) 0 (uChar n)
            (fun U => wilsonLoop (uChar n) U x₂ p₂) :=
  gibbsExpectation_mul_wilsonPaths_zero_of_disjoint (haarU n)
    (measurable_uChar n) x₁ x₂ p₁ p₂ hdisj

/-- **G2. UNCONDITIONAL on U(n): vanishing truncated correlation of
    two closed, link-disjoint Wilson loops at β = 0.** -/
theorem truncatedCorrelation_unitaryWilsonLoops_zero_of_disjoint
    (n : ℕ) [NeZero n] {N : ℕ} [NeZero N] [Fintype (Site N)]
    (x₁ x₂ : Site N) (p₁ p₂ : List Step)
    (_hp₁ : IsClosed x₁ p₁) (_hp₂ : IsClosed x₂ p₂)
    (hdisj : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂)) :
    truncatedCorrelation (N := N) (haarU n) 0 (uChar n)
      (fun U => wilsonLoop (uChar n) U x₁ p₁)
      (fun U => wilsonLoop (uChar n) U x₂ p₂) = 0 :=
  truncatedCorrelation_wilsonPaths_zero_of_disjoint (haarU n)
    (measurable_uChar n) x₁ x₂ p₁ p₂ hdisj

end LatticeGauge
