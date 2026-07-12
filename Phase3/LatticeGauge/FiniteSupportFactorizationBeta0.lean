/-
LatticeGauge/FiniteSupportFactorizationBeta0.lean — Phase 3,
twenty-sixth stone.

EXACT FINITE-FAMILY FACTORIZATION AT β = 0 (architecture: Sol/GPT-5.6;
execution: Fable). ARCHITECTURAL PROMOTION: the main theorem is
GENERIC — any finite family of measurable observables with pairwise
link-disjoint supports factorizes exactly under the product measure;
Wilson paths enter only as a geometric corollary through pathLinkSet.
Conceptual credit: stone 11 provides the binary factorization; this
stone proves the finite extension and the API for families of local
observables. LIMITS: exact finite-family factorization at β = 0;
mutual independence in product-expectation form; supports pairwise
link-disjoint; paths may repeat their own links and share vertices;
no claim for β > 0; no distance decay; no mass gap; no area law; no
confinement; not a nontrivial cluster expansion. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.WilsonLoop
import LatticeGauge.Beta0
import LatticeGauge.WilsonExpectation
import LatticeGauge.WilsonDisjointBeta0
import LatticeGauge.UnitaryChar
import LatticeGauge.HaarUnitary

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

section GenericFamily

variable {ι : Type*} [DecidableEq ι]

/-- **A. The support of a finite family of observables**, by simple
    existential membership — no iUnion, no Finset.sup, no subtypes. -/
def familySupport [NeZero N] (supp : ι → Set (Link N))
    (s : Finset ι) : Set (Link N) :=
  {ℓ | ∃ i ∈ s, ℓ ∈ supp i}

/-- **B. A finite product depends only on the family support.** -/
theorem dependsOnlyOn_finsetProd [NeZero N]
    (s : Finset ι) (f : ι → Config N G → ℝ)
    (supp : ι → Set (Link N))
    (hf : ∀ i ∈ s, DependsOnlyOn (f i) (supp i)) :
    DependsOnlyOn (fun U : Config N G => ∏ i ∈ s, f i U)
      (familySupport supp s) := by
  intro U V hUV
  show ∏ i ∈ s, f i U = ∏ i ∈ s, f i V
  refine Finset.prod_congr rfl ?_
  intro i hi
  exact hf i hi U V (by
    intro ℓ hℓ
    exact hUV ℓ ⟨i, hi, hℓ⟩)

section MeasureG

variable [MeasurableSpace G]

/-- **C. Measurability of a finite product of observables.** -/
theorem measurable_finsetProd (s : Finset ι)
    (f : ι → Config N G → ℝ)
    (mf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun U : Config N G => ∏ i ∈ s, f i U) := by
  classical
  revert mf
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using
      (measurable_const : Measurable (fun _ : Config N G => (1 : ℝ)))
  | @insert a t ha ih =>
    intro mf
    have hma : Measurable (f a) := mf a (by simp)
    have hmt : ∀ i ∈ t, Measurable (f i) := by
      intro i hi
      exact mf i (Finset.mem_insert_of_mem hi)
    have hrest := ih hmt
    simpa [Finset.prod_insert, ha] using hma.mul hrest

variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **D. GENERIC FINITE-FAMILY FACTORIZATION of the integral** under
    the product measure: pairwise disjoint supports ⇒
    ∫ ∏ᵢ fᵢ = ∏ᵢ ∫ fᵢ. Binary base: stone 11. -/
theorem integral_finsetProd_of_pairwise_disjoint_support [NeZero N]
    (s : Finset ι) (f : ι → Config N G → ℝ)
    (supp : ι → Set (Link N))
    (hf : ∀ i ∈ s, DependsOnlyOn (f i) (supp i))
    (mf : ∀ i ∈ s, Measurable (f i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (supp i) (supp j)) :
    ∫ U : Config N G, ∏ i ∈ s, f i U ∂(configMeasure μm N)
      = ∏ i ∈ s, ∫ U : Config N G, f i U ∂(configMeasure μm N) := by
  classical
  revert hf mf hdisj
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ _
    simp
  | @insert a t ha ih =>
    intro hf mf hdisj
    have hfa : DependsOnlyOn (f a) (supp a) := hf a (by simp)
    have hma : Measurable (f a) := mf a (by simp)
    have hft : ∀ i ∈ t, DependsOnlyOn (f i) (supp i) := by
      intro i hi
      exact hf i (Finset.mem_insert_of_mem hi)
    have hmt : ∀ i ∈ t, Measurable (f i) := by
      intro i hi
      exact mf i (Finset.mem_insert_of_mem hi)
    have hdisj_t : ∀ i ∈ t, ∀ j ∈ t, i ≠ j →
        Disjoint (supp i) (supp j) := by
      intro i hi j hj hij
      exact hdisj i (Finset.mem_insert_of_mem hi)
        j (Finset.mem_insert_of_mem hj) hij
    have hrest0 : DependsOnlyOn
        (fun U : Config N G => ∏ i ∈ t, f i U)
        (familySupport supp t) :=
      dependsOnlyOn_finsetProd t f supp hft
    have hrestSub : familySupport supp t ⊆ (supp a)ᶜ := by
      intro ℓ hℓ
      rcases hℓ with ⟨j, hj, hℓj⟩
      simp only [Set.mem_compl_iff]
      intro hℓa
      have haj : a ≠ j := by
        intro h
        apply ha
        simpa [h] using hj
      have hd := hdisj a (by simp) j
        (Finset.mem_insert_of_mem hj) haj
      exact Set.disjoint_left.1 hd hℓa hℓj
    have hrest : DependsOnlyOn
        (fun U : Config N G => ∏ i ∈ t, f i U) (supp a)ᶜ :=
      dependsOnlyOn_mono hrest0 hrestSub
    have mrest : Measurable (fun U : Config N G => ∏ i ∈ t, f i U) :=
      measurable_finsetProd t f hmt
    have hfactor := integral_mul_of_disjoint_support (N := N) μm
      (supp a) hfa hrest hma mrest
    calc ∫ U : Config N G, ∏ i ∈ insert a t, f i U
          ∂(configMeasure μm N)
        = ∫ U : Config N G, f a U * ∏ i ∈ t, f i U
            ∂(configMeasure μm N) := by
          congr 1
          funext U
          simp [Finset.prod_insert, ha]
      _ = (∫ U : Config N G, f a U ∂(configMeasure μm N))
            * ∫ U : Config N G, ∏ i ∈ t, f i U
                ∂(configMeasure μm N) := hfactor
      _ = (∫ U : Config N G, f a U ∂(configMeasure μm N))
            * ∏ i ∈ t, ∫ U : Config N G, f i U
                ∂(configMeasure μm N) := by
          rw [ih hft hmt hdisj_t]
      _ = ∏ i ∈ insert a t, ∫ U : Config N G, f i U
            ∂(configMeasure μm N) := by
          simp [Finset.prod_insert, ha]

/-- **E. GENERIC FINITE-FAMILY FACTORIZATION of the Gibbs expectation
    at β = 0** — mutual independence in product-expectation form. No
    measurability of χ is required: at β = 0 the reduction to the
    product measure is purely algebraic. -/
theorem gibbsExpectation_finsetProd_zero_of_pairwise_disjoint_support
    [NeZero N] [Fintype (Site N)] (χ : G → ℝ)
    (s : Finset ι) (f : ι → Config N G → ℝ)
    (supp : ι → Set (Link N))
    (hf : ∀ i ∈ s, DependsOnlyOn (f i) (supp i))
    (mf : ∀ i ∈ s, Measurable (f i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (supp i) (supp j)) :
    gibbsExpectation (N := N) μm 0 χ (fun U => ∏ i ∈ s, f i U)
      = ∏ i ∈ s, gibbsExpectation (N := N) μm 0 χ (f i) := by
  rw [gibbsExpectation_zero (N := N) μm χ,
    integral_finsetProd_of_pairwise_disjoint_support (N := N) μm
      s f supp hf mf hdisj]
  exact Finset.prod_congr rfl fun i _ =>
    (gibbsExpectation_zero (N := N) μm χ (f i)).symm

end MeasureG

end GenericFamily

/-! ## Wilson observables: the geometric corollary -/

section Wilson

variable {ι : Type*} [DecidableEq ι]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]
variable {χ : G → ℝ}

/-- **F. Finite families of pairwise link-disjoint Wilson paths
    factorize exactly at β = 0.** -/
theorem gibbsExpectation_prod_wilsonPaths_zero_of_pairwise_disjoint
    [NeZero N] [Fintype (Site N)] (mχ : Measurable χ)
    (s : Finset ι) (x : ι → Site N) (p : ι → List Step)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (pathLinkSet (N := N) (x i) (p i))
        (pathLinkSet (N := N) (x j) (p j))) :
    gibbsExpectation (N := N) μm 0 χ
        (fun U => ∏ i ∈ s, wilsonLoop χ U (x i) (p i))
      = ∏ i ∈ s, gibbsExpectation (N := N) μm 0 χ
          (fun U => wilsonLoop χ U (x i) (p i)) :=
  gibbsExpectation_finsetProd_zero_of_pairwise_disjoint_support μm χ s
    (fun i U => wilsonLoop χ U (x i) (p i))
    (fun i => pathLinkSet (N := N) (x i) (p i))
    (fun i _ => wilsonPath_dependsOnlyOn_pathLinkSet χ (x i) (p i))
    (fun i _ => measurable_wilsonLoop mχ (x i) (p i))
    hdisj

/-- **G. Physical wrapper: finite families of closed, pairwise
    link-disjoint Wilson LOOPS factorize exactly at β = 0.** The
    closedness hypotheses certify each member is the gauge-invariant
    physical observable; the factorization uses only the supports. -/
theorem gibbsExpectation_prod_wilsonLoops_zero_of_pairwise_disjoint
    [NeZero N] [Fintype (Site N)] (mχ : Measurable χ)
    (s : Finset ι) (x : ι → Site N) (p : ι → List Step)
    (_hclosed : ∀ i ∈ s, IsClosed (x i) (p i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (pathLinkSet (N := N) (x i) (p i))
        (pathLinkSet (N := N) (x j) (p j))) :
    gibbsExpectation (N := N) μm 0 χ
        (fun U => ∏ i ∈ s, wilsonLoop χ U (x i) (p i))
      = ∏ i ∈ s, gibbsExpectation (N := N) μm 0 χ
          (fun U => wilsonLoop χ U (x i) (p i)) :=
  gibbsExpectation_prod_wilsonPaths_zero_of_pairwise_disjoint
    μm mχ s x p hdisj

end Wilson

/-- **H. UNCONDITIONAL on U(n): finite families of closed, pairwise
    link-disjoint Wilson loops factorize exactly at β = 0** — only
    structural conditions remain. -/
theorem gibbsExpectation_prod_unitaryWilsonLoops_zero_of_pairwise_disjoint
    (n : ℕ) [NeZero n] {N : ℕ} [NeZero N] [Fintype (Site N)]
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → Site N) (p : ι → List Step)
    (_hclosed : ∀ i ∈ s, IsClosed (x i) (p i))
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (pathLinkSet (N := N) (x i) (p i))
        (pathLinkSet (N := N) (x j) (p j))) :
    gibbsExpectation (N := N) (haarU n) 0 (uChar n)
        (fun U => ∏ i ∈ s, wilsonLoop (uChar n) U (x i) (p i))
      = ∏ i ∈ s, gibbsExpectation (N := N) (haarU n) 0 (uChar n)
          (fun U => wilsonLoop (uChar n) U (x i) (p i)) :=
  gibbsExpectation_prod_wilsonPaths_zero_of_pairwise_disjoint
    (haarU n) (measurable_uChar n) s x p hdisj

end LatticeGauge
