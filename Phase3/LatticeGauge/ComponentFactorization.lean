/-
LatticeGauge/ComponentFactorization.lean — Phase 3, thirty-fourth
stone.

FINITE CONNECTED-COMPONENT FACTORIZATION OF THE MAYER TERMS
(architecture: Sol/GPT-5.6; execution: Fable). PRECISE LANGUAGE
(architect's correction): the Mayer SUM does not factorize — EACH TERM
indexed by A factorizes as the product of the weights of the
connected components of A; substituting into the stone-32 identity,
realZ becomes a SUM over subsets A of PRODUCTS over components. The
whole sum remains a sum. This is NOT yet a polymer-gas
representation: no `Polymer` object, no compatibility relation, no
reindexing of the sum by families of connected sets, no
subset ↔ compatible-family bijection, no Ursell functions, no trees,
no tree-graph inequality, no component counting, no log realZ, no
convergence estimate, no volume uniformity, no thermodynamic limit.
Vocabulary of this stone: connected component, component/block
activity, component weight — "polymer" is born only at the
reindexing stone. EMPTY CASE handled without artificial hypotheses:
componentFamily ∅ = ∅, empty union = ∅, empty product = 1, and the
capstones hold for A = ∅ with E₀[1] = 1 through the general
machinery. Geometry is consumed from stone 33 AS AN INTERFACE (no
path arguments are re-proved); the probabilistic factorization is
stone 26 applied to the family C ↦ blockActivity indexed by
componentFamily A : Finset (Finset _) — no dependent types.
Credit: stone 26 (finite-family factorization), stone 32 (finite
Mayer subset identity), stone 33 (component geometry), stone 34
(component factorization of the Mayer terms). NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.Beta0
import LatticeGauge.WilsonDisjointBeta0
import LatticeGauge.FiniteSupportFactorizationBeta0
import LatticeGauge.PlaquetteActivity
import LatticeGauge.PlaquetteConnectivity

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

/-- **1. The family of connected components of A** — plain
    `Finset (Finset _)` via image; duplicates collapse, no quotient,
    no chosen representatives. `componentFamily ∅ = ∅`. -/
noncomputable def componentFamily [NeZero N]
    (A : Finset (Site N × Dir × Dir)) :
    Finset (Finset (Site N × Dir × Dir)) :=
  A.image (plaquetteComponent A)

@[simp] theorem componentFamily_empty [NeZero N] :
    componentFamily (∅ : Finset (Site N × Dir × Dir)) = ∅ :=
  Finset.image_empty _

section Family

variable [NeZero N] [Fintype (Site N)]
variable {A : Finset (Site N × Dir × Dir)}

/-- **A. Each member of the family is contained in A.** -/
theorem componentFamily_mem_subset
    (hA : A ⊆ admissiblePlaquettes N)
    {C : Finset (Site N × Dir × Dir)}
    (hC : C ∈ componentFamily A) : C ⊆ A := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hC
  exact plaquetteComponent_subset hA p

/-- **B. Each member of the family is nonempty.** -/
theorem componentFamily_mem_nonempty
    (hA : A ⊆ admissiblePlaquettes N)
    {C : Finset (Site N × Dir × Dir)}
    (hC : C ∈ componentFamily A) : C.Nonempty := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
  exact ⟨p, mem_plaquetteComponent_self hA hp⟩

/-- **C. Every element of A belongs to some member of the family.** -/
theorem exists_componentFamily_mem
    (hA : A ⊆ admissiblePlaquettes N)
    {p : Site N × Dir × Dir} (hp : p ∈ A) :
    ∃ C ∈ componentFamily A, p ∈ C :=
  ⟨plaquetteComponent A p, Finset.mem_image_of_mem _ hp,
    mem_plaquetteComponent_self hA hp⟩

/-- **D. The union of the components is exactly A**
    (empty union = ∅ for A = ∅). -/
theorem biUnion_componentFamily
    (hA : A ⊆ admissiblePlaquettes N) :
    (componentFamily A).biUnion id = A := by
  ext p
  simp only [Finset.mem_biUnion, id]
  constructor
  · rintro ⟨C, hC, hpC⟩
    exact componentFamily_mem_subset hA hC hpC
  · intro hp
    exact ⟨plaquetteComponent A p, Finset.mem_image_of_mem _ hp,
      mem_plaquetteComponent_self hA hp⟩

/-- **E. Distinct members of the family are disjoint Finsets.** -/
theorem componentFamily_pairwise_disjoint
    (hA : A ⊆ admissiblePlaquettes N)
    {C D : Finset (Site N × Dir × Dir)}
    (hC : C ∈ componentFamily A) (hD : D ∈ componentFamily A)
    (hne : C ≠ D) : Disjoint C D := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hD
  exact plaquetteComponent_disjoint_of_ne hA hne

/-- **F. Each member of the family is connected within A.** -/
theorem componentFamily_mem_connected
    (hA : A ⊆ admissiblePlaquettes N)
    {C : Finset (Site N × Dir × Dir)}
    (hC : C ∈ componentFamily A) :
    ∀ a ∈ C, ∀ b ∈ C, connectedWithin A a b := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hC
  intro a ha b hb
  obtain ⟨_, hpa⟩ := mem_plaquetteComponent_iff.mp ha
  obtain ⟨_, hpb⟩ := mem_plaquetteComponent_iff.mp hb
  exact connectedWithin_trans (connectedWithin_symm hpa) hpb

/-- **Distinct members of the family have disjoint link supports** —
    stone 33 consumed as an interface. -/
theorem componentFamily_blockLinkSupport_disjoint
    (hA : A ⊆ admissiblePlaquettes N)
    {C D : Finset (Site N × Dir × Dir)}
    (hC : C ∈ componentFamily A) (hD : D ∈ componentFamily A)
    (hne : C ≠ D) :
    Disjoint (blockLinkSupport C) (blockLinkSupport D) := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hC
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hD
  exact blockLinkSupport_disjoint_of_ne_component hA hne

end Family

/-- **2. The activity of a block (component weight integrand)**:
    the product of the plaquette activities over the block. -/
noncomputable def blockActivity [NeZero N] (β : ℝ) (χ : G → ℝ)
    (C : Finset (Site N × Dir × Dir)) (U : Config N G) : ℝ :=
  ∏ p ∈ C, plaquetteActivity β χ U p

/-- **3a. The local link (deliberately left out of stone 33): a
    plaquette activity depends only on the four links of its
    plaquette.** -/
theorem plaquetteActivity_dependsOnlyOn [NeZero N] (β : ℝ)
    (χ : G → ℝ) (p : Site N × Dir × Dir) :
    DependsOnlyOn (fun U : Config N G => plaquetteActivity β χ U p)
      (↑(plaqLinkSet p) : Set (Link N)) := by
  intro U V hUV
  show plaquetteActivity β χ U p = plaquetteActivity β χ V p
  have hplaq : plaquette U p.1 p.2.1 p.2.2
      = plaquette V p.1 p.2.1 p.2.2 := by
    unfold plaquette
    rw [hUV (p.1, p.2.1) (by simp [plaqLinkSet]),
      hUV (shift p.1 p.2.1, p.2.2) (by simp [plaqLinkSet]),
      hUV (shift p.1 p.2.2, p.2.1) (by simp [plaqLinkSet]),
      hUV (p.1, p.2.2) (by simp [plaqLinkSet])]
  unfold plaquetteActivity localPlaquetteAction
  rw [hplaq]

/-- **3b. A block activity depends only on the block link support**
    (generic support lemma of stone 26, no new support theory). -/
theorem blockActivity_dependsOnlyOn [NeZero N] (β : ℝ) (χ : G → ℝ)
    (C : Finset (Site N × Dir × Dir)) :
    DependsOnlyOn (fun U : Config N G => blockActivity β χ C U)
      (blockLinkSupport C) :=
  dependsOnlyOn_finsetProd C
    (fun p U => plaquetteActivity β χ U p)
    (fun p => (↑(plaqLinkSet p) : Set (Link N)))
    (fun p _ => plaquetteActivity_dependsOnlyOn β χ p)

section Measure

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **Measurability of the block activity.** -/
theorem measurable_blockActivity [NeZero N] (β : ℝ) {χ : G → ℝ}
    (mχ : Measurable χ) (C : Finset (Site N × Dir × Dir)) :
    Measurable (fun U : Config N G => blockActivity β χ C U) := by
  have hmeas : Measurable (fun U : Config N G =>
      ∏ p ∈ C, plaquetteActivity β χ U p) :=
    measurable_finsetProd C (fun p U => plaquetteActivity β χ U p)
      (fun p _ => measurable_plaquetteActivity β mχ p)
  exact hmeas

/-- **2'. ALGEBRAIC DECOMPOSITION of the Mayer term**: the product of
    activities over A equals the product of the block activities over
    the connected components of A (Finset.prod_biUnion + stone 33
    disjointness). -/
theorem prod_activity_eq_prod_blockActivity [NeZero N]
    [Fintype (Site N)] {A : Finset (Site N × Dir × Dir)}
    (hA : A ⊆ admissiblePlaquettes N) (β : ℝ) (χ : G → ℝ)
    (U : Config N G) :
    ∏ p ∈ A, plaquetteActivity β χ U p
      = ∏ C ∈ componentFamily A, blockActivity β χ C U := by
  have hdisj : Set.PairwiseDisjoint
      (↑(componentFamily A) : Set (Finset (Site N × Dir × Dir)))
      (id : Finset (Site N × Dir × Dir) →
        Finset (Site N × Dir × Dir)) := by
    intro C hC D hD hne
    exact componentFamily_pairwise_disjoint hA hC hD hne
  conv_lhs => rw [← biUnion_componentFamily hA]
  exact Finset.prod_biUnion hdisj

/-- **5. CAPSTONE (probabilistic): each Mayer term factorizes over
    connected components at β = 0** —
    E₀[∏_{p∈A} m_p] = ∏_{C ∈ Comp(A)} E₀[block C]. Stone 26 applied
    to the family indexed by componentFamily A (no dependent types).
    Holds for A = ∅ with both sides equal to E₀[1] = 1; no artificial
    Nonempty hypothesis. -/
theorem gibbsExpectation_prod_activity_eq_prod_component [NeZero N]
    [Fintype (Site N)] (χ : G → ℝ) {β : ℝ} (mχ : Measurable χ)
    {A : Finset (Site N × Dir × Dir)}
    (hA : A ⊆ admissiblePlaquettes N) :
    gibbsExpectation (N := N) μm 0 χ
        (fun U => ∏ p ∈ A, plaquetteActivity β χ U p)
      = ∏ C ∈ componentFamily A,
          gibbsExpectation (N := N) μm 0 χ
            (fun U => blockActivity β χ C U) := by
  have hdecomp : (fun U : Config N G =>
      ∏ p ∈ A, plaquetteActivity β χ U p)
      = fun U => ∏ C ∈ componentFamily A, blockActivity β χ C U := by
    funext U
    exact prod_activity_eq_prod_blockActivity hA β χ U
  rw [hdecomp]
  exact gibbsExpectation_finsetProd_zero_of_pairwise_disjoint_support
    μm χ (componentFamily A)
    (fun C U => blockActivity β χ C U)
    blockLinkSupport
    (fun C _ => blockActivity_dependsOnlyOn β χ C)
    (fun C _ => measurable_blockActivity β mχ C)
    (fun C hC D hD hne =>
      componentFamily_blockLinkSupport_disjoint hA hC hD hne)

/-- **6. FINAL CAPSTONE: the exact connected form of realZ** —
    realZ_β = Σ over ALL subsets A of the product, over the connected
    components of A, of the component weights E₀[block C]. An exact
    finite-volume identity: each Mayer term factorizes over the
    connected components of ITS subset; the sum is still indexed by
    all subsets A — no reindexing by polymer families has been done;
    no convergence estimate; no volume uniformity; no log Z; no
    clustering; no mass gap. -/
theorem realZ_eq_sum_component_weights [NeZero N] [Fintype (Site N)]
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) :
    realZ (N := N) μm β χ
      = ∑ A ∈ (admissiblePlaquettes N).powerset,
          ∏ C ∈ componentFamily A,
            gibbsExpectation (N := N) μm 0 χ
              (fun U => blockActivity β χ C U) := by
  rw [realZ_eq_sum_integral_prod_activity μm hβ mχ hχabs]
  refine Finset.sum_congr rfl fun A hA => ?_
  have hA' : A ⊆ admissiblePlaquettes N := Finset.mem_powerset.mp hA
  rw [← gibbsExpectation_zero (N := N) μm χ]
  exact gibbsExpectation_prod_activity_eq_prod_component μm χ mχ hA'

end Measure

end LatticeGauge
