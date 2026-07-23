/-
LatticeGauge/LinkCovering.lean — Phase 3, forty-fifth stone (a).

COVERING THE INCOMPATIBILITIES BY LINKS
(architecture: Sol/GPT-5.6; execution: Fable). To control the whole
incompatible neighbourhood of a block C it suffices to stand guard at
each of its at most 4·|C| support links: for any NONNEGATIVE function
a on the finite polymer universe,
  Σ_{D incompatible with C} a(D)
    ≤ Σ_{ℓ ∈ linkSupport C} Σ_{D whose support contains ℓ} a(D)
      ≤ 4·|C|·B   whenever every rooted link sum is ≤ B.
The OVERCOUNTING is deliberate and legitimate: a polymer D sharing
several links with C appears once on the left and possibly several
times on the right; nonnegativity of a makes the inequality sound.
"Rooted at a link" means only that the support contains ℓ — no
oriented root, and the same polymer may lie in several rooted sets.
The factor 4 is independent of the volume N AND of the dimension (a
plaquette has four sides regardless of the ambient dimension); only
≤ 4 is claimed, robust to periodic identifications in small volumes.
The universe `allPlaquettePolymers` is finite in the fixed volume;
the covering inequality holds in EVERY volume, but NO bound uniform
in N for the rooted link sum exists yet — that uniformity is exactly
the stone-45b geometric counting, NOT done here: no counting of
polymers using a link, no M(d), no Δ(d), no connected-set counting,
no Euler tours, no Penrose-tree reuse for counting, no sums by size,
no choice of α or β, no Kotecký–Preiss, no cluster series, no
log realZ, no convergence, no thermodynamic limit. The KP-shaped
weight |w_β(D)|·exp(α·|D|) is specialized at the end (nonnegative
with no sign condition on α; future uses will take α ≥ 0) and bounded
pointwise by the stone-44 activity bound. NO axioms.

Naming note (item 1 of the brief): the map's `componentLinkSupport`
is this library's `blockLinkSupport` (a Set, stone 33); its Finset
presentation `blockLinkFinset := C.biUnion plaqLinkSet` is introduced
here with the membership bridge.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.Beta0
import LatticeGauge.PlaquetteActivity
import LatticeGauge.PlaquetteConnectivity
import LatticeGauge.ComponentFactorization
import LatticeGauge.PolymerGeometry
import LatticeGauge.PolymerGas
import LatticeGauge.PolymerActivityBound

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N]

/-! ## 1/8. The Finset presentation of the link support -/

/-- **The link support of a block, as a Finset** (the stone-33
    `blockLinkSupport` is a Set; the two agree elementwise). -/
noncomputable def blockLinkFinset
    (C : Finset (Site N × Dir × Dir)) : Finset (Link N) :=
  C.biUnion plaqLinkSet

theorem mem_blockLinkFinset {C : Finset (Site N × Dir × Dir)}
    {ℓ : Link N} :
    ℓ ∈ blockLinkFinset C ↔ ℓ ∈ blockLinkSupport C := by
  unfold blockLinkFinset blockLinkSupport familySupport
  simp only [Finset.mem_biUnion, Set.mem_setOf_eq, Finset.mem_coe]

/-! ## 2. The incompatible polymers of a block -/

variable [Fintype (Site N)]

/-- **Total for ANY finite block C** (C need not be a polymer — the
    lemma stays usable for intermediate blocks). -/
noncomputable def incompatiblePolymers
    (C : Finset (Site N × Dir × Dir)) :
    Finset (Finset (Site N × Dir × Dir)) :=
  (allPlaquettePolymers N).filter
    (fun D => ¬ PlaquetteCompatible C D)

theorem mem_incompatiblePolymers {C D : Finset (Site N × Dir × Dir)} :
    D ∈ incompatiblePolymers C
      ↔ D ∈ allPlaquettePolymers N ∧ ¬ PlaquetteCompatible C D := by
  unfold incompatiblePolymers
  simp [Finset.mem_filter]

/-! ## 3. The polymers rooted at a link -/

/-- "Rooted at ℓ" = the support contains ℓ; no oriented root; the
    same polymer may belong to several of these Finsets. -/
noncomputable def polymersUsingLink (ℓ : Link N) :
    Finset (Finset (Site N × Dir × Dir)) :=
  (allPlaquettePolymers N).filter
    (fun D => ℓ ∈ blockLinkFinset D)

theorem mem_polymersUsingLink {ℓ : Link N}
    {D : Finset (Site N × Dir × Dir)} :
    D ∈ polymersUsingLink ℓ
      ↔ D ∈ allPlaquettePolymers N ∧ ℓ ∈ blockLinkSupport D := by
  unfold polymersUsingLink
  simp [Finset.mem_filter, mem_blockLinkFinset]

/-! ## 4. The incompatibility witness -/

/-- **Incompatibility = a shared support link** (by the stone-35
    definition through Set disjointness; the relevant notion is the
    LINK support, not plaquette intersection). -/
theorem incompatible_iff_exists_shared_link
    {C D : Finset (Site N × Dir × Dir)} :
    ¬ PlaquetteCompatible C D
      ↔ ∃ ℓ : Link N,
          ℓ ∈ blockLinkSupport C ∧ ℓ ∈ blockLinkSupport D := by
  unfold PlaquetteCompatible
  exact Set.not_disjoint_iff

/-! ## 5. The covering by rooted Finsets -/

/-- The right-hand side is just the union of the polymers using at
    least one support link of C. -/
theorem incompatiblePolymers_subset_biUnion
    (C : Finset (Site N × Dir × Dir)) :
    incompatiblePolymers C
      ⊆ (blockLinkFinset C).biUnion polymersUsingLink := by
  intro D hD
  obtain ⟨hall, hinc⟩ := mem_incompatiblePolymers.mp hD
  obtain ⟨ℓ, hℓC, hℓD⟩ := incompatible_iff_exists_shared_link.mp hinc
  rw [Finset.mem_biUnion]
  exact ⟨ℓ, mem_blockLinkFinset.mpr hℓC,
    mem_polymersUsingLink.mpr ⟨hall, hℓD⟩⟩

/-! ## 6. The generic cover-sum lemma (the one new abstract Finset
    lemma of this stone) -/

/-- Sum over a possibly overlapping union ≤ sum of the sums —
    elements of the intersections are counted several times on the
    right, which nonnegativity makes legitimate. Local induction, no
    multiplicity counting, no Multiset. -/
theorem sum_biUnion_le_sum_sum {α ι : Type*} [DecidableEq α]
    {S : Finset ι} {B : ι → Finset α} {f : α → ℝ}
    (hf : ∀ x ∈ S.biUnion B, 0 ≤ f x) :
    (∑ x ∈ S.biUnion B, f x) ≤ ∑ i ∈ S, ∑ x ∈ B i, f x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    rw [Finset.biUnion_insert] at hf ⊢
    rw [Finset.sum_insert hi]
    have hsub : ∀ x ∈ T.biUnion B, 0 ≤ f x := fun x hx =>
      hf x (Finset.mem_union_right _ hx)
    have hinter : 0 ≤ ∑ x ∈ B i ∩ T.biUnion B, f x :=
      Finset.sum_nonneg (fun x hx =>
        hf x (Finset.mem_union_left _ (Finset.mem_inter.mp hx).1))
    have hui : (∑ x ∈ B i ∪ T.biUnion B, f x)
          + ∑ x ∈ B i ∩ T.biUnion B, f x
        = (∑ x ∈ B i, f x) + ∑ x ∈ T.biUnion B, f x :=
      Finset.sum_union_inter
    have hstep : (∑ x ∈ B i ∪ T.biUnion B, f x)
        ≤ (∑ x ∈ B i, f x) + ∑ x ∈ T.biUnion B, f x := by
      linarith
    exact hstep.trans (add_le_add_left (ih hsub) _)

theorem sum_le_sum_over_cover {α ι : Type*} [DecidableEq α]
    {A : Finset α} {S : Finset ι} {B : ι → Finset α} {f : α → ℝ}
    (hA : A ⊆ S.biUnion B)
    (hf : ∀ x ∈ S.biUnion B, 0 ≤ f x) :
    (∑ x ∈ A, f x) ≤ ∑ i ∈ S, ∑ x ∈ B i, f x :=
  (Finset.sum_le_sum_of_subset_of_nonneg hA
    (fun x hx _ => hf x hx)).trans (sum_biUnion_le_sum_sum hf)

/-! ## 7. GENERIC COVERING CAPSTONE -/

/-- **The covering inequality**: the right side deliberately
    overcounts polymers sharing several links with C; purely finite
    and geometric; NO estimate yet of how many polymers use a link.
    Uses nothing particular about `polymerWeight`. -/
theorem incompatiblePolymer_sum_le_link_sum
    {a : Finset (Site N × Dir × Dir) → ℝ}
    (ha : ∀ D ∈ allPlaquettePolymers N, 0 ≤ a D)
    (C : Finset (Site N × Dir × Dir)) :
    (∑ D ∈ incompatiblePolymers C, a D)
      ≤ ∑ ℓ ∈ blockLinkFinset C,
          ∑ D ∈ polymersUsingLink ℓ, a D := by
  refine sum_le_sum_over_cover
    (incompatiblePolymers_subset_biUnion C) ?_
  intro D hD
  rw [Finset.mem_biUnion] at hD
  obtain ⟨ℓ, -, hDl⟩ := hD
  exact ha D (mem_polymersUsingLink.mp hDl).1

/-! ## 8. Cardinality of the link support -/

/-- A plaquette has AT MOST four boundary links — only ≤ 4 is
    claimed (robust to periodic identifications in small volumes);
    no dimension d enters. -/
theorem card_plaqLinkSet_le (p : Site N × Dir × Dir) :
    (plaqLinkSet p).card ≤ 4 := by
  unfold plaqLinkSet
  have h1 := Finset.card_insert_le ((p.1, p.2.1) : Link N)
    {(shift p.1 p.2.1, p.2.2), (shift p.1 p.2.2, p.2.1), (p.1, p.2.2)}
  have h2 := Finset.card_insert_le ((shift p.1 p.2.1, p.2.2) : Link N)
    {(shift p.1 p.2.2, p.2.1), (p.1, p.2.2)}
  have h3 := Finset.card_insert_le ((shift p.1 p.2.2, p.2.1) : Link N)
    {(p.1, p.2.2)}
  have h4 : ({(p.1, p.2.2)} : Finset (Link N)).card = 1 :=
    Finset.card_singleton _
  omega

theorem blockLinkFinset_card_le (C : Finset (Site N × Dir × Dir)) :
    (blockLinkFinset C).card ≤ 4 * C.card := by
  unfold blockLinkFinset
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ p ∈ C, (plaqLinkSet p).card
      ≤ ∑ _p ∈ C, 4 :=
        Finset.sum_le_sum (fun p _ => card_plaqLinkSet_le p)
    _ = 4 * C.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-! ## 10. Reduction to a uniform per-link bound -/

theorem incompatiblePolymer_sum_le_card_mul
    {a : Finset (Site N × Dir × Dir) → ℝ}
    (ha : ∀ D ∈ allPlaquettePolymers N, 0 ≤ a D)
    (C : Finset (Site N × Dir × Dir)) {B : ℝ}
    (hroot : ∀ ℓ ∈ blockLinkFinset C,
      (∑ D ∈ polymersUsingLink ℓ, a D) ≤ B) :
    (∑ D ∈ incompatiblePolymers C, a D)
      ≤ ((blockLinkFinset C).card : ℝ) * B := by
  refine (incompatiblePolymer_sum_le_link_sum ha C).trans ?_
  have h := Finset.sum_le_card_nsmul (blockLinkFinset C)
    (fun ℓ => ∑ D ∈ polymersUsingLink ℓ, a D) B hroot
  rwa [nsmul_eq_mul] at h

/-- **Operational form**: guard duty at each of the ≤ 4·|C| gates.
    B need not be attained — it is just a uniform majorant of the
    rooted sums. -/
theorem incompatiblePolymer_sum_le_four_mul
    {a : Finset (Site N × Dir × Dir) → ℝ}
    (ha : ∀ D ∈ allPlaquettePolymers N, 0 ≤ a D)
    (C : Finset (Site N × Dir × Dir)) {B : ℝ} (hB : 0 ≤ B)
    (hroot : ∀ ℓ ∈ blockLinkFinset C,
      (∑ D ∈ polymersUsingLink ℓ, a D) ≤ B) :
    (∑ D ∈ incompatiblePolymers C, a D)
      ≤ ((4 * C.card : ℕ) : ℝ) * B := by
  refine (incompatiblePolymer_sum_le_card_mul ha C hroot).trans ?_
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast blockLinkFinset_card_le C) hB

/-! ## 11-13. The Kotecký–Preiss-shaped weight -/

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- The weight the future convergence criterion will sum:
    |w_β(D)|·exp(α·|D|). Nonnegative with NO sign condition on α
    (exp is positive); future applications will take α ≥ 0. -/
noncomputable def kpActivityWeight [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) (α : ℝ)
    (D : Finset (Site N × Dir × Dir)) : ℝ :=
  |polymerWeight (N := N) μm β χ D| * Real.exp (α * D.card)

theorem kpActivityWeight_nonneg [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) (α : ℝ)
    (D : Finset (Site N × Dir × Dir)) :
    0 ≤ kpActivityWeight μm β χ α D :=
  mul_nonneg (abs_nonneg _) (Real.exp_pos _).le

/-- **Item 12**: the covering specialized to the exponential weight —
    a short corollary; no claim that any α satisfies KP. -/
theorem incompatible_kpActivity_sum_le_link_sum [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) (α : ℝ)
    (C : Finset (Site N × Dir × Dir)) :
    (∑ D ∈ incompatiblePolymers C, kpActivityWeight μm β χ α D)
      ≤ ∑ ℓ ∈ blockLinkFinset C,
          ∑ D ∈ polymersUsingLink ℓ, kpActivityWeight μm β χ α D :=
  incompatiblePolymer_sum_le_link_sum
    (fun D _ => kpActivityWeight_nonneg μm β χ α D) C

/-- **Item 13**: stone 44 consumed pointwise (the collapsed form
    (2β·e^α)^|D| is deliberately NOT forced). -/
theorem kpActivityWeight_le [Fintype (Site N)]
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (α : ℝ)
    (D : Finset (Site N × Dir × Dir)) :
    kpActivityWeight μm β χ α D
      ≤ (2 * β) ^ D.card * Real.exp (α * D.card) :=
  mul_le_mul_of_nonneg_right
    (polymerWeight_abs_le μm hβ mχ hχabs D) (Real.exp_pos _).le

/-! ## 14. THE OPERATIONAL CAPSTONE -/

/-- **To control the whole incompatible neighbourhood of C it
    suffices to control uniformly the polymers containing one fixed
    link**; the factor 4·|C| is the maximal number of support links.
    The next bottleneck (stone 45b) is estimating the rooted sum per
    link; NO convergence criterion is proved yet. -/
theorem incompatible_kpActivity_sum_le_four_mul [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) (α : ℝ)
    (C : Finset (Site N × Dir × Dir)) {B : ℝ} (hB : 0 ≤ B)
    (hroot : ∀ ℓ ∈ blockLinkFinset C,
      (∑ D ∈ polymersUsingLink ℓ, kpActivityWeight μm β χ α D) ≤ B) :
    (∑ D ∈ incompatiblePolymers C, kpActivityWeight μm β χ α D)
      ≤ ((4 * C.card : ℕ) : ℝ) * B :=
  incompatiblePolymer_sum_le_four_mul
    (fun D _ => kpActivityWeight_nonneg μm β χ α D) C hB hroot

/-! ## 15. Sanity -/

/-- The empty block is compatible with everything (its link support
    is empty). -/
theorem plaquetteCompatible_empty_left
    (D : Finset (Site N × Dir × Dir)) :
    PlaquetteCompatible (∅ : Finset (Site N × Dir × Dir)) D := by
  unfold PlaquetteCompatible blockLinkSupport familySupport
  rw [Set.disjoint_left]
  intro ℓ hℓ
  simp only [Set.mem_setOf_eq] at hℓ
  obtain ⟨p, hp, -⟩ := hℓ
  exact absurd hp (Finset.not_mem_empty p)

theorem blockLinkFinset_empty :
    blockLinkFinset (∅ : Finset (Site N × Dir × Dir))
      = (∅ : Finset (Link N)) := by
  unfold blockLinkFinset
  exact Finset.biUnion_empty

theorem incompatiblePolymers_empty [Fintype (Site N)] :
    incompatiblePolymers (∅ : Finset (Site N × Dir × Dir)) = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro D hD
  exact (mem_incompatiblePolymers.mp hD).2
    (plaquetteCompatible_empty_left D)

/-- If everything is compatible with C the left sum has no terms
    (the a = 0 case and the double-counting of a two-link sharer are
    documentation: both are immediate from the statements above). -/
theorem incompatiblePolymers_eq_empty_of_all_compatible
    [Fintype (Site N)] {C : Finset (Site N × Dir × Dir)}
    (h : ∀ D ∈ allPlaquettePolymers N, PlaquetteCompatible C D) :
    incompatiblePolymers C = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro D hD
  obtain ⟨hall, hinc⟩ := mem_incompatiblePolymers.mp hD
  exact hinc (h D hall)

end LatticeGauge
