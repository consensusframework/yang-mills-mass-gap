/-
LatticeGauge/KPWeightFactorization.lean — stone 47 (b-iiB), GATE III.

THE ASSIGNMENT EQUIVALENCE AND THE EXACT WEIGHT FACTORIZATION
(architecture: Sol/GPT-5.6; execution: Fable). Polymers and
activities enter for the FIRST time — and only pointwise: the weight
of one enumerated tree at one global assignment factors EXACTLY as
the product of its ordered-component contributions. NOTHING is
summed: no sums over γ, η, trees, blocks or polymers; no
fixedRootBlockSum, no F(B), no relabeling to Fin (m+1), no
factorials, no partition counting, no recurrence, no partial sums,
no KP hypothesis, no Real.exp, no Summable; the branch stays
unmerged until the A-package (Gates I-IV) closes.

III.1 — the global assignments Fin n → Polymer are EQUIVALENT to the
ordered per-component data (root value at each mark + tail values),
with both roundtrips proved (the future Gate-IV reindexation of
Σ_γ Π_j into Π_j Σ will be a pure reindexation along this
equivalence, not a new combinatorial proof — the architect's point).
III.2 — the activity product factors by blocks (partition of Fin n),
each block splitting as ρ(ηⱼ) times its tail product: every marked
activity EXACTLY once, every tail activity EXACTLY once, γ₀ absent.
III.3 — the hard-core indicator of the reconstructed tree factors as
Π_j (incompatibility(γ₀, ηⱼ) · internal indicator of block j), by
the disjoint edge partition of Gate II (root edges carry their
canonical orientation, so the root factor is literally the
γ₀-vs-mark incompatibility switch).
III.4 — the internal rooted weight of a block: internal indicator
times TAIL activities only (the mark acts as internal root WITHOUT
its activity — it will later match the summand of
kpTreeCoeff (componentSize j) ρ ηⱼ after relabeling; NOT proved
here). III.5 — CAPSTONE `enumeratedTreeWeight_factorization`:
  rootedTreeWeight ρ γ₀ γ ET
    = Π_j incompat(γ₀,ηⱼ) · ρ(ηⱼ) · internalWeight j
for an enumerated tree (ET, e), via the general reconstruction
version and Gate II's decomposeThenReconstruct. Activity audit: k
marked vertices contribute the k explicit ρ(ηⱼ); the n−k tail
vertices contribute inside the internal weights; nobody is omitted,
nobody is counted twice, γ₀ never carries an activity. Edge cases:
k = 0 forces n = 0; a unit block has empty tail AND empty internal
tree (its indicator product is 1). NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.UrsellCoefficients
import LatticeGauge.UrsellSymmetry
import LatticeGauge.UrsellBounds
import LatticeGauge.EdgeFibers
import LatticeGauge.PolymerTreeBound
import LatticeGauge.KPCoefficients
import LatticeGauge.RootDecomposition
import LatticeGauge.KPEnumerations
import LatticeGauge.KPOrderedDecomposition

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)] {n k : ℕ}

/-! ## III.1 — assignment data per component -/

/-- The tail of a block: the block minus its mark. -/
noncomputable def ODtail (OD : OrderedDecomposition n k)
    (j : Fin k) : Finset (Fin n) :=
  (OD.block j).erase (OD.marked j)

noncomputable def orderedRootValue (γ : Fin n → Polymer N)
    (OD : OrderedDecomposition n k) (j : Fin k) : Polymer N :=
  γ (OD.marked j)

noncomputable def orderedTailAssignment (γ : Fin n → Polymer N)
    (OD : OrderedDecomposition n k) (j : Fin k)
    (v : {x // x ∈ ODtail OD j}) : Polymer N :=
  γ v.val

@[simp] theorem orderedTailAssignment_apply
    (γ : Fin n → Polymer N) (OD : OrderedDecomposition n k)
    (j : Fin k) (v : {x // x ∈ ODtail OD j}) :
    orderedTailAssignment γ OD j v = γ v.val := rfl

/-- Ordered assignment data for a fixed decomposition (no redundant
    proofs carried). -/
structure OrderedAssignmentData {N : ℕ} [NeZero N] [Fintype (Site N)]
    (OD : OrderedDecomposition n k) where
  rootValue : Fin k → Polymer N
  tailValue : ∀ j : Fin k, {x // x ∈ ODtail OD j} → Polymer N

theorem OrderedAssignmentData.ext'
    {OD : OrderedDecomposition n k}
    {A₁ A₂ : OrderedAssignmentData (N := N) OD}
    (hr : A₁.rootValue = A₂.rootValue)
    (ht : A₁.tailValue = A₂.tailValue) : A₁ = A₂ := by
  cases A₁
  cases A₂
  dsimp only at hr ht
  subst hr
  subst ht
  rfl

noncomputable def decomposeAssignment (OD : OrderedDecomposition n k)
    (γ : Fin n → Polymer N) : OrderedAssignmentData (N := N) OD where
  rootValue j := γ (OD.marked j)
  tailValue j v := γ v.val

/-! ## The unique block index (existence from cover, uniqueness from
    disjointness — the Gate-II theorem consumed) -/

noncomputable def blockIndex (OD : OrderedDecomposition n k)
    (v : Fin n) : Fin k :=
  Classical.choose (OD.cover v)

theorem blockIndex_mem (OD : OrderedDecomposition n k) (v : Fin n) :
    v ∈ OD.block (blockIndex OD v) :=
  Classical.choose_spec (OD.cover v)

theorem blockIndex_eq (OD : OrderedDecomposition n k) {v : Fin n}
    {j : Fin k} (h : v ∈ OD.block j) : blockIndex OD v = j := by
  by_contra hne
  exact Finset.disjoint_left.mp (OD.disj _ _ hne)
    (blockIndex_mem OD v) h

noncomputable def reconstructAssignment
    (OD : OrderedDecomposition n k)
    (A : OrderedAssignmentData (N := N) OD) (v : Fin n) : Polymer N :=
  if h : v = OD.marked (blockIndex OD v) then
    A.rootValue (blockIndex OD v)
  else
    A.tailValue (blockIndex OD v)
      ⟨v, Finset.mem_erase.mpr ⟨h, blockIndex_mem OD v⟩⟩

theorem reconstructAssignment_marked
    (OD : OrderedDecomposition n k)
    (A : OrderedAssignmentData (N := N) OD) (j : Fin k) :
    reconstructAssignment OD A (OD.marked j) = A.rootValue j := by
  have hb : blockIndex OD (OD.marked j) = j :=
    blockIndex_eq OD (OD.marked_mem j)
  unfold reconstructAssignment
  rw [dif_pos (congrArg OD.marked hb.symm)]
  rw [hb]

theorem reconstructAssignment_tail
    (OD : OrderedDecomposition n k)
    (A : OrderedAssignmentData (N := N) OD) {j : Fin k} {v : Fin n}
    (hv : v ∈ ODtail OD j) :
    reconstructAssignment OD A v = A.tailValue j ⟨v, hv⟩ := by
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hv
  have hb : blockIndex OD v = j := blockIndex_eq OD hmem
  have hcond : ¬ v = OD.marked (blockIndex OD v) := by
    rw [hb]
    exact hne
  unfold reconstructAssignment
  rw [dif_neg hcond]
  subst hb
  rfl

/-- **III.1 CAPSTONE: global assignments ≃ ordered per-component
    data** — the future Gate-IV reindexation rides this. -/
noncomputable def globalAssignmentEquivOrderedAssignments
    (OD : OrderedDecomposition n k) :
    (Fin n → Polymer N) ≃ OrderedAssignmentData (N := N) OD where
  toFun := decomposeAssignment OD
  invFun := reconstructAssignment OD
  left_inv γ := by
    funext v
    obtain ⟨j, hj⟩ := OD.cover v
    by_cases hm : v = OD.marked j
    · subst hm
      exact reconstructAssignment_marked OD _ j
    · have hv : v ∈ ODtail OD j :=
        Finset.mem_erase.mpr ⟨hm, hj⟩
      exact reconstructAssignment_tail OD _ hv
  right_inv A := by
    refine OrderedAssignmentData.ext' ?_ ?_
    · funext j
      exact reconstructAssignment_marked OD A j
    · funext j v
      show reconstructAssignment OD A v.val = _
      rw [reconstructAssignment_tail OD A v.2]

/-! ## III.2 — activity factorization -/

theorem univ_eq_biUnion_blocks (OD : OrderedDecomposition n k) :
    (Finset.univ : Finset (Fin n))
      = Finset.univ.biUnion (fun j => OD.block j) := by
  ext v
  simp only [Finset.mem_univ, true_iff, Finset.mem_biUnion]
  obtain ⟨j, hj⟩ := OD.cover v
  exact ⟨j, Finset.mem_univ j, hj⟩

/-- 8. The activity product splits by blocks. -/
theorem prod_activity_by_blocks (OD : OrderedDecomposition n k)
    (ρ : Polymer N → ℝ) (γ : Fin n → Polymer N) :
    (∏ v : Fin n, ρ (γ v))
      = ∏ j : Fin k, ∏ v ∈ OD.block j, ρ (γ v) := by
  rw [show (∏ v : Fin n, ρ (γ v))
      = ∏ v ∈ Finset.univ.biUnion (fun j => OD.block j), ρ (γ v) by
    rw [← univ_eq_biUnion_blocks OD]]
  exact Finset.prod_biUnion
    (fun j₁ _ j₂ _ hne => OD.disj j₁ j₂ hne)

/-- 9. One block splits as mark activity times tail product. -/
theorem prod_activity_block_split (OD : OrderedDecomposition n k)
    (ρ : Polymer N → ℝ) (γ : Fin n → Polymer N) (j : Fin k) :
    (∏ v ∈ OD.block j, ρ (γ v))
      = ρ (orderedRootValue γ OD j)
        * ∏ v : {x // x ∈ ODtail OD j},
            ρ (orderedTailAssignment γ OD j v) := by
  rw [Finset.prod_coe_sort]
  unfold orderedRootValue ODtail
  exact (Finset.mul_prod_erase (OD.block j) (fun v => ρ (γ v))
    (OD.marked_mem j)).symm

/-- **10. ACTIVITY CAPSTONE**: every marked activity exactly once,
    every tail activity exactly once, γ₀ absent. -/
theorem globalActivityFactorization (OD : OrderedDecomposition n k)
    (ρ : Polymer N → ℝ) (γ : Fin n → Polymer N) :
    (∏ v : Fin n, ρ (γ v))
      = ∏ j : Fin k,
          (ρ (orderedRootValue γ OD j)
            * ∏ v : {x // x ∈ ODtail OD j},
                ρ (orderedTailAssignment γ OD j v)) := by
  rw [prod_activity_by_blocks OD ρ γ]
  exact Finset.prod_congr rfl
    (fun j _ => prod_activity_block_split OD ρ γ j)

/-! ## III.3 — hard-core indicator factorization -/

/-- The γ₀-vs-mark incompatibility switch. -/
noncomputable def incompatibilityIndicator
    (γ₀ η : Polymer N) : ℕ :=
  if PlaquetteCompatible γ₀.val η.val then 0 else 1

/-- 11. The root-edge factor IS the incompatibility switch (the
    canonical orientation of stone 47b-iiA does the matching). -/
theorem rootEdge_indicator (γ₀ : Polymer N)
    (γ : Fin n → Polymer N) (OD : OrderedDecomposition n k)
    (j : Fin k) :
    hardCoreEdgeIndicator (rootedTuple γ₀ γ)
        (rootEdge (OD.marked j))
      = incompatibilityIndicator γ₀ (orderedRootValue γ OD j) := by
  show (if PlaquetteCompatible
      ((rootedTuple γ₀ γ) 0)
      ((rootedTuple γ₀ γ) (OD.marked j).succ) then 0 else 1) = _
  rw [rootedTuple_zero, rootedTuple_succ]
  rfl

/-- 12. The internal indicator of one component (global-assignment
    representation; internal edges never touch vertex 0). -/
noncomputable def orderedInternalTreeIndicator
    (γ₀ : Polymer N) (γ : Fin n → Polymer N)
    (OD : OrderedDecomposition n k) (j : Fin k) : ℕ :=
  ∏ ed ∈ OD.itree j,
    hardCoreEdgeIndicator (rootedTuple γ₀ γ) ed

/-- **14. INDICATOR CAPSTONE** — exact equality via the disjoint
    edge partition of Gate II (no edge in two components, none both
    internal and root, none joining distinct blocks). -/
theorem hardCoreIndicator_factorization (γ₀ : Polymer N)
    (γ : Fin n → Polymer N) (OD : OrderedDecomposition n k) :
    hardCoreTreeIndicator (rootedTuple γ₀ γ) (reconstructTree OD)
      = ∏ j : Fin k,
          (incompatibilityIndicator γ₀ (orderedRootValue γ OD j)
            * orderedInternalTreeIndicator γ₀ γ OD j) := by
  unfold hardCoreTreeIndicator reconstructTree
  have hdisj : Disjoint
      (Finset.univ.image (fun j => rootEdge (OD.marked j)))
      (Finset.univ.biUnion (fun j => OD.itree j)) := by
    rw [Finset.disjoint_left]
    intro ed h1 h2
    rw [Finset.mem_image] at h1
    obtain ⟨j, -, hj⟩ := h1
    rw [Finset.mem_biUnion] at h2
    obtain ⟨j', -, hj'⟩ := h2
    refine itree_fst_ne_zero hj' ?_
    rw [← hj]
    rfl
  rw [Finset.prod_union hdisj]
  have hinj : ∀ x ∈ (Finset.univ : Finset (Fin k)),
      ∀ y ∈ (Finset.univ : Finset (Fin k)),
      rootEdge (OD.marked x) = rootEdge (OD.marked y) → x = y :=
    fun x _ y _ h => OD.marked_inj (rootEdge_injective h)
  rw [Finset.prod_image hinj,
    Finset.prod_biUnion
      (fun j₁ _ j₂ _ hne => itree_pairwise_disjoint OD hne),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [rootEdge_indicator]
  rfl

/-! ## III.4 — the internal rooted weight (mark WITHOUT activity) -/

/-- The internal rooted weight of a block: internal indicator times
    TAIL activities only — the mark is the internal root and carries
    no activity here (it will later match the summand of
    `kpTreeCoeff (componentSize j) ρ ηⱼ` after relabeling; NOT
    proved in this gate). -/
noncomputable def orderedInternalRootedWeight
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) (γ : Fin n → Polymer N)
    (OD : OrderedDecomposition n k) (j : Fin k) : ℝ :=
  (orderedInternalTreeIndicator γ₀ γ OD j : ℝ)
    * ∏ v : {x // x ∈ ODtail OD j},
        ρ (orderedTailAssignment γ OD j v)

theorem orderedInternalRootedWeight_nonneg
    {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η) (γ₀ : Polymer N)
    (γ : Fin n → Polymer N) (OD : OrderedDecomposition n k)
    (j : Fin k) :
    0 ≤ orderedInternalRootedWeight ρ γ₀ γ OD j :=
  mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg (fun v _ => hρ _))

/-! ## III.5 — the total weight factorization -/

/-- The reconstruction version (item 20 — proved first, as the
    general engine). -/
theorem reconWeight_factorization (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) (γ : Fin n → Polymer N)
    (OD : OrderedDecomposition n k) :
    rootedTreeWeight ρ γ₀ γ (reconstructTree OD)
      = ∏ j : Fin k,
          (incompatibilityIndicator γ₀ (orderedRootValue γ OD j)
              * ρ (orderedRootValue γ OD j)
              * orderedInternalRootedWeight ρ γ₀ γ OD j) := by
  unfold rootedTreeWeight orderedInternalRootedWeight
  rw [hardCoreIndicator_factorization γ₀ γ OD,
    globalActivityFactorization OD ρ γ]
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  ring

/-- **GATE III CAPSTONE: `enumeratedTreeWeight_factorization`** —
    the weight of an enumerated tree at one assignment factors
    exactly over its ordered components. Activity audit: the k marks
    contribute the k explicit ρ(ηⱼ); the n−k tail vertices sit
    inside the internal weights; none omitted, none doubled; γ₀
    carries no activity. -/
theorem enumeratedTreeWeight_factorization (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) (γ : Fin n → Polymer N)
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ treesWithKRootNeighbors n k)
    (e : RootEnumeration ET k) :
    rootedTreeWeight ρ γ₀ γ ET
      = ∏ j : Fin k,
          (incompatibilityIndicator γ₀
              (orderedRootValue γ (decompose hET e) j)
            * ρ (orderedRootValue γ (decompose hET e) j)
            * orderedInternalRootedWeight ρ γ₀ γ
                (decompose hET e) j) := by
  rw [← decomposeThenReconstruct hET e]
  exact reconWeight_factorization ρ γ₀ γ (decompose hET e)

/-! ## Edge cases (criteria) -/

/-- k = 0 forces n = 0 (the cover has nowhere to send a vertex). -/
theorem OrderedDecomposition.n_eq_zero_of_k_zero
    (OD : OrderedDecomposition n 0) : n = 0 := by
  by_contra hn
  obtain ⟨j, -⟩ := OD.cover ⟨0, Nat.pos_of_ne_zero hn⟩
  exact j.elim0

/-- A unit block has an empty internal tree (both endpoints of an
    internal edge would collapse). -/
theorem itree_eq_empty_of_block_singleton
    (OD : OrderedDecomposition n k) {j : Fin k} {a : Fin n}
    (hj : OD.block j = {a}) :
    OD.itree j = (∅ : Finset (OrderedEdge (n + 1))) := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro ed hed
  obtain ⟨h1, h2⟩ := OD.sub j ed hed
  rw [hj] at h1 h2
  obtain ⟨b₁, hb₁, he₁⟩ := mem_succImage.mp h1
  obtain ⟨b₂, hb₂, he₂⟩ := mem_succImage.mp h2
  rw [Finset.mem_singleton] at hb₁ hb₂
  subst hb₁
  subst hb₂
  have : ed.val.1 = ed.val.2 := he₁.symm.trans he₂
  have hlt := ed.2
  rw [this] at hlt
  exact lt_irrefl _ hlt

/-- A unit block contributes indicator 1 and empty tail product. -/
theorem orderedInternalRootedWeight_of_block_singleton
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) (γ : Fin n → Polymer N)
    (OD : OrderedDecomposition n k) {j : Fin k} {a : Fin n}
    (hj : OD.block j = {a}) :
    orderedInternalRootedWeight ρ γ₀ γ OD j = 1 := by
  unfold orderedInternalRootedWeight orderedInternalTreeIndicator
  rw [itree_eq_empty_of_block_singleton OD hj, Finset.prod_empty,
    Finset.prod_coe_sort]
  have hmark : OD.marked j = a := by
    have := OD.marked_mem j
    rw [hj, Finset.mem_singleton] at this
    exact this
  unfold ODtail
  rw [hj, hmark, Finset.erase_singleton, Finset.prod_empty]
  norm_num

end LatticeGauge
