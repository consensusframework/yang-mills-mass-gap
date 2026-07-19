/-
LatticeGauge/PenroseIdentity.lean — Phase 3, forty-second stone (b).

THE PENROSE CANCELLATION AND THE TREE-GRAPH BOUND
(architecture: Sol/GPT-5.6; execution: Fable). The lemma stored since
stone 37 finally leaves the drawer. Two formal reindexations — the
Ursell sum grouped by the (pairwise disjoint, exactly covering)
Penrose fibres of 42a, then each fibre traded for the powerset of its
free extra edges — expose the alternating sum (1−1)^|extras|: every
fibre with a nonempty switch panel cancels IN PAIRS, and only the
PENROSE TREES survive (spanning trees whose closure adds no edge).
Since every spanning tree on Fin (n+1) has exactly n edges (stone 40
retraction + stone 40b inverse), the sign is constant and the
identity is EXACT:  graphUrsellCoeff G = (−1)^n · #PenroseTrees(G),
hence |φ(G)| = #PenroseTrees(G) ≤ #SpanningTrees(G) — the finite
TREE-GRAPH BOUND for the stone-37 coefficient, replacing the 2^|E|
scale of stone 39 by the spanning-tree scale. The identity is purely
combinatorial and finite: it controls the coefficient by the NUMBER
of spanning trees but does NOT count them (no Cayley/Prüfer), inserts
NO polymer activities, defines NO series, proves NO convergence
criterion, and implies NOTHING about clustering or a mass gap. Fibres
with extra edges contribute exactly zero — this is stated, not
hidden. FIN 0: the rooted partition scheme covers graphs with at
least one vertex; the empty case is separate and trivial (Mathlib's
Connected requires an inhabitant, so the stone-37 disconnected
theorem applies). NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.UrsellCoefficients
import LatticeGauge.UrsellSymmetry
import LatticeGauge.UrsellBounds
import LatticeGauge.PenroseTree
import LatticeGauge.PenroseTreeB
import LatticeGauge.PenroseClosure
import LatticeGauge.PenroseFibers
import LatticeGauge.EdgeFibers

open scoped Classical

namespace LatticeGauge

variable {n : ℕ}

/-! ## 1. The surviving Penrose trees -/

/-- **The Penrose trees of G**: spanning trees whose closure relative
    to G adds no edge — the survivors of the interval cancellation.
    NOT, in general, all spanning trees of G. -/
noncomputable def penroseTreeEdgeSets (G : SimpleGraph (Fin (n + 1))) :
    Finset (Finset (OrderedEdge (n + 1))) :=
  (spanningTreeEdgeSets G).filter
    (fun ET => penroseExtraEdges G ET = ∅)

theorem mem_penroseTreeEdgeSets {G : SimpleGraph (Fin (n + 1))}
    {ET : Finset (OrderedEdge (n + 1))} :
    ET ∈ penroseTreeEdgeSets G
      ↔ ET ∈ spanningTreeEdgeSets G ∧ penroseExtraEdges G ET = ∅ := by
  unfold penroseTreeEdgeSets
  simp [Finset.mem_filter]

/-! ## 7 (early, used throughout). Spanning trees have n edges -/

/-- **Every spanning-tree edge set on Fin (n+1) has exactly n
    edges** — via the stone-40 retraction (trees are fixed points of
    the BFS extraction) and the 40a edge count; no new theory of tree
    edge counts. -/
theorem card_of_mem_spanningTreeEdgeSets
    {G : SimpleGraph (Fin (n + 1))}
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets G) :
    ET.card = n := by
  obtain ⟨-, hTree⟩ := mem_spanningTreeEdgeSets.mp hET
  have h1 : penroseTreeEdges (graphOfEdges ET)
      = availableEdges (graphOfEdges ET) :=
    penroseTreeEdges_eq_of_isTree hTree
  have h2 := card_penroseTreeEdges hTree.isConnected
  rw [h1, availableEdges_graphOfEdges] at h2
  exact h2

/-! ## 2. First reindexation: connected sets grouped by fibres -/

/-- **Reindexation 1**: the Ursell sum grouped by the pairwise
    disjoint fibres of 42a, indexed by the spanning trees. -/
theorem graphUrsellCoeff_eq_sum_fibers
    (G : SimpleGraph (Fin (n + 1))) :
    graphUrsellCoeff G
      = ∑ ET ∈ spanningTreeEdgeSets G,
          ∑ E ∈ penroseEdgeFiber G ET, (-1 : ℤ) ^ E.card := by
  unfold graphUrsellCoeff
  rw [← biUnion_penroseEdgeFiber G]
  exact Finset.sum_biUnion
    (fun ET₁ _ ET₂ _ hne => penroseEdgeFiber_disjoint hne)

/-! ## 3. Second reindexation: fibre traded for the switch panel -/

/-- **Reindexation 2**: the fibre sum carried to the powerset of the
    extra edges through the 42a bijection E ↦ E \ ET, F ↦ ET ∪ F.
    Only under the spanning-tree hypothesis. -/
theorem sum_fiber_eq_sum_powerset {G : SimpleGraph (Fin (n + 1))}
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets G) :
    (∑ E ∈ penroseEdgeFiber G ET, (-1 : ℤ) ^ E.card)
      = ∑ F ∈ (penroseExtraEdges G ET).powerset,
          (-1 : ℤ) ^ (ET ∪ F).card := by
  refine Finset.sum_bij (fun E _ => E \ ET) ?_ ?_ ?_ ?_
  · intro E hE
    show E \ ET ∈ (penroseExtraEdges G ET).powerset
    exact fiberToExtras_mem hET hE
  · intro E₁ h₁ E₂ h₂ heq
    simp only [] at heq
    calc E₁ = ET ∪ (E₁ \ ET) := (union_sdiff_fiber hET h₁).symm
      _ = ET ∪ (E₂ \ ET) := by rw [heq]
      _ = E₂ := union_sdiff_fiber hET h₂
  · intro F hF
    refine ⟨ET ∪ F, extrasToFiber_mem hET (Finset.mem_powerset.mp hF), ?_⟩
    show F = (ET ∪ F) \ ET
    exact (sdiff_union_extras (Finset.mem_powerset.mp hF)).symm
  · intro E hE
    show (-1 : ℤ) ^ E.card = (-1 : ℤ) ^ (ET ∪ (E \ ET)).card
    rw [union_sdiff_fiber hET hE]

/-! ## 4. Sign factorization -/

theorem sum_powerset_sign_factor {G : SimpleGraph (Fin (n + 1))}
    {ET : Finset (OrderedEdge (n + 1))} :
    (∑ F ∈ (penroseExtraEdges G ET).powerset,
        (-1 : ℤ) ^ (ET ∪ F).card)
      = (-1 : ℤ) ^ ET.card *
          ∑ F ∈ (penroseExtraEdges G ET).powerset,
            (-1 : ℤ) ^ F.card := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun F hF => ?_)
  exact neg_one_pow_card_union (Finset.mem_powerset.mp hF)

/-! ## 5. The cancellation trigger -/

/-- **The extra edges fall in pairs**: the fibre sum is (−1)^|ET| if
    the switch panel is empty and 0 otherwise — the stone-37 lemma
    (1−1)^|S| finally consumed. NOT yet the tree-graph bound. -/
theorem penrose_fiber_sign_sum {G : SimpleGraph (Fin (n + 1))}
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets G) :
    (∑ E ∈ penroseEdgeFiber G ET, (-1 : ℤ) ^ E.card)
      = if penroseExtraEdges G ET = ∅
        then (-1 : ℤ) ^ ET.card else 0 := by
  rw [sum_fiber_eq_sum_powerset hET, sum_powerset_sign_factor,
    sum_powerset_neg_one_pow_card]
  by_cases h : penroseExtraEdges G ET = ∅ <;> simp [h]

/-! ## 6. Collapse of the outer sum -/

/-- **The partition identity**: only the Penrose trees survive.
    Spanning trees with nonempty extra edges contribute EXACTLY
    zero — this is where they disappear, not hidden. -/
theorem graphUrsellCoeff_eq_sum_penrose_trees
    (G : SimpleGraph (Fin (n + 1))) :
    graphUrsellCoeff G
      = ∑ ET ∈ penroseTreeEdgeSets G, (-1 : ℤ) ^ ET.card := by
  calc graphUrsellCoeff G
      = ∑ ET ∈ spanningTreeEdgeSets G,
          ∑ E ∈ penroseEdgeFiber G ET, (-1 : ℤ) ^ E.card :=
        graphUrsellCoeff_eq_sum_fibers G
    _ = ∑ ET ∈ spanningTreeEdgeSets G,
          if penroseExtraEdges G ET = ∅
          then (-1 : ℤ) ^ ET.card else 0 :=
        Finset.sum_congr rfl (fun ET hET => penrose_fiber_sign_sum hET)
    _ = ∑ ET ∈ penroseTreeEdgeSets G, (-1 : ℤ) ^ ET.card := by
        unfold penroseTreeEdgeSets
        exact (Finset.sum_filter _ _).symm

/-! ## 8. The exact Penrose identity -/

/-- **THE PENROSE IDENTITY**: exact value of the graphic Ursell
    coefficient by the partition scheme. Each fibre is a boolean
    interval (42a); all fibres with extra edges cancel (item 5); the
    survivors are the spanning trees equal to their own closure; each
    has exactly n edges, so the sign is constant. -/
theorem penrose_identity (G : SimpleGraph (Fin (n + 1))) :
    graphUrsellCoeff G
      = (-1 : ℤ) ^ n * ((penroseTreeEdgeSets G).card : ℤ) := by
  rw [graphUrsellCoeff_eq_sum_penrose_trees]
  have hconst : ∀ ET ∈ penroseTreeEdgeSets G,
      (-1 : ℤ) ^ ET.card = (-1 : ℤ) ^ n := by
    intro ET hET
    rw [card_of_mem_spanningTreeEdgeSets
      (mem_penroseTreeEdgeSets.mp hET).1]
  calc (∑ ET ∈ penroseTreeEdgeSets G, (-1 : ℤ) ^ ET.card)
      = ∑ _ET ∈ penroseTreeEdgeSets G, (-1 : ℤ) ^ n :=
        Finset.sum_congr rfl hconst
    _ = (penroseTreeEdgeSets G).card • ((-1 : ℤ) ^ n) :=
        Finset.sum_const _
    _ = (-1 : ℤ) ^ n * ((penroseTreeEdgeSets G).card : ℤ) := by
        rw [nsmul_eq_mul, mul_comm]

/-! ## 9. Exact absolute value -/

theorem penrose_identity_natAbs (G : SimpleGraph (Fin (n + 1))) :
    (graphUrsellCoeff G).natAbs = (penroseTreeEdgeSets G).card := by
  have h1 : ((-1 : ℤ)).natAbs = 1 := rfl
  rw [penrose_identity, Int.natAbs_mul, Int.natAbs_pow, h1]
  simp

/-! ## 10. The tree-graph bound -/

theorem penrose_tree_count_le_spanning_tree_count
    (G : SimpleGraph (Fin (n + 1))) :
    (penroseTreeEdgeSets G).card ≤ (spanningTreeEdgeSets G).card := by
  unfold penroseTreeEdgeSets
  exact Finset.card_filter_le _ _

/-- **THE TREE-GRAPH BOUND** for the stone-37 Ursell coefficient:
    |φ(G)| ≤ #SpanningTrees(G). Finite and structural — NOT yet a
    convergence criterion (the trees are bounded, not counted). -/
theorem tree_graph_bound (G : SimpleGraph (Fin (n + 1))) :
    (graphUrsellCoeff G).natAbs ≤ (spanningTreeEdgeSets G).card := by
  rw [penrose_identity_natAbs]
  exact penrose_tree_count_le_spanning_tree_count G

/-! ## 11. Sanity: disconnected graphs -/

theorem spanningTreeEdgeSets_eq_empty_of_not_connected
    {G : SimpleGraph (Fin (n + 1))} (h : ¬ G.Connected) :
    spanningTreeEdgeSets G = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro ET hET
  obtain ⟨hsub, hTree⟩ := mem_spanningTreeEdgeSets.mp hET
  exact h (hTree.isConnected.mono (graphOfEdges_le hsub))

/-- Consistency check with the STRUCTURAL stone-37 zero (which needs
    no cancellation): for disconnected G both sides of the identity
    vanish. Not a new long proof. -/
theorem penroseTreeEdgeSets_eq_empty_of_not_connected
    {G : SimpleGraph (Fin (n + 1))} (h : ¬ G.Connected) :
    penroseTreeEdgeSets G = ∅ := by
  unfold penroseTreeEdgeSets
  rw [spanningTreeEdgeSets_eq_empty_of_not_connected h,
    Finset.filter_empty]

/-! ## 12. Sanity: the tree case recovers stone 39 -/

theorem spanningTreeEdgeSets_of_isTree
    {G : SimpleGraph (Fin (n + 1))} (hG : G.IsTree) :
    spanningTreeEdgeSets G = {availableEdges G} := by
  have hself : availableEdges G ∈ spanningTreeEdgeSets G := by
    rw [mem_spanningTreeEdgeSets]
    refine ⟨Finset.Subset.refl _, ?_⟩
    rw [graphOfEdges_availableEdges]
    exact hG
  have hcardG : (availableEdges G).card = n :=
    card_of_mem_spanningTreeEdgeSets hself
  ext ET
  rw [Finset.mem_singleton]
  constructor
  · intro hET
    obtain ⟨hsub, -⟩ := mem_spanningTreeEdgeSets.mp hET
    refine Finset.eq_of_subset_of_card_le hsub ?_
    rw [hcardG, card_of_mem_spanningTreeEdgeSets hET]
  · intro hEq
    rw [hEq]
    exact hself

theorem penroseExtraEdges_of_isTree
    {G : SimpleGraph (Fin (n + 1))} (_hG : G.IsTree) :
    penroseExtraEdges G (availableEdges G) = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro e he
  obtain ⟨hin, hnot⟩ := Finset.mem_sdiff.mp he
  exact hnot (penroseEdgeClosure_subset_available G (availableEdges G) hin)

theorem penroseTreeEdgeSets_of_isTree
    {G : SimpleGraph (Fin (n + 1))} (hG : G.IsTree) :
    penroseTreeEdgeSets G = {availableEdges G} := by
  unfold penroseTreeEdgeSets
  rw [spanningTreeEdgeSets_of_isTree hG, Finset.filter_singleton,
    if_pos (penroseExtraEdges_of_isTree hG)]

/-- The identity recovers the stone-39 exact tree value
    φ(T) = (−1)^n (consistency, stone 39 proved (−1)^|E| by
    uniqueness of the connected spanning edge set). -/
theorem graphUrsellCoeff_of_isTree_penrose
    {G : SimpleGraph (Fin (n + 1))} (hG : G.IsTree) :
    graphUrsellCoeff G = (-1 : ℤ) ^ n := by
  rw [penrose_identity, penroseTreeEdgeSets_of_isTree hG]
  simp

theorem graphUrsellCoeff_natAbs_of_isTree_penrose
    {G : SimpleGraph (Fin (n + 1))} (hG : G.IsTree) :
    (graphUrsellCoeff G).natAbs = 1 := by
  rw [penrose_identity_natAbs, penroseTreeEdgeSets_of_isTree hG,
    Finset.card_singleton]

/-! ## 13. The Fin 0 case, separate and trivial -/

/-- **Fin 0**: the rooted partition scheme covers graphs with at
    least one vertex; the empty case is separate — Mathlib's
    `Connected` requires an inhabitant, so the stone-37 structural
    zero applies. No artificial root, no `Option root`, no closure
    generalization. -/
theorem graphUrsellCoeff_fin_zero (G : SimpleGraph (Fin 0)) :
    graphUrsellCoeff G = 0 :=
  graphUrsellCoeff_of_not_connected G
    (fun h => h.nonempty.elim (fun x => x.elim0))

end LatticeGauge
