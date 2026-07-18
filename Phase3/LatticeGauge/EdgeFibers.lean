/-
LatticeGauge/EdgeFibers.lean — Phase 3, forty-second stone (a).

EDGE-SET PARTITION AND THE FREE COORDINATES OF THE PENROSE FIBRES
(architecture: Sol/GPT-5.6; execution: Fable). The Ursell sum lives on
Finset (OrderedEdge (n+1)); this stone transports the stone-41 fibre
theory to that domain and equips each fibre with FREE COORDINATES:
for a spanning tree ET of the ambient G, the connected edge sets
extracting ET are EXACTLY the interval ET ⊆ E ⊆ R_G(ET) (transport of
the 41b equivalence through the graphOfEdges/availableEdges inverse
pair), and choosing a member of the fibre is the same as choosing an
arbitrary SUBSET of the extra edges X_T = closure \ ET — a switch
panel, one independent switch per extra edge (explicit inverse maps
E ↦ E \ ET and F ↦ ET ∪ F, plus an internal subtype Equiv for 42b).
EXPLICIT CONDITION (architect): the bijection is only asserted when
ET IS a spanning tree of G — without it ET ∪ F need not be connected;
every bijection statement carries hET. Cardinalities split
(|ET ∪ F| = |ET| + |F|) and the sign factorizes — but NO sums are
reindexed here, no (1−1)^m is applied, no surviving trees are
defined, no Penrose identity, no tree-graph bound, no counting, no
series, no convergence. FIN 0 NOTE: the whole rooted Penrose
infrastructure lives on Fin (n+1); the Fin 0 case of the Ursell
coefficient does not use a rooted extraction and will be handled
separately in the FINAL theorem of 42b — no artificial root is
introduced on the empty type, and this stone is NOT generalized to
Fin n with a Nonempty hypothesis. NO axioms.
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

open scoped Classical

namespace LatticeGauge

variable {n : ℕ}

/-! ## Transport bridges (graphs ↔ edge Finsets) -/

theorem graphOfEdges_le_iff {m : ℕ} {E E' : Finset (OrderedEdge m)} :
    graphOfEdges E ≤ graphOfEdges E' ↔ E ⊆ E' := by
  constructor
  · intro h e he
    have hadj : (graphOfEdges E).Adj e.val.1 e.val.2 := by
      rw [graphOfEdges_adj_iff_canonical (ne_of_lt e.2),
        canonicalOrderedEdge_val]
      exact he
    have h2 := h hadj
    rwa [graphOfEdges_adj_iff_canonical (ne_of_lt e.2),
      canonicalOrderedEdge_val] at h2
  · exact graphOfEdges_mono

theorem graphOfEdges_le_iff_subset_available {m : ℕ}
    {G : SimpleGraph (Fin m)} {E : Finset (OrderedEdge m)} :
    graphOfEdges E ≤ G ↔ E ⊆ availableEdges G := by
  conv_lhs => rw [← graphOfEdges_availableEdges G]
  exact graphOfEdges_le_iff

/-! ## 1. Spanning trees in edge sets -/

/-- **The universe of spanning-tree edge sets** ("spanning" is built
    into the vertex type Fin (n+1); the conditions are: edges of G,
    and the generated graph is a tree). -/
noncomputable def spanningTreeEdgeSets (G : SimpleGraph (Fin (n + 1))) :
    Finset (Finset (OrderedEdge (n + 1))) :=
  (availableEdges G).powerset.filter
    (fun ET => (graphOfEdges ET).IsTree)

theorem mem_spanningTreeEdgeSets {G : SimpleGraph (Fin (n + 1))}
    {ET : Finset (OrderedEdge (n + 1))} :
    ET ∈ spanningTreeEdgeSets G
      ↔ ET ⊆ availableEdges G ∧ (graphOfEdges ET).IsTree := by
  unfold spanningTreeEdgeSets
  simp [Finset.mem_filter, Finset.mem_powerset]

/-! ## 2. The extracted tree of a connected edge set -/

/-- The extracted BFS edges of a connected edge set stay inside it. -/
theorem extractedTreeEdges_subset {E : Finset (OrderedEdge (n + 1))} :
    penroseTreeEdges (graphOfEdges E) ⊆ E := by
  have h := penroseTreeEdges_subset_availableEdges (graphOfEdges E)
  rwa [availableEdges_graphOfEdges] at h

/-- **The canonical index of a connected edge set is a spanning
    tree.** -/
theorem extractedTree_mem_spanningTreeEdgeSets
    {G : SimpleGraph (Fin (n + 1))} {E : Finset (OrderedEdge (n + 1))}
    (hE : E ∈ connectedSpanningEdgeSets G) :
    penroseTreeEdges (graphOfEdges E) ∈ spanningTreeEdgeSets G := by
  obtain ⟨hsub, hconn⟩ := mem_connectedSpanningEdgeSets.mp hE
  rw [mem_spanningTreeEdgeSets]
  exact ⟨fun e he => hsub (extractedTreeEdges_subset he),
    penroseTree_isTree hconn⟩

/-! ## 3. The fibre in edge sets -/

/-- **The fibre of ET**: connected edge sets whose extracted tree is
    ET. Total for any Finset. -/
noncomputable def penroseEdgeFiber (G : SimpleGraph (Fin (n + 1)))
    (ET : Finset (OrderedEdge (n + 1))) :
    Finset (Finset (OrderedEdge (n + 1))) :=
  (connectedSpanningEdgeSets G).filter
    (fun E => penroseTreeEdges (graphOfEdges E) = ET)

theorem mem_penroseEdgeFiber {G : SimpleGraph (Fin (n + 1))}
    {ET E : Finset (OrderedEdge (n + 1))} :
    E ∈ penroseEdgeFiber G ET
      ↔ E ∈ connectedSpanningEdgeSets G ∧
        penroseTreeEdges (graphOfEdges E) = ET := by
  unfold penroseEdgeFiber
  simp [Finset.mem_filter]

/-! ## 4. The closure in edge sets -/

noncomputable def penroseEdgeClosure (G : SimpleGraph (Fin (n + 1)))
    (ET : Finset (OrderedEdge (n + 1))) :
    Finset (OrderedEdge (n + 1)) :=
  penroseClosureEdges G (graphOfEdges ET)

/-- The two closure presentations agree definitionally. -/
theorem graphOfEdges_penroseEdgeClosure
    (G : SimpleGraph (Fin (n + 1)))
    (ET : Finset (OrderedEdge (n + 1))) :
    graphOfEdges (penroseEdgeClosure G ET)
      = penroseClosure G (graphOfEdges ET) := rfl

theorem penroseEdgeClosure_subset_available
    (G : SimpleGraph (Fin (n + 1)))
    (ET : Finset (OrderedEdge (n + 1))) :
    penroseEdgeClosure G ET ⊆ availableEdges G := by
  unfold penroseEdgeClosure penroseClosureEdges
  exact Finset.filter_subset _ _

theorem subset_penroseEdgeClosure {G : SimpleGraph (Fin (n + 1))}
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets G) :
    ET ⊆ penroseEdgeClosure G ET := by
  obtain ⟨hsub, -⟩ := mem_spanningTreeEdgeSets.mp hET
  intro e he
  unfold penroseEdgeClosure
  rw [mem_penroseClosureEdges]
  refine ⟨hsub he, Or.inl ?_⟩
  rw [availableEdges_graphOfEdges]
  exact he

/-! ## 5. CAPSTONE: the fibre IS the edge-set interval -/

/-- **The fibre of a spanning tree is exactly the boolean interval
    [ET, R_G(ET)] in edge sets** — the stone-41 equivalence
    transported through the graphOfEdges/availableEdges bridges.
    Connectivity in the converse direction is DERIVED from the tree
    inside, never assumed. -/
theorem mem_penroseEdgeFiber_iff_interval
    {G : SimpleGraph (Fin (n + 1))}
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets G)
    {E : Finset (OrderedEdge (n + 1))} :
    E ∈ penroseEdgeFiber G ET
      ↔ ET ⊆ E ∧ E ⊆ penroseEdgeClosure G ET := by
  obtain ⟨hsubG, hTree⟩ := mem_spanningTreeEdgeSets.mp hET
  rw [mem_penroseEdgeFiber]
  constructor
  · rintro ⟨hE, hfib⟩
    obtain ⟨hEsub, hconn⟩ := mem_connectedSpanningEdgeSets.mp hE
    have hπ : penroseTree (graphOfEdges E) = graphOfEdges ET :=
      congrArg graphOfEdges hfib
    obtain ⟨hTH, hHR⟩ := inPenroseInterval_of_penroseTree_eq hconn
      (graphOfEdges_le_iff_subset_available.mpr hEsub) hπ
    refine ⟨graphOfEdges_le_iff.mp hTH, ?_⟩
    rw [← graphOfEdges_penroseEdgeClosure] at hHR
    exact graphOfEdges_le_iff.mp hHR
  · rintro ⟨hTE, hEC⟩
    have hTH : graphOfEdges ET ≤ graphOfEdges E :=
      graphOfEdges_mono hTE
    have hHR : graphOfEdges E ≤ penroseClosure G (graphOfEdges ET) := by
      rw [← graphOfEdges_penroseEdgeClosure]
      exact graphOfEdges_mono hEC
    have hπ := penroseTree_eq_of_mem_interval hTree hTH hHR
    have hconn : (graphOfEdges E).Connected :=
      hTree.isConnected.mono hTH
    refine ⟨mem_connectedSpanningEdgeSets.mpr
      ⟨hEC.trans (penroseEdgeClosure_subset_available G ET), hconn⟩, ?_⟩
    have h1 : availableEdges (penroseTree (graphOfEdges E))
        = penroseTreeEdges (graphOfEdges E) := by
      unfold penroseTree
      rw [availableEdges_graphOfEdges]
    have h2 := congrArg availableEdges hπ
    rw [h1, availableEdges_graphOfEdges] at h2
    exact h2

/-! ## 6. The free extra edges -/

/-- **The switch panel**: the closure edges outside the tree. -/
noncomputable def penroseExtraEdges (G : SimpleGraph (Fin (n + 1)))
    (ET : Finset (OrderedEdge (n + 1))) :
    Finset (OrderedEdge (n + 1)) :=
  penroseEdgeClosure G ET \ ET

theorem disjoint_penroseExtraEdges
    (G : SimpleGraph (Fin (n + 1)))
    (ET : Finset (OrderedEdge (n + 1))) :
    Disjoint ET (penroseExtraEdges G ET) :=
  Finset.disjoint_sdiff

theorem union_penroseExtraEdges {G : SimpleGraph (Fin (n + 1))}
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets G) :
    ET ∪ penroseExtraEdges G ET = penroseEdgeClosure G ET :=
  Finset.union_sdiff_of_subset (subset_penroseEdgeClosure hET)

theorem union_subset_closure {G : SimpleGraph (Fin (n + 1))}
    {ET F : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets G)
    (hF : F ⊆ penroseExtraEdges G ET) :
    ET ∪ F ⊆ penroseEdgeClosure G ET :=
  Finset.union_subset (subset_penroseEdgeClosure hET)
    (hF.trans Finset.sdiff_subset)

theorem sdiff_subset_extraEdges {G : SimpleGraph (Fin (n + 1))}
    {ET E : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets G)
    (hE : E ∈ penroseEdgeFiber G ET) :
    E \ ET ⊆ penroseExtraEdges G ET := by
  obtain ⟨-, hEC⟩ := (mem_penroseEdgeFiber_iff_interval hET).mp hE
  exact Finset.sdiff_subset_sdiff hEC (Finset.Subset.refl ET)

/-! ## 7-9. The inverse coordinate maps -/

/-- **Fibre → free coordinates.** -/
theorem fiberToExtras_mem {G : SimpleGraph (Fin (n + 1))}
    {ET E : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets G)
    (hE : E ∈ penroseEdgeFiber G ET) :
    E \ ET ∈ (penroseExtraEdges G ET).powerset :=
  Finset.mem_powerset.mpr (sdiff_subset_extraEdges hET hE)

/-- **Free coordinates → fibre** — the direction that NEEDS ET to be
    a spanning tree (otherwise ET ∪ F need not be connected). -/
theorem extrasToFiber_mem {G : SimpleGraph (Fin (n + 1))}
    {ET F : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets G)
    (hF : F ⊆ penroseExtraEdges G ET) :
    ET ∪ F ∈ penroseEdgeFiber G ET :=
  (mem_penroseEdgeFiber_iff_interval hET).mpr
    ⟨Finset.subset_union_left, union_subset_closure hET hF⟩

/-- **9A. Left inverse**: reattaching the tree recovers the member. -/
theorem union_sdiff_fiber {G : SimpleGraph (Fin (n + 1))}
    {ET E : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets G)
    (hE : E ∈ penroseEdgeFiber G ET) :
    ET ∪ (E \ ET) = E :=
  Finset.union_sdiff_of_subset
    ((mem_penroseEdgeFiber_iff_interval hET).mp hE).1

/-- **9B. Right inverse**: stripping the tree recovers the
    coordinates. -/
theorem sdiff_union_extras {G : SimpleGraph (Fin (n + 1))}
    {ET F : Finset (OrderedEdge (n + 1))}
    (hF : F ⊆ penroseExtraEdges G ET) :
    (ET ∪ F) \ ET = F :=
  Finset.union_sdiff_cancel_left
    (Finset.disjoint_of_subset_right hF
      (disjoint_penroseExtraEdges G ET))

/-! ## 10. The internal bijection and the cardinality -/

/-- **The fibre ≃ the powerset of the extra edges** (internal subtype
    Equiv, for the 42b reindexation; the public API stays on plain
    Finsets via the four lemmas above). -/
noncomputable def penroseFiberEquiv {G : SimpleGraph (Fin (n + 1))}
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets G) :
    {E // E ∈ penroseEdgeFiber G ET}
      ≃ {F // F ∈ (penroseExtraEdges G ET).powerset} where
  toFun E := ⟨E.val \ ET, fiberToExtras_mem hET E.2⟩
  invFun F := ⟨ET ∪ F.val,
    extrasToFiber_mem hET (Finset.mem_powerset.mp F.2)⟩
  left_inv := by
    rintro ⟨E, hE⟩
    exact Subtype.ext (union_sdiff_fiber hET hE)
  right_inv := by
    rintro ⟨F, hF⟩
    exact Subtype.ext (sdiff_union_extras (Finset.mem_powerset.mp hF))

theorem card_penroseEdgeFiber {G : SimpleGraph (Fin (n + 1))}
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets G) :
    (penroseEdgeFiber G ET).card
      = ((penroseExtraEdges G ET).powerset).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (penroseFiberEquiv hET)

/-! ## 11. Cardinality and sign preparation -/

theorem card_union_extras {G : SimpleGraph (Fin (n + 1))}
    {ET F : Finset (OrderedEdge (n + 1))}
    (hF : F ⊆ penroseExtraEdges G ET) :
    (ET ∪ F).card = ET.card + F.card :=
  Finset.card_union_of_disjoint
    (Finset.disjoint_of_subset_right hF
      (disjoint_penroseExtraEdges G ET))

/-- Sign factorization — consumed by 42b, no sums taken here. -/
theorem neg_one_pow_card_union {G : SimpleGraph (Fin (n + 1))}
    {ET F : Finset (OrderedEdge (n + 1))}
    (hF : F ⊆ penroseExtraEdges G ET) :
    (-1 : ℤ) ^ (ET ∪ F).card
      = (-1 : ℤ) ^ ET.card * (-1 : ℤ) ^ F.card := by
  rw [card_union_extras hF, pow_add]

/-! ## 12-14. Cover, disjointness, exact union of the fibres -/

theorem mem_fiber_extracted {G : SimpleGraph (Fin (n + 1))}
    {E : Finset (OrderedEdge (n + 1))}
    (hE : E ∈ connectedSpanningEdgeSets G) :
    E ∈ penroseEdgeFiber G (penroseTreeEdges (graphOfEdges E)) := by
  rw [mem_penroseEdgeFiber]
  exact ⟨hE, rfl⟩

theorem penroseEdgeFiber_disjoint {G : SimpleGraph (Fin (n + 1))}
    {ET₁ ET₂ : Finset (OrderedEdge (n + 1))} (hne : ET₁ ≠ ET₂) :
    Disjoint (penroseEdgeFiber G ET₁) (penroseEdgeFiber G ET₂) := by
  rw [Finset.disjoint_left]
  intro E h1 h2
  exact hne ((mem_penroseEdgeFiber.mp h1).2.symm.trans
    (mem_penroseEdgeFiber.mp h2).2)

/-- **CAPSTONE (structural union): the fibres indexed by the spanning
    trees cover the connected edge sets exactly.** -/
theorem biUnion_penroseEdgeFiber (G : SimpleGraph (Fin (n + 1))) :
    (spanningTreeEdgeSets G).biUnion (fun ET => penroseEdgeFiber G ET)
      = connectedSpanningEdgeSets G := by
  ext E
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨ET, -, hE⟩
    exact (mem_penroseEdgeFiber.mp hE).1
  · intro hE
    exact ⟨penroseTreeEdges (graphOfEdges E),
      extractedTree_mem_spanningTreeEdgeSets hE,
      mem_fiber_extracted hE⟩

end LatticeGauge
