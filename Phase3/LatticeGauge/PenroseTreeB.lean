/-
LatticeGauge/PenroseTreeB.lean — Phase 3, fortieth stone (part b).

CONNECTED MINIMALITY, TREENESS AND RETRACTION OF THE BFS EXTRACTION
(architecture: Sol/GPT-5.6; execution: Fable). This part closes items
9 and 11 of the stone-40 specification WITHOUT any Walk.IsCycle
surgery, via the architect's cardinal route: (1) every connected
graph on Fin (n+1) contains its canonical BFS tree, hence has AT
LEAST n edges (a general, reusable lower bound); (2) a connected
graph with EXACTLY n edges can spare no edge — every available edge
is essential; (3) essential edges are bridges (the only walk
manipulation is a SIMPLE Walk induction building a detour through the
surviving reachability — no cycles, no rotations); (4) by Mathlib's
isAcyclic_iff_forall_adj_isBridge, the graph is acyclic, hence a
tree. This is the LOCAL, REUSABLE SUBSTITUTE for the cardinal
converse absent from the pinned v4.15 (which only has the forward
IsTree.card_edgeFinset). Applied to the BFS extraction:
penroseTree H is a tree; on a tree the extraction changes NOTHING
(any missing available edge could be erased keeping connectivity,
contradicting stone 39's edge-essentiality of trees), so
penroseTreeEdges T = availableEdges T, penroseTree T = T, and the
extraction is idempotent. Sym2 appears ONLY in a local endpoint
adapter (eraseOrderedEdgeGraph = deleteEdges of the corresponding
Sym2 singleton); no general Sym2 ↔ OrderedEdge library is built —
that equivalence remains registered technical debt. NOT HERE: no
Penrose closure, no P1/P2, no fibres, no intervals, no (1−1)^m
application, no Penrose identity, no tree-graph bound, no tree
counting, no series, no log Z, no convergence. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.UrsellCoefficients
import LatticeGauge.UrsellSymmetry
import LatticeGauge.UrsellBounds
import LatticeGauge.PenroseTree

open scoped Classical

namespace LatticeGauge

variable {n : ℕ}

/-! ## 2. Generated graphs recover their edge sets; edge removal -/

/-- **availableEdges is a retraction of graphOfEdges** — fully general
    and reusable. -/
theorem availableEdges_graphOfEdges {m : ℕ}
    (S : Finset (OrderedEdge m)) :
    availableEdges (graphOfEdges S) = S := by
  ext f
  rw [mem_availableEdges,
    graphOfEdges_adj_iff_canonical (ne_of_lt f.2),
    canonicalOrderedEdge_val]

/-- Removal of one canonical edge, at the graph level. -/
noncomputable def eraseOrderedEdgeGraph {m : ℕ}
    (G : SimpleGraph (Fin m)) (e : OrderedEdge m) :
    SimpleGraph (Fin m) :=
  graphOfEdges ((availableEdges G).erase e)

theorem eraseOrderedEdgeGraph_le {m : ℕ}
    (G : SimpleGraph (Fin m)) (e : OrderedEdge m) :
    eraseOrderedEdgeGraph G e ≤ G := by
  have h := graphOfEdges_mono
    (Finset.erase_subset e (availableEdges G))
  rwa [graphOfEdges_availableEdges] at h

/-! ## 1. Lower bound: connected graphs have at least n edges -/

theorem penroseTreeEdges_subset_availableEdges
    (H : SimpleGraph (Fin (n + 1))) :
    penroseTreeEdges H ⊆ availableEdges H :=
  fun _ he => mem_availableEdges.mpr (penroseTreeEdges_adj he)

/-- **CAPSTONE (general lower bound): every connected graph on
    Fin (n+1) has at least n edges** — it contains its canonical BFS
    tree. -/
theorem connected_card_availableEdges_ge
    {G : SimpleGraph (Fin (n + 1))} (hG : G.Connected) :
    n ≤ (availableEdges G).card := by
  calc n = (penroseTreeEdges G).card :=
        (card_penroseTreeEdges hG).symm
    _ ≤ (availableEdges G).card :=
        Finset.card_le_card (penroseTreeEdges_subset_availableEdges G)

/-! ## 3. Cardinal minimality makes every edge essential -/

theorem essential_of_card_eq {G : SimpleGraph (Fin (n + 1))}
    (hG : G.Connected)
    (hcard : (availableEdges G).card = n)
    {e : OrderedEdge (n + 1)} (he : e ∈ availableEdges G) :
    ¬ (eraseOrderedEdgeGraph G e).Connected := by
  intro hconn
  have hge := connected_card_availableEdges_ge hconn
  have hcard' : (availableEdges (eraseOrderedEdgeGraph G e)).card
      = (availableEdges G).card - 1 := by
    unfold eraseOrderedEdgeGraph
    rw [availableEdges_graphOfEdges, Finset.card_erase_of_mem he]
  have hpos : 0 < (availableEdges G).card :=
    Finset.card_pos.mpr ⟨e, he⟩
  omega

/-! ## 4. The minimal Sym2 adapter -/

/-- **Local adapter (the ONLY Sym2 contact)**: erasing a canonical
    edge is deleting the corresponding Sym2 singleton. -/
theorem eraseOrderedEdgeGraph_eq_deleteEdges {m : ℕ}
    {G : SimpleGraph (Fin m)} {e : OrderedEdge m}
    (he : e ∈ availableEdges G) :
    eraseOrderedEdgeGraph G e
      = G.deleteEdges {s(e.val.1, e.val.2)} := by
  ext i j
  unfold eraseOrderedEdgeGraph
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · intro h
    have hne : i ≠ j := h.ne
    rw [graphOfEdges_adj_iff_canonical hne, Finset.mem_erase] at h
    obtain ⟨hnee, hmem⟩ := h
    refine ⟨(adj_canonicalOrderedEdge G hne).mp
      (mem_availableEdges.mp hmem), ?_⟩
    rw [Set.mem_singleton_iff]
    intro hsym
    apply hnee
    rcases Sym2.eq_iff.mp hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2
      exact canonicalOrderedEdge_val e
    · subst h1; subst h2
      rw [canonicalOrderedEdge_comm]
      exact canonicalOrderedEdge_val e
  · rintro ⟨hadj, hnot⟩
    have hne : i ≠ j := hadj.ne
    rw [graphOfEdges_adj_iff_canonical hne, Finset.mem_erase]
    refine ⟨?_, mem_availableEdges.mpr
      ((adj_canonicalOrderedEdge G hne).mpr hadj)⟩
    intro heq
    apply hnot
    rw [Set.mem_singleton_iff, ← heq]
    rcases hne.lt_or_lt with h' | h'
    · rw [canonicalOrderedEdge_of_lt h' hne]
    · rw [canonicalOrderedEdge_of_gt h' hne]
      exact Sym2.eq_swap

/-- **The detour lemma (simple Walk induction — no cycles)**: if the
    endpoints of the deleted edge remain reachable, every walk of G
    transfers to the deleted graph, edge by edge, using the detour
    whenever the deleted edge appears. -/
private theorem reachable_delete_of_reachable {V : Type*}
    {G : SimpleGraph V} {u v : V}
    (hdet : (G.deleteEdges {s(u, v)}).Reachable u v) :
    ∀ {x y : V}, G.Walk x y →
      (G.deleteEdges {s(u, v)}).Reachable x y := by
  intro x y p
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | @cons a b c hadj q ih =>
    refine SimpleGraph.Reachable.trans ?_ ih
    by_cases hsy : s(a, b) = s(u, v)
    · rcases Sym2.eq_iff.mp hsy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · subst h1; subst h2
        exact hdet
      · subst h1; subst h2
        exact hdet.symm
    · exact ⟨SimpleGraph.Walk.cons
        (SimpleGraph.deleteEdges_adj.mpr
          ⟨hadj, by simpa using hsy⟩)
        SimpleGraph.Walk.nil⟩

/-! ## 5. CAPSTONE: the cardinal converse -/

/-- **THE LOCAL CARDINAL CONVERSE (absent from the pinned Mathlib):
    a connected graph on n+1 vertices with exactly n edges is a
    tree.** Proof by edge minimality, not by explicit cycle surgery:
    every edge is essential; an essential edge is a bridge (any walk
    between its endpoints avoiding it would let the erased graph stay
    connected via the detour lemma); acyclicity follows from
    isAcyclic_iff_forall_adj_isBridge. -/
theorem isTree_of_connected_card {G : SimpleGraph (Fin (n + 1))}
    (hG : G.Connected)
    (hcard : (availableEdges G).card = n) :
    G.IsTree := by
  rw [SimpleGraph.isTree_iff]
  refine ⟨hG, ?_⟩
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro u v hadj
  rw [SimpleGraph.isBridge_iff]
  refine ⟨hadj, ?_⟩
  intro hreach
  have hne := hadj.ne
  have hmem : canonicalOrderedEdge u v hne ∈ availableEdges G :=
    mem_availableEdges.mpr
      ((adj_canonicalOrderedEdge G hne).mpr hadj)
  have hsymeq : s((canonicalOrderedEdge u v hne).val.1,
      (canonicalOrderedEdge u v hne).val.2) = s(u, v) := by
    rcases hne.lt_or_lt with h' | h'
    · rw [canonicalOrderedEdge_of_lt h' hne]
    · rw [canonicalOrderedEdge_of_gt h' hne]
      exact Sym2.eq_swap
  apply essential_of_card_eq hG hcard hmem
  rw [eraseOrderedEdgeGraph_eq_deleteEdges hmem, hsymeq]
  rw [SimpleGraph.connected_iff]
  refine ⟨fun a b => ?_, ⟨0⟩⟩
  obtain ⟨p⟩ := hG.preconnected a b
  exact reachable_delete_of_reachable hreach p

/-! ## 6. The BFS extraction produces a tree -/

/-- **CAPSTONE (item 9 of stone 40): the canonical BFS extraction of
    a connected graph is a tree.** -/
theorem penroseTree_isTree {H : SimpleGraph (Fin (n + 1))}
    (hH : H.Connected) : (penroseTree H).IsTree := by
  apply isTree_of_connected_card (penroseTree_connected hH)
  unfold penroseTree
  rw [availableEdges_graphOfEdges]
  exact card_penroseTreeEdges hH

/-! ## 7-8. Retraction on trees -/

/-- **On a tree, the extraction keeps EVERY edge** (a missing
    available edge could be erased while preserving connectivity —
    contradicting stone 39's essentiality of tree edges). -/
theorem penroseTreeEdges_eq_of_isTree
    {T : SimpleGraph (Fin (n + 1))} (hT : T.IsTree) :
    penroseTreeEdges T = availableEdges T := by
  refine Finset.Subset.antisymm
    (penroseTreeEdges_subset_availableEdges T) ?_
  by_contra hnot
  obtain ⟨e, heav, henot⟩ :
      ∃ e ∈ availableEdges T, e ∉ penroseTreeEdges T := by
    by_contra h
    push_neg at h
    exact hnot h
  have hsub' : penroseTreeEdges T ⊆ (availableEdges T).erase e :=
    fun x hx => Finset.mem_erase.mpr
      ⟨fun hxe => henot (hxe ▸ hx),
        penroseTreeEdges_subset_availableEdges T hx⟩
  have hconnT := penroseTree_connected hT.isConnected
  have hconn' :
      (graphOfEdges ((availableEdges T).erase e)).Connected :=
    hconnT.mono (graphOfEdges_mono hsub')
  exact (isTree_all_edges_essential hT e heav).2 hconn'

/-- **CAPSTONE (item 11 of stone 40): trees are fixed points of the
    extraction.** -/
theorem penroseTree_eq_self_of_isTree
    {T : SimpleGraph (Fin (n + 1))} (hT : T.IsTree) :
    penroseTree T = T := by
  unfold penroseTree
  rw [penroseTreeEdges_eq_of_isTree hT, graphOfEdges_availableEdges]

/-! ## 9. Idempotence -/

/-- **CAPSTONE: the extraction is idempotent** — required by the
    fibre theory of stone 41. -/
theorem penroseTree_idem {H : SimpleGraph (Fin (n + 1))}
    (hH : H.Connected) :
    penroseTree (penroseTree H) = penroseTree H :=
  penroseTree_eq_self_of_isTree (penroseTree_isTree hH)

end LatticeGauge
