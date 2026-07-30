/-
LatticeGauge/RootDecomposition.lean — Phase 3, stone 47 (b-iiA).

THE PARTITION OF A SPANNING TREE AFTER REMOVING THE ROOT
(architecture: Sol/GPT-5.6; execution: Fable; the enumeration route
for the future k! was chosen by the architect — NOTHING of it enters
here: no Fin k ≃ rootNeighbors, no equivalence counting, no
factorial, no Perm action, no orbit-stabilizer, no size
compositions, no F(B), no recurrence, no partial sums, no KP
hypothesis, no Real.exp, no Summable).

For a spanning tree ET over Fin (n+1) rooted at 0 (the LEAST index,
so every root edge is literally ⟨(0, i.succ), _⟩ — proved, not
presumed, via the canonical-orientation lemma): the root neighbours
form a Finset of Fin n (the root excluded BY TYPE); removing the
root leaves the child forest, whose reachability relation partitions
the non-root vertices into components;每 component contains EXACTLY
ONE root neighbour (the central lemma: an internal path between two
root neighbours plus their two root edges would give two distinct
0→s paths in a tree, contradicting isTree_iff_existsUnique_path);
every non-root vertex lies in the component of some root neighbour
(the first edge of the unique root path); the edges of ET factor as
the disjoint union of the root edges and the per-component internal
edges; and ET is reconstructed exactly from its decomposition data.
The child forest lives on Fin (n+1) with the root ISOLATED (walks
between non-root vertices can never touch 0 — proved), while the
components themselves are Finsets of Fin n, as the brief prefers;
this consumes the existing graphOfEdges formalism instead of
inventing edge transport to Fin n. SCOPED NOTE (item 8): the
restriction of the forest to each block is proved CONNECTED WITHIN
the block; the tree-ness (acyclicity/cardinality) of the restriction
is deliberately deferred — the F(B) identification of 47b-iiB will
proceed by relabeling (47b-i) plus the 40b cardinal converse, which
does not consume it. Edge cases n = 0, n > 0, n = 1 are explicit.
NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.UrsellCoefficients
import LatticeGauge.UrsellSymmetry
import LatticeGauge.UrsellBounds
import LatticeGauge.PenroseTree
import LatticeGauge.PenroseTreeB
import LatticeGauge.EdgeFibers
import LatticeGauge.PolymerTreeBound
import LatticeGauge.KPCoefficients

open scoped Classical

namespace LatticeGauge

variable {n : ℕ}

/-! ## 1. Root edges and root neighbours -/

/-- The canonical edge from the root 0 to the non-root vertex
    i.succ. Total. -/
def rootEdge (i : Fin n) : OrderedEdge (n + 1) :=
  ⟨((0 : Fin (n + 1)), i.succ), Fin.succ_pos i⟩

/-- **The canonical orientation is the expected one** — 0 is the
    least index, so canonicalization of (0, i.succ) is literally
    `rootEdge i` (a lemma, not an assumption). -/
theorem canonicalOrderedEdge_zero_succ (i : Fin n) :
    canonicalOrderedEdge (0 : Fin (n + 1)) i.succ
        (Fin.succ_ne_zero i).symm
      = rootEdge i :=
  canonicalOrderedEdge_of_lt (Fin.succ_pos i) _

/-- The root neighbours, as a Finset of Fin n: the root is excluded
    by TYPE, and the future enumeration Fin k ≃ this set is natural. -/
noncomputable def rootNeighbors (ET : Finset (OrderedEdge (n + 1))) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => rootEdge i ∈ ET)

theorem mem_rootNeighbors {ET : Finset (OrderedEdge (n + 1))}
    {i : Fin n} :
    i ∈ rootNeighbors ET ↔ rootEdge i ∈ ET := by
  unfold rootNeighbors
  simp [Finset.mem_filter]

/-- Adjacency of the root to i.succ in the generated graph is
    exactly membership of the root edge. -/
theorem adj_zero_succ_iff {ET : Finset (OrderedEdge (n + 1))}
    {i : Fin n} :
    (graphOfEdges ET).Adj 0 i.succ ↔ rootEdge i ∈ ET := by
  constructor
  · rintro (⟨h, hm⟩ | ⟨h, hm⟩)
    · exact hm
    · exact absurd h (Fin.not_lt_zero _)
  · intro hm
    exact Or.inl ⟨Fin.succ_pos i, hm⟩

/-! ## 2. Child edges and the child forest (root isolated) -/

/-- Edges not incident to the root: since e.1 < e.2, root incidence
    is exactly e.1 = 0. -/
noncomputable def childEdges (ET : Finset (OrderedEdge (n + 1))) :
    Finset (OrderedEdge (n + 1)) :=
  ET.filter (fun e => e.val.1 ≠ 0)

noncomputable def rootEdgesOf (ET : Finset (OrderedEdge (n + 1))) :
    Finset (OrderedEdge (n + 1)) :=
  ET.filter (fun e => e.val.1 = 0)

theorem mem_childEdges {ET : Finset (OrderedEdge (n + 1))}
    {e : OrderedEdge (n + 1)} :
    e ∈ childEdges ET ↔ e ∈ ET ∧ e.val.1 ≠ 0 := by
  unfold childEdges
  simp [Finset.mem_filter]

theorem rootEdgesOf_union_childEdges
    (ET : Finset (OrderedEdge (n + 1))) :
    rootEdgesOf ET ∪ childEdges ET = ET := by
  unfold rootEdgesOf childEdges
  exact Finset.filter_union_filter_neg_eq _ ET

theorem rootEdgesOf_disjoint_childEdges
    (ET : Finset (OrderedEdge (n + 1))) :
    Disjoint (rootEdgesOf ET) (childEdges ET) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  unfold rootEdgesOf at h1
  rw [Finset.mem_filter] at h1
  exact (mem_childEdges.mp h2).2 h1.2

/-- **The root edges are exactly the images of the root
    neighbours.** -/
theorem rootEdgesOf_eq_image (ET : Finset (OrderedEdge (n + 1))) :
    rootEdgesOf ET = (rootNeighbors ET).image rootEdge := by
  ext e
  unfold rootEdgesOf
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hmem, h0⟩
    obtain ⟨⟨a, b⟩, hab⟩ := e
    dsimp only at h0
    subst h0
    rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨j, rfl⟩
    · exact absurd hab (Fin.not_lt_zero _)
    · exact ⟨j, mem_rootNeighbors.mpr (by
        show rootEdge j ∈ ET
        convert hmem using 1), rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨mem_rootNeighbors.mp hi, rfl⟩

/-- Adjacency in the child forest forces both endpoints away from
    the root (the root is ISOLATED there). -/
theorem child_not_adj_zero {ET : Finset (OrderedEdge (n + 1))}
    (x : Fin (n + 1)) :
    ¬ (graphOfEdges (childEdges ET)).Adj 0 x := by
  rintro (⟨h, hm⟩ | ⟨h, hm⟩)
  · exact (mem_childEdges.mp hm).2 rfl
  · exact absurd h (Fin.not_lt_zero _)

theorem child_adj_ne_zero {ET : Finset (OrderedEdge (n + 1))}
    {a b : Fin (n + 1)}
    (h : (graphOfEdges (childEdges ET)).Adj a b) :
    a ≠ 0 := by
  intro ha
  subst ha
  exact child_not_adj_zero b h

/-- Adjacency away from the root descends from ET to the child
    forest (the disjunctive Adj makes this immediate). -/
theorem adj_child_of_adj {ET : Finset (OrderedEdge (n + 1))}
    {a b : Fin (n + 1)} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (graphOfEdges ET).Adj a b) :
    (graphOfEdges (childEdges ET)).Adj a b := by
  rcases h with ⟨hlt, hm⟩ | ⟨hlt, hm⟩
  · exact Or.inl ⟨hlt, mem_childEdges.mpr ⟨hm, ha⟩⟩
  · exact Or.inr ⟨hlt, mem_childEdges.mpr ⟨hm, hb⟩⟩

theorem childGraph_le {ET : Finset (OrderedEdge (n + 1))} :
    graphOfEdges (childEdges ET) ≤ graphOfEdges ET :=
  graphOfEdges_mono (Finset.filter_subset _ ET)

/-- Walks in the child forest between non-root vertices never touch
    the root. -/
theorem zero_not_mem_child_walk_support
    {ET : Finset (OrderedEdge (n + 1))} {a b : Fin (n + 1)}
    (ha : a ≠ 0)
    (w : (graphOfEdges (childEdges ET)).Walk a b) :
    (0 : Fin (n + 1)) ∉ w.support := by
  induction w with
  | nil =>
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
    exact fun h => ha h.symm
  | @cons a x c hadj p ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons]
    push_neg
    refine ⟨fun h => ha h.symm, ih ?_⟩
    intro hx
    subst hx
    exact child_not_adj_zero a hadj.symm

/-! ## 3-4. The component relation and the rooted components -/

/-- Same component of the root-deleted forest (as reachability of
    the successors in the child forest — no induced subtype
    graphs). -/
def sameRootDeletedComponent (ET : Finset (OrderedEdge (n + 1)))
    (i j : Fin n) : Prop :=
  (graphOfEdges (childEdges ET)).Reachable i.succ j.succ

theorem sameRootDeletedComponent_refl
    (ET : Finset (OrderedEdge (n + 1))) (i : Fin n) :
    sameRootDeletedComponent ET i i :=
  SimpleGraph.Reachable.refl _

theorem sameRootDeletedComponent_symm
    {ET : Finset (OrderedEdge (n + 1))} {i j : Fin n}
    (h : sameRootDeletedComponent ET i j) :
    sameRootDeletedComponent ET j i :=
  h.symm

theorem sameRootDeletedComponent_trans
    {ET : Finset (OrderedEdge (n + 1))} {i j k : Fin n}
    (h1 : sameRootDeletedComponent ET i j)
    (h2 : sameRootDeletedComponent ET j k) :
    sameRootDeletedComponent ET i k :=
  h1.trans h2

/-- The component of a (candidate) root neighbour, as a Finset of
    the non-root vertices. Total in r. -/
noncomputable def rootComponent (ET : Finset (OrderedEdge (n + 1)))
    (r : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => sameRootDeletedComponent ET v r)

theorem mem_rootComponent {ET : Finset (OrderedEdge (n + 1))}
    {r v : Fin n} :
    v ∈ rootComponent ET r ↔ sameRootDeletedComponent ET v r := by
  unfold rootComponent
  simp [Finset.mem_filter]

theorem self_mem_rootComponent
    (ET : Finset (OrderedEdge (n + 1))) (r : Fin n) :
    r ∈ rootComponent ET r :=
  mem_rootComponent.mpr (sameRootDeletedComponent_refl ET r)

theorem rootComponent_nonempty
    (ET : Finset (OrderedEdge (n + 1))) (r : Fin n) :
    (rootComponent ET r).Nonempty :=
  ⟨r, self_mem_rootComponent ET r⟩

/-- Intersecting components coincide. -/
theorem rootComponent_eq_of_mem
    {ET : Finset (OrderedEdge (n + 1))} {r s v : Fin n}
    (hv : v ∈ rootComponent ET r) (hv' : v ∈ rootComponent ET s) :
    rootComponent ET r = rootComponent ET s := by
  ext w
  rw [mem_rootComponent, mem_rootComponent]
  have h1 := mem_rootComponent.mp hv
  have h2 := mem_rootComponent.mp hv'
  constructor
  · intro hw
    exact (hw.trans h1.symm).trans h2
  · intro hw
    exact (hw.trans h2.symm).trans h1

theorem rootComponent_disjoint
    {ET : Finset (OrderedEdge (n + 1))} {r s : Fin n}
    (hne : rootComponent ET r ≠ rootComponent ET s) :
    Disjoint (rootComponent ET r) (rootComponent ET s) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  exact hne (rootComponent_eq_of_mem h1 h2)

/-! ## 5. Every non-root vertex belongs to a rooted component -/

/-- ET-walks avoiding the root descend to child-forest
    reachability. -/
theorem child_reachable_of_walk
    {ET : Finset (OrderedEdge (n + 1))} {a b : Fin (n + 1)}
    (w : (graphOfEdges ET).Walk a b)
    (h0 : (0 : Fin (n + 1)) ∉ w.support) :
    (graphOfEdges (childEdges ET)).Reachable a b := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a x c hadj p ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at h0
    push_neg at h0
    obtain ⟨h0a, h0p⟩ := h0
    have hx : x ≠ 0 := by
      intro hx
      subst hx
      exact h0p p.start_mem_support
    refine SimpleGraph.Reachable.trans
      ⟨SimpleGraph.Walk.cons
        (adj_child_of_adj (fun h => h0a h.symm) hx hadj)
        SimpleGraph.Walk.nil⟩ (ih h0p)

/-- **Item 5: the cover.** The unique root path's first edge marks
    the neighbour whose component contains the vertex. -/
theorem exists_rootNeighbor_component
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))))
    (v : Fin n) :
    ∃ r ∈ rootNeighbors ET, v ∈ rootComponent ET r := by
  obtain ⟨-, hTree⟩ := mem_spanningTreeEdgeSets.mp hET
  obtain ⟨w⟩ := hTree.isConnected 0 v.succ
  obtain ⟨w', hw'⟩ := w.toPath
  cases w' with
  | cons hadj rest =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hw'
    obtain ⟨hrest, h0rest⟩ := hw'
    rename_i x
    have hx : x ≠ 0 := fun h => (h ▸ hadj).ne rfl
    obtain ⟨r, rfl⟩ :=
      (Fin.eq_zero_or_eq_succ x).resolve_left hx
    refine ⟨r, mem_rootNeighbors.mpr (adj_zero_succ_iff.mp hadj), ?_⟩
    rw [mem_rootComponent]
    exact (child_reachable_of_walk rest h0rest).symm

/-! ## 6. THE CENTRAL LEMMA: one root neighbour per component -/

/-- Child-forest walks lift to ET-walks with the SAME support list
    (edge-by-edge rebuild — no hom unfolding). -/
theorem exists_walkUp {ET : Finset (OrderedEdge (n + 1))}
    {a b : Fin (n + 1)}
    (w : (graphOfEdges (childEdges ET)).Walk a b) :
    ∃ w' : (graphOfEdges ET).Walk a b, w'.support = w.support := by
  induction w with
  | nil => exact ⟨SimpleGraph.Walk.nil, rfl⟩
  | cons hadj p ih =>
    obtain ⟨p', hp'⟩ := ih
    refine ⟨SimpleGraph.Walk.cons (childGraph_le hadj) p', ?_⟩
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
      hp']

/-- **Two root neighbours in the same component coincide** — an
    internal path plus the two root edges would give two distinct
    IsPath walks 0 → r.succ in the tree, against
    `isTree_iff_existsUnique_path`. -/
theorem rootNeighbor_eq_of_mem_component
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))))
    {r s : Fin n} (hr : r ∈ rootNeighbors ET)
    (hs : s ∈ rootNeighbors ET)
    (hmem : s ∈ rootComponent ET r) :
    s = r := by
  by_contra hne
  obtain ⟨-, hTree⟩ := mem_spanningTreeEdgeSets.mp hET
  have hreach : (graphOfEdges (childEdges ET)).Reachable
      s.succ r.succ := mem_rootComponent.mp hmem
  obtain ⟨wc⟩ := hreach
  obtain ⟨pc, hpc⟩ := wc.toPath
  have hadjr : (graphOfEdges ET).Adj 0 r.succ :=
    adj_zero_succ_iff.mpr (mem_rootNeighbors.mp hr)
  have hadjs : (graphOfEdges ET).Adj 0 s.succ :=
    adj_zero_succ_iff.mpr (mem_rootNeighbors.mp hs)
  -- path 1: the single root edge to r
  set P1 : (graphOfEdges ET).Walk 0 r.succ :=
    SimpleGraph.Walk.cons hadjr SimpleGraph.Walk.nil with hP1
  have hP1path : P1.IsPath := by
    rw [hP1, SimpleGraph.Walk.cons_isPath_iff]
    refine ⟨SimpleGraph.Walk.IsPath.mk' (by simp), ?_⟩
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton]
    exact (Fin.succ_ne_zero r).symm
  -- path 2: root edge to s, then the internal path lifted to ET
  obtain ⟨W, hWsupp⟩ := exists_walkUp pc
  have hWpath : W.IsPath :=
    SimpleGraph.Walk.IsPath.mk' (hWsupp ▸ hpc.support_nodup)
  have h0W : (0 : Fin (n + 1)) ∉ W.support := by
    rw [hWsupp]
    exact zero_not_mem_child_walk_support (Fin.succ_ne_zero s) pc
  set P2 : (graphOfEdges ET).Walk 0 r.succ :=
    SimpleGraph.Walk.cons hadjs W with hP2
  have hP2path : P2.IsPath := by
    rw [hP2, SimpleGraph.Walk.cons_isPath_iff]
    exact ⟨hWpath, h0W⟩
  -- uniqueness in the tree
  obtain ⟨-, huniq⟩ :=
    SimpleGraph.isTree_iff_existsUnique_path.mp hTree
  obtain ⟨q, -, hq⟩ := huniq 0 r.succ
  have h12 : P1 = P2 := (hq P1 hP1path).trans (hq P2 hP2path).symm
  -- but their second vertices differ
  have e1 : P1.getVert 1 = r.succ := rfl
  have e2 : P2.getVert 1 = s.succ := by
    show W.getVert 0 = s.succ
    exact W.getVert_zero
  rw [h12, e2] at e1
  exact hne (Fin.succ_injective n e1)

/-- **Item 6/7 capstone: exactly one marked root neighbour per
    vertex.** -/
theorem existsUnique_rootNeighbor_component
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))))
    (v : Fin n) :
    ∃! r : Fin n, r ∈ rootNeighbors ET ∧ v ∈ rootComponent ET r := by
  obtain ⟨r, hr, hv⟩ := exists_rootNeighbor_component hET v
  refine ⟨r, ⟨hr, hv⟩, ?_⟩
  rintro s ⟨hs, hv'⟩
  have hcomp : rootComponent ET s = rootComponent ET r :=
    rootComponent_eq_of_mem hv' hv
  refine rootNeighbor_eq_of_mem_component hET hr hs ?_
  rw [← hcomp]
  exact self_mem_rootComponent ET s

/-! ## 8 (scoped). Connectivity within each block; the tree-ness of
    the restriction is DEFERRED to 47b-iiB (the F(B) identification
    proceeds by relabeling + the 40b cardinal converse instead). -/

theorem child_reachable_within_component
    {ET : Finset (OrderedEdge (n + 1))} {r a b : Fin n}
    (ha : a ∈ rootComponent ET r) (hb : b ∈ rootComponent ET r) :
    (graphOfEdges (childEdges ET)).Reachable a.succ b.succ :=
  (mem_rootComponent.mp ha).trans (mem_rootComponent.mp hb).symm

/-! ## 9. The edge factorization -/

/-- The internal edges of one component: child edges whose (lower)
    endpoint lies in the block. -/
noncomputable def componentEdges (ET : Finset (OrderedEdge (n + 1)))
    (r : Fin n) : Finset (OrderedEdge (n + 1)) :=
  (childEdges ET).filter
    (fun e => e.val.1 ∈ (rootComponent ET r).image Fin.succ)

theorem componentEdges_subset (ET : Finset (OrderedEdge (n + 1)))
    (r : Fin n) : componentEdges ET r ⊆ childEdges ET :=
  Finset.filter_subset _ _

/-- The endpoints of a child edge are adjacent in the child forest,
    hence in the same component. -/
theorem child_edge_adj {ET : Finset (OrderedEdge (n + 1))}
    {e : OrderedEdge (n + 1)} (he : e ∈ childEdges ET) :
    (graphOfEdges (childEdges ET)).Adj e.val.1 e.val.2 :=
  Or.inl ⟨e.2, by
    obtain ⟨⟨a, b⟩, hab⟩ := e
    exact he⟩

/-- **The child edges split exactly by component.** -/
theorem childEdges_eq_biUnion
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1)))) :
    childEdges ET
      = (rootNeighbors ET).biUnion (fun r => componentEdges ET r) := by
  ext e
  rw [Finset.mem_biUnion]
  constructor
  · intro he
    have h1 := (mem_childEdges.mp he).2
    obtain ⟨a, ha⟩ := (Fin.eq_zero_or_eq_succ e.val.1).resolve_left h1
    obtain ⟨r, hr, hcomp⟩ := exists_rootNeighbor_component hET a
    refine ⟨r, hr, ?_⟩
    unfold componentEdges
    rw [Finset.mem_filter]
    refine ⟨he, ?_⟩
    rw [Finset.mem_image]
    exact ⟨a, hcomp, ha.symm⟩
  · rintro ⟨r, -, he⟩
    exact componentEdges_subset ET r he

/-- Distinct components have disjoint internal edges (the lower
    endpoint determines the block). -/
theorem componentEdges_disjoint
    {ET : Finset (OrderedEdge (n + 1))} {r s : Fin n}
    (hne : rootComponent ET r ≠ rootComponent ET s) :
    Disjoint (componentEdges ET r) (componentEdges ET s) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  unfold componentEdges at h1 h2
  rw [Finset.mem_filter, Finset.mem_image] at h1 h2
  obtain ⟨-, a, ha, hea⟩ := h1
  obtain ⟨-, b, hb, heb⟩ := h2
  have hab : a = b := Fin.succ_injective n (hea.trans heb.symm)
  subst hab
  exact Finset.disjoint_left.mp (rootComponent_disjoint hne) ha hb

/-! ## 10. Reconstruction -/

/-- **decompose-then-reconstruct = identity**: the root edges of the
    neighbours together with the per-component internal edges give
    back ET exactly. -/
theorem reconstruct_eq
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1)))) :
    ((rootNeighbors ET).image rootEdge)
        ∪ (rootNeighbors ET).biUnion (fun r => componentEdges ET r)
      = ET := by
  rw [← rootEdgesOf_eq_image, ← childEdges_eq_biUnion hET]
  exact rootEdgesOf_union_childEdges ET

/-! ## 11. Edge cases -/

/-- n = 0: the tree is the root alone; no neighbours, no
    components. -/
theorem rootNeighbors_fin_zero (ET : Finset (OrderedEdge 1)) :
    rootNeighbors ET = (∅ : Finset (Fin 0)) := by
  unfold rootNeighbors
  rw [Finset.univ_eq_empty, Finset.filter_empty]

/-- n > 0: a spanning tree has at least one root neighbour. -/
theorem rootNeighbors_nonempty
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))))
    (hn : 0 < n) :
    (rootNeighbors ET).Nonempty := by
  obtain ⟨r, hr, -⟩ :=
    exists_rootNeighbor_component hET ⟨0, hn⟩
  exact ⟨r, hr⟩

/-- n = 1: exactly one root neighbour, one unit component, no
    internal edges. -/
theorem rootNeighbors_card_fin_one
    {ET : Finset (OrderedEdge 2)}
    (hET : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin 2))) :
    (rootNeighbors ET).card = 1 := by
  have h1 : (rootNeighbors ET).Nonempty :=
    rootNeighbors_nonempty hET (by omega)
  have h2 : (rootNeighbors ET).card ≤ 1 := by
    have := Finset.card_le_card
      (Finset.subset_univ (rootNeighbors ET))
    simpa using this
  have h3 := Finset.card_pos.mpr h1
  omega

end LatticeGauge
