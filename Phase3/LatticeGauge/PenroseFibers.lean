/-
LatticeGauge/PenroseFibers.lean — Phase 3, forty-first stone (b).

DEPTH PRESERVATION AND THE EXACT FIBRE CHARACTERIZATION (architecture:
Sol/GPT-5.6; execution: Fable). HEART B and the converse fibre
direction: P1 and P2 edges create no shortcuts towards the root
(1-Lipschitz interface lemma consuming the 41a characterizations —
orientation handled once), so by ONE new Walk induction (the general
form depth_T b ≤ depth_T a + length, later specialized to the root)
every graph in the interval [T, R_G(T)] has EXACTLY the BFS levels of
T. THE KEY SUBTLETY (architect): the closure MAY add parent
candidates — but only with labels STRICTLY greater than the original
parent (tree branch forces equality via the tree's singleton
candidate set, P1 is impossible at consecutive depths, P2 gives
p < u by definition) — so only the MINIMUM is preserved, never the
full candidate sets; no false set equality is claimed. Hence the
extracted parents coincide pointwise, the extracted edge sets
coincide, and π(H) = T: THE FIBRES OF THE CANONICAL EXTRACTION ARE
EXACTLY THE INTERVALS [T, R_G(T)] on connected subgraphs of G
(equivalence capstone), with T the minimum and R_G(T) the maximum of
its own fibre. Connectivity of H is DERIVED (hT.isConnected.mono) in
the converse direction, never assumed; the explicit H.Connected
appears only in the equivalence, declaring the domain. Unused
hypotheses were trimmed from intermediate signatures (a
strengthening, recorded here). NOT HERE: no fibre sums, no global
Finset of spanning trees, no reindexing of connectedSpanningEdgeSets,
no (1−1)^m application, no Penrose identity, no tree-graph bound, no
counting, no series, no log Z, no convergence. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.UrsellCoefficients
import LatticeGauge.UrsellSymmetry
import LatticeGauge.UrsellBounds
import LatticeGauge.PenroseTree
import LatticeGauge.PenroseTreeB
import LatticeGauge.PenroseClosure

open scoped Classical

namespace LatticeGauge

variable {n : ℕ}

/-! ## 1. Closure edges are 1-Lipschitz in depth (single interface) -/

/-- **Interface lemma**: along any closure edge, the T-depths are
    equal or consecutive — tree edges by the metric trichotomy, P1 by
    definition, P2 by definition. All orientation handling lives
    here. -/
theorem penroseClosure_adj_depth {G T : SimpleGraph (Fin (n + 1))}
    (hT : T.IsTree) {a b : Fin (n + 1)}
    (hadj : (penroseClosure G T).Adj a b) :
    penroseDepth T a = penroseDepth T b ∨
    penroseDepth T a + 1 = penroseDepth T b ∨
    penroseDepth T b + 1 = penroseDepth T a := by
  have hne := hadj.ne
  have hmem : canonicalOrderedEdge a b hne ∈ penroseClosureEdges G T := by
    unfold penroseClosure at hadj
    rwa [graphOfEdges_adj_iff_canonical hne] at hadj
  rw [mem_penroseClosureEdges] at hmem
  rcases hmem.2 with hTe | hP1 | hP2
  · have hTadj : T.Adj a b :=
      (adj_canonicalOrderedEdge T hne).mp (mem_availableEdges.mp hTe)
    exact penroseDepth_adj_cases hT.isConnected hTadj
  · rw [penroseSameLevelEdge_iff] at hP1
    left
    rcases hne.lt_or_lt with h' | h'
    · rw [canonicalOrderedEdge_of_lt h' hne] at hP1
      exact hP1
    · rw [canonicalOrderedEdge_of_gt h' hne] at hP1
      exact hP1.symm
  · rw [penroseForwardEdge_iff] at hP2
    rcases hne.lt_or_lt with h' | h'
    · rw [canonicalOrderedEdge_of_lt h' hne] at hP2
      rcases hP2 with ⟨hd, -⟩ | ⟨hd, -⟩
      · right; left; exact hd
      · right; right; exact hd
    · rw [canonicalOrderedEdge_of_gt h' hne] at hP2
      rcases hP2 with ⟨hd, -⟩ | ⟨hd, -⟩
      · right; right; exact hd
      · right; left; exact hd

/-! ## 2-3. The single new Walk induction, and the root bound -/

/-- **The one new Walk induction of this stone (general form)**: along
    any walk of H ≤ R_G(T), the T-depth grows by at most the length. -/
theorem walk_depth_le_start_add_length
    {G T H : SimpleGraph (Fin (n + 1))} (hT : T.IsTree)
    (hHR : H ≤ penroseClosure G T) :
    ∀ {a b : Fin (n + 1)} (w : H.Walk a b),
      penroseDepth T b ≤ penroseDepth T a + w.length := by
  intro a b w
  induction w with
  | nil => simp
  | @cons x y z hadj q ih =>
    have hstep := penroseClosure_adj_depth hT (hHR hadj)
    rw [SimpleGraph.Walk.length_cons]
    omega

/-- **Root lower bound via a chosen geodesic** (the authorized
    route): every distance in H dominates the T-depth. -/
theorem penroseDepth_le_of_le_closure
    {G T H : SimpleGraph (Fin (n + 1))} (hT : T.IsTree)
    (hHR : H ≤ penroseClosure G T) (hH : H.Connected)
    (v : Fin (n + 1)) :
    penroseDepth T v ≤ penroseDepth H v := by
  obtain ⟨w, hw⟩ := (hH.preconnected 0 v).exists_walk_length_eq_dist
  have h := walk_depth_le_start_add_length hT hHR w
  rw [penroseDepth_zero] at h
  have h2 : penroseDepth H v = w.length := by
    unfold penroseDepth
    exact hw.symm
  omega

/-! ## 4. Upper bound from T ≤ H -/

theorem penroseDepth_le_of_le {T H : SimpleGraph (Fin (n + 1))}
    (hTconn : T.Connected) (hTH : T ≤ H) (v : Fin (n + 1)) :
    penroseDepth H v ≤ penroseDepth T v := by
  obtain ⟨w, hw⟩ := (hTconn.preconnected 0 v).exists_walk_length_eq_dist
  have h := SimpleGraph.dist_le
    (w.map (SimpleGraph.Hom.mapSpanningSubgraphs hTH))
  rw [SimpleGraph.Walk.length_map, hw] at h
  exact h

/-! ## 5. HEART B -/

/-- **HEART B: every graph in the interval has exactly the BFS levels
    of T** — closure edges never shorten root distances, and T inside
    H never lets them grow. Connectivity of H is DERIVED. -/
theorem penroseDepth_eq_of_mem_interval
    {G T H : SimpleGraph (Fin (n + 1))} (hT : T.IsTree)
    (hTH : T ≤ H) (hHR : H ≤ penroseClosure G T)
    (v : Fin (n + 1)) :
    penroseDepth H v = penroseDepth T v := by
  have hH : H.Connected := hT.isConnected.mono hTH
  exact le_antisymm (penroseDepth_le_of_le hT.isConnected hTH v)
    (penroseDepth_le_of_le_closure hT hHR hH v)

/-! ## 6-8. Preservation of the minimal parent -/

/-- In a tree, ANY parent candidate is THE canonical parent (via the
    retraction T = π(T) and the extracted-adjacency dichotomy). -/
theorem penroseParent?_eq_of_candidate_isTree
    {T : SimpleGraph (Fin (n + 1))} (hT : T.IsTree)
    {v u : Fin (n + 1)}
    (hu : u ∈ penroseParentCandidates T v) :
    penroseParent? T v = some u := by
  obtain ⟨hadj, hd⟩ := mem_penroseParentCandidates.mp hu
  have hadjπ : (penroseTree T).Adj u v := by
    rw [penroseTree_eq_self_of_isTree hT]
    exact hadj
  rcases penroseTree_adj_parent hadjπ with h | h
  · exact h
  · have := penroseParent?_depth h
    omega

/-- **The minimal parent is preserved on the interval.** The closure
    MAY add parent candidates, but only with labels strictly greater
    than the original parent (tree branch: candidate = parent; P1:
    impossible at consecutive depths; P2: p < u by definition) — so
    the MINIMUM never moves. No equality of full candidate sets is
    claimed. -/
theorem penroseParent?_eq_of_mem_interval
    {G T H : SimpleGraph (Fin (n + 1))} (hT : T.IsTree)
    (hTH : T ≤ H) (hHR : H ≤ penroseClosure G T)
    {v : Fin (n + 1)} (hv : v ≠ 0) :
    penroseParent? H v = penroseParent? T v := by
  have hdep : ∀ w, penroseDepth H w = penroseDepth T w :=
    fun w => penroseDepth_eq_of_mem_interval hT hTH hHR w
  obtain ⟨p, hp⟩ := penroseParent?_eq_some hT.isConnected hv
  have hpH : p ∈ penroseParentCandidates H v := by
    obtain ⟨hadjT, hdT⟩ :=
      mem_penroseParentCandidates.mp (penroseParent?_spec hp).2.1
    refine mem_penroseParentCandidates.mpr ⟨hTH hadjT, ?_⟩
    rw [hdep, hdep]
    exact hdT
  have hmin : ∀ u ∈ penroseParentCandidates H v, p ≤ u := by
    intro u hu
    obtain ⟨hadjH, hdH⟩ := mem_penroseParentCandidates.mp hu
    have hadjC := hHR hadjH
    have hne := hadjH.ne
    have hmem : canonicalOrderedEdge u v hne
        ∈ penroseClosureEdges G T := by
      unfold penroseClosure at hadjC
      rwa [graphOfEdges_adj_iff_canonical hne] at hadjC
    rw [mem_penroseClosureEdges] at hmem
    rcases hmem.2 with hTe | hP1 | hP2
    · have hadjT : T.Adj u v :=
        (adj_canonicalOrderedEdge T hne).mp
          (mem_availableEdges.mp hTe)
      have huT : u ∈ penroseParentCandidates T v := by
        refine mem_penroseParentCandidates.mpr ⟨hadjT, ?_⟩
        rw [← hdep, ← hdep]
        exact hdH
      have heq := penroseParent?_eq_of_candidate_isTree hT huT
      rw [hp] at heq
      exact le_of_eq (Option.some.inj heq)
    · rw [penroseSameLevelEdge_iff] at hP1
      have hd' : penroseDepth T u = penroseDepth T v := by
        rcases hne.lt_or_lt with h' | h'
        · rw [canonicalOrderedEdge_of_lt h' hne] at hP1
          exact hP1
        · rw [canonicalOrderedEdge_of_gt h' hne] at hP1
          exact hP1.symm
      rw [hdep, hdep] at hdH
      omega
    · rw [penroseForwardEdge_iff] at hP2
      rw [hdep, hdep] at hdH
      rcases hne.lt_or_lt with h' | h'
      · rw [canonicalOrderedEdge_of_lt h' hne] at hP2
        rcases hP2 with ⟨-, q, hq, hlt⟩ | ⟨hd2, -⟩
        · rw [hp] at hq
          have hpq : p = q := Option.some.inj hq
          rw [hpq]
          exact le_of_lt hlt
        · dsimp only at hd2
          omega
      · rw [canonicalOrderedEdge_of_gt h' hne] at hP2
        rcases hP2 with ⟨hd2, -⟩ | ⟨-, q, hq, hlt⟩
        · dsimp only at hd2
          omega
        · rw [hp] at hq
          have hpq : p = q := Option.some.inj hq
          rw [hpq]
          exact le_of_lt hlt
  rw [hp]
  unfold penroseParent?
  rw [if_neg hv, dif_pos ⟨p, hpH⟩]
  congr 1
  apply le_antisymm
  · exact Finset.min'_le _ _ hpH
  · exact Finset.le_min' _ _ _ hmin

/-! ## 9-10. Equal extracted edges and the converse direction -/

theorem penroseTreeEdges_eq_of_mem_interval
    {G T H : SimpleGraph (Fin (n + 1))} (hT : T.IsTree)
    (hTH : T ≤ H) (hHR : H ≤ penroseClosure G T) :
    penroseTreeEdges H = penroseTreeEdges T := by
  have hpar : ∀ v, penroseParent? H v = penroseParent? T v := by
    intro v
    by_cases hv : v = 0
    · subst hv
      rw [penroseParent?_root, penroseParent?_root]
    · exact penroseParent?_eq_of_mem_interval hT hTH hHR hv
  ext e
  rw [mem_penroseTreeEdges, mem_penroseTreeEdges, hpar, hpar]

/-- **CAPSTONE (converse fibre direction)**: any graph in the interval
    extracts exactly T. -/
theorem penroseTree_eq_of_mem_interval
    {G T H : SimpleGraph (Fin (n + 1))} (hT : T.IsTree)
    (hTH : T ≤ H) (hHR : H ≤ penroseClosure G T) :
    penroseTree H = T := by
  unfold penroseTree
  rw [penroseTreeEdges_eq_of_mem_interval hT hTH hHR,
    penroseTreeEdges_eq_of_isTree hT, graphOfEdges_availableEdges]

/-! ## 11. THE EQUIVALENCE: fibres are exactly the intervals -/

/-- **FINAL CAPSTONE (pedra 41): on connected subgraphs of the
    ambient G, the fibres of the canonical extraction are EXACTLY the
    Penrose intervals.** The connectivity hypothesis declares the
    domain; the converse direction does not use it essentially. -/
theorem penroseTree_eq_iff_inPenroseInterval
    {G T H : SimpleGraph (Fin (n + 1))} (hT : T.IsTree)
    (hH : H.Connected) (hHG : H ≤ G) :
    penroseTree H = T ↔ InPenroseInterval G T H := by
  constructor
  · exact inPenroseInterval_of_penroseTree_eq hH hHG
  · rintro ⟨hTH, hHR⟩
    exact penroseTree_eq_of_mem_interval hT hTH hHR

/-! ## 12-13. The closure is the maximum of its fibre; sanity -/

/-- **The closure extracts T as well** — T is the minimum and R_G(T)
    the maximum of the same fibre. -/
theorem penroseTree_penroseClosure
    {G T : SimpleGraph (Fin (n + 1))} (hT : T.IsTree) (hTG : T ≤ G) :
    penroseTree (penroseClosure G T) = T :=
  penroseTree_eq_of_mem_interval hT (le_penroseClosure hTG)
    (le_refl _)

theorem inPenroseInterval_self
    {G T : SimpleGraph (Fin (n + 1))} (hTG : T ≤ G) :
    InPenroseInterval G T T :=
  ⟨le_refl T, le_penroseClosure hTG⟩

theorem inPenroseInterval_closure
    {G T : SimpleGraph (Fin (n + 1))} (hTG : T ≤ G) :
    InPenroseInterval G T (penroseClosure G T) :=
  ⟨le_penroseClosure hTG, le_refl _⟩

theorem connected_of_inPenroseInterval
    {G T H : SimpleGraph (Fin (n + 1))} (hT : T.IsTree)
    (h : InPenroseInterval G T H) : H.Connected :=
  hT.isConnected.mono h.1

end LatticeGauge
