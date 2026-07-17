/-
LatticeGauge/PenroseTree.lean — Phase 3, fortieth stone (part a).

CANONICAL BFS TREE EXTRACTION (architecture: Sol/GPT-5.6; execution:
Fable). Over Fin (n+1) with canonical root 0 (the architect's
adjustment: the root exists by construction — no Nonempty/NeZero
plumbing; the n = 0 Ursell case stays separate). For ANY labelled
graph H the construction is TOTAL and deterministic — no Connected
proof is taken as data, no Classical.choose on a connectivity
witness: levels are distances from the root (Mathlib SimpleGraph.dist,
API verified in the pinned v4.15 source: dist_self, dist_le,
Reachable.exists_walk_length_eq_dist), parent candidates are the
neighbours one generation below, and the canonical parent is the
LEAST-LABELLED candidate (Finset.min'), Option-valued. Connectivity
enters only in the THEOREMS: under H.Connected, every non-root vertex
has a parent (extracted from the penultimate vertex of a geodesic),
the tree edges number exactly n (one per non-root child; the child of
an edge is its deeper endpoint), penroseTree H ≤ H holds
unconditionally, penroseTree H is connected, and — formalized, not
just named "BFS" — its root distances EQUAL penroseDepth (the strong
induction produces a walk of EXACT length d, giving ≤; the spanning-
subgraph map gives ≥). RECORDED STOP (executor, per the architect's
parada protocol): the IsTree capstone and the tree-retraction/
idempotence items are NOT in this file — the pinned v4.15 has NO
converse "connected + card = n ⟹ acyclic" (only IsTree.card_
edgeFinset forward), and the authorized depth-fallback requires
Walk.IsCycle surgery (rotate/three_le_length/edges_reverse/support
permutations) whose API was not yet censused; attempt map and cost
estimate are in PEDRA40_ESTADO.md, awaiting the architect's ruling
(40b) rather than silently inflating or weakening this stone.
NOT HERE: no Penrose closure, no same-generation edges, no P1/P2, no
intervals, no reindexing, no (1−1)^m application, no Penrose
identity, no tree-graph bound, no tree counting, no cluster series,
no log Z, no convergence. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.UrsellCoefficients
import LatticeGauge.UrsellSymmetry
import LatticeGauge.UrsellBounds

open scoped Classical

namespace LatticeGauge

variable {n : ℕ}

/-! ## 2. Depth: distance from the canonical root 0 -/

/-- **Depth**: distance from the root 0 in H. -/
noncomputable def penroseDepth (H : SimpleGraph (Fin (n + 1)))
    (v : Fin (n + 1)) : ℕ :=
  H.dist 0 v

theorem penroseDepth_zero (H : SimpleGraph (Fin (n + 1))) :
    penroseDepth H 0 = 0 := by
  unfold penroseDepth
  exact SimpleGraph.dist_self

/-! ## 3. Parent candidates -/

/-- **Parent candidates of v**: neighbours exactly one generation
    below. -/
noncomputable def penroseParentCandidates
    (H : SimpleGraph (Fin (n + 1))) (v : Fin (n + 1)) :
    Finset (Fin (n + 1)) :=
  Finset.univ.filter
    (fun u => H.Adj u v ∧ penroseDepth H u + 1 = penroseDepth H v)

theorem mem_penroseParentCandidates {H : SimpleGraph (Fin (n + 1))}
    {v u : Fin (n + 1)} :
    u ∈ penroseParentCandidates H v
      ↔ H.Adj u v ∧ penroseDepth H u + 1 = penroseDepth H v := by
  unfold penroseParentCandidates
  simp

/-- **A. Under connectivity, every non-root vertex has a candidate**:
    the penultimate vertex of a geodesic from the root. -/
theorem penroseParentCandidates_nonempty
    {H : SimpleGraph (Fin (n + 1))} (hH : H.Connected)
    {v : Fin (n + 1)} (hv : v ≠ 0) :
    (penroseParentCandidates H v).Nonempty := by
  obtain ⟨p, hp⟩ :=
    (hH.preconnected 0 v).exists_walk_length_eq_dist
  cases hrev : p.reverse with
  | nil => exact absurd rfl hv
  | cons hadj q =>
    rename_i w
    refine ⟨w, mem_penroseParentCandidates.mpr ⟨hadj.symm, ?_⟩⟩
    have hlen : p.length = q.length + 1 := by
      have h := congrArg SimpleGraph.Walk.length hrev
      rwa [SimpleGraph.Walk.length_reverse,
        SimpleGraph.Walk.length_cons] at h
    have h1 : penroseDepth H w ≤ q.length := by
      have h := SimpleGraph.dist_le q.reverse
      rwa [SimpleGraph.Walk.length_reverse] at h
    have h2 : penroseDepth H v ≤ penroseDepth H w + 1 := by
      obtain ⟨r, hr⟩ :=
        (hH.preconnected 0 w).exists_walk_length_eq_dist
      have h := SimpleGraph.dist_le (r.concat hadj.symm)
      rwa [SimpleGraph.Walk.length_concat, hr] at h
    have h3 : penroseDepth H v = p.length := by
      unfold penroseDepth
      exact hp.symm
    omega

/-! ## 4. The canonical parent -/

/-- **The canonical parent**: none at the root; otherwise the LEAST
    candidate, when one exists. Total; Option-valued; the Nonempty
    proof never appears in the API. -/
noncomputable def penroseParent? (H : SimpleGraph (Fin (n + 1)))
    (v : Fin (n + 1)) : Option (Fin (n + 1)) :=
  if v = 0 then none
  else if h : (penroseParentCandidates H v).Nonempty
    then some ((penroseParentCandidates H v).min' h)
    else none

theorem penroseParent?_root (H : SimpleGraph (Fin (n + 1))) :
    penroseParent? H 0 = none := by
  unfold penroseParent?
  rw [if_pos rfl]

/-- Specification of a successful parent lookup. -/
theorem penroseParent?_spec {H : SimpleGraph (Fin (n + 1))}
    {v u : Fin (n + 1)} (h : penroseParent? H v = some u) :
    v ≠ 0 ∧ u ∈ penroseParentCandidates H v ∧
      ∀ w ∈ penroseParentCandidates H v, u ≤ w := by
  unfold penroseParent? at h
  split at h
  · exact absurd h (by simp)
  · rename_i hv
    split at h
    · rename_i hne
      injection h with h
      subst h
      exact ⟨hv, Finset.min'_mem _ _,
        fun w hw => Finset.min'_le _ _ hw⟩
    · exact absurd h (by simp)

theorem penroseParent?_adj {H : SimpleGraph (Fin (n + 1))}
    {v u : Fin (n + 1)} (h : penroseParent? H v = some u) :
    H.Adj u v :=
  (mem_penroseParentCandidates.mp (penroseParent?_spec h).2.1).1

theorem penroseParent?_depth {H : SimpleGraph (Fin (n + 1))}
    {v u : Fin (n + 1)} (h : penroseParent? H v = some u) :
    penroseDepth H u + 1 = penroseDepth H v :=
  (mem_penroseParentCandidates.mp (penroseParent?_spec h).2.1).2

theorem penroseParent?_ne {H : SimpleGraph (Fin (n + 1))}
    {v u : Fin (n + 1)} (h : penroseParent? H v = some u) :
    u ≠ v := by
  intro huv
  have hd := penroseParent?_depth h
  rw [huv] at hd
  omega

/-- **Under connectivity, every non-root vertex has a parent.** -/
theorem penroseParent?_eq_some {H : SimpleGraph (Fin (n + 1))}
    (hH : H.Connected) {v : Fin (n + 1)} (hv : v ≠ 0) :
    ∃ u, penroseParent? H v = some u := by
  unfold penroseParent?
  rw [if_neg hv,
    dif_pos (penroseParentCandidates_nonempty hH hv)]
  exact ⟨_, rfl⟩

/-! ## 5. Tree edges and the extracted tree -/

/-- **The BFS tree edges**: canonical edges whose deeper endpoint has
    the other endpoint as canonical parent. -/
noncomputable def penroseTreeEdges (H : SimpleGraph (Fin (n + 1))) :
    Finset (OrderedEdge (n + 1)) :=
  Finset.univ.filter
    (fun e => penroseParent? H e.val.2 = some e.val.1 ∨
      penroseParent? H e.val.1 = some e.val.2)

theorem mem_penroseTreeEdges {H : SimpleGraph (Fin (n + 1))}
    {e : OrderedEdge (n + 1)} :
    e ∈ penroseTreeEdges H
      ↔ penroseParent? H e.val.2 = some e.val.1 ∨
        penroseParent? H e.val.1 = some e.val.2 := by
  unfold penroseTreeEdges
  simp

/-- **The extracted tree.** -/
noncomputable def penroseTree (H : SimpleGraph (Fin (n + 1))) :
    SimpleGraph (Fin (n + 1)) :=
  graphOfEdges (penroseTreeEdges H)

theorem canonical_parent_mem_penroseTreeEdges
    {H : SimpleGraph (Fin (n + 1))} {v u : Fin (n + 1)}
    (h : penroseParent? H v = some u) (hne : u ≠ v) :
    canonicalOrderedEdge u v hne ∈ penroseTreeEdges H := by
  rw [mem_penroseTreeEdges]
  rcases hne.lt_or_lt with h' | h'
  · rw [canonicalOrderedEdge_of_lt h' hne]
    exact Or.inl h
  · rw [canonicalOrderedEdge_of_gt h' hne]
    exact Or.inr h

/-! ## 6. Subgraph of the original (no hypothesis) -/

theorem penroseTreeEdges_adj {H : SimpleGraph (Fin (n + 1))}
    {e : OrderedEdge (n + 1)} (h : e ∈ penroseTreeEdges H) :
    H.Adj e.val.1 e.val.2 := by
  rcases mem_penroseTreeEdges.mp h with h' | h'
  · exact penroseParent?_adj h'
  · exact (penroseParent?_adj h').symm

/-- **CAPSTONE: the extracted tree is a subgraph of H — with no
    connectivity hypothesis** (every included edge carries adjacency
    through its candidate). -/
theorem penroseTree_le (H : SimpleGraph (Fin (n + 1))) :
    penroseTree H ≤ H := by
  intro i j hij
  rcases hij with ⟨_, hm⟩ | ⟨_, hm⟩
  · exact penroseTreeEdges_adj hm
  · exact (penroseTreeEdges_adj hm).symm

/-! ## 7. Exactly one edge per non-root vertex -/

/-- The child (deeper endpoint) of a tree edge. -/
noncomputable def childOfEdge (H : SimpleGraph (Fin (n + 1)))
    (e : OrderedEdge (n + 1)) : Fin (n + 1) :=
  if penroseParent? H e.val.2 = some e.val.1 then e.val.2
  else e.val.1

/-- On a tree edge, exactly ONE of the two parent equations holds
    (both together would force contradictory depths). -/
theorem penroseTreeEdges_exclusive {H : SimpleGraph (Fin (n + 1))}
    {e : OrderedEdge (n + 1)} (he : e ∈ penroseTreeEdges H) :
    (penroseParent? H e.val.2 = some e.val.1 ∧
      ¬ penroseParent? H e.val.1 = some e.val.2) ∨
    (penroseParent? H e.val.1 = some e.val.2 ∧
      ¬ penroseParent? H e.val.2 = some e.val.1) := by
  rcases mem_penroseTreeEdges.mp he with h | h
  · by_cases h' : penroseParent? H e.val.1 = some e.val.2
    · have d1 := penroseParent?_depth h
      have d2 := penroseParent?_depth h'
      omega
    · exact Or.inl ⟨h, h'⟩
  · by_cases h' : penroseParent? H e.val.2 = some e.val.1
    · have d1 := penroseParent?_depth h
      have d2 := penroseParent?_depth h'
      omega
    · exact Or.inr ⟨h, h'⟩

/-- **CAPSTONE: the tree has exactly n edges — one per non-root
    child.** -/
theorem card_penroseTreeEdges {H : SimpleGraph (Fin (n + 1))}
    (hH : H.Connected) :
    (penroseTreeEdges H).card = n := by
  have hbij : (penroseTreeEdges H).card
      = (Finset.univ.filter
          (fun v : Fin (n + 1) => v ≠ 0)).card := by
    refine Finset.card_bij (fun e _ => childOfEdge H e) ?_ ?_ ?_
    · -- child is non-root
      intro e he
      rcases penroseTreeEdges_exclusive he with ⟨h, _⟩ | ⟨h, h'⟩
      · have hc : childOfEdge H e = e.val.2 := by
          unfold childOfEdge
          rw [if_pos h]
        rw [hc]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (penroseParent?_spec h).1
      · have hc : childOfEdge H e = e.val.1 := by
          unfold childOfEdge
          rw [if_neg h']
        rw [hc]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (penroseParent?_spec h).1
    · -- injectivity
      intro e₁ h₁ e₂ h₂ heq
      rcases penroseTreeEdges_exclusive h₁ with ⟨p1, q1⟩ | ⟨p1, q1⟩ <;>
        rcases penroseTreeEdges_exclusive h₂ with ⟨p2, q2⟩ | ⟨p2, q2⟩
      · have hc1 : childOfEdge H e₁ = e₁.val.2 := by
          unfold childOfEdge; rw [if_pos p1]
        have hc2 : childOfEdge H e₂ = e₂.val.2 := by
          unfold childOfEdge; rw [if_pos p2]
        rw [hc1, hc2] at heq
        rw [heq] at p1
        rw [p2] at p1
        injection p1 with p1
        exact Subtype.ext (Prod.ext p1.symm heq)
      · have hc1 : childOfEdge H e₁ = e₁.val.2 := by
          unfold childOfEdge; rw [if_pos p1]
        have hc2 : childOfEdge H e₂ = e₂.val.1 := by
          unfold childOfEdge; rw [if_neg q2]
        rw [hc1, hc2] at heq
        -- e₁.2 = e₂.1 =: v; parents: p1 : parent? v = some e₁.1;
        -- p2 : parent? v = some e₂.2 → e₁.1 = e₂.2
        rw [heq] at p1
        rw [p2] at p1
        injection p1 with p1
        -- e₁ = (e₁.1, v), e₁.1 < v; e₂ = (v, e₂.2) = (v, e₁.1), v < e₁.1
        have hlt1 := e₁.2
        have hlt2 := e₂.2
        rw [heq] at hlt1
        rw [← p1] at hlt2
        exact absurd hlt1 (lt_asymm hlt2)
      · have hc1 : childOfEdge H e₁ = e₁.val.1 := by
          unfold childOfEdge; rw [if_neg q1]
        have hc2 : childOfEdge H e₂ = e₂.val.2 := by
          unfold childOfEdge; rw [if_pos p2]
        rw [hc1, hc2] at heq
        rw [heq] at p1
        rw [p2] at p1
        injection p1 with p1
        have hlt1 := e₁.2
        have hlt2 := e₂.2
        rw [heq] at hlt1
        rw [← p1] at hlt2
        exact absurd hlt2 (lt_asymm hlt1)
      · have hc1 : childOfEdge H e₁ = e₁.val.1 := by
          unfold childOfEdge; rw [if_neg q1]
        have hc2 : childOfEdge H e₂ = e₂.val.1 := by
          unfold childOfEdge; rw [if_neg q2]
        rw [hc1, hc2] at heq
        rw [heq] at p1
        rw [p2] at p1
        injection p1 with p1
        exact Subtype.ext (Prod.ext heq p1.symm)
    · -- surjectivity
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      obtain ⟨u, hpar⟩ := penroseParent?_eq_some hH hv
      have hne : u ≠ v := penroseParent?_ne hpar
      refine ⟨canonicalOrderedEdge u v hne,
        canonical_parent_mem_penroseTreeEdges hpar hne, ?_⟩
      rcases hne.lt_or_lt with h' | h'
      · rw [canonicalOrderedEdge_of_lt h' hne]
        unfold childOfEdge
        rw [if_pos hpar]
      · rw [canonicalOrderedEdge_of_gt h' hne]
        unfold childOfEdge
        rw [if_neg ?_]
        · rfl
        · intro hbad
          have d1 := penroseParent?_depth hpar
          have d2 := penroseParent?_depth hbad
          omega
  rw [hbij, Finset.filter_ne', Finset.card_erase_of_mem
    (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fin]

/-! ## 8 + 10. Connectivity and exact BFS distances -/

/-- **Strong induction on depth**: under connectivity, the tree
    contains a walk from the root to v of length EXACTLY
    penroseDepth H v (the parent chain). -/
theorem exists_penroseTree_walk {H : SimpleGraph (Fin (n + 1))}
    (hH : H.Connected) :
    ∀ (d : ℕ) (v : Fin (n + 1)), penroseDepth H v = d →
      ∃ p : (penroseTree H).Walk 0 v, p.length = d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro v hdv
    by_cases hv : v = 0
    · subst hv
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      have h0 := penroseDepth_zero H
      simp only [SimpleGraph.Walk.length_nil]
      omega
    · obtain ⟨u, hpar⟩ := penroseParent?_eq_some hH hv
      have hdep := penroseParent?_depth hpar
      have hne : u ≠ v := penroseParent?_ne hpar
      obtain ⟨q, hq⟩ := ih (penroseDepth H u) (by omega) u rfl
      have hadjT : (penroseTree H).Adj u v := by
        unfold penroseTree
        rw [graphOfEdges_adj_iff_canonical hne]
        exact canonical_parent_mem_penroseTreeEdges hpar hne
      refine ⟨q.concat hadjT, ?_⟩
      rw [SimpleGraph.Walk.length_concat, hq]
      omega

/-- **CAPSTONE: the extracted tree is connected.** -/
theorem penroseTree_connected {H : SimpleGraph (Fin (n + 1))}
    (hH : H.Connected) : (penroseTree H).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun a b => ?_, ⟨0⟩⟩
  obtain ⟨pa, -⟩ := exists_penroseTree_walk hH _ a rfl
  obtain ⟨pb, -⟩ := exists_penroseTree_walk hH _ b rfl
  exact ⟨pa.reverse.append pb⟩

/-- **CAPSTONE (formalized BFS property): the tree preserves root
    distances** — not just the name. -/
theorem penroseTree_dist {H : SimpleGraph (Fin (n + 1))}
    (hH : H.Connected) (v : Fin (n + 1)) :
    (penroseTree H).dist 0 v = penroseDepth H v := by
  obtain ⟨p, hp⟩ := exists_penroseTree_walk hH _ v rfl
  apply le_antisymm
  · rw [← hp]
    exact SimpleGraph.dist_le p
  · obtain ⟨r, hr⟩ :=
      (⟨p⟩ : (penroseTree H).Reachable 0 v).exists_walk_length_eq_dist
    have hmap := SimpleGraph.dist_le
      (r.map (SimpleGraph.Hom.mapSpanningSubgraphs (penroseTree_le H)))
    rw [SimpleGraph.Walk.length_map, hr] at hmap
    exact hmap

end LatticeGauge
