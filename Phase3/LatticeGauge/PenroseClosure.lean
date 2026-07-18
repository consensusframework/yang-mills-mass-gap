/-
LatticeGauge/PenroseClosure.lean — Phase 3, forty-first stone (a).

THE PENROSE CLOSURE AND THE DIRECT FIBRE INCLUSION (architecture:
Sol/GPT-5.6; execution: Fable). For an ambient graph G and a spanning
tree T on Fin (n+1), the closure R_G(T) adds to T exactly the
available edges of G that are P1 (endpoints in the SAME generation of
T) or P2 (endpoints in CONSECUTIVE generations whose shallow endpoint
has label STRICTLY greater than the canonical parent of the deep
endpoint — the parent's own edge lives in T and is never an "extra").
ORIENTATION DISCIPLINE (architect's warning): OrderedEdge orders by
LABEL, which says nothing about depth; both predicates are defined by
explicit existentials through canonicalOrderedEdge and characterized
once by endpoints (penroseSameLevelEdge_iff / penroseForwardEdge_iff)
— no later proof repeats orientation splits. Definitions are TOTAL
(no connectivity data); decidability is supplied classically (the
predicates live in classical filters), recorded here rather than
claimed constructive. PROVED: T ≤ R_G(T) (needs only T ≤ G) and
R_G(T) ≤ G (no hypothesis); the parent computed in the extracted tree
equals the parent computed in H (candidates in the tree form exactly
the singleton of H's parent, by preserved depths); the depth
trichotomy along an edge; and HEART A — every available edge of a
connected H is a tree edge, a P1 edge, or a P2 edge of T = π(H),
because the shallow endpoint of a consecutive-generation edge is a
parent CANDIDATE, and the canonical parent is the MINIMUM: p = u
gives the tree edge, p < u gives P2, and p > u is impossible. Hence
the fibre inclusion π(H) = T → T ≤ H ≤ R_G(T) (InPenroseInterval).
NOT PROVED HERE (41b): the closure does not shorten distances; the
converse fibre direction; the interval-fibre equality; any partition,
Finsets of subgraphs, cancellation, Penrose identity, tree-graph
bound, counting, series, log Z or convergence. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.UrsellCoefficients
import LatticeGauge.UrsellSymmetry
import LatticeGauge.UrsellBounds
import LatticeGauge.PenroseTree
import LatticeGauge.PenroseTreeB

open scoped Classical

namespace LatticeGauge

variable {n : ℕ}

/-! ## 1-3. The two predicates, with single-point orientation
handling -/

/-- **P1: same-generation edge** (existential presentation — the
    label order of OrderedEdge is never used as depth orientation). -/
def penroseSameLevelEdge (T : SimpleGraph (Fin (n + 1)))
    (e : OrderedEdge (n + 1)) : Prop :=
  ∃ (u v : Fin (n + 1)) (h : u ≠ v),
    e = canonicalOrderedEdge u v h ∧
    penroseDepth T u = penroseDepth T v

/-- **P1 characterized by endpoints** — proves in particular the
    independence from the chosen orientation. -/
theorem penroseSameLevelEdge_iff {T : SimpleGraph (Fin (n + 1))}
    {e : OrderedEdge (n + 1)} :
    penroseSameLevelEdge T e
      ↔ penroseDepth T e.val.1 = penroseDepth T e.val.2 := by
  constructor
  · rintro ⟨u, v, h, rfl, hd⟩
    rcases h.lt_or_lt with h' | h'
    · rw [canonicalOrderedEdge_of_lt h' h]
      exact hd
    · rw [canonicalOrderedEdge_of_gt h' h]
      exact hd.symm
  · intro hd
    exact ⟨e.val.1, e.val.2, ne_of_lt e.2,
      (canonicalOrderedEdge_val e).symm, hd⟩

/-- **P2: consecutive-generation EXTRA edge**: shallow endpoint u,
    deep endpoint v, and the canonical parent p of v satisfies the
    STRICT inequality p < u (the p = u edge is the tree edge itself;
    p > u is impossible by parent minimality). -/
def penroseForwardEdge (T : SimpleGraph (Fin (n + 1)))
    (e : OrderedEdge (n + 1)) : Prop :=
  ∃ (u v p : Fin (n + 1)) (h : u ≠ v),
    e = canonicalOrderedEdge u v h ∧
    penroseDepth T u + 1 = penroseDepth T v ∧
    penroseParent? T v = some p ∧
    p < u

/-- **P2 characterized by endpoints.** -/
theorem penroseForwardEdge_iff {T : SimpleGraph (Fin (n + 1))}
    {e : OrderedEdge (n + 1)} :
    penroseForwardEdge T e ↔
      (penroseDepth T e.val.1 + 1 = penroseDepth T e.val.2 ∧
        ∃ p, penroseParent? T e.val.2 = some p ∧ p < e.val.1) ∨
      (penroseDepth T e.val.2 + 1 = penroseDepth T e.val.1 ∧
        ∃ p, penroseParent? T e.val.1 = some p ∧ p < e.val.2) := by
  constructor
  · rintro ⟨u, v, p, h, rfl, hdep, hpar, hlt⟩
    rcases h.lt_or_lt with h' | h'
    · rw [canonicalOrderedEdge_of_lt h' h]
      exact Or.inl ⟨hdep, p, hpar, hlt⟩
    · rw [canonicalOrderedEdge_of_gt h' h]
      exact Or.inr ⟨hdep, p, hpar, hlt⟩
  · rintro (⟨hdep, p, hpar, hlt⟩ | ⟨hdep, p, hpar, hlt⟩)
    · exact ⟨e.val.1, e.val.2, p, ne_of_lt e.2,
        (canonicalOrderedEdge_val e).symm, hdep, hpar, hlt⟩
    · refine ⟨e.val.2, e.val.1, p, (ne_of_lt e.2).symm, ?_,
        hdep, hpar, hlt⟩
      rw [canonicalOrderedEdge_comm]
      exact (canonicalOrderedEdge_val e).symm

/-! ## 4. The closure -/

/-- **The Penrose closure edges**, relative to the ambient G: tree
    edges plus P1 plus P2, always inside the available edges of G.
    Total definition; classical decidability. -/
noncomputable def penroseClosureEdges (G T : SimpleGraph (Fin (n + 1))) :
    Finset (OrderedEdge (n + 1)) :=
  (availableEdges G).filter
    (fun e => e ∈ availableEdges T ∨
      penroseSameLevelEdge T e ∨ penroseForwardEdge T e)

/-- **The Penrose closure R_G(T).** -/
noncomputable def penroseClosure (G T : SimpleGraph (Fin (n + 1))) :
    SimpleGraph (Fin (n + 1)) :=
  graphOfEdges (penroseClosureEdges G T)

theorem mem_penroseClosureEdges {G T : SimpleGraph (Fin (n + 1))}
    {e : OrderedEdge (n + 1)} :
    e ∈ penroseClosureEdges G T
      ↔ e ∈ availableEdges G ∧
        (e ∈ availableEdges T ∨
          penroseSameLevelEdge T e ∨ penroseForwardEdge T e) := by
  unfold penroseClosureEdges
  simp [Finset.mem_filter]

/-! ## 5. The sandwich T ≤ R_G(T) ≤ G -/

/-- **Upper half of the sandwich — no hypotheses.** -/
theorem penroseClosure_le (G T : SimpleGraph (Fin (n + 1))) :
    penroseClosure G T ≤ G := by
  have h := graphOfEdges_mono
    (Finset.filter_subset _ (availableEdges G))
  rwa [graphOfEdges_availableEdges] at h

/-- **Lower half of the sandwich** — needs only T ≤ G (IsTree is not
    required for the inclusion itself). -/
theorem le_penroseClosure {G T : SimpleGraph (Fin (n + 1))}
    (hTG : T ≤ G) : T ≤ penroseClosure G T := by
  intro i j hij
  have hne := hij.ne
  unfold penroseClosure
  rw [graphOfEdges_adj_iff_canonical hne]
  rw [mem_penroseClosureEdges]
  exact ⟨mem_availableEdges.mpr
      ((adj_canonicalOrderedEdge G hne).mpr (hTG hij)),
    Or.inl (mem_availableEdges.mpr
      ((adj_canonicalOrderedEdge T hne).mpr hij))⟩

/-- **CAPSTONE (sandwich).** -/
theorem penroseClosure_sandwich {G T : SimpleGraph (Fin (n + 1))}
    (hTG : T ≤ G) :
    T ≤ penroseClosure G T ∧ penroseClosure G T ≤ G :=
  ⟨le_penroseClosure hTG, penroseClosure_le G T⟩

/-! ## 6. The parent in the extracted tree -/

theorem penroseTree_adj_parent {H : SimpleGraph (Fin (n + 1))}
    {a b : Fin (n + 1)} (h : (penroseTree H).Adj a b) :
    penroseParent? H b = some a ∨ penroseParent? H a = some b := by
  rcases h with ⟨_, hm⟩ | ⟨_, hm⟩
  · exact mem_penroseTreeEdges.mp hm
  · exact Or.symm (mem_penroseTreeEdges.mp hm)

/-- **Interface lemma for heart A: the canonical parent computed in
    the extracted tree equals the one computed in H** — the tree's
    candidate set at v is exactly the singleton of H's parent
    (preserved depths force the orientation). -/
theorem penroseParent?_penroseTree {H : SimpleGraph (Fin (n + 1))}
    (hH : H.Connected) {v : Fin (n + 1)} (hv : v ≠ 0) :
    penroseParent? (penroseTree H) v = penroseParent? H v := by
  obtain ⟨p, hp⟩ := penroseParent?_eq_some hH hv
  have hdT : ∀ w, penroseDepth (penroseTree H) w = penroseDepth H w :=
    fun w => penroseTree_dist hH w
  have hcand : penroseParentCandidates (penroseTree H) v = {p} := by
    ext u
    rw [mem_penroseParentCandidates, Finset.mem_singleton]
    constructor
    · rintro ⟨hadj, hd⟩
      rcases penroseTree_adj_parent hadj with h | h
      · rw [hp] at h
        exact (Option.some.inj h).symm
      · have hdv := penroseParent?_depth h
        rw [hdT, hdT] at hd
        omega
    · intro hu
      rw [hu]
      refine ⟨?_, ?_⟩
      · have hne : p ≠ v := penroseParent?_ne hp
        unfold penroseTree
        rw [graphOfEdges_adj_iff_canonical hne]
        exact canonical_parent_mem_penroseTreeEdges hp hne
      · rw [hdT, hdT]
        exact penroseParent?_depth hp
  rw [hp]
  unfold penroseParent?
  rw [if_neg hv]
  have hne : (penroseParentCandidates (penroseTree H) v).Nonempty := by
    rw [hcand]
    exact ⟨p, Finset.mem_singleton_self p⟩
  rw [dif_pos hne]
  have hmin : (penroseParentCandidates (penroseTree H) v).min' hne
      = p := by
    apply le_antisymm
    · exact Finset.min'_le _ _
        (by rw [hcand]; exact Finset.mem_singleton_self p)
    · apply Finset.le_min'
      intro y hy
      rw [hcand, Finset.mem_singleton] at hy
      rw [hy]
      exact le_refl p
  rw [hmin]

/-! ## 7. Depth trichotomy along an edge -/

theorem penroseDepth_adj_cases {H : SimpleGraph (Fin (n + 1))}
    (hH : H.Connected) {u v : Fin (n + 1)} (hadj : H.Adj u v) :
    penroseDepth H u = penroseDepth H v ∨
    penroseDepth H u + 1 = penroseDepth H v ∨
    penroseDepth H v + 1 = penroseDepth H u := by
  have h1 : penroseDepth H v ≤ penroseDepth H u + 1 := by
    obtain ⟨r, hr⟩ :=
      (hH.preconnected 0 u).exists_walk_length_eq_dist
    have h := SimpleGraph.dist_le (r.concat hadj)
    rwa [SimpleGraph.Walk.length_concat, hr] at h
  have h2 : penroseDepth H u ≤ penroseDepth H v + 1 := by
    obtain ⟨r, hr⟩ :=
      (hH.preconnected 0 v).exists_walk_length_eq_dist
    have h := SimpleGraph.dist_le (r.concat hadj.symm)
    rwa [SimpleGraph.Walk.length_concat, hr] at h
  omega

/-! ## 8. HEART A: classification of every fibre edge -/

/-- **HEART A**: every available edge of a connected H is a tree edge,
    a P1 edge or a P2 edge of T = penroseTree H. The shallow endpoint
    of a consecutive-generation edge is a parent CANDIDATE of the deep
    one; the canonical parent p is the least candidate, so p ≤ u:
    p = u yields the tree edge, p < u yields P2 — p > u never
    happens. -/
theorem edge_classification {H : SimpleGraph (Fin (n + 1))}
    (hH : H.Connected) {e : OrderedEdge (n + 1)}
    (he : e ∈ availableEdges H) :
    e ∈ availableEdges (penroseTree H)
      ∨ penroseSameLevelEdge (penroseTree H) e
      ∨ penroseForwardEdge (penroseTree H) e := by
  have hadj : H.Adj e.val.1 e.val.2 := mem_availableEdges.mp he
  have hdT : ∀ w, penroseDepth (penroseTree H) w = penroseDepth H w :=
    fun w => penroseTree_dist hH w
  rcases penroseDepth_adj_cases hH hadj with hd | hd | hd
  · right; left
    rw [penroseSameLevelEdge_iff, hdT, hdT]
    exact hd
  · have hv0 : e.val.2 ≠ 0 := by
      intro h0
      have hz := penroseDepth_zero H
      rw [h0] at hd
      omega
    obtain ⟨p, hp⟩ := penroseParent?_eq_some hH hv0
    have hcand : e.val.1 ∈ penroseParentCandidates H e.val.2 :=
      mem_penroseParentCandidates.mpr ⟨hadj, hd⟩
    have hple : p ≤ e.val.1 := (penroseParent?_spec hp).2.2 _ hcand
    rcases eq_or_lt_of_le hple with heq | hlt
    · left
      unfold penroseTree
      rw [availableEdges_graphOfEdges, mem_penroseTreeEdges]
      left
      rw [heq] at hp
      exact hp
    · right; right
      rw [penroseForwardEdge_iff]
      left
      exact ⟨by rw [hdT, hdT]; exact hd, p,
        by rw [penroseParent?_penroseTree hH hv0]; exact hp, hlt⟩
  · have hv0 : e.val.1 ≠ 0 := by
      intro h0
      have hz := penroseDepth_zero H
      rw [h0] at hd
      omega
    obtain ⟨p, hp⟩ := penroseParent?_eq_some hH hv0
    have hcand : e.val.2 ∈ penroseParentCandidates H e.val.1 :=
      mem_penroseParentCandidates.mpr ⟨hadj.symm, hd⟩
    have hple : p ≤ e.val.2 := (penroseParent?_spec hp).2.2 _ hcand
    rcases eq_or_lt_of_le hple with heq | hlt
    · left
      unfold penroseTree
      rw [availableEdges_graphOfEdges, mem_penroseTreeEdges]
      right
      rw [heq] at hp
      exact hp
    · right; right
      rw [penroseForwardEdge_iff]
      right
      exact ⟨by rw [hdT, hdT]; exact hd, p,
        by rw [penroseParent?_penroseTree hH hv0]; exact hp, hlt⟩

/-! ## 9-10. The direct fibre inclusion -/

/-- **CAPSTONE (heart A packaged): every connected H ≤ G lies below
    the closure of its own canonical tree.** -/
theorem penroseTree_fiber_le_closure
    {G H : SimpleGraph (Fin (n + 1))}
    (hH : H.Connected) (hHG : H ≤ G) :
    H ≤ penroseClosure G (penroseTree H) := by
  intro i j hij
  have hne := hij.ne
  unfold penroseClosure
  rw [graphOfEdges_adj_iff_canonical hne, mem_penroseClosureEdges]
  refine ⟨mem_availableEdges.mpr
    ((adj_canonicalOrderedEdge G hne).mpr (hHG hij)), ?_⟩
  exact edge_classification hH
    (mem_availableEdges.mpr ((adj_canonicalOrderedEdge H hne).mpr hij))

/-- **The interval predicate** (no Finset of subgraphs yet; the
    global partition is stone 41b/42 material). -/
def InPenroseInterval (G T H : SimpleGraph (Fin (n + 1))) : Prop :=
  T ≤ H ∧ H ≤ penroseClosure G T

/-- **FINAL CAPSTONE (41a): the direct fibre inclusion** —
    π(H) = T implies H lies in the interval [T, R_G(T)]. The converse
    is deliberately NOT proved here (41b). -/
theorem inPenroseInterval_of_penroseTree_eq
    {G H T : SimpleGraph (Fin (n + 1))}
    (hH : H.Connected) (hHG : H ≤ G)
    (hTree : penroseTree H = T) :
    InPenroseInterval G T H := by
  subst hTree
  exact ⟨penroseTree_le H, penroseTree_fiber_le_closure hH hHG⟩

end LatticeGauge
