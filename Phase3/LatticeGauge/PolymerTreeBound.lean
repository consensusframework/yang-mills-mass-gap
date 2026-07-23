/-
LatticeGauge/PolymerTreeBound.lean — Phase 3, forty-third stone.

THE HARD-CORE TREE-GRAPH BOUND FOR POLYMER TUPLES
(architecture: Sol/GPT-5.6, including the strategic ruling that the
tree structure — not the raw tree count — is the interface that
survives; execution: Fable). The stone-42 graphic tree-graph bound is
specialized to the incompatibility graph of a tuple of polymer
candidates, and the spanning-tree count is PRESENTED as a sum over
labelled trees of the COMPLETE graph with a hard-core indicator
product on the edges: each edge of each tree remembers exactly which
two polymer occurrences are incompatible. This is the format the
future sum over polymer activities can consume without losing the
local incompatibility constraints (trees incompatible with the tuple
receive weight zero; the labelled tree universe is independent of γ).
Multiplicities are NOT identified: distinct occurrences of the same
polymer remain distinct vertices (stone 38's permutation invariance
of the LEFT side, ursellCoeff_perm, is on record; invariance of the
right-hand weighted sum would need tree transport again and is NOT
claimed here). The right-hand side contains NO activities; no
polymerWeight, no sums over tuples, no 1/(n+1)!, no cluster series,
no log realZ, no convergence claim, no Cayley/Prüfer, no polymer
counting, no thermodynamic limit. DEFERRED (registered, not
discarded): the parent-function bound #trees ≤ (n+1)^n via root 0,
parent code Fin n → Fin (n+1) and the stone-40 reconstruction — it
erases the local incompatibility structure and, alone, will not be
the main interface toward a Kotecký–Preiss-type criterion. Fin 0 is
covered by the separate stone-42b result. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.PolymerGeometry
import LatticeGauge.UrsellCoefficients
import LatticeGauge.UrsellSymmetry
import LatticeGauge.UrsellBounds
import LatticeGauge.PenroseTree
import LatticeGauge.PenroseTreeB
import LatticeGauge.PenroseClosure
import LatticeGauge.PenroseFibers
import LatticeGauge.EdgeFibers
import LatticeGauge.PenroseIdentity

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} {n : ℕ}

/-! ## 1. The complete reference graph -/

/-- On ordered edges every pair is admissible for `⊤`. -/
theorem availableEdges_top :
    availableEdges (⊤ : SimpleGraph (Fin (n + 1))) = Finset.univ := by
  ext e
  simp only [Finset.mem_univ, iff_true, mem_availableEdges,
    SimpleGraph.top_adj]
  exact ne_of_lt e.2

theorem availableEdges_subset_top {G : SimpleGraph (Fin (n + 1))} :
    availableEdges G ⊆ availableEdges (⊤ : SimpleGraph (Fin (n + 1))) := by
  rw [availableEdges_top]
  exact Finset.subset_univ _

/-- Every spanning tree of G lives in the universe of labelled
    spanning trees of the complete graph. -/
theorem spanningTreeEdgeSets_subset_top {G : SimpleGraph (Fin (n + 1))} :
    spanningTreeEdgeSets G
      ⊆ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))) := by
  intro ET hET
  obtain ⟨hsub, hTree⟩ := mem_spanningTreeEdgeSets.mp hET
  exact mem_spanningTreeEdgeSets.mpr
    ⟨hsub.trans availableEdges_subset_top, hTree⟩

/-! ## 2. The generic subgraph indicator -/

noncomputable def spanningTreeSubgraphIndicator
    (G : SimpleGraph (Fin (n + 1)))
    (ET : Finset (OrderedEdge (n + 1))) : ℕ :=
  if ET ⊆ availableEdges G then 1 else 0

theorem spanningTreeSubgraphIndicator_eq_one_iff
    {G : SimpleGraph (Fin (n + 1))}
    {ET : Finset (OrderedEdge (n + 1))} :
    spanningTreeSubgraphIndicator G ET = 1
      ↔ ET ⊆ availableEdges G := by
  unfold spanningTreeSubgraphIndicator
  by_cases h : ET ⊆ availableEdges G <;> simp [h]

theorem spanningTreeSubgraphIndicator_eq_zero_iff
    {G : SimpleGraph (Fin (n + 1))}
    {ET : Finset (OrderedEdge (n + 1))} :
    spanningTreeSubgraphIndicator G ET = 0
      ↔ ¬ ET ⊆ availableEdges G := by
  unfold spanningTreeSubgraphIndicator
  by_cases h : ET ⊆ availableEdges G <;> simp [h]

theorem spanningTreeSubgraphIndicator_le_one
    (G : SimpleGraph (Fin (n + 1)))
    (ET : Finset (OrderedEdge (n + 1))) :
    spanningTreeSubgraphIndicator G ET ≤ 1 := by
  unfold spanningTreeSubgraphIndicator
  split <;> omega

/-! ## 3. Generic presentation of the tree count -/

theorem spanningTreeEdgeSets_eq_filter (G : SimpleGraph (Fin (n + 1))) :
    spanningTreeEdgeSets G
      = (spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1)))).filter
          (fun ET => ET ⊆ availableEdges G) := by
  ext ET
  rw [Finset.mem_filter, mem_spanningTreeEdgeSets,
    mem_spanningTreeEdgeSets]
  constructor
  · rintro ⟨hsub, hTree⟩
    exact ⟨⟨hsub.trans availableEdges_subset_top, hTree⟩, hsub⟩
  · rintro ⟨⟨-, hTree⟩, hsub⟩
    exact ⟨hsub, hTree⟩

/-- **Generic tree-count presentation**: the spanning trees of G,
    counted over the labelled tree universe of the complete graph via
    the subgraph indicator. NOT via the Penrose identity — this is
    pure counting. -/
theorem spanningTree_count_eq_complete_tree_indicator_sum
    (G : SimpleGraph (Fin (n + 1))) :
    (spanningTreeEdgeSets G).card
      = ∑ ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))),
          spanningTreeSubgraphIndicator G ET := by
  rw [spanningTreeEdgeSets_eq_filter G, Finset.card_filter]
  rfl

/-! ## 4. The hard-core edge indicator -/

/-- **One switch per tree edge**: 1 exactly when the two polymer
    occurrences at the endpoints are incompatible (hard-core).
    `e.1 ≠ e.2` is built into `OrderedEdge`; distinct occurrences of
    the same polymer remain allowed and multiplicities are NOT
    identified. -/
noncomputable def hardCoreEdgeIndicator [NeZero N]
    (γ : Fin (n + 1) → Finset (Site N × Dir × Dir))
    (e : OrderedEdge (n + 1)) : ℕ :=
  if PlaquetteCompatible (γ e.val.1) (γ e.val.2) then 0 else 1

theorem hardCoreEdgeIndicator_eq_ite [NeZero N]
    (γ : Fin (n + 1) → Finset (Site N × Dir × Dir))
    (e : OrderedEdge (n + 1)) :
    hardCoreEdgeIndicator γ e
      = if e ∈ availableEdges (polymerIncompatibilityGraph γ)
        then 1 else 0 := by
  unfold hardCoreEdgeIndicator
  by_cases h : PlaquetteCompatible (γ e.val.1) (γ e.val.2)
  · rw [if_pos h, if_neg]
    intro hmem
    have hadj : e.val.1 ≠ e.val.2 ∧
        ¬ PlaquetteCompatible (γ e.val.1) (γ e.val.2) :=
      mem_availableEdges.mp hmem
    exact hadj.2 h
  · rw [if_neg h, if_pos]
    exact mem_availableEdges.mpr ⟨ne_of_lt e.2, h⟩

theorem hardCoreEdgeIndicator_eq_one_iff [NeZero N]
    {γ : Fin (n + 1) → Finset (Site N × Dir × Dir)}
    {e : OrderedEdge (n + 1)} :
    hardCoreEdgeIndicator γ e = 1
      ↔ e ∈ availableEdges (polymerIncompatibilityGraph γ) := by
  rw [hardCoreEdgeIndicator_eq_ite]
  by_cases h : e ∈ availableEdges (polymerIncompatibilityGraph γ) <;>
    simp [h]

theorem hardCoreEdgeIndicator_eq_zero_iff [NeZero N]
    {γ : Fin (n + 1) → Finset (Site N × Dir × Dir)}
    {e : OrderedEdge (n + 1)} :
    hardCoreEdgeIndicator γ e = 0
      ↔ e ∉ availableEdges (polymerIncompatibilityGraph γ) := by
  rw [hardCoreEdgeIndicator_eq_ite]
  by_cases h : e ∈ availableEdges (polymerIncompatibilityGraph γ) <;>
    simp [h]

/-! ## 5. The hard-core weight of a tree -/

/-- **The hard-core tree weight** (kept in ℕ): the product of the
    edge switches — 1 iff EVERY edge of ET joins incompatible
    occurrences, 0 as soon as one edge joins compatible ones. -/
noncomputable def hardCoreTreeIndicator [NeZero N]
    (γ : Fin (n + 1) → Finset (Site N × Dir × Dir))
    (ET : Finset (OrderedEdge (n + 1))) : ℕ :=
  ∏ e ∈ ET, hardCoreEdgeIndicator γ e

theorem hardCoreTreeIndicator_eq_one [NeZero N]
    {γ : Fin (n + 1) → Finset (Site N × Dir × Dir)}
    {ET : Finset (OrderedEdge (n + 1))}
    (h : ∀ e ∈ ET,
      e ∈ availableEdges (polymerIncompatibilityGraph γ)) :
    hardCoreTreeIndicator γ ET = 1 :=
  Finset.prod_eq_one
    (fun e he => hardCoreEdgeIndicator_eq_one_iff.mpr (h e he))

theorem hardCoreTreeIndicator_eq_zero [NeZero N]
    {γ : Fin (n + 1) → Finset (Site N × Dir × Dir)}
    {ET : Finset (OrderedEdge (n + 1))} {e : OrderedEdge (n + 1)}
    (he : e ∈ ET)
    (h : PlaquetteCompatible (γ e.val.1) (γ e.val.2)) :
    hardCoreTreeIndicator γ ET = 0 :=
  Finset.prod_eq_zero he (by unfold hardCoreEdgeIndicator; rw [if_pos h])

/-- **CAPSTONE (item 5)**: the hard-core tree weight IS the subgraph
    indicator of the incompatibility graph. -/
theorem hardCoreTreeIndicator_eq_subgraphIndicator [NeZero N]
    (γ : Fin (n + 1) → Finset (Site N × Dir × Dir))
    (ET : Finset (OrderedEdge (n + 1))) :
    hardCoreTreeIndicator γ ET
      = spanningTreeSubgraphIndicator
          (polymerIncompatibilityGraph γ) ET := by
  unfold hardCoreTreeIndicator spanningTreeSubgraphIndicator
  calc (∏ e ∈ ET, hardCoreEdgeIndicator γ e)
      = ∏ e ∈ ET,
          if e ∈ availableEdges (polymerIncompatibilityGraph γ)
          then 1 else 0 :=
        Finset.prod_congr rfl
          (fun e _ => hardCoreEdgeIndicator_eq_ite γ e)
    _ = if ∀ e ∈ ET,
          e ∈ availableEdges (polymerIncompatibilityGraph γ)
        then 1 else 0 := by
        by_cases h : ∀ e ∈ ET,
            e ∈ availableEdges (polymerIncompatibilityGraph γ)
        · rw [if_pos h]
          exact Finset.prod_eq_one (fun e he => by rw [if_pos (h e he)])
        · rw [if_neg h]
          push_neg at h
          obtain ⟨e, he, hnot⟩ := h
          exact Finset.prod_eq_zero he (by rw [if_neg hnot])
    _ = if ET ⊆ availableEdges (polymerIncompatibilityGraph γ)
        then 1 else 0 := by
        by_cases h : ET ⊆ availableEdges (polymerIncompatibilityGraph γ)
        · rw [if_pos (fun e he => h he), if_pos h]
        · rw [if_neg (fun hall => h (fun e he => hall e he)),
            if_neg h]

/-! ## 6. Hard-core weighted tree count -/

/-- **The format that survives for the analysis**: the sum runs over
    labelled trees INDEPENDENT of γ; each edge contributes the local
    incompatibility condition; trees incompatible with the tuple get
    weight zero. -/
theorem incompatibility_spanningTree_count [NeZero N]
    (γ : Fin (n + 1) → Finset (Site N × Dir × Dir)) :
    (spanningTreeEdgeSets (polymerIncompatibilityGraph γ)).card
      = ∑ ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))),
          hardCoreTreeIndicator γ ET := by
  rw [spanningTree_count_eq_complete_tree_indicator_sum]
  exact Finset.sum_congr rfl
    (fun ET _ => (hardCoreTreeIndicator_eq_subgraphIndicator γ ET).symm)

/-! ## 7. Gluing graphic → polymers -/

/-- **First capstone**: the tuple Ursell coefficient is controlled by
    the number of spanning trees of its incompatibility graph — a
    short corollary of the stone-42b tree-graph bound, NOT reproved. -/
theorem ursellCoeff_tree_graph_bound [NeZero N]
    (γ : Fin (n + 1) → Finset (Site N × Dir × Dir)) :
    (ursellCoeff γ).natAbs
      ≤ (spanningTreeEdgeSets (polymerIncompatibilityGraph γ)).card := by
  unfold ursellCoeff
  exact tree_graph_bound _

/-! ## 8. THE HARD-CORE CAPSTONE -/

/-- **THE HARD-CORE TREE-GRAPH BOUND**: the Ursell coefficient of a
    polymer tuple is controlled by a sum over labelled trees of the
    complete graph, where the product over each tree records
    incompatibility on ALL of its edges. This formulation preserves
    the structure needed for future iterated sums over polymers; the
    right-hand side contains NO activities yet; no series or
    convergence is asserted. -/
theorem ursellCoeff_hardCoreTree_bound [NeZero N]
    (γ : Fin (n + 1) → Finset (Site N × Dir × Dir)) :
    (ursellCoeff γ).natAbs
      ≤ ∑ ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))),
          hardCoreTreeIndicator γ ET := by
  rw [← incompatibility_spanningTree_count γ]
  exact ursellCoeff_tree_graph_bound γ

/-! ## 9. Real-valued version -/

/-- The same bound with real coercions, for the future absolute
    activity estimates. The `natAbs` form remains the main capstone;
    this is NOT a general ℕ→ℝ migration. -/
theorem ursellCoeff_hardCoreTree_bound_real [NeZero N]
    (γ : Fin (n + 1) → Finset (Site N × Dir × Dir)) :
    |((ursellCoeff γ : ℤ) : ℝ)|
      ≤ ∑ ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))),
          (hardCoreTreeIndicator γ ET : ℝ) := by
  have h := ursellCoeff_hardCoreTree_bound γ
  have hz : |ursellCoeff γ|
      ≤ ((∑ ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))),
            hardCoreTreeIndicator γ ET : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h
  exact_mod_cast hz

/-! ## 11. Sanity cases (disconnected: `ursellCoeff_of_not_connected`
    and `ursellCoeff_of_pairwise_compatible` already exist in stone
    37 — not reproved). -/

/-- **B. All pairs compatible ⟹ every tree weight is zero** (for at
    least two vertices, every spanning tree has an edge). -/
theorem hardCoreTreeIndicator_eq_zero_of_pairwise_compatible [NeZero N]
    (hn : 1 ≤ n) {γ : Fin (n + 1) → Finset (Site N × Dir × Dir)}
    (h : ∀ i j, i ≠ j → PlaquetteCompatible (γ i) (γ j))
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1)))) :
    hardCoreTreeIndicator γ ET = 0 := by
  have hcard : ET.card = n := card_of_mem_spanningTreeEdgeSets hET
  have hpos : 0 < ET.card := by rw [hcard]; omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  exact hardCoreTreeIndicator_eq_zero he (h _ _ (ne_of_lt e.2))

/-- **C. Incompatibility graph a tree ⟹ the bound is saturated at
    1** (stone 42b consumed, not reproved). -/
theorem ursellCoeff_natAbs_of_isTree [NeZero N]
    (γ : Fin (n + 1) → Finset (Site N × Dir × Dir))
    (hG : (polymerIncompatibilityGraph γ).IsTree) :
    (ursellCoeff γ).natAbs = 1 := by
  unfold ursellCoeff
  exact graphUrsellCoeff_natAbs_of_isTree_penrose hG

/-- **D (support)**: on one vertex the labelled tree universe is the
    empty edge set alone. -/
theorem spanningTreeEdgeSets_top_fin_one :
    spanningTreeEdgeSets (⊤ : SimpleGraph (Fin 1))
      = {(∅ : Finset (OrderedEdge 1))} := by
  ext ET
  rw [Finset.mem_singleton]
  constructor
  · intro hET
    exact Finset.card_eq_zero.mp (card_of_mem_spanningTreeEdgeSets hET)
  · intro hEq
    rw [hEq, mem_spanningTreeEdgeSets]
    refine ⟨Finset.empty_subset _, isTree_of_connected_card ?_ ?_⟩
    · rw [SimpleGraph.connected_iff]
      refine ⟨?_, ⟨0⟩⟩
      intro u v
      have hu := u.isLt
      have hv := v.isLt
      have huv : u = v := Fin.ext (by omega)
      rw [huv]
      exact ⟨SimpleGraph.Walk.nil⟩
    · rw [availableEdges_graphOfEdges]
      exact Finset.card_empty

/-- **D. A single occurrence: the empty tree contributes exactly 1**
    (empty product convention), matching `ursellCoeff_single` = 1. -/
theorem hardCoreTree_sum_fin_one [NeZero N]
    (γ : Fin 1 → Finset (Site N × Dir × Dir)) :
    (∑ ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin 1)),
        hardCoreTreeIndicator γ ET) = 1 := by
  rw [spanningTreeEdgeSets_top_fin_one, Finset.sum_singleton]
  exact Finset.prod_empty

/-! ## 12. Fin 0, separate (stone 42b consumed) -/

/-- The rooted hard-core tree representation covers nonempty tuples
    on Fin (n+1); the empty tuple is separate and trivial. -/
theorem ursellCoeff_fin_zero [NeZero N]
    (γ : Fin 0 → Finset (Site N × Dir × Dir)) :
    ursellCoeff γ = 0 := by
  unfold ursellCoeff
  exact graphUrsellCoeff_fin_zero _

end LatticeGauge
