/-
LatticeGauge/KPOrderedDecomposition.lean — stone 47 (b-iiB), GATE II.

ORDERED COMPONENTS DERIVED FROM AN ENUMERATION, AND THE STRUCTURAL
BIDIRECTIONAL CORRESPONDENCE (architecture: Sol/GPT-5.6; execution:
Fable). GATE II ONLY — purely structural: NO polymer assignments, no
hard-core indicators, no activities, no weight factorization, no
F(B), no partition counting, no recurrence; nothing merges to main
before the A-package (Gates I-IV) is complete.

From (ET, e) with e : Fin k ≃ rootNeighbors ET, the ordered data are
DERIVED: ordered neighbour, ordered block, block tail and
componentSize (no truncated subtraction: the MAIN identity is
  Σ_j componentSize j + k = n,
with n − k only as a corollary), ordered internal trees; cover,
disjointness, unique marked neighbour per block. The admissible
ordered decompositions are a structure whose fields are exactly what
survives decomposition AND suffices for reconstruction — the key
design point: admissibility carries the GLOBAL edge count
  Σ_j (itree j).card + k = n
instead of per-block tree-ness, so the reconstructed graph is proved
a spanning tree by the stone-40b LOCAL CARDINAL CONVERSE (connected,
n edges), never needing the deferred per-block acyclicity. The
CAPSTONE `enumeratedTree_equiv_orderedDecomposition` exhibits the
equivalence with BOTH inverses proved (decompose∘reconstruct = id on
admissible data AND reconstruct∘decompose = id on enumerated trees —
not merely the tree remounting). Two confinement inductions do the
work: walks in the union of block-trees never change block (blocks
are disjoint and each edge lives inside one block), and child-forest
walks starting in a component stay inside its componentEdges.
NO axioms.
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

open scoped Classical

namespace LatticeGauge

variable {n k : ℕ}

/-! ## Successor images (the bridge Fin n ↔ non-root Fin (n+1)) -/

theorem mem_succImage {B : Finset (Fin n)} {x : Fin (n + 1)} :
    x ∈ B.image Fin.succ ↔ ∃ b ∈ B, b.succ = x := by
  simp [Finset.mem_image]

theorem succImage_ne_zero {B : Finset (Fin n)} {x : Fin (n + 1)}
    (h : x ∈ B.image Fin.succ) : x ≠ 0 := by
  obtain ⟨b, -, rfl⟩ := mem_succImage.mp h
  exact Fin.succ_ne_zero b

theorem succImage_disjoint {B C : Finset (Fin n)}
    (h : Disjoint B C) :
    Disjoint (B.image Fin.succ) (C.image Fin.succ) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨b, hb, rfl⟩ := mem_succImage.mp hx
  obtain ⟨c, hc, hcb⟩ := mem_succImage.mp hx'
  have : c = b := Fin.succ_injective n hcb
  subst this
  exact Finset.disjoint_left.mp h hb hc

/-! ## Gate II, item 5: ordered neighbours and blocks -/

noncomputable def orderedRootNeighbor
    (ET : Finset (OrderedEdge (n + 1)))
    (e : RootEnumeration ET k) (j : Fin k) : Fin n :=
  (e j).val

noncomputable def orderedRootBlock
    (ET : Finset (OrderedEdge (n + 1)))
    (e : RootEnumeration ET k) (j : Fin k) : Finset (Fin n) :=
  rootComponent ET (orderedRootNeighbor ET e j)

noncomputable def orderedInternalTree
    (ET : Finset (OrderedEdge (n + 1)))
    (e : RootEnumeration ET k) (j : Fin k) :
    Finset (OrderedEdge (n + 1)) :=
  componentEdges ET (orderedRootNeighbor ET e j)

theorem orderedRootNeighbor_mem_block
    (ET : Finset (OrderedEdge (n + 1)))
    (e : RootEnumeration ET k) (j : Fin k) :
    orderedRootNeighbor ET e j ∈ orderedRootBlock ET e j :=
  self_mem_rootComponent ET _

theorem orderedRootBlock_nonempty
    (ET : Finset (OrderedEdge (n + 1)))
    (e : RootEnumeration ET k) (j : Fin k) :
    (orderedRootBlock ET e j).Nonempty :=
  ⟨_, orderedRootNeighbor_mem_block ET e j⟩

theorem orderedRootBlock_cover
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))))
    (e : RootEnumeration ET k) (v : Fin n) :
    ∃ j : Fin k, v ∈ orderedRootBlock ET e j := by
  obtain ⟨r, hr, hv⟩ := exists_rootNeighbor_component hET v
  obtain ⟨j, hj⟩ := e.surjective ⟨r, hr⟩
  refine ⟨j, ?_⟩
  unfold orderedRootBlock orderedRootNeighbor
  rw [hj]
  exact hv

theorem orderedRootBlock_disjoint
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))))
    (e : RootEnumeration ET k) {j₁ j₂ : Fin k} (hne : j₁ ≠ j₂) :
    Disjoint (orderedRootBlock ET e j₁) (orderedRootBlock ET e j₂) := by
  refine rootComponent_disjoint ?_
  intro heq
  have h1 : orderedRootNeighbor ET e j₁ ∈
      rootComponent ET (orderedRootNeighbor ET e j₂) := by
    rw [← heq]
    exact self_mem_rootComponent ET _
  have h2 := rootNeighbor_eq_of_mem_component hET
    (e j₂).2 (e j₁).2 h1
  exact hne (e.injective (Subtype.ext h2))

/-- The unique `rootNeighbors` member of block j is its mark. -/
theorem marked_unique_in_block
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))))
    (e : RootEnumeration ET k) {j : Fin k} {s : Fin n}
    (hs : s ∈ rootNeighbors ET)
    (hmem : s ∈ orderedRootBlock ET e j) :
    s = orderedRootNeighbor ET e j :=
  rootNeighbor_eq_of_mem_component hET (e j).2 hs hmem

/-! ## Gate II, item 6: sizes without truncated subtraction -/

noncomputable def orderedBlockTail
    (ET : Finset (OrderedEdge (n + 1)))
    (e : RootEnumeration ET k) (j : Fin k) : Finset (Fin n) :=
  (orderedRootBlock ET e j).erase (orderedRootNeighbor ET e j)

noncomputable def componentSize
    (ET : Finset (OrderedEdge (n + 1)))
    (e : RootEnumeration ET k) (j : Fin k) : ℕ :=
  (orderedBlockTail ET e j).card

theorem card_orderedRootBlock
    (ET : Finset (OrderedEdge (n + 1)))
    (e : RootEnumeration ET k) (j : Fin k) :
    (orderedRootBlock ET e j).card = componentSize ET e j + 1 := by
  unfold componentSize orderedBlockTail
  have h := Finset.card_erase_of_mem
    (orderedRootNeighbor_mem_block ET e j)
  have hpos := Finset.card_pos.mpr (orderedRootBlock_nonempty ET e j)
  omega

/-- **The MAIN size identity** (no subtraction):
    Σ componentSize + k = n. -/
theorem sum_componentSize_add_k
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))))
    (e : RootEnumeration ET k) :
    (∑ j : Fin k, componentSize ET e j) + k = n := by
  have hcover : Finset.univ.biUnion
        (fun j : Fin k => orderedRootBlock ET e j)
      = (Finset.univ : Finset (Fin n)) := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      iff_true]
    obtain ⟨j, hj⟩ := orderedRootBlock_cover hET e v
    exact ⟨j, hj⟩
  have hdisj : ∀ j₁ ∈ (Finset.univ : Finset (Fin k)),
      ∀ j₂ ∈ (Finset.univ : Finset (Fin k)), j₁ ≠ j₂ →
      Disjoint (orderedRootBlock ET e j₁)
        (orderedRootBlock ET e j₂) :=
    fun j₁ _ j₂ _ hne => orderedRootBlock_disjoint hET e hne
  have hcard := Finset.card_biUnion hdisj
  rw [hcover, Finset.card_univ, Fintype.card_fin] at hcard
  have hsum : (∑ j : Fin k, (orderedRootBlock ET e j).card)
      = ∑ j : Fin k, (componentSize ET e j + 1) :=
    Finset.sum_congr rfl (fun j _ => card_orderedRootBlock ET e j)
  rw [hsum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hcard
  omega

/-- Corollary form (only under k ≤ n). -/
theorem sum_componentSize_eq
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))))
    (e : RootEnumeration ET k) :
    (∑ j : Fin k, componentSize ET e j) = n - k := by
  have h := sum_componentSize_add_k hET e
  omega

/-! ## The internal trees: endpoints confined to the block -/

theorem componentEdges_endpoints
    {ET : Finset (OrderedEdge (n + 1))} {r : Fin n}
    {ed : OrderedEdge (n + 1)}
    (hed : ed ∈ componentEdges ET r) :
    ed.val.1 ∈ (rootComponent ET r).image Fin.succ
      ∧ ed.val.2 ∈ (rootComponent ET r).image Fin.succ := by
  unfold componentEdges at hed
  rw [Finset.mem_filter] at hed
  obtain ⟨hchild, h1⟩ := hed
  refine ⟨h1, ?_⟩
  obtain ⟨a, ha, ha1⟩ := mem_succImage.mp h1
  have hne2 : ed.val.2 ≠ 0 := by
    have := ed.2
    intro h0
    rw [h0] at this
    exact Fin.not_lt_zero _ this
  obtain ⟨b, hb2⟩ :=
    (Fin.eq_zero_or_eq_succ ed.val.2).resolve_left hne2
  have hadj := child_edge_adj hchild
  rw [← ha1, hb2] at hadj
  have hreach : sameRootDeletedComponent ET b a :=
    (SimpleGraph.Adj.reachable hadj).symm
  have hbmem : b ∈ rootComponent ET r := by
    rw [mem_rootComponent]
    exact hreach.trans (mem_rootComponent.mp ha)
  rw [hb2]
  exact mem_succImage.mpr ⟨b, hbmem, rfl⟩

/-- Child-forest walks starting in a component stay inside its
    componentEdges (second confinement induction). -/
theorem confined_walk_componentEdges
    {ET : Finset (OrderedEdge (n + 1))} {r : Fin n}
    {x y : Fin (n + 1)}
    (w : (graphOfEdges (childEdges ET)).Walk x y)
    (hx : x ∈ (rootComponent ET r).image Fin.succ) :
    (graphOfEdges (componentEdges ET r)).Reachable x y := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj p ih =>
    obtain ⟨a', ha', rfl⟩ := mem_succImage.mp hx
    have hbne : b ≠ 0 := by
      intro h0
      subst h0
      exact child_not_adj_zero _ hadj.symm
    obtain ⟨b', rfl⟩ := (Fin.eq_zero_or_eq_succ b).resolve_left hbne
    have hb' : b' ∈ rootComponent ET r := by
      rw [mem_rootComponent]
      refine SimpleGraph.Reachable.trans ?_ (mem_rootComponent.mp ha')
      exact (SimpleGraph.Adj.reachable hadj).symm
    have hbmem : b'.succ ∈ (rootComponent ET r).image Fin.succ :=
      mem_succImage.mpr ⟨b', hb', rfl⟩
    refine SimpleGraph.Reachable.trans
      ⟨SimpleGraph.Walk.cons ?_ SimpleGraph.Walk.nil⟩ (ih hbmem)
    rcases hadj with ⟨hlt, hm⟩ | ⟨hlt, hm⟩
    · refine Or.inl ⟨hlt, ?_⟩
      unfold componentEdges
      rw [Finset.mem_filter]
      exact ⟨hm, mem_succImage.mpr ⟨a', ha', rfl⟩⟩
    · refine Or.inr ⟨hlt, ?_⟩
      unfold componentEdges
      rw [Finset.mem_filter]
      exact ⟨hm, hbmem⟩

/-- The derived internal tree connects its block to the mark. -/
theorem orderedInternalTree_conn
    {ET : Finset (OrderedEdge (n + 1))}
    (e : RootEnumeration ET k) (j : Fin k) {v : Fin n}
    (hv : v ∈ orderedRootBlock ET e j) :
    (graphOfEdges (orderedInternalTree ET e j)).Reachable
      v.succ (orderedRootNeighbor ET e j).succ := by
  have hreach := mem_rootComponent.mp hv
  obtain ⟨w⟩ := hreach
  exact confined_walk_componentEdges w
    (mem_succImage.mpr ⟨v, hv, rfl⟩)

/-- Global edge count of the derived data. -/
theorem sum_orderedInternalTree_card
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))))
    (e : RootEnumeration ET k)
    (hk : (rootNeighbors ET).card = k) :
    (∑ j : Fin k, (orderedInternalTree ET e j).card) + k = n := by
  have hchild : childEdges ET
      = Finset.univ.biUnion
          (fun j : Fin k => orderedInternalTree ET e j) := by
    rw [childEdges_eq_biUnion hET]
    ext ed
    rw [Finset.mem_biUnion, Finset.mem_biUnion]
    constructor
    · rintro ⟨r, hr, hed⟩
      obtain ⟨j, hj⟩ := e.surjective ⟨r, hr⟩
      refine ⟨j, Finset.mem_univ j, ?_⟩
      unfold orderedInternalTree orderedRootNeighbor
      rw [hj]
      exact hed
    · rintro ⟨j, -, hed⟩
      exact ⟨orderedRootNeighbor ET e j, (e j).2, hed⟩
  have hdisj : ∀ j₁ ∈ (Finset.univ : Finset (Fin k)),
      ∀ j₂ ∈ (Finset.univ : Finset (Fin k)), j₁ ≠ j₂ →
      Disjoint (orderedInternalTree ET e j₁)
        (orderedInternalTree ET e j₂) := by
    intro j₁ _ j₂ _ hne
    refine componentEdges_disjoint ?_
    intro heq
    have hd := orderedRootBlock_disjoint hET e hne
    have hmem : orderedRootNeighbor ET e j₁
        ∈ orderedRootBlock ET e j₁ :=
      orderedRootNeighbor_mem_block ET e j₁
    have hmem2 : orderedRootNeighbor ET e j₁
        ∈ orderedRootBlock ET e j₂ := by
      unfold orderedRootBlock
      rw [← heq]
      exact hmem
    exact Finset.disjoint_left.mp hd hmem hmem2
  have hcard := Finset.card_biUnion hdisj
  rw [← hchild] at hcard
  have hETcard : ET.card = n := card_of_mem_spanningTreeEdgeSets hET
  have hrootinj : Function.Injective (rootEdge (n := n)) := by
    intro a b hab
    have h2 := congrArg (fun ed : OrderedEdge (n + 1) => ed.val.2) hab
    exact Fin.succ_injective n h2
  have hroot : (rootEdgesOf ET).card = k := by
    rw [rootEdgesOf_eq_image,
      Finset.card_image_of_injective _ hrootinj]
    exact hk
  have hsplit : (rootEdgesOf ET).card + (childEdges ET).card
      = n := by
    rw [← Finset.card_union_of_disjoint
      (rootEdgesOf_disjoint_childEdges ET),
      rootEdgesOf_union_childEdges, hETcard]
  omega

end LatticeGauge
