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

/-! ## Gate II.2: promoted helpers -/

theorem rootEdge_injective :
    Function.Injective (rootEdge (n := n)) := by
  intro a b hab
  have h2 := congrArg (fun ed : OrderedEdge (n + 1) => ed.val.2) hab
  exact Fin.succ_injective n h2

/-- The child edges reindexed by the enumeration (promoted from the
    local step of the size identity). -/
theorem childEdges_eq_biUnion_ordered
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))))
    (e : RootEnumeration ET k) :
    childEdges ET
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

/-! ## Gate II.2: the admissible ordered decompositions -/

/-- **Admissible ordered decomposition** — exactly what survives
    decomposition and suffices for reconstruction: the tree-ness of
    each block is NOT carried; the GLOBAL edge count together with
    per-block connectivity pins every block to exactly |Bⱼ|−1 edges,
    and the 40b cardinal converse certifies the reconstruction. -/
structure OrderedDecomposition (n k : ℕ) where
  block : Fin k → Finset (Fin n)
  marked : Fin k → Fin n
  itree : Fin k → Finset (OrderedEdge (n + 1))
  marked_mem : ∀ j, marked j ∈ block j
  marked_inj : Function.Injective marked
  cover : ∀ v : Fin n, ∃ j, v ∈ block j
  disj : ∀ j₁ j₂ : Fin k, j₁ ≠ j₂ → Disjoint (block j₁) (block j₂)
  sub : ∀ j, ∀ ed ∈ itree j,
    ed.val.1 ∈ (block j).image Fin.succ
      ∧ ed.val.2 ∈ (block j).image Fin.succ
  conn : ∀ j, ∀ v ∈ block j,
    (graphOfEdges (itree j)).Reachable v.succ (marked j).succ
  cardSum : (∑ j, (itree j).card) + k = n

theorem OrderedDecomposition.ext' {D₁ D₂ : OrderedDecomposition n k}
    (hb : D₁.block = D₂.block) (hm : D₁.marked = D₂.marked)
    (hi : D₁.itree = D₂.itree) : D₁ = D₂ := by
  cases D₁
  cases D₂
  dsimp only at hb hm hi
  subst hb
  subst hm
  subst hi
  rfl

/-! ## Decomposition of an enumerated tree -/

noncomputable def decompose {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ treesWithKRootNeighbors n k)
    (e : RootEnumeration ET k) : OrderedDecomposition n k where
  block := orderedRootBlock ET e
  marked := orderedRootNeighbor ET e
  itree := orderedInternalTree ET e
  marked_mem := orderedRootNeighbor_mem_block ET e
  marked_inj := by
    intro j₁ j₂ h
    exact e.injective (Subtype.ext h)
  cover := orderedRootBlock_cover (mem_treesWithKRootNeighbors.mp hET).1 e
  disj := fun j₁ j₂ hne =>
    orderedRootBlock_disjoint (mem_treesWithKRootNeighbors.mp hET).1 e hne
  sub := fun j ed hed => componentEdges_endpoints hed
  conn := fun j v hv => orderedInternalTree_conn e j hv
  cardSum := sum_orderedInternalTree_card
    (mem_treesWithKRootNeighbors.mp hET).1 e
    (mem_treesWithKRootNeighbors.mp hET).2

/-! ## Reconstruction -/

noncomputable def reconstructTree (D : OrderedDecomposition n k) :
    Finset (OrderedEdge (n + 1)) :=
  (Finset.univ.image (fun j => rootEdge (D.marked j)))
    ∪ Finset.univ.biUnion (fun j => D.itree j)

theorem mem_reconstructTree {D : OrderedDecomposition n k}
    {ed : OrderedEdge (n + 1)} :
    ed ∈ reconstructTree D
      ↔ (∃ j, rootEdge (D.marked j) = ed) ∨ ∃ j, ed ∈ D.itree j := by
  unfold reconstructTree
  simp [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion]

theorem itree_fst_ne_zero {D : OrderedDecomposition n k} {j : Fin k}
    {ed : OrderedEdge (n + 1)} (hed : ed ∈ D.itree j) :
    ed.val.1 ≠ 0 :=
  succImage_ne_zero (D.sub j ed hed).1

/-- rootNeighbors of the reconstruction = image of the marks. -/
theorem rootNeighbors_reconstructTree (D : OrderedDecomposition n k) :
    rootNeighbors (reconstructTree D)
      = Finset.univ.image D.marked := by
  ext i
  rw [mem_rootNeighbors, mem_reconstructTree, Finset.mem_image]
  constructor
  · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      have h2 := congrArg
        (fun ed : OrderedEdge (n + 1) => ed.val.2) hj
      exact Fin.succ_injective n h2
    · exact absurd rfl (itree_fst_ne_zero hj)
  · rintro ⟨j, -, hj⟩
    exact Or.inl ⟨j, by rw [hj]⟩

theorem card_rootNeighbors_reconstructTree
    (D : OrderedDecomposition n k) :
    (rootNeighbors (reconstructTree D)).card = k := by
  rw [rootNeighbors_reconstructTree,
    Finset.card_image_of_injective _ D.marked_inj,
    Finset.card_univ, Fintype.card_fin]

theorem childEdges_reconstructTree (D : OrderedDecomposition n k) :
    childEdges (reconstructTree D)
      = Finset.univ.biUnion (fun j => D.itree j) := by
  ext ed
  rw [mem_childEdges, mem_reconstructTree, Finset.mem_biUnion]
  constructor
  · rintro ⟨⟨j, hj⟩ | ⟨j, hj⟩, hne⟩
    · refine absurd ?_ hne
      rw [← hj]
      rfl
    · exact ⟨j, Finset.mem_univ j, hj⟩
  · rintro ⟨j, -, hj⟩
    exact ⟨Or.inr ⟨j, hj⟩, itree_fst_ne_zero hj⟩

theorem itree_pairwise_disjoint (D : OrderedDecomposition n k)
    {j₁ j₂ : Fin k} (hne : j₁ ≠ j₂) :
    Disjoint (D.itree j₁) (D.itree j₂) := by
  rw [Finset.disjoint_left]
  intro ed h1 h2
  have e1 := (D.sub j₁ ed h1).1
  have e2 := (D.sub j₂ ed h2).1
  exact Finset.disjoint_left.mp
    (succImage_disjoint (D.disj j₁ j₂ hne)) e1 e2

theorem card_reconstructTree (D : OrderedDecomposition n k) :
    (reconstructTree D).card = n := by
  unfold reconstructTree
  have hdisj : Disjoint
      (Finset.univ.image (fun j => rootEdge (D.marked j)))
      (Finset.univ.biUnion (fun j => D.itree j)) := by
    rw [Finset.disjoint_left]
    intro ed h1 h2
    rw [Finset.mem_image] at h1
    obtain ⟨j, -, hj⟩ := h1
    rw [Finset.mem_biUnion] at h2
    obtain ⟨j', -, hj'⟩ := h2
    refine itree_fst_ne_zero hj' ?_
    rw [← hj]
    rfl
  have hinj : Function.Injective
      (fun j : Fin k => rootEdge (D.marked j)) :=
    fun a b h => D.marked_inj (rootEdge_injective h)
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_fin,
    Finset.card_biUnion
      (fun j₁ _ j₂ _ hne => itree_pairwise_disjoint D hne)]
  have := D.cardSum
  omega

/-- Every vertex of the reconstruction reaches the root. -/
theorem reconstructTree_reachable_zero (D : OrderedDecomposition n k)
    (x : Fin (n + 1)) :
    (graphOfEdges (reconstructTree D)).Reachable x 0 := by
  rcases Fin.eq_zero_or_eq_succ x with rfl | ⟨v, rfl⟩
  · exact SimpleGraph.Reachable.refl _
  · obtain ⟨j, hj⟩ := D.cover v
    have hle : graphOfEdges (D.itree j)
        ≤ graphOfEdges (reconstructTree D) := by
      refine graphOfEdges_mono ?_
      intro ed hed
      exact mem_reconstructTree.mpr (Or.inr ⟨j, hed⟩)
    have h1 : (graphOfEdges (reconstructTree D)).Reachable
        v.succ (D.marked j).succ := by
      obtain ⟨w⟩ := D.conn j v hj
      exact ⟨w.mapLe hle⟩
    refine h1.trans ?_
    have hadj : (graphOfEdges (reconstructTree D)).Adj
        0 (D.marked j).succ :=
      adj_zero_succ_iff.mpr
        (mem_reconstructTree.mpr (Or.inl ⟨j, rfl⟩))
    exact (SimpleGraph.Adj.reachable hadj).symm

theorem reconstructTree_mem_stratum (D : OrderedDecomposition n k) :
    reconstructTree D ∈ treesWithKRootNeighbors n k := by
  refine mem_treesWithKRootNeighbors.mpr ⟨?_, ?_⟩
  · refine mem_spanningTreeEdgeSets.mpr ⟨?_, ?_⟩
    · rw [availableEdges_top]
      exact Finset.subset_univ _
    · refine isTree_of_connected_card ?_ ?_
      · rw [SimpleGraph.connected_iff]
        refine ⟨?_, ⟨0⟩⟩
        intro a b
        exact (reconstructTree_reachable_zero D a).trans
          (reconstructTree_reachable_zero D b).symm
      · rw [availableEdges_graphOfEdges]
        exact card_reconstructTree D
  · exact card_rootNeighbors_reconstructTree D

/-- The induced enumeration of the reconstruction. -/
noncomputable def reconstructEnum (D : OrderedDecomposition n k) :
    RootEnumeration (reconstructTree D) k :=
  Equiv.ofBijective
    (fun j => ⟨D.marked j, by
      rw [rootNeighbors_reconstructTree, Finset.mem_image]
      exact ⟨j, Finset.mem_univ j, rfl⟩⟩)
    (by
      constructor
      · intro j₁ j₂ h
        exact D.marked_inj (congrArg Subtype.val h)
      · rintro ⟨i, hi⟩
        rw [rootNeighbors_reconstructTree, Finset.mem_image] at hi
        obtain ⟨j, -, hj⟩ := hi
        exact ⟨j, Subtype.ext hj⟩)

@[simp] theorem reconstructEnum_val (D : OrderedDecomposition n k)
    (j : Fin k) :
    ((reconstructEnum D) j).val = D.marked j := rfl

/-! ## First confinement: reconstructed child walks never change
    block -/

theorem recon_walk_confined (D : OrderedDecomposition n k)
    {j : Fin k} {x y : Fin (n + 1)}
    (w : (graphOfEdges (childEdges (reconstructTree D))).Walk x y)
    (hx : x ∈ (D.block j).image Fin.succ) :
    y ∈ (D.block j).image Fin.succ := by
  induction w with
  | nil => exact hx
  | @cons a b c hadj p ih =>
    refine ih ?_
    have hstep : ∀ (ed : OrderedEdge (n + 1)),
        ed ∈ childEdges (reconstructTree D) →
        (ed.val.1 = a ∧ ed.val.2 = b) ∨
        (ed.val.1 = b ∧ ed.val.2 = a) →
        b ∈ (D.block j).image Fin.succ := by
      intro ed hed hcase
      rw [childEdges_reconstructTree, Finset.mem_biUnion] at hed
      obtain ⟨j', -, hed'⟩ := hed
      obtain ⟨h1, h2⟩ := D.sub j' ed hed'
      have haj' : a ∈ (D.block j').image Fin.succ := by
        rcases hcase with ⟨e1, -⟩ | ⟨-, e2⟩
        · rw [← e1]; exact h1
        · rw [← e2]; exact h2
      have hbj' : b ∈ (D.block j').image Fin.succ := by
        rcases hcase with ⟨-, e2⟩ | ⟨e1, -⟩
        · rw [← e2]; exact h2
        · rw [← e1]; exact h1
      have hjj' : j = j' := by
        by_contra hne
        obtain ⟨a', ha', ha1⟩ := mem_succImage.mp hx
        obtain ⟨a'', ha'', ha2⟩ := mem_succImage.mp haj'
        have : a'' = a' :=
          Fin.succ_injective n (ha2.trans ha1.symm)
        subst this
        exact Finset.disjoint_left.mp (D.disj j j' hne) ha' ha''
      rw [hjj']
      exact hbj'
    rcases hadj with ⟨hlt, hm⟩ | ⟨hlt, hm⟩
    · exact hstep _ hm (Or.inl ⟨rfl, rfl⟩)
    · exact hstep _ hm (Or.inr ⟨rfl, rfl⟩)

/-- **Roundtrip half 1 of the second inverse: the deleted-root
    component of the mark is exactly the block.** -/
theorem rootComponent_reconstructTree (D : OrderedDecomposition n k)
    (j : Fin k) :
    rootComponent (reconstructTree D) (D.marked j) = D.block j := by
  ext v
  rw [mem_rootComponent]
  constructor
  · intro hreach
    have hw := hreach.symm
    obtain ⟨w⟩ := hw
    have hmem : (D.marked j).succ ∈ (D.block j).image Fin.succ :=
      mem_succImage.mpr ⟨D.marked j, D.marked_mem j, rfl⟩
    have := recon_walk_confined D w hmem
    obtain ⟨v', hv', hveq⟩ := mem_succImage.mp this
    have : v' = v := Fin.succ_injective n hveq
    subst this
    exact hv'
  · intro hv
    have hle : graphOfEdges (D.itree j)
        ≤ graphOfEdges (childEdges (reconstructTree D)) := by
      refine graphOfEdges_mono ?_
      intro ed hed
      rw [childEdges_reconstructTree, Finset.mem_biUnion]
      exact ⟨j, Finset.mem_univ j, hed⟩
    obtain ⟨w⟩ := D.conn j v hv
    exact ⟨w.mapLe hle⟩

/-- **Roundtrip half 2: the recovered internal tree is the given
    one, extensionally.** -/
theorem componentEdges_reconstructTree (D : OrderedDecomposition n k)
    (j : Fin k) :
    componentEdges (reconstructTree D) (D.marked j) = D.itree j := by
  ext ed
  unfold componentEdges
  rw [Finset.mem_filter, childEdges_reconstructTree,
    Finset.mem_biUnion, rootComponent_reconstructTree]
  constructor
  · rintro ⟨⟨j', -, hed⟩, hfst⟩
    have hjj' : j = j' := by
      by_contra hne
      have h1 := (D.sub j' ed hed).1
      exact Finset.disjoint_left.mp
        (succImage_disjoint (D.disj j j' hne)) hfst h1
    rw [hjj']
    exact hed
  · intro hed
    exact ⟨⟨j, Finset.mem_univ j, hed⟩, (D.sub j ed hed).1⟩

/-! ## The two capstone roundtrips and the equivalence -/

/-- **decomposeThenReconstruct**: internal edges, root-mark edges,
    the original tree — all recovered exactly. -/
theorem decomposeThenReconstruct
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ treesWithKRootNeighbors n k)
    (e : RootEnumeration ET k) :
    reconstructTree (decompose hET e) = ET := by
  have hspan := (mem_treesWithKRootNeighbors.mp hET).1
  unfold reconstructTree decompose
  have himg : Finset.univ.image
        (fun j : Fin k => rootEdge (orderedRootNeighbor ET e j))
      = rootEdgesOf ET := by
    rw [rootEdgesOf_eq_image]
    ext ed
    rw [Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨j, -, hj⟩
      exact ⟨orderedRootNeighbor ET e j, (e j).2, hj⟩
    · rintro ⟨r, hr, hj⟩
      obtain ⟨j, hej⟩ := e.surjective ⟨r, hr⟩
      refine ⟨j, Finset.mem_univ j, ?_⟩
      unfold orderedRootNeighbor
      rw [hej]
      exact hj
  rw [himg, ← childEdges_eq_biUnion_ordered hspan e]
  exact rootEdgesOf_union_childEdges ET

/-- **reconstructThenDecompose**: blocks, marks and internal trees
    all recovered exactly (no cardinality substitute). -/
theorem reconstructThenDecompose (D : OrderedDecomposition n k) :
    decompose (reconstructTree_mem_stratum D) (reconstructEnum D)
      = D := by
  refine OrderedDecomposition.ext' ?_ ?_ ?_
  · funext j
    show orderedRootBlock (reconstructTree D) (reconstructEnum D) j
      = D.block j
    unfold orderedRootBlock orderedRootNeighbor
    rw [reconstructEnum_val]
    exact rootComponent_reconstructTree D j
  · funext j
    show orderedRootNeighbor (reconstructTree D) (reconstructEnum D) j
      = D.marked j
    unfold orderedRootNeighbor
    rw [reconstructEnum_val]
  · funext j
    show orderedInternalTree (reconstructTree D) (reconstructEnum D) j
      = D.itree j
    unfold orderedInternalTree orderedRootNeighbor
    rw [reconstructEnum_val]
    exact componentEdges_reconstructTree D j

/-! ## The packaged equivalence -/

structure EnumeratedTree (n k : ℕ) where
  ET : Finset (OrderedEdge (n + 1))
  mem : ET ∈ treesWithKRootNeighbors n k
  enum : RootEnumeration ET k

theorem EnumeratedTree.ext' {T₁ T₂ : EnumeratedTree n k}
    (hET : T₁.ET = T₂.ET)
    (henum : ∀ j, (T₁.enum j).val = (T₂.enum j).val) :
    T₁ = T₂ := by
  cases T₁
  cases T₂
  dsimp only at hET henum
  subst hET
  have h : ∀ j, _ = _ := fun j => Subtype.ext (henum j)
  have he := Equiv.ext h
  subst he
  rfl

/-- **GATE II CAPSTONE: the structural bidirectional
    correspondence** — enumerated trees ≃ admissible ordered
    decompositions, both inverses proved. -/
noncomputable def enumeratedTree_equiv_orderedDecomposition :
    EnumeratedTree n k ≃ OrderedDecomposition n k where
  toFun T := decompose T.mem T.enum
  invFun D := ⟨reconstructTree D, reconstructTree_mem_stratum D,
    reconstructEnum D⟩
  left_inv T := by
    refine EnumeratedTree.ext' ?_ ?_
    · exact decomposeThenReconstruct T.mem T.enum
    · intro j
      rw [reconstructEnum_val]
      rfl
  right_inv D := reconstructThenDecompose D

end LatticeGauge
