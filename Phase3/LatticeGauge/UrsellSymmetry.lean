/-
LatticeGauge/UrsellSymmetry.lean — Phase 3, thirty-eighth stone.

PERMUTATION INVARIANCE OF THE URSELL COEFFICIENTS (architecture:
Sol/GPT-5.6, hybrid route; execution: Fable). The Ursell coefficient
is invariant under reordering of the occurrences:
ursellCoeff (γ ∘ σ) = ursellCoeff γ for every σ : Equiv.Perm (Fin n).
Structurally, relabelling IS comap — polymerIncompatibilityGraph
(γ ∘ σ) = (polymerIncompatibilityGraph γ).comap σ — so the whole
content is the graph-level theorem graphUrsellCoeff (G.comap σ) =
graphUrsellCoeff G, proved by an explicit Finset.sum_bij on connected
spanning edge sets, with connectivity transported through a
SimpleGraph.Iso (Iso.preconnected_iff; the Nonempty side is identical
on both sides). ALL order cases (σ preserving or reversing i < j) are
concentrated in ONE canonicalization helper (canonicalOrderedEdge) and
its three little lemmas — no later proof repeats the case split.
DELIBERATE LIMITS (architect): generality stays at Fin n and
Equiv.Perm — no arbitrary vertex types, no Fin n ≃ Fin m, no graph
isomorphisms between different types (that would force simultaneous
changes to the edge canonicalization and the sum type without helping
the future series, which uses Fin n tuples precisely). CONSEQUENCE
(promised in stone 37's docstring): ursellCoeff is invariant under
reordering and therefore depends only on the UNORDERED TUPLE of
polymer occurrences, INCLUDING MULTIPLICITIES — repeated polymers are
neither identified nor eliminated; repetitions remain essential for
the future cluster series. NOTHING
analytic: no tuple quotients, no orbit sums, no multisets, no cluster
series, no 1/n!, no log realZ, no tree-graph inequality, no tree
counting, no Penrose, no Kotecký–Preiss, no convergence. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.PolymerGeometry
import LatticeGauge.UrsellCoefficients

open scoped Classical

namespace LatticeGauge

/-! ## 1. Canonicalization: the ONLY place with order cases -/

/-- The canonical ordered edge on an unordered pair of distinct
    indices. -/
def canonicalOrderedEdge {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    OrderedEdge n :=
  if hlt : i < j then ⟨(i, j), hlt⟩
  else ⟨(j, i), (h.lt_or_lt.resolve_left hlt)⟩

theorem canonicalOrderedEdge_of_lt {n : ℕ} {i j : Fin n}
    (h' : i < j) (h : i ≠ j) :
    canonicalOrderedEdge i j h = ⟨(i, j), h'⟩ := by
  unfold canonicalOrderedEdge
  rw [dif_pos h']

theorem canonicalOrderedEdge_of_gt {n : ℕ} {i j : Fin n}
    (h' : j < i) (h : i ≠ j) :
    canonicalOrderedEdge i j h = ⟨(j, i), h'⟩ := by
  unfold canonicalOrderedEdge
  rw [dif_neg (lt_asymm h')]

/-- **C. The unordered endpoints are what matters**: canonicalization
    is symmetric in its two arguments. -/
theorem canonicalOrderedEdge_comm {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    canonicalOrderedEdge i j h = canonicalOrderedEdge j i h.symm := by
  rcases h.lt_or_lt with h' | h'
  · rw [canonicalOrderedEdge_of_lt h' h,
      canonicalOrderedEdge_of_gt h' h.symm]
  · rw [canonicalOrderedEdge_of_gt h' h,
      canonicalOrderedEdge_of_lt h' h.symm]

/-- Canonicalizing an already-canonical edge reproduces it. -/
theorem canonicalOrderedEdge_val {n : ℕ} (e : OrderedEdge n) :
    canonicalOrderedEdge e.val.1 e.val.2 (ne_of_lt e.2) = e := by
  rw [canonicalOrderedEdge_of_lt e.2]

/-- Adjacency of a graph at the canonical edge's endpoints is
    adjacency at the original pair (in either order). -/
theorem adj_canonicalOrderedEdge {n : ℕ} (H : SimpleGraph (Fin n))
    {i j : Fin n} (h : i ≠ j) :
    H.Adj (canonicalOrderedEdge i j h).val.1
        (canonicalOrderedEdge i j h).val.2
      ↔ H.Adj i j := by
  rcases h.lt_or_lt with h' | h'
  · rw [canonicalOrderedEdge_of_lt h' h]
  · rw [canonicalOrderedEdge_of_gt h' h]
    exact ⟨fun ha => ha.symm, fun ha => ha.symm⟩

/-- Membership in graphOfEdges, phrased through canonicalization —
    the bridge that hides the disjunction of stone 37. -/
theorem graphOfEdges_adj_iff_canonical {n : ℕ}
    {E : Finset (OrderedEdge n)} {i j : Fin n} (h : i ≠ j) :
    (graphOfEdges E).Adj i j ↔ canonicalOrderedEdge i j h ∈ E := by
  rcases h.lt_or_lt with h' | h'
  · rw [canonicalOrderedEdge_of_lt h' h]
    constructor
    · rintro (⟨hlt, hm⟩ | ⟨hlt, hm⟩)
      · exact hm
      · exact absurd hlt (lt_asymm h')
    · intro hm
      exact Or.inl ⟨h', hm⟩
  · rw [canonicalOrderedEdge_of_gt h' h]
    constructor
    · rintro (⟨hlt, hm⟩ | ⟨hlt, hm⟩)
      · exact absurd hlt (lt_asymm h')
      · exact hm
    · intro hm
      exact Or.inr ⟨h', hm⟩

/-! ## 2. The edge relabelling equivalence -/

/-- The underlying relabelling function. -/
def relabelOrderedEdgeFun {n : ℕ} (σ : Equiv.Perm (Fin n))
    (e : OrderedEdge n) : OrderedEdge n :=
  canonicalOrderedEdge (σ e.val.1) (σ e.val.2)
    (fun hc => ne_of_lt e.2 (σ.injective hc))

/-- **B (kernel): σ.symm undoes σ** — proved once; every later lemma
    consumes this instead of re-splitting order cases. -/
theorem relabel_symm_cancel {n : ℕ} (σ : Equiv.Perm (Fin n))
    (e : OrderedEdge n) :
    relabelOrderedEdgeFun σ.symm (relabelOrderedEdgeFun σ e) = e := by
  unfold relabelOrderedEdgeFun
  have hne : σ e.val.1 ≠ σ e.val.2 :=
    fun hc => ne_of_lt e.2 (σ.injective hc)
  rcases hne.lt_or_lt with h' | h'
  · rw [canonicalOrderedEdge_of_lt h' hne]
    simp only [Equiv.symm_apply_apply]
    exact canonicalOrderedEdge_val e
  · rw [canonicalOrderedEdge_of_gt h' hne]
    simp only [Equiv.symm_apply_apply]
    rw [canonicalOrderedEdge_comm]
    exact canonicalOrderedEdge_val e

/-- **1. The edge relabelling as an Equiv.** -/
def relabelOrderedEdge {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    OrderedEdge n ≃ OrderedEdge n where
  toFun := relabelOrderedEdgeFun σ
  invFun := relabelOrderedEdgeFun σ.symm
  left_inv := relabel_symm_cancel σ
  right_inv := by
    intro e
    have h := relabel_symm_cancel σ.symm e
    simpa using h

/-- **A. Relabelling by the identity is the identity.** -/
theorem relabelOrderedEdge_refl {n : ℕ} :
    relabelOrderedEdge (Equiv.refl (Fin n)) = Equiv.refl _ := by
  apply Equiv.ext
  intro e
  show relabelOrderedEdgeFun (Equiv.refl (Fin n)) e = e
  unfold relabelOrderedEdgeFun
  simp only [Equiv.refl_apply]
  exact canonicalOrderedEdge_val e

/-- **B (packaged): the inverse Equiv is relabelling by σ.symm.** -/
theorem relabelOrderedEdge_symm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (relabelOrderedEdge σ).symm = relabelOrderedEdge σ.symm := by
  apply Equiv.ext
  intro e
  rfl

/-! ## 3. Relabelling of edge Finsets -/

def relabelEdgeSet {n : ℕ} (σ : Equiv.Perm (Fin n))
    (E : Finset (OrderedEdge n)) : Finset (OrderedEdge n) :=
  E.map (relabelOrderedEdge σ).toEmbedding

theorem mem_relabelEdgeSet {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {E : Finset (OrderedEdge n)} {e : OrderedEdge n} :
    e ∈ relabelEdgeSet σ E ↔ (relabelOrderedEdge σ).symm e ∈ E := by
  unfold relabelEdgeSet
  exact Finset.mem_map_equiv

/-- **D. Cardinality is preserved.** -/
theorem card_relabelEdgeSet {n : ℕ} (σ : Equiv.Perm (Fin n))
    (E : Finset (OrderedEdge n)) :
    (relabelEdgeSet σ E).card = E.card :=
  Finset.card_map _

/-- Relabelling by σ and then σ.symm (as set operations) cancels. -/
theorem relabelEdgeSet_symm_cancel {n : ℕ} (σ : Equiv.Perm (Fin n))
    (F : Finset (OrderedEdge n)) :
    relabelEdgeSet σ (relabelEdgeSet σ.symm F) = F := by
  ext e
  rw [mem_relabelEdgeSet, mem_relabelEdgeSet]
  have hval : (relabelOrderedEdge σ.symm).symm
      ((relabelOrderedEdge σ).symm e) = e :=
    relabel_symm_cancel σ.symm e
  rw [hval]

/-! ## 4. Transport of available edges under comap -/

/-- The available edges of G.comap σ are carried bijectively onto the
    available edges of G — with the orientation of Mathlib's comap:
    (G.comap σ).Adj i j ↔ G.Adj (σ i) (σ j). -/
theorem relabelEdgeSet_availableEdges_comap {n : ℕ}
    (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) :
    relabelEdgeSet σ (availableEdges (G.comap ⇑σ)) = availableEdges G := by
  ext e
  rw [mem_relabelEdgeSet, mem_availableEdges, mem_availableEdges]
  show (G.comap ⇑σ).Adj (relabelOrderedEdgeFun σ.symm e).val.1
      (relabelOrderedEdgeFun σ.symm e).val.2 ↔ _
  unfold relabelOrderedEdgeFun
  rw [adj_canonicalOrderedEdge]
  show G.Adj (σ (σ.symm e.val.1)) (σ (σ.symm e.val.2))
      ↔ G.Adj e.val.1 e.val.2
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem relabelEdgeSet_subset_available {n : ℕ}
    {G : SimpleGraph (Fin n)} {σ : Equiv.Perm (Fin n)}
    {E : Finset (OrderedEdge n)} :
    relabelEdgeSet σ E ⊆ availableEdges G
      ↔ E ⊆ availableEdges (G.comap ⇑σ) := by
  rw [← relabelEdgeSet_availableEdges_comap G σ]
  unfold relabelEdgeSet
  exact Finset.map_subset_map

/-! ## 5. Transport of adjacency and connectivity -/

private theorem relabelFun_canonical {n : ℕ} (σ : Equiv.Perm (Fin n))
    {i j : Fin n} (h : i ≠ j) :
    relabelOrderedEdgeFun σ (canonicalOrderedEdge i j h)
      = canonicalOrderedEdge (σ i) (σ j)
        (fun hc => h (σ.injective hc)) := by
  unfold relabelOrderedEdgeFun
  rcases h.lt_or_lt with h' | h'
  · rw [canonicalOrderedEdge_of_lt h' h]
  · rw [canonicalOrderedEdge_of_gt h' h]
    exact canonicalOrderedEdge_comm _

theorem graphOfEdges_relabelEdgeSet_adj {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (E : Finset (OrderedEdge n))
    {i j : Fin n} (h : i ≠ j) :
    (graphOfEdges (relabelEdgeSet σ E)).Adj (σ i) (σ j)
      ↔ (graphOfEdges E).Adj i j := by
  have hσ : σ i ≠ σ j := fun hc => h (σ.injective hc)
  rw [graphOfEdges_adj_iff_canonical hσ,
    graphOfEdges_adj_iff_canonical h, mem_relabelEdgeSet]
  have hkey : (relabelOrderedEdge σ).symm
      (canonicalOrderedEdge (σ i) (σ j) hσ)
      = canonicalOrderedEdge i j h := by
    show relabelOrderedEdgeFun σ.symm
        (canonicalOrderedEdge (σ i) (σ j) hσ) = _
    rw [← relabelFun_canonical σ h]
    exact relabel_symm_cancel σ _
  rw [hkey]

/-- **4. The vertex permutation is a graph isomorphism between the
    generated graphs** — built once, used only through
    Iso.preconnected_iff. -/
def graphOfEdgesRelabelIso {n : ℕ} (σ : Equiv.Perm (Fin n))
    (E : Finset (OrderedEdge n)) :
    graphOfEdges E ≃g graphOfEdges (relabelEdgeSet σ E) where
  toEquiv := σ
  map_rel_iff' := by
    intro i j
    constructor
    · intro hadj
      have h : i ≠ j := fun hc => hadj.ne (congrArg σ hc)
      exact (graphOfEdges_relabelEdgeSet_adj σ E h).mp hadj
    · intro hadj
      exact (graphOfEdges_relabelEdgeSet_adj σ E hadj.ne).mpr hadj

theorem graphOfEdges_relabel_connected_iff {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (E : Finset (OrderedEdge n)) :
    (graphOfEdges (relabelEdgeSet σ E)).Connected
      ↔ (graphOfEdges E).Connected := by
  rw [SimpleGraph.connected_iff, SimpleGraph.connected_iff,
    (graphOfEdgesRelabelIso σ E).preconnected_iff]

/-! ## 6. Transport of connected spanning edge sets and invariance -/

/-- **5 (central lemma).** -/
theorem mem_connectedSpanningEdgeSets_comap {n : ℕ}
    (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n))
    {E : Finset (OrderedEdge n)} :
    E ∈ connectedSpanningEdgeSets (G.comap ⇑σ)
      ↔ relabelEdgeSet σ E ∈ connectedSpanningEdgeSets G := by
  rw [mem_connectedSpanningEdgeSets, mem_connectedSpanningEdgeSets,
    graphOfEdges_relabel_connected_iff σ E]
  constructor
  · rintro ⟨hs, hc⟩
    exact ⟨relabelEdgeSet_subset_available.mpr hs, hc⟩
  · rintro ⟨hs, hc⟩
    exact ⟨relabelEdgeSet_subset_available.mp hs, hc⟩

/-- **6. GRAPHIC INVARIANCE**: relabelling the vertices of the base
    graph does not change the Ursell coefficient. All five sum_bij
    obligations are explicit. -/
theorem graphUrsellCoeff_comap_perm {n : ℕ}
    (G : SimpleGraph (Fin n)) (σ : Equiv.Perm (Fin n)) :
    graphUrsellCoeff (G.comap ⇑σ) = graphUrsellCoeff G := by
  unfold graphUrsellCoeff
  exact Finset.sum_bij
    (fun E _ => relabelEdgeSet σ E)
    (fun E hE => (mem_connectedSpanningEdgeSets_comap G σ).mp hE)
    (fun E₁ _ E₂ _ heq =>
      Finset.map_injective (relabelOrderedEdge σ).toEmbedding heq)
    (fun F hF => ⟨relabelEdgeSet σ.symm F,
      (mem_connectedSpanningEdgeSets_comap G σ).mpr
        (by rw [relabelEdgeSet_symm_cancel]; exact hF),
      relabelEdgeSet_symm_cancel σ F⟩)
    (fun E _ => by rw [card_relabelEdgeSet])

/-! ## 7-8. Application to polymer tuples -/

variable {N : ℕ}

/-- **7. Relabelling IS comap** for the incompatibility graph. -/
theorem polymerIncompatibilityGraph_comp_perm [NeZero N] {n : ℕ}
    (γ : Fin n → Finset (Site N × Dir × Dir))
    (σ : Equiv.Perm (Fin n)) :
    polymerIncompatibilityGraph (γ ∘ ⇑σ)
      = (polymerIncompatibilityGraph γ).comap ⇑σ := by
  ext i j
  show (i ≠ j ∧ ¬ PlaquetteCompatible (γ (σ i)) (γ (σ j)))
    ↔ (σ i ≠ σ j ∧ ¬ PlaquetteCompatible (γ (σ i)) (γ (σ j)))
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨fun hc => hne (σ.injective hc), h⟩
  · rintro ⟨hne, h⟩
    exact ⟨fun hc => hne (congrArg σ hc), h⟩

/-- **8. CAPSTONE (pedra 38): the Ursell coefficient is invariant
    under permutation of the occurrences.** The coefficient is
    invariant under reordering and therefore depends only on the
    unordered tuple of polymer occurrences, including multiplicities —
    repetitions are neither identified nor eliminated, and remain
    essential for the future cluster series. No series, no convergence, no log Z
    statement is made. Sanity cases (n = 0, n = 1, the transposition
    at n = 2, disconnected graphs) are direct corollaries and are
    deliberately not duplicated as separate theorems. -/
theorem ursellCoeff_perm [NeZero N] {n : ℕ}
    (γ : Fin n → Finset (Site N × Dir × Dir))
    (σ : Equiv.Perm (Fin n)) :
    ursellCoeff (γ ∘ ⇑σ) = ursellCoeff γ := by
  unfold ursellCoeff
  rw [polymerIncompatibilityGraph_comp_perm γ σ]
  exact graphUrsellCoeff_comap_perm _ σ

/-- Free companion: composition with σ.symm. -/
theorem ursellCoeff_perm_symm [NeZero N] {n : ℕ}
    (γ : Fin n → Finset (Site N × Dir × Dir))
    (σ : Equiv.Perm (Fin n)) :
    ursellCoeff (γ ∘ ⇑σ.symm) = ursellCoeff γ :=
  ursellCoeff_perm γ σ.symm

end LatticeGauge
