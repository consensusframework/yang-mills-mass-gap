/-
LatticeGauge/KPCoefficients.lean — Phase 3, forty-seventh stone (b-i).

FINITE ROOTED COEFFICIENTS, NONNEGATIVITY, TREE MAJORANT AND
RELABELING (architecture: Sol/GPT-5.6; adversarial audit of the
frozen manuscript PEDRA47A_PROOF.md at ede2ba63d2: Kimi/Moonshot;
execution: Fable). The layer BEFORE the root decomposition of the
Kotecký–Preiss induction: the rooted Ursell coefficient Aₙ and its
tree majorant Tₙ as FINITE sums over the real polymer universe, with
the manuscript's vertex convention encapsulated once and for all in
`rootedTuple` (vertex 0 carries the root γ₀ WITHOUT its activity;
vertex i.succ carries γ i, each contributing exactly one activity);
the zero cases A₀ = T₀ = 1; nonnegativity of everything (consumed
by 47c); Aₙ ≤ Tₙ termwise from the stone-43 theorem
`ursellCoeff_hardCoreTree_bound` (consumed, not reproved); and the
NAMED RELABELING LEMMAS: transport of the labelled-tree universe and
of the hard-core tree weights along any permutation of the indices
(the stone-38 canonical-edge machinery extended from graphs to tree
sums: spanning trees of ⊤ are stable under relabelEdgeSet via the
LOCAL cardinal converse of 40b — no acyclicity transport needed),
plus the root-preserving extension of a tail permutation and the
invariance of the rooted summand. SCOPE NOTE on the generic-V form
of the manuscript's relabeling lemma: this library's OrderedEdge is
built on the linear order of Fin, so the formal statement is by
permutations of Fin (n+1) (the canonical machinery of stone 38
exists precisely to absorb non-monotone relabelings); the transport
of a BLOCK B ⊆ Fin (n+1) to standard position via Finset.equivFin —
and the identification of the block sum with m!·Tₘ — is deliberately
DEFERRED to 47b-ii, as authorized by the gate of item 11.

NOT here: no root-removal decomposition, no components, no
Perm (Fin k) action, no orbit-stabilizer, no recurrence, no sums
over n, no S_M, no Real.exp, no consumption of the stone-46 KP
hypothesis, no convergence claims. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.Beta0
import LatticeGauge.PlaquetteActivity
import LatticeGauge.PlaquetteConnectivity
import LatticeGauge.ComponentFactorization
import LatticeGauge.PolymerGeometry
import LatticeGauge.PolymerGas
import LatticeGauge.UrsellCoefficients
import LatticeGauge.UrsellSymmetry
import LatticeGauge.UrsellBounds
import LatticeGauge.EdgeFibers
import LatticeGauge.PenroseIdentity
import LatticeGauge.PolymerTreeBound
import LatticeGauge.PolymerActivityBound
import LatticeGauge.LinkCovering
import LatticeGauge.LocalGeometry
import LatticeGauge.PolymerWalkCount
import LatticeGauge.KPSmallness

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## 1. The finite polymer universe (the real one — no abstract
    theory) -/

/-- The subtype of the finite polymer universe. Fintype and
    (classical) DecidableEq come for free from the Finset. -/
abbrev Polymer (N : ℕ) [NeZero N] [Fintype (Site N)] :=
  {D : Finset (Site N × Dir × Dir) // D ∈ allPlaquettePolymers N}

/-! ## 2. The rooted tuple: the whole index convention lives here -/

/-- Vertex 0 carries γ₀; vertex i.succ carries γ i. -/
noncomputable def rootedTuple {n : ℕ} (γ₀ : Polymer N)
    (γ : Fin n → Polymer N) :
    Fin (n + 1) → Finset (Site N × Dir × Dir) :=
  Fin.cons γ₀.val (fun i => (γ i).val)

@[simp] theorem rootedTuple_zero {n : ℕ} (γ₀ : Polymer N)
    (γ : Fin n → Polymer N) :
    rootedTuple γ₀ γ 0 = γ₀.val :=
  Fin.cons_zero _ _

@[simp] theorem rootedTuple_succ {n : ℕ} (γ₀ : Polymer N)
    (γ : Fin n → Polymer N) (i : Fin n) :
    rootedTuple γ₀ γ i.succ = (γ i).val :=
  Fin.cons_succ _ _ _

/-! ## 3. The weight of one labelled tree -/

/-- Hard-core indicator of the tree times the activities of the NON
    ROOT vertices only (the root activity is deliberately absent —
    manuscript §1). Codomain ℝ at this layer. -/
noncomputable def rootedTreeWeight {n : ℕ}
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) (γ : Fin n → Polymer N)
    (ET : Finset (OrderedEdge (n + 1))) : ℝ :=
  (hardCoreTreeIndicator (rootedTuple γ₀ γ) ET : ℝ)
    * ∏ i : Fin n, ρ (γ i)

theorem rootedTreeWeight_nonneg {n : ℕ}
    {ρ : Polymer N → ℝ} (hρ : ∀ γ, 0 ≤ ρ γ)
    (γ₀ : Polymer N) (γ : Fin n → Polymer N)
    (ET : Finset (OrderedEdge (n + 1))) :
    0 ≤ rootedTreeWeight ρ γ₀ γ ET :=
  mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg (fun i _ => hρ (γ i)))

/-! ## 4. The tree coefficient Tₙ -/

noncomputable def rootedTreeSum (n : ℕ)
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) : ℝ :=
  ∑ γ : Fin n → Polymer N,
    ∑ ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))),
      rootedTreeWeight ρ γ₀ γ ET

noncomputable def kpTreeCoeff (n : ℕ)
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) : ℝ :=
  rootedTreeSum n ρ γ₀ / (n ! : ℝ)

/-! ## 5. The Ursell coefficient Aₙ -/

noncomputable def kpUrsellCoeff (n : ℕ)
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) : ℝ :=
  (∑ γ : Fin n → Polymer N,
      ((ursellCoeff (rootedTuple γ₀ γ)).natAbs : ℝ)
        * ∏ i : Fin n, ρ (γ i)) / (n ! : ℝ)

/-! ## 6. The zero cases: only the root, coefficient 1 -/

theorem rootedTreeSum_zero (ρ : Polymer N → ℝ) (γ₀ : Polymer N) :
    rootedTreeSum 0 ρ γ₀ = 1 := by
  unfold rootedTreeSum rootedTreeWeight
  rw [Finset.univ_unique, Finset.sum_singleton,
    spanningTreeEdgeSets_top_fin_one, Finset.sum_singleton]
  unfold hardCoreTreeIndicator
  rw [Finset.prod_empty]
  simp

/-- **T₀ = 1**: the unique empty tree over the root alone, empty
    products, 0! = 1 — nothing hidden in simp. -/
theorem kpTreeCoeff_zero (ρ : Polymer N → ℝ) (γ₀ : Polymer N) :
    kpTreeCoeff 0 ρ γ₀ = 1 := by
  unfold kpTreeCoeff
  rw [rootedTreeSum_zero, Nat.factorial_zero, Nat.cast_one, div_one]

/-- **A₀ = 1**: the unit case of the stone-37 Ursell coefficient. -/
theorem kpUrsellCoeff_zero (ρ : Polymer N → ℝ) (γ₀ : Polymer N) :
    kpUrsellCoeff 0 ρ γ₀ = 1 := by
  unfold kpUrsellCoeff
  rw [Finset.univ_unique, Finset.sum_singleton,
    ursellCoeff_single (rootedTuple γ₀ default)]
  simp

/-! ## 7. Nonnegativity (consumed directly by 47c) -/

theorem rootedTreeSum_nonneg (n : ℕ)
    {ρ : Polymer N → ℝ} (hρ : ∀ γ, 0 ≤ ρ γ) (γ₀ : Polymer N) :
    0 ≤ rootedTreeSum n ρ γ₀ :=
  Finset.sum_nonneg (fun γ _ => Finset.sum_nonneg
    (fun ET _ => rootedTreeWeight_nonneg hρ γ₀ γ ET))

theorem kpTreeCoeff_nonneg (n : ℕ)
    {ρ : Polymer N → ℝ} (hρ : ∀ γ, 0 ≤ ρ γ) (γ₀ : Polymer N) :
    0 ≤ kpTreeCoeff n ρ γ₀ :=
  div_nonneg (rootedTreeSum_nonneg n hρ γ₀) (Nat.cast_nonneg _)

theorem kpUrsellCoeff_nonneg (n : ℕ)
    {ρ : Polymer N → ℝ} (hρ : ∀ γ, 0 ≤ ρ γ) (γ₀ : Polymer N) :
    0 ≤ kpUrsellCoeff n ρ γ₀ := by
  unfold kpUrsellCoeff
  refine div_nonneg (Finset.sum_nonneg (fun γ _ => ?_))
    (Nat.cast_nonneg _)
  exact mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg (fun i _ => hρ (γ i)))

/-! ## 8. THE TREE MAJORANT: Aₙ ≤ Tₙ -/

/-- **Aₙ ≤ Tₙ, termwise** — stone 43's
    `ursellCoeff_hardCoreTree_bound` for each fixed tuple, times the
    nonnegative activity product, summed, divided by n! > 0. Penrose
    and the tree bound are consumed, never reproved. -/
theorem kpUrsellCoeff_le_kpTreeCoeff (n : ℕ)
    {ρ : Polymer N → ℝ} (hρ : ∀ γ, 0 ≤ ρ γ) (γ₀ : Polymer N) :
    kpUrsellCoeff n ρ γ₀ ≤ kpTreeCoeff n ρ γ₀ := by
  unfold kpUrsellCoeff kpTreeCoeff rootedTreeSum rootedTreeWeight
  refine div_le_div_of_nonneg_right ?_ ?_
  · refine Finset.sum_le_sum (fun γ _ => ?_)
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_
      (Finset.prod_nonneg (fun i _ => hρ (γ i)))
    exact_mod_cast ursellCoeff_hardCoreTree_bound (rootedTuple γ₀ γ)
  · exact_mod_cast Nat.factorial_pos n

/-! ## 9. Relabeling: the tree universe is stable under
    permutations (stone-38 machinery + the 40b cardinal converse —
    no acyclicity transport) -/

theorem relabelEdgeSet_mem_spanningTreeEdgeSets_top {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1)))
    {ET : Finset (OrderedEdge (n + 1))}
    (h : ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1)))) :
    relabelEdgeSet σ ET
      ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))) := by
  obtain ⟨-, hTree⟩ := mem_spanningTreeEdgeSets.mp h
  have hcard : ET.card = n := card_of_mem_spanningTreeEdgeSets h
  refine mem_spanningTreeEdgeSets.mpr ⟨?_, ?_⟩
  · rw [availableEdges_top]
    exact Finset.subset_univ _
  · refine isTree_of_connected_card ?_ ?_
    · exact (graphOfEdges_relabel_connected_iff σ ET).mpr
        hTree.isConnected
    · rw [availableEdges_graphOfEdges, card_relabelEdgeSet]
      exact hcard

/-- **The hard-core weight transports along the relabeling** (43ª
    capstone + 38ª comap identities; the subset condition rides
    Finset.map). -/
theorem hardCoreTreeIndicator_comp_perm {n : ℕ}
    (t : Fin (n + 1) → Finset (Site N × Dir × Dir))
    (σ : Equiv.Perm (Fin (n + 1)))
    (ET : Finset (OrderedEdge (n + 1))) :
    hardCoreTreeIndicator (t ∘ ⇑σ) ET
      = hardCoreTreeIndicator t (relabelEdgeSet σ ET) := by
  rw [hardCoreTreeIndicator_eq_subgraphIndicator,
    hardCoreTreeIndicator_eq_subgraphIndicator]
  unfold spanningTreeSubgraphIndicator
  rw [polymerIncompatibilityGraph_comp_perm]
  have hiff : ET ⊆ availableEdges
        ((polymerIncompatibilityGraph t).comap ⇑σ)
      ↔ relabelEdgeSet σ ET
          ⊆ availableEdges (polymerIncompatibilityGraph t) := by
    rw [← relabelEdgeSet_availableEdges_comap
      (polymerIncompatibilityGraph t) σ]
    unfold relabelEdgeSet
    exact Finset.map_subset_map.symm
  exact if_congr hiff rfl rfl

/-- **Item 9 (scoped): invariance of the tree sum under any
    permutation of the vertex indices** — sum_bij along
    relabelEdgeSet. -/
theorem treeSum_comp_perm {n : ℕ}
    (t : Fin (n + 1) → Finset (Site N × Dir × Dir))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (∑ ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))),
        (hardCoreTreeIndicator (t ∘ ⇑σ) ET : ℝ))
      = ∑ ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))),
          (hardCoreTreeIndicator t ET : ℝ) := by
  refine Finset.sum_bij
    (fun ET _ => relabelEdgeSet σ ET) ?_ ?_ ?_ ?_
  · intro ET hET
    exact relabelEdgeSet_mem_spanningTreeEdgeSets_top σ hET
  · intro E₁ h₁ E₂ h₂ heq
    simp only [] at heq
    have h := congrArg (relabelEdgeSet σ.symm) heq
    rwa [relabelEdgeSet_symm_cancel, relabelEdgeSet_symm_cancel] at h
  · intro ET' hET'
    refine ⟨relabelEdgeSet σ.symm ET',
      relabelEdgeSet_mem_spanningTreeEdgeSets_top σ.symm hET', ?_⟩
    show relabelEdgeSet σ (relabelEdgeSet σ.symm ET') = ET'
    have h := relabelEdgeSet_symm_cancel σ.symm ET'
    rwa [Equiv.symm_symm] at h
  · intro ET hET
    rw [hardCoreTreeIndicator_comp_perm]

/-! ## 10. Relabeling with marked root: the root-fixing extension of
    a tail permutation and the invariance of the rooted summand -/

/-- Extension of π : Perm (Fin n) to Perm (Fin (n+1)) FIXING the
    root index 0 and permuting the tails. -/
noncomputable def extendPermSucc {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.cons 0 (fun i => (π i).succ)
  invFun := Fin.cons 0 (fun i => (π.symm i).succ)
  left_inv := by
    intro i
    refine Fin.cases ?_ ?_ i
    · rw [Fin.cons_zero, Fin.cons_zero]
    · intro j
      rw [Fin.cons_succ, Fin.cons_succ, Equiv.symm_apply_apply]
  right_inv := by
    intro i
    refine Fin.cases ?_ ?_ i
    · rw [Fin.cons_zero, Fin.cons_zero]
    · intro j
      rw [Fin.cons_succ, Fin.cons_succ, Equiv.apply_symm_apply]

@[simp] theorem extendPermSucc_zero {n : ℕ}
    (π : Equiv.Perm (Fin n)) :
    extendPermSucc π 0 = 0 :=
  Fin.cons_zero _ _

@[simp] theorem extendPermSucc_succ {n : ℕ}
    (π : Equiv.Perm (Fin n)) (i : Fin n) :
    extendPermSucc π i.succ = (π i).succ :=
  Fin.cons_succ _ _ _

/-- The rooted tuple of a permuted tail is the composed tuple: the
    root stays at 0, the tails follow π. -/
theorem rootedTuple_comp_perm {n : ℕ} (γ₀ : Polymer N)
    (γ : Fin n → Polymer N) (π : Equiv.Perm (Fin n)) :
    rootedTuple γ₀ (γ ∘ ⇑π)
      = rootedTuple γ₀ γ ∘ ⇑(extendPermSucc π) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [rootedTuple_zero]
    show _ = rootedTuple γ₀ γ (extendPermSucc π 0)
    rw [extendPermSucc_zero, rootedTuple_zero]
  · intro j
    rw [rootedTuple_succ]
    show _ = rootedTuple γ₀ γ (extendPermSucc π j.succ)
    rw [extendPermSucc_succ, rootedTuple_succ]
    rfl

/-- **Item 10 (scoped): the rooted tree-sum summand is invariant
    under tail permutations** — trees transported by the extension,
    activities reindexed by π. -/
theorem rootedSummand_comp_perm {n : ℕ}
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N)
    (γ : Fin n → Polymer N) (π : Equiv.Perm (Fin n)) :
    (∑ ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))),
        rootedTreeWeight ρ γ₀ (γ ∘ ⇑π) ET)
      = ∑ ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))),
          rootedTreeWeight ρ γ₀ γ ET := by
  unfold rootedTreeWeight
  have hprod : (∏ i : Fin n, ρ ((γ ∘ ⇑π) i))
      = ∏ i : Fin n, ρ (γ i) :=
    Equiv.prod_comp π (fun i => ρ (γ i))
  simp only [hprod]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  congr 1
  have h := treeSum_comp_perm (N := N) (rootedTuple γ₀ γ)
    (extendPermSucc π)
  rw [← rootedTuple_comp_perm] at h
  exact h

end LatticeGauge
