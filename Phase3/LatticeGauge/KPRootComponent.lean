/-
LatticeGauge/KPRootComponent.lean — stone 49C-III, Gate III-1:
ROOT COMPONENT AND EDGE SPLIT (architecture: Sol/GPT-5.6;
execution: Fable).

Target of the stone: the exact root-component recurrence
  (n+1)·A_{n+1} = Σ_{j=0}^n (j+1)·B_{j+1}·A_{n-j},
obtained by decomposing each selected graph into the connected
component containing the distinguished root and an arbitrary
graph on the remaining vertices. THIS GATE builds the numerators
(no factorial in the combinatorial path — the architect's
separation), the root component of a selected edge set, its
closure certificates, the no-crossing property for SELECTED
edges, and the exact split/reconstruction rootEdges ⊔ restEdges.

FUTURE ADVERSARIAL AUDIT TARGETS (recorded on the architect's
order):
A1. the component is taken in graphOfEdges E, NOT in the base
    incompatibility graph;
A2. no SELECTED edge crosses root/rest — AVAILABLE cross edges
    may exist and are killed only by the component fibering;
A3. the bijection E ↔ (Eroot, Erest) is round-trip, both ways;
A4. choose n j counts only the OTHER vertices of the root
    component;
A5. the factor (j+1) is born only from factorials, never from a
    root choice;
A6. repeated polymer occurrences remain PERMITTED on the B side
    (Ursell universe, Stone 37 design);
A7. zero exp/log in this stone.
NOT touched: Real.exp, Real.log, logPartition, FormalPowerSeries,
t-derivatives, KP smallness, β ≤ 1/40000, thermodynamic limit,
clustering, mass gap. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.UrsellCoefficients
import LatticeGauge.KPUnrooted
import LatticeGauge.KPGasCoefficients

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## III-1.a — the numerators (factorials quarantined) -/

/-- Numerator of Aₙ: the raw all-edge tuple sum, NO division. -/
noncomputable def gasNumerator (n : ℕ) (z : Polymer N → ℝ) : ℝ :=
  ∑ δ : Fin n → Polymer N,
    ((graphAllEdgeCoeff (polymerIncompatibilityGraph (N := N)
        (fun m => (δ m).val)) : ℤ) : ℝ)
      * ∏ i : Fin n, z (δ i)

/-- Numerator of Bₙ: the raw connected tuple sum, NO division. -/
noncomputable def ursellNumerator (n : ℕ) (z : Polymer N → ℝ) :
    ℝ :=
  ∑ δ : Fin n → Polymer N,
    ((ursellCoeff (fun m => (δ m).val) : ℤ) : ℝ)
      * ∏ i : Fin n, z (δ i)

theorem kpGasCoeff_eq_gasNumerator_div (n : ℕ)
    (z : Polymer N → ℝ) :
    kpGasCoeff n z
      = gasNumerator n z / ((Nat.factorial n : ℕ) : ℝ) := rfl

theorem kpSignedUnrootedCoeff_eq_ursellNumerator_div (k : ℕ)
    (z : Polymer N → ℝ) :
    kpSignedUnrootedCoeff k z
      = ursellNumerator k z / ((Nat.factorial k : ℕ) : ℝ) := rfl

/-! ## III-1.b — the root component of a SELECTED edge set
    (audit A1: taken in graphOfEdges E, not in the base graph) -/

/-- The vertices reachable from the root through SELECTED edges. -/
noncomputable def selectedRootComponent {m : ℕ} (r : Fin m)
    (E : Finset (OrderedEdge m)) : Finset (Fin m) :=
  Finset.univ.filter (fun v => (graphOfEdges E).Reachable r v)

theorem mem_selectedRootComponent_iff {m : ℕ} {r v : Fin m}
    {E : Finset (OrderedEdge m)} :
    v ∈ selectedRootComponent r E ↔ (graphOfEdges E).Reachable r v := by
  unfold selectedRootComponent
  simp [Finset.mem_filter]

theorem root_mem_selectedRootComponent {m : ℕ} (r : Fin m)
    (E : Finset (OrderedEdge m)) : r ∈ selectedRootComponent r E :=
  mem_selectedRootComponent_iff.mpr (SimpleGraph.Reachable.refl r)

/-- Closure: a selected step never leaves the component. -/
theorem selectedRootComponent_closed {m : ℕ} {r v w : Fin m}
    {E : Finset (OrderedEdge m)}
    (hv : v ∈ selectedRootComponent r E)
    (hadj : (graphOfEdges E).Adj v w) :
    w ∈ selectedRootComponent r E := by
  rw [mem_selectedRootComponent_iff] at hv ⊢
  exact hv.trans hadj.reachable

/-- **No-crossing (audit A2)**: a SELECTED edge has either both
    endpoints in the root component or both outside. AVAILABLE
    cross edges may exist — only selected ones cannot cross. -/
theorem selected_edge_mem_iff {m : ℕ} {r : Fin m}
    {E : Finset (OrderedEdge m)} {e : OrderedEdge m}
    (he : e ∈ E) :
    e.val.1 ∈ selectedRootComponent r E
      ↔ e.val.2 ∈ selectedRootComponent r E := by
  have hadj : (graphOfEdges E).Adj e.val.1 e.val.2 :=
    Or.inl ⟨e.property, he⟩
  constructor
  · intro h1
    exact selectedRootComponent_closed h1 hadj
  · intro h2
    exact selectedRootComponent_closed h2 hadj.symm

/-! ## III-1.c — the split and its reconstruction (audit A3,
    forward half: the split is exact and disjoint) -/

/-- Selected edges inside the root component. -/
noncomputable def rootEdges {m : ℕ} (r : Fin m)
    (E : Finset (OrderedEdge m)) : Finset (OrderedEdge m) :=
  E.filter (fun e => e.val.1 ∈ selectedRootComponent r E)

/-- Selected edges outside the root component. -/
noncomputable def restEdges {m : ℕ} (r : Fin m)
    (E : Finset (OrderedEdge m)) : Finset (OrderedEdge m) :=
  E.filter (fun e => ¬ e.val.1 ∈ selectedRootComponent r E)

theorem rootEdges_subset {m : ℕ} (r : Fin m)
    (E : Finset (OrderedEdge m)) : rootEdges r E ⊆ E :=
  Finset.filter_subset _ E

theorem restEdges_subset {m : ℕ} (r : Fin m)
    (E : Finset (OrderedEdge m)) : restEdges r E ⊆ E :=
  Finset.filter_subset _ E

theorem mem_rootEdges_both {m : ℕ} {r : Fin m}
    {E : Finset (OrderedEdge m)} {e : OrderedEdge m}
    (he : e ∈ rootEdges r E) :
    e.val.1 ∈ selectedRootComponent r E
      ∧ e.val.2 ∈ selectedRootComponent r E := by
  obtain ⟨heE, h1⟩ := Finset.mem_filter.mp he
  exact ⟨h1, (selected_edge_mem_iff heE).mp h1⟩

theorem mem_restEdges_both {m : ℕ} {r : Fin m}
    {E : Finset (OrderedEdge m)} {e : OrderedEdge m}
    (he : e ∈ restEdges r E) :
    ¬ e.val.1 ∈ selectedRootComponent r E
      ∧ ¬ e.val.2 ∈ selectedRootComponent r E := by
  obtain ⟨heE, h1⟩ := Finset.mem_filter.mp he
  exact ⟨h1, fun h2 => h1 ((selected_edge_mem_iff heE).mpr h2)⟩

theorem disjoint_rootEdges_restEdges {m : ℕ} (r : Fin m)
    (E : Finset (OrderedEdge m)) :
    Disjoint (rootEdges r E) (restEdges r E) := by
  refine Finset.disjoint_left.mpr ?_
  intro e he hne
  exact (Finset.mem_filter.mp hne).2 (Finset.mem_filter.mp he).2

theorem rootEdges_union_restEdges {m : ℕ} (r : Fin m)
    (E : Finset (OrderedEdge m)) :
    rootEdges r E ∪ restEdges r E = E := by
  unfold rootEdges restEdges
  exact Finset.filter_union_filter_neg_eq _ E

/-- Cardinality split (the sign (−1)^|E| will factor through it). -/
theorem card_rootEdges_add_card_restEdges {m : ℕ} (r : Fin m)
    (E : Finset (OrderedEdge m)) :
    (rootEdges r E).card + (restEdges r E).card = E.card := by
  rw [← Finset.card_union_of_disjoint
    (disjoint_rootEdges_restEdges r E),
    rootEdges_union_restEdges]

/-! ## III-1.d — walk confinement: reachability inside the
    component uses only root edges (the certificate that the
    root piece is CONNECTED on its vertex set) -/

private theorem walk_confined {m : ℕ} {r : Fin m}
    {E : Finset (OrderedEdge m)} :
    ∀ {u v : Fin m}, (graphOfEdges E).Walk u v →
      u ∈ selectedRootComponent r E →
      (graphOfEdges (rootEdges r E)).Reachable u v := by
  intro u v w
  induction w with
  | nil =>
    intro _
    exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj p ih =>
    intro ha
    have hb : b ∈ selectedRootComponent r E := selectedRootComponent_closed ha hadj
    have hadj' : (graphOfEdges (rootEdges r E)).Adj a b := by
      rcases hadj with ⟨hlt, hm⟩ | ⟨hlt, hm⟩
      · exact Or.inl ⟨hlt, Finset.mem_filter.mpr ⟨hm, ha⟩⟩
      · exact Or.inr ⟨hlt, Finset.mem_filter.mpr ⟨hm, hb⟩⟩
    exact hadj'.reachable.trans (ih hb)

/-- **The component is spanned by its own edges**: reachability
    from the root through E, restricted to component members, is
    achieved inside rootEdges — and conversely (audit A3 seed). -/
theorem reachable_rootEdges_iff {m : ℕ} {r v : Fin m}
    {E : Finset (OrderedEdge m)} :
    (graphOfEdges (rootEdges r E)).Reachable r v
      ↔ v ∈ selectedRootComponent r E := by
  constructor
  · intro h
    exact mem_selectedRootComponent_iff.mpr
      (SimpleGraph.Reachable.mono
        (graphOfEdges_mono (rootEdges_subset r E)) h)
  · intro hv
    obtain ⟨w⟩ := mem_selectedRootComponent_iff.mp hv
    exact walk_confined w (root_mem_selectedRootComponent r E)

/-- The root component of the root edges is the root component
    itself (idempotence — the fibering will need it). -/
theorem selectedRootComponent_rootEdges {m : ℕ} (r : Fin m)
    (E : Finset (OrderedEdge m)) :
    selectedRootComponent r (rootEdges r E) = selectedRootComponent r E := by
  ext v
  rw [mem_selectedRootComponent_iff, ← reachable_rootEdges_iff (E := E)]

end LatticeGauge
