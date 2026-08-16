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

/-! ## III-2.a — strictly monotone edge transport (the local
    order-iso route: ONE strictMono application per lt proof, no
    casts, no dependent transport — the architect's trava
    respected) -/

/-- Transport of an ordered edge along a strictly monotone map:
    order is preserved, so no Sym2 and no canonicalization. -/
def edgeUp {m k : ℕ} {f : Fin k → Fin m} (hf : StrictMono f) :
    OrderedEdge k → OrderedEdge m :=
  fun e => ⟨(f e.val.1, f e.val.2), hf e.property⟩

theorem edgeUp_injective {m k : ℕ} {f : Fin k → Fin m}
    (hf : StrictMono f) :
    Function.Injective (edgeUp hf) := by
  intro e₁ e₂ h
  have h1 : f e₁.val.1 = f e₂.val.1 :=
    congrArg (fun e : OrderedEdge m => e.val.1) h
  have h2 : f e₁.val.2 = f e₂.val.2 :=
    congrArg (fun e : OrderedEdge m => e.val.2) h
  exact Subtype.ext
    (Prod.ext (hf.injective h1) (hf.injective h2))

/-- **Adjacency transports exactly** along the edge image. -/
theorem graphOfEdges_image_adj {m k : ℕ} {f : Fin k → Fin m}
    (hf : StrictMono f) (F : Finset (OrderedEdge k))
    (i j : Fin k) :
    (graphOfEdges (F.image (edgeUp hf))).Adj (f i) (f j)
      ↔ (graphOfEdges F).Adj i j := by
  constructor
  · intro h
    rcases h with ⟨hlt, hm⟩ | ⟨hlt, hm⟩
    · obtain ⟨e', he'F, heq⟩ := Finset.mem_image.mp hm
      have hi : e'.val.1 = i := hf.injective
        (congrArg (fun e : OrderedEdge m => e.val.1) heq)
      have hj : e'.val.2 = j := hf.injective
        (congrArg (fun e : OrderedEdge m => e.val.2) heq)
      have hij : i < j := by
        have hp := e'.property
        rw [hi, hj] at hp
        exact hp
      have he : e' = (⟨(i, j), hij⟩ : OrderedEdge k) :=
        Subtype.ext (Prod.ext hi hj)
      exact Or.inl ⟨hij, he ▸ he'F⟩
    · obtain ⟨e', he'F, heq⟩ := Finset.mem_image.mp hm
      have hi : e'.val.1 = j := hf.injective
        (congrArg (fun e : OrderedEdge m => e.val.1) heq)
      have hj : e'.val.2 = i := hf.injective
        (congrArg (fun e : OrderedEdge m => e.val.2) heq)
      have hij : j < i := by
        have hp := e'.property
        rw [hi, hj] at hp
        exact hp
      have he : e' = (⟨(j, i), hij⟩ : OrderedEdge k) :=
        Subtype.ext (Prod.ext hi hj)
      exact Or.inr ⟨hij, he ▸ he'F⟩
  · intro h
    rcases h with ⟨hlt, hm⟩ | ⟨hlt, hm⟩
    · exact Or.inl ⟨hf hlt, Finset.mem_image_of_mem _ hm⟩
    · exact Or.inr ⟨hf hlt, Finset.mem_image_of_mem _ hm⟩

/-- Walk transport UP: reachability pushes along the image. -/
theorem reachable_image_of_reachable {m k : ℕ}
    {f : Fin k → Fin m} (hf : StrictMono f)
    {F : Finset (OrderedEdge k)} {i j : Fin k}
    (h : (graphOfEdges F).Reachable i j) :
    (graphOfEdges (F.image (edgeUp hf))).Reachable (f i) (f j) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj p ih =>
    exact (((graphOfEdges_image_adj hf F a b).mpr
      hadj).reachable).trans ih

/-- Walk transport DOWN: a walk in the image graph never leaves
    the range of `f` (every image edge has both endpoints there),
    so it pulls back step by step. -/
theorem reachable_of_reachable_image {m k : ℕ}
    {f : Fin k → Fin m} (hf : StrictMono f)
    {F : Finset (OrderedEdge k)} {i j : Fin k}
    (h : (graphOfEdges (F.image (edgeUp hf))).Reachable
      (f i) (f j)) :
    (graphOfEdges F).Reachable i j := by
  obtain ⟨w⟩ := h
  suffices haux : ∀ {u v : Fin m},
      (graphOfEdges (F.image (edgeUp hf))).Walk u v →
      ∀ {i j : Fin k}, u = f i → v = f j →
      (graphOfEdges F).Reachable i j by
    exact haux w rfl rfl
  intro u v w'
  induction w' with
  | nil =>
    intro i j hu hv
    have hij : i = j := hf.injective (hu.symm.trans hv)
    subst hij
    exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj p ih =>
    intro i j ha hc
    have hb : ∃ t : Fin k, b = f t := by
      rcases hadj with ⟨hlt, hm⟩ | ⟨hlt, hm⟩
      · obtain ⟨e', -, heq⟩ := Finset.mem_image.mp hm
        exact ⟨e'.val.2, (congrArg
          (fun e : OrderedEdge m => e.val.2) heq).symm⟩
      · obtain ⟨e', -, heq⟩ := Finset.mem_image.mp hm
        exact ⟨e'.val.1, (congrArg
          (fun e : OrderedEdge m => e.val.1) heq).symm⟩
    obtain ⟨t, rfl⟩ := hb
    have hstep : (graphOfEdges F).Adj i t := by
      have hadj' : (graphOfEdges
          (F.image (edgeUp hf))).Adj (f i) (f t) := ha ▸ hadj
      exact (graphOfEdges_image_adj hf F i t).mp hadj'
    exact hstep.reachable.trans (ih rfl hc)

/-- **Reachability transports exactly** (both walk lemmas glued). -/
theorem reachable_image_iff {m k : ℕ} {f : Fin k → Fin m}
    (hf : StrictMono f) (F : Finset (OrderedEdge k))
    (i j : Fin k) :
    (graphOfEdges (F.image (edgeUp hf))).Reachable (f i) (f j)
      ↔ (graphOfEdges F).Reachable i j :=
  ⟨reachable_of_reachable_image hf,
    reachable_image_of_reachable hf⟩

end LatticeGauge
