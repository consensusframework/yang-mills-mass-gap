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

/-! ## III-2.b — the canonical embedding of S and the certified
    connected piece (censused: Finset.orderIsoOfFin, Sort.lean:156;
    OrderIso.apply_symm_apply :784; Subtype.coe_lt_coe :1103).
    Stone 38 NOT imported: the order-iso route gives the equality
    directly, no permutation transport needed. -/

noncomputable def sEmb {m : ℕ} (S : Finset (Fin m)) {k : ℕ}
    (h : S.card = k) : Fin k → Fin m :=
  fun i => ((S.orderIsoOfFin h) i : Fin m)

theorem sEmb_strictMono {m : ℕ} {S : Finset (Fin m)} {k : ℕ}
    (h : S.card = k) : StrictMono (sEmb S h) :=
  fun _ _ hab =>
    Subtype.coe_lt_coe.mpr ((S.orderIsoOfFin h).strictMono hab)

theorem sEmb_mem {m : ℕ} {S : Finset (Fin m)} {k : ℕ}
    (h : S.card = k) (i : Fin k) : sEmb S h i ∈ S :=
  ((S.orderIsoOfFin h) i).property

theorem sEmb_symm_apply {m : ℕ} {S : Finset (Fin m)} {k : ℕ}
    (h : S.card = k) {v : Fin m} (hv : v ∈ S) :
    sEmb S h ((S.orderIsoOfFin h).symm ⟨v, hv⟩) = v := by
  unfold sEmb
  rw [OrderIso.apply_symm_apply]

/-- Incompatibility adjacency transports exactly along any
    injective reindexing of the tuple. -/
theorem incompat_comp_adj {k m : ℕ}
    (γ : Fin m → Finset (Site N × Dir × Dir))
    {f : Fin k → Fin m} (hinj : Function.Injective f)
    (i j : Fin k) :
    (polymerIncompatibilityGraph (N := N)
        (fun t => γ (f t))).Adj i j
      ↔ (polymerIncompatibilityGraph (N := N) γ).Adj
          (f i) (f j) := by
  constructor
  · rintro ⟨hne, hnc⟩
    exact ⟨fun hfe => hne (hinj hfe), hnc⟩
  · rintro ⟨hne, hnc⟩
    exact ⟨fun he => hne (congrArg f he), hnc⟩

/-- Available-edge correspondence across the embedding. -/
theorem edgeUp_mem_availableEdges_iff {k m : ℕ}
    (γ : Fin m → Finset (Site N × Dir × Dir))
    {f : Fin k → Fin m} (hf : StrictMono f)
    (e : OrderedEdge k) :
    edgeUp hf e ∈ availableEdges
        (polymerIncompatibilityGraph (N := N) γ)
      ↔ e ∈ availableEdges (polymerIncompatibilityGraph (N := N)
          (fun t => γ (f t))) := by
  rw [mem_availableEdges, mem_availableEdges]
  exact (incompat_comp_adj γ hf.injective e.val.1 e.val.2).symm

/-- Down/up roundtrip: an edge with both endpoints in S is the
    image of a unique k-side edge (uniqueness = injectivity). -/
theorem exists_edgeUp_eq {m : ℕ} {S : Finset (Fin m)} {k : ℕ}
    (h : S.card = k) {e' : OrderedEdge m}
    (h1 : e'.val.1 ∈ S) (h2 : e'.val.2 ∈ S) :
    ∃ e : OrderedEdge k, edgeUp (sEmb_strictMono h) e = e' := by
  have hlt : (S.orderIsoOfFin h).symm ⟨e'.val.1, h1⟩
      < (S.orderIsoOfFin h).symm ⟨e'.val.2, h2⟩ := by
    rw [← (S.orderIsoOfFin h).lt_iff_lt,
      OrderIso.apply_symm_apply, OrderIso.apply_symm_apply]
    exact Subtype.coe_lt_coe.mp e'.property
  refine ⟨⟨((S.orderIsoOfFin h).symm ⟨e'.val.1, h1⟩,
    (S.orderIsoOfFin h).symm ⟨e'.val.2, h2⟩), hlt⟩, ?_⟩
  exact Subtype.ext (Prod.ext
    (sEmb_symm_apply h h1) (sEmb_symm_apply h h2))

/-- Vertices reachable from an image vertex stay in the range. -/
theorem reachable_image_range {m k : ℕ} {f : Fin k → Fin m}
    (hf : StrictMono f) {F : Finset (OrderedEdge k)}
    {i : Fin k} {v : Fin m}
    (h : (graphOfEdges (F.image (edgeUp hf))).Reachable (f i) v) :
    ∃ t : Fin k, v = f t := by
  obtain ⟨w⟩ := h
  suffices haux : ∀ {u v : Fin m},
      (graphOfEdges (F.image (edgeUp hf))).Walk u v →
      (∃ s : Fin k, u = f s) → ∃ t : Fin k, v = f t by
    exact haux w ⟨i, rfl⟩
  intro u v w'
  induction w' with
  | nil => intro hu; exact hu
  | @cons a b c hadj p ih =>
    intro _
    refine ih ?_
    rcases hadj with ⟨hlt, hm⟩ | ⟨hlt, hm⟩
    · obtain ⟨e', -, heq⟩ := Finset.mem_image.mp hm
      exact ⟨e'.val.2, (congrArg
        (fun e : OrderedEdge m => e.val.2) heq).symm⟩
    · obtain ⟨e', -, heq⟩ := Finset.mem_image.mp hm
      exact ⟨e'.val.1, (congrArg
        (fun e : OrderedEdge m => e.val.1) heq).symm⟩

/-- Activity-product transport (fita item 7): the product over
    the canonical enumeration of S is the product over S. -/
theorem prod_sEmb {m : ℕ} {S : Finset (Fin m)} {k : ℕ}
    (h : S.card = k) (g : Fin m → ℝ) :
    (∏ i : Fin k, g (sEmb S h i)) = ∏ v ∈ S, g v := by
  refine Finset.prod_bij
    (i := fun (i : Fin k) _ => sEmb S h i) ?_ ?_ ?_ ?_
  · intro i _
    exact sEmb_mem h i
  · intro a _ b _ hab
    exact (sEmb_strictMono h).injective hab
  · intro v hv
    exact ⟨(S.orderIsoOfFin h).symm ⟨v, hv⟩, Finset.mem_univ _,
      sEmb_symm_apply h hv⟩
  · intro i _
    rfl

/-- The root pieces on S: selected edge sets inside S whose root
    component is EXACTLY S. -/
noncomputable def rootPieceSets {m : ℕ} (r : Fin m)
    (S : Finset (Fin m)) (G : SimpleGraph (Fin m)) :
    Finset (Finset (OrderedEdge m)) :=
  (availableEdges G).powerset.filter (fun E =>
    (∀ e ∈ E, e.val.1 ∈ S ∧ e.val.2 ∈ S)
      ∧ selectedRootComponent r E = S)

/-- **CAPSTONE III-2b**: the signed sum over the root pieces on S
    is EXACTLY the Ursell coefficient of the canonically
    relabelled local tuple — the extracted piece is certified as
    a `Fin k` object that ursellNumerator recognizes. -/
theorem sum_rootPieceSets_eq_ursellCoeff {m k : ℕ}
    {S : Finset (Fin m)} (h : S.card = k) {r : Fin m}
    (hr : r ∈ S) (γ : Fin m → Finset (Site N × Dir × Dir)) :
    (∑ E ∈ rootPieceSets r S
        (polymerIncompatibilityGraph (N := N) γ),
      (-1 : ℤ) ^ E.card)
      = ursellCoeff (N := N) (fun i => γ (sEmb S h i)) := by
  have hpos : 0 < k := h ▸ Finset.card_pos.mpr ⟨r, hr⟩
  have hf := sEmb_strictMono h
  have hfr0 : sEmb S h ((S.orderIsoOfFin h).symm ⟨r, hr⟩) = r :=
    sEmb_symm_apply h hr
  unfold ursellCoeff graphUrsellCoeff
  refine (Finset.sum_bij
    (i := fun F _ => F.image (edgeUp hf)) ?_ ?_ ?_ ?_).symm
  · intro F hF
    obtain ⟨hsub, hconn⟩ := mem_connectedSpanningEdgeSets.mp hF
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ?_, ?_, ?_⟩
    · intro e'' he''
      obtain ⟨e, heF, rfl⟩ := Finset.mem_image.mp he''
      exact (edgeUp_mem_availableEdges_iff γ hf e).mpr (hsub heF)
    · intro e'' he''
      obtain ⟨e, heF, rfl⟩ := Finset.mem_image.mp he''
      exact ⟨sEmb_mem h e.val.1, sEmb_mem h e.val.2⟩
    · ext v
      rw [mem_selectedRootComponent_iff]
      constructor
      · intro hv
        rw [← hfr0] at hv
        obtain ⟨t, rfl⟩ := reachable_image_range hf hv
        exact sEmb_mem h t
      · intro hv
        have hreach := hconn.preconnected
          ((S.orderIsoOfFin h).symm ⟨r, hr⟩)
          ((S.orderIsoOfFin h).symm ⟨v, hv⟩)
        have hup := reachable_image_of_reachable hf hreach
        rw [hfr0, sEmb_symm_apply h hv] at hup
        exact hup
  · intro F₁ _ F₂ _ hFF
    exact Finset.image_injective (edgeUp_injective hf) hFF
  · intro E hE
    obtain ⟨hpow, hin, hcomp⟩ := Finset.mem_filter.mp hE
    have hEsub := Finset.mem_powerset.mp hpow
    have himg : ((availableEdges (polymerIncompatibilityGraph
        (N := N) (fun t => γ (sEmb S h t)))).filter
          (fun e => edgeUp hf e ∈ E)).image (edgeUp hf) = E := by
      ext e'
      constructor
      · intro he'
        obtain ⟨e, heF, rfl⟩ := Finset.mem_image.mp he'
        exact (Finset.mem_filter.mp heF).2
      · intro he'
        obtain ⟨hv1, hv2⟩ := hin e' he'
        obtain ⟨e, rfl⟩ := exists_edgeUp_eq h hv1 hv2
        refine Finset.mem_image_of_mem _
          (Finset.mem_filter.mpr ⟨?_, he'⟩)
        exact (edgeUp_mem_availableEdges_iff γ hf e).mp
          (hEsub he')
    refine ⟨(availableEdges (polymerIncompatibilityGraph (N := N)
      (fun t => γ (sEmb S h t)))).filter
        (fun e => edgeUp hf e ∈ E), ?_, himg⟩
    refine mem_connectedSpanningEdgeSets.mpr
      ⟨Finset.filter_subset _ _, ?_⟩
    haveI : Nonempty (Fin k) := ⟨⟨0, hpos⟩⟩
    refine ⟨fun i j => ?_⟩
    have hi : sEmb S h i ∈ selectedRootComponent r E :=
      hcomp.symm ▸ sEmb_mem h i
    have hj : sEmb S h j ∈ selectedRootComponent r E :=
      hcomp.symm ▸ sEmb_mem h j
    rw [mem_selectedRootComponent_iff] at hi hj
    have hij := hi.symm.trans hj
    rw [← himg] at hij
    exact reachable_of_reachable_image hf hij
  · intro F _
    rw [Finset.card_image_of_injective _ (edgeUp_injective hf)]

/-! ## III-3.a — THE SEAM: converse reconstruction and the
    fixed-S edge-sum factorization (A3 closed both ways) -/

noncomputable def restPieceSets {m : ℕ} (S : Finset (Fin m))
    (G : SimpleGraph (Fin m)) : Finset (Finset (OrderedEdge m)) :=
  (availableEdges G).powerset.filter (fun E =>
    ∀ e ∈ E, ¬ e.val.1 ∈ S ∧ ¬ e.val.2 ∈ S)

noncomputable def globalEdgeFiber {m : ℕ} (r : Fin m)
    (S : Finset (Fin m)) (G : SimpleGraph (Fin m)) :
    Finset (Finset (OrderedEdge m)) :=
  (availableEdges G).powerset.filter (fun E =>
    selectedRootComponent r E = S)

private theorem union_walk_stays {m : ℕ} {S : Finset (Fin m)}
    {E₁ E₂ : Finset (OrderedEdge m)}
    (h1 : ∀ e ∈ E₁, e.val.1 ∈ S ∧ e.val.2 ∈ S)
    (h2 : ∀ e ∈ E₂, ¬ e.val.1 ∈ S ∧ ¬ e.val.2 ∈ S) :
    ∀ {u v : Fin m}, (graphOfEdges (E₁ ∪ E₂)).Walk u v →
      u ∈ S → v ∈ S ∧ (graphOfEdges E₁).Reachable u v := by
  intro u v w
  induction w with
  | nil =>
    intro hu
    exact ⟨hu, SimpleGraph.Reachable.refl _⟩
  | @cons a b c hadj p ih =>
    intro ha
    have hstep : b ∈ S ∧ (graphOfEdges E₁).Adj a b := by
      rcases hadj with ⟨hlt, hm⟩ | ⟨hlt, hm⟩
      · rcases Finset.mem_union.mp hm with hm1 | hm2
        · exact ⟨(h1 _ hm1).2, Or.inl ⟨hlt, hm1⟩⟩
        · exact absurd ha (h2 _ hm2).1
      · rcases Finset.mem_union.mp hm with hm1 | hm2
        · exact ⟨(h1 _ hm1).1, Or.inr ⟨hlt, hm1⟩⟩
        · exact absurd ha (h2 _ hm2).2
    obtain ⟨hres, hreach⟩ := ih hstep.1
    exact ⟨hres, hstep.2.reachable.trans hreach⟩

/-- **THE A3 CONVERSE**: a valid pair (connected root piece on S,
    arbitrary rest piece off S) reunites with root component
    EXACTLY S. -/
theorem selectedRootComponent_union {m : ℕ} {r : Fin m}
    {S : Finset (Fin m)} {G : SimpleGraph (Fin m)}
    {Eroot Erest : Finset (OrderedEdge m)}
    (hroot : Eroot ∈ rootPieceSets r S G)
    (hrest : Erest ∈ restPieceSets S G) :
    selectedRootComponent r (Eroot ∪ Erest) = S := by
  obtain ⟨-, hinR, hcompR⟩ := Finset.mem_filter.mp hroot
  obtain ⟨-, hinT⟩ := Finset.mem_filter.mp hrest
  have hrS : r ∈ S := hcompR ▸ root_mem_selectedRootComponent r Eroot
  ext v
  rw [mem_selectedRootComponent_iff]
  constructor
  · intro hv
    obtain ⟨w⟩ := hv
    exact (union_walk_stays hinR hinT w hrS).1
  · intro hv
    have hv' : v ∈ selectedRootComponent r Eroot :=
      hcompR.symm ▸ hv
    rw [mem_selectedRootComponent_iff] at hv'
    exact SimpleGraph.Reachable.mono
      (graphOfEdges_mono (fun e he => Finset.mem_union.mpr
        (Or.inl he))) hv'

/-- Roundtrip 1a: the split recovers the root piece. -/
theorem rootEdges_union_pieces {m : ℕ} {r : Fin m}
    {S : Finset (Fin m)} {G : SimpleGraph (Fin m)}
    {Eroot Erest : Finset (OrderedEdge m)}
    (hroot : Eroot ∈ rootPieceSets r S G)
    (hrest : Erest ∈ restPieceSets S G) :
    rootEdges r (Eroot ∪ Erest) = Eroot := by
  have hS := selectedRootComponent_union hroot hrest
  obtain ⟨-, hinR, -⟩ := Finset.mem_filter.mp hroot
  obtain ⟨-, hinT⟩ := Finset.mem_filter.mp hrest
  unfold rootEdges
  ext e
  rw [Finset.mem_filter, Finset.mem_union, hS]
  constructor
  · rintro ⟨hor | hor, h1⟩
    · exact hor
    · exact absurd h1 (hinT e hor).1
  · intro he
    exact ⟨Or.inl he, (hinR e he).1⟩

/-- Roundtrip 1b: the split recovers the rest piece. -/
theorem restEdges_union_pieces {m : ℕ} {r : Fin m}
    {S : Finset (Fin m)} {G : SimpleGraph (Fin m)}
    {Eroot Erest : Finset (OrderedEdge m)}
    (hroot : Eroot ∈ rootPieceSets r S G)
    (hrest : Erest ∈ restPieceSets S G) :
    restEdges r (Eroot ∪ Erest) = Erest := by
  have hS := selectedRootComponent_union hroot hrest
  obtain ⟨-, hinR, -⟩ := Finset.mem_filter.mp hroot
  obtain ⟨-, hinT⟩ := Finset.mem_filter.mp hrest
  unfold restEdges
  ext e
  rw [Finset.mem_filter, Finset.mem_union, hS]
  constructor
  · rintro ⟨hor | hor, h1⟩
    · exact absurd (hinR e hor).1 h1
    · exact hor
  · intro he
    exact ⟨Or.inr he, (hinT e he).1⟩

/-- Extraction membership (root side; roundtrip 2 is
    `rootEdges_union_restEdges`, Gate III-1). -/
theorem rootEdges_mem_rootPieceSets {m : ℕ} {r : Fin m}
    {S : Finset (Fin m)} {G : SimpleGraph (Fin m)}
    {E : Finset (OrderedEdge m)}
    (hE : E ∈ globalEdgeFiber r S G) :
    rootEdges r E ∈ rootPieceSets r S G := by
  obtain ⟨hpow, hcomp⟩ := Finset.mem_filter.mp hE
  refine Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (fun e he =>
      Finset.mem_powerset.mp hpow (rootEdges_subset r E he)),
      ?_, ?_⟩
  · intro e he
    have hb := mem_rootEdges_both he
    rw [hcomp] at hb
    exact hb
  · rw [selectedRootComponent_rootEdges, hcomp]

theorem restEdges_mem_restPieceSets {m : ℕ} {r : Fin m}
    {S : Finset (Fin m)} {G : SimpleGraph (Fin m)}
    {E : Finset (OrderedEdge m)}
    (hE : E ∈ globalEdgeFiber r S G) :
    restEdges r E ∈ restPieceSets S G := by
  obtain ⟨hpow, hcomp⟩ := Finset.mem_filter.mp hE
  refine Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (fun e he =>
      Finset.mem_powerset.mp hpow (restEdges_subset r E he)),
      ?_⟩
  intro e he
  have hb := mem_restEdges_both he
  rw [hcomp] at hb
  exact hb

/-- Sign factorization (named, in ℤ, as ordered). -/
theorem neg_one_pow_card_disjUnion {α : Type*} [DecidableEq α]
    {s t : Finset α} (hd : Disjoint s t) :
    (-1 : ℤ) ^ (s ∪ t).card
      = (-1 : ℤ) ^ s.card * (-1 : ℤ) ^ t.card := by
  rw [Finset.card_union_of_disjoint hd, pow_add]

theorem disjoint_pieceSets {m : ℕ} {r : Fin m}
    {S : Finset (Fin m)} {G : SimpleGraph (Fin m)}
    {Eroot Erest : Finset (OrderedEdge m)}
    (hroot : Eroot ∈ rootPieceSets r S G)
    (hrest : Erest ∈ restPieceSets S G) :
    Disjoint Eroot Erest := by
  obtain ⟨-, hinR, -⟩ := Finset.mem_filter.mp hroot
  obtain ⟨-, hinT⟩ := Finset.mem_filter.mp hrest
  exact Finset.disjoint_left.mpr
    (fun e he1 he2 => (hinT e he2).1 (hinR e he1).1)

/-- **Fixed-S edge-sum factorization**: the global fiber is the
    product of the two piece sums (the fibering sum_bij, both
    roundtrips consumed). -/
theorem sum_globalEdgeFiber_eq_mul {m : ℕ} (r : Fin m)
    (S : Finset (Fin m)) (G : SimpleGraph (Fin m)) :
    (∑ E ∈ globalEdgeFiber r S G, (-1 : ℤ) ^ E.card)
      = (∑ E1 ∈ rootPieceSets r S G, (-1 : ℤ) ^ E1.card)
        * (∑ E2 ∈ restPieceSets S G, (-1 : ℤ) ^ E2.card) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product'
    (f := fun E1 E2 : Finset (OrderedEdge m) =>
      (-1 : ℤ) ^ E1.card * (-1 : ℤ) ^ E2.card)]
  refine (Finset.sum_bij
    (i := fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_).symm
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.union_subset
        (Finset.mem_powerset.mp (Finset.mem_filter.mp h1).1)
        (Finset.mem_powerset.mp (Finset.mem_filter.mp h2).1)),
        selectedRootComponent_union h1 h2⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    obtain ⟨h11, h12⟩ := Finset.mem_product.mp hp₁
    obtain ⟨h21, h22⟩ := Finset.mem_product.mp hp₂
    have heq' : p₁.1 ∪ p₁.2 = p₂.1 ∪ p₂.2 := heq
    have e1 : p₁.1 = p₂.1 := by
      rw [← rootEdges_union_pieces h11 h12,
        ← rootEdges_union_pieces h21 h22, heq']
    have e2 : p₁.2 = p₂.2 := by
      rw [← restEdges_union_pieces h11 h12,
        ← restEdges_union_pieces h21 h22, heq']
    exact Prod.ext e1 e2
  · intro E hE
    exact ⟨(rootEdges r E, restEdges r E),
      Finset.mem_product.mpr
        ⟨rootEdges_mem_rootPieceSets hE,
          restEdges_mem_restPieceSets hE⟩,
      rootEdges_union_restEdges r E⟩
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    exact (neg_one_pow_card_disjUnion (disjoint_pieceSets h1 h2)).symm

/-- **Root factor identified (III-2b consumed)**: for a tuple γ
    and S ∋ r with the canonical enumeration, the fixed-S global
    fiber factorizes as Ursell(local tuple) × rest signed sum.
    The rest is NOT relabelled — deliberately (architect order). -/
theorem sum_globalEdgeFiber_eq_ursell_mul {m k : ℕ}
    {S : Finset (Fin m)} (h : S.card = k) {r : Fin m}
    (hr : r ∈ S) (γ : Fin m → Finset (Site N × Dir × Dir)) :
    (∑ E ∈ globalEdgeFiber r S
        (polymerIncompatibilityGraph (N := N) γ),
      (-1 : ℤ) ^ E.card)
      = ursellCoeff (N := N) (fun i => γ (sEmb S h i))
        * (∑ E2 ∈ restPieceSets S
            (polymerIncompatibilityGraph (N := N) γ),
          (-1 : ℤ) ^ E2.card) := by
  rw [sum_globalEdgeFiber_eq_mul,
    sum_rootPieceSets_eq_ursellCoeff h hr γ]

/-! ## III-3.b — the complement, the tuple split, and the fixed-S
    contribution B_|S|·A_|T| (numerators only — no factorial, no
    choose; l = 0 works with NO positivity hypothesis) -/

theorem mem_compl_iff_not_mem {m : ℕ} {S : Finset (Fin m)}
    {v : Fin m} : v ∈ Sᶜ ↔ ¬ v ∈ S := Finset.mem_compl

/-- Rest signed sum = the ALL-edge coefficient of the canonically
    relabelled complement tuple (mirror of III-2b, easier: no
    connectivity filter on either side). -/
theorem sum_restPieceSets_eq_graphAllEdgeCoeff {m l : ℕ}
    {S : Finset (Fin m)} (ht : (Sᶜ : Finset (Fin m)).card = l)
    (γ : Fin m → Finset (Site N × Dir × Dir)) :
    (∑ E ∈ restPieceSets S
        (polymerIncompatibilityGraph (N := N) γ),
      (-1 : ℤ) ^ E.card)
      = graphAllEdgeCoeff (polymerIncompatibilityGraph (N := N)
          (fun i => γ (sEmb Sᶜ ht i))) := by
  have hf := sEmb_strictMono ht
  unfold graphAllEdgeCoeff
  refine (Finset.sum_bij
    (i := fun F _ => F.image (edgeUp hf)) ?_ ?_ ?_ ?_).symm
  · intro F hF
    have hsub := Finset.mem_powerset.mp hF
    refine Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro e'' he''
      obtain ⟨e, heF, rfl⟩ := Finset.mem_image.mp he''
      exact (edgeUp_mem_availableEdges_iff γ hf e).mpr (hsub heF)
    · intro e'' he''
      obtain ⟨e, heF, rfl⟩ := Finset.mem_image.mp he''
      exact ⟨Finset.mem_compl.mp (sEmb_mem ht e.val.1),
        Finset.mem_compl.mp (sEmb_mem ht e.val.2)⟩
  · intro F₁ _ F₂ _ hFF
    exact Finset.image_injective (edgeUp_injective hf) hFF
  · intro E hE
    obtain ⟨hpow, hin⟩ := Finset.mem_filter.mp hE
    have hEsub := Finset.mem_powerset.mp hpow
    have himg : ((availableEdges (polymerIncompatibilityGraph
        (N := N) (fun t => γ (sEmb Sᶜ ht t)))).filter
          (fun e => edgeUp hf e ∈ E)).image (edgeUp hf) = E := by
      ext e'
      constructor
      · intro he'
        obtain ⟨e, heF, rfl⟩ := Finset.mem_image.mp he'
        exact (Finset.mem_filter.mp heF).2
      · intro he'
        obtain ⟨hv1, hv2⟩ := hin e' he'
        obtain ⟨e, rfl⟩ := exists_edgeUp_eq ht
          (Finset.mem_compl.mpr hv1) (Finset.mem_compl.mpr hv2)
        refine Finset.mem_image_of_mem _
          (Finset.mem_filter.mpr ⟨?_, he'⟩)
        exact (edgeUp_mem_availableEdges_iff γ hf e).mp
          (hEsub he')
    exact ⟨_, Finset.mem_powerset.mpr
      (Finset.filter_subset _ _), himg⟩
  · intro F _
    rw [Finset.card_image_of_injective _ (edgeUp_injective hf)]

/-- Fixed-S FULL edge factorization: Ursell(S) × allEdge(Sᶜ). -/
theorem sum_globalEdgeFiber_eq_ursell_mul_allEdge {m k l : ℕ}
    {S : Finset (Fin m)} (hs : S.card = k)
    (ht : (Sᶜ : Finset (Fin m)).card = l) {r : Fin m}
    (hr : r ∈ S) (γ : Fin m → Finset (Site N × Dir × Dir)) :
    (∑ E ∈ globalEdgeFiber r S
        (polymerIncompatibilityGraph (N := N) γ),
      (-1 : ℤ) ^ E.card)
      = ursellCoeff (N := N) (fun i => γ (sEmb S hs i))
        * graphAllEdgeCoeff (polymerIncompatibilityGraph
            (N := N) (fun i => γ (sEmb Sᶜ ht i))) := by
  rw [sum_globalEdgeFiber_eq_ursell_mul hs hr γ,
    sum_restPieceSets_eq_graphAllEdgeCoeff ht γ]

/-! ### the tuple split (canonical inverses from the order-isos) -/

noncomputable def splitTuple {m k l : ℕ} {α : Type*}
    {S : Finset (Fin m)} (hs : S.card = k)
    (ht : (Sᶜ : Finset (Fin m)).card = l) (δ : Fin m → α) :
    (Fin k → α) × (Fin l → α) :=
  (fun i => δ (sEmb S hs i), fun i => δ (sEmb Sᶜ ht i))

noncomputable def mergeTuple {m k l : ℕ} {α : Type*}
    {S : Finset (Fin m)} (hs : S.card = k)
    (ht : (Sᶜ : Finset (Fin m)).card = l)
    (p : (Fin k → α) × (Fin l → α)) : Fin m → α :=
  fun v =>
    if hv : v ∈ S then
      p.1 ((S.orderIsoOfFin hs).symm ⟨v, hv⟩)
    else
      p.2 ((Sᶜ.orderIsoOfFin ht).symm
        ⟨v, Finset.mem_compl.mpr hv⟩)

theorem splitTuple_mergeTuple {m k l : ℕ} {α : Type*}
    {S : Finset (Fin m)} (hs : S.card = k)
    (ht : (Sᶜ : Finset (Fin m)).card = l)
    (p : (Fin k → α) × (Fin l → α)) :
    splitTuple hs ht (mergeTuple hs ht p) = p := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp only [splitTuple, mergeTuple, dif_pos (sEmb_mem hs i)]
    have h1 : (⟨sEmb S hs i, sEmb_mem hs i⟩ : ↥S)
        = (S.orderIsoOfFin hs) i := Subtype.ext rfl
    rw [h1, OrderIso.symm_apply_apply]
  · have hns : ¬ sEmb Sᶜ ht i ∈ S :=
      Finset.mem_compl.mp (sEmb_mem ht i)
    simp only [splitTuple, mergeTuple, dif_neg hns]
    have h1 : (⟨sEmb Sᶜ ht i, Finset.mem_compl.mpr hns⟩ : ↥Sᶜ)
        = (Sᶜ.orderIsoOfFin ht) i := Subtype.ext rfl
    rw [h1, OrderIso.symm_apply_apply]

theorem mergeTuple_splitTuple {m k l : ℕ} {α : Type*}
    {S : Finset (Fin m)} (hs : S.card = k)
    (ht : (Sᶜ : Finset (Fin m)).card = l) (δ : Fin m → α) :
    mergeTuple hs ht (splitTuple hs ht δ) = δ := by
  funext v
  by_cases hv : v ∈ S
  · simp only [splitTuple, mergeTuple, dif_pos hv,
      sEmb_symm_apply hs hv]
  · simp only [splitTuple, mergeTuple, dif_neg hv,
      sEmb_symm_apply ht (Finset.mem_compl.mpr hv)]

theorem splitTuple_bijective {m k l : ℕ} {α : Type*}
    {S : Finset (Fin m)} (hs : S.card = k)
    (ht : (Sᶜ : Finset (Fin m)).card = l) :
    Function.Bijective (splitTuple (α := α) hs ht) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨mergeTuple hs ht,
      fun δ => mergeTuple_splitTuple hs ht δ,
      fun p => splitTuple_mergeTuple hs ht p⟩

/-- Global activity product factorization (no manual index
    juggling: `prod_mul_prod_compl` + the two `prod_sEmb`). -/
theorem prod_split_global {m k l : ℕ} {S : Finset (Fin m)}
    (hs : S.card = k) (ht : (Sᶜ : Finset (Fin m)).card = l)
    (g : Fin m → ℝ) :
    (∏ v : Fin m, g v)
      = (∏ i : Fin k, g (sEmb S hs i))
        * (∏ i : Fin l, g (sEmb Sᶜ ht i)) := by
  rw [prod_sEmb hs g, prod_sEmb ht g,
    Finset.prod_mul_prod_compl S g]

/-- **CAPSTONE III-3b — the fixed-S tuple contribution**: for
    0 ∈ S, |S| = k, |Sᶜ| = l, the tuple sum of the fixed-S edge
    fiber weighted by activities is EXACTLY B-numerator(k) times
    A-numerator(l). No factorial; l = 0 allowed (this is j = n:
    the empty rest carries gasNumerator 0 = A₀-numerator = 1
    through empty sums/products with no positivity hypothesis). -/
theorem fixedS_tuple_contribution {m k l : ℕ} [NeZero m]
    {S : Finset (Fin m)} (hs : S.card = k)
    (ht : (Sᶜ : Finset (Fin m)).card = l)
    (h0 : (0 : Fin m) ∈ S) (z : Polymer N → ℝ) :
    (∑ δ : Fin m → Polymer N,
      ((∑ E ∈ globalEdgeFiber 0 S
          (polymerIncompatibilityGraph (N := N)
            (fun t => (δ t).val)),
        (-1 : ℤ) ^ E.card : ℤ) : ℝ)
        * ∏ i : Fin m, z (δ i))
      = ursellNumerator k z * gasNumerator l z := by
  have hstep : ∀ δ : Fin m → Polymer N,
      ((∑ E ∈ globalEdgeFiber 0 S
          (polymerIncompatibilityGraph (N := N)
            (fun t => (δ t).val)),
        (-1 : ℤ) ^ E.card : ℤ) : ℝ)
        * ∏ i : Fin m, z (δ i)
      = (((ursellCoeff (N := N)
            (fun i => (δ (sEmb S hs i)).val) : ℤ) : ℝ)
          * ∏ i : Fin k, z (δ (sEmb S hs i)))
        * (((graphAllEdgeCoeff (polymerIncompatibilityGraph
            (N := N) (fun i => (δ (sEmb Sᶜ ht i)).val)) : ℤ) : ℝ)
          * ∏ i : Fin l, z (δ (sEmb Sᶜ ht i))) := by
    intro δ
    rw [sum_globalEdgeFiber_eq_ursell_mul_allEdge hs ht h0
      (fun t => (δ t).val),
      prod_split_global hs ht (fun v => z (δ v))]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun δ _ => hstep δ)]
  refine Eq.trans (Fintype.sum_bijective (splitTuple hs ht)
    (splitTuple_bijective hs ht) _
    (fun p : (Fin k → Polymer N) × (Fin l → Polymer N) =>
      (((ursellCoeff (N := N)
          (fun i => (p.1 i).val) : ℤ) : ℝ)
        * ∏ i : Fin k, z (p.1 i))
      * (((graphAllEdgeCoeff (polymerIncompatibilityGraph
          (N := N) (fun i => (p.2 i).val)) : ℤ) : ℝ)
        * ∏ i : Fin l, z (p.2 i)))
    (fun δ => rfl)) ?_
  refine Eq.trans (Fintype.sum_prod_type
    (f := fun p : (Fin k → Polymer N) × (Fin l → Polymer N) =>
      (((ursellCoeff (N := N)
          (fun i => (p.1 i).val) : ℤ) : ℝ)
        * ∏ i : Fin k, z (p.1 i))
      * (((graphAllEdgeCoeff (polymerIncompatibilityGraph
          (N := N) (fun i => (p.2 i).val)) : ℤ) : ℝ)
        * ∏ i : Fin l, z (p.2 i)))) ?_
  show (∑ x : Fin k → Polymer N, ∑ y : Fin l → Polymer N,
      (((ursellCoeff (N := N)
          (fun i => (x i).val) : ℤ) : ℝ)
        * ∏ i : Fin k, z (x i))
      * (((graphAllEdgeCoeff (polymerIncompatibilityGraph
          (N := N) (fun i => (y i).val)) : ℤ) : ℝ)
        * ∏ i : Fin l, z (y i)))
    = ursellNumerator k z * gasNumerator l z
  rw [← Finset.sum_mul_sum]
  rfl

/-! ## III-3.c — counting the root sets and THE NUMERATOR
    RECURRENCE (no (j+1) here: that factor is born only from the
    factorials in III-4 — a (j+1) in THIS recurrence would mean
    the root was counted twice) -/

/-- All-edge fibration by root component: the powerset sum
    regroups over the possible components of the root. -/
theorem graphAllEdgeCoeff_fiber_rootComponent {n : ℕ}
    (γ : Fin (n + 1) → Finset (Site N × Dir × Dir)) :
    graphAllEdgeCoeff (polymerIncompatibilityGraph (N := N) γ)
      = ∑ S ∈ Finset.univ.filter
          (fun S : Finset (Fin (n + 1)) =>
            (0 : Fin (n + 1)) ∈ S),
          ∑ E ∈ globalEdgeFiber 0 S
            (polymerIncompatibilityGraph (N := N) γ),
            (-1 : ℤ) ^ E.card := by
  unfold graphAllEdgeCoeff globalEdgeFiber
  refine (Finset.sum_fiberwise_of_maps_to ?_
    (fun E : Finset (OrderedEdge (n + 1)) =>
      (-1 : ℤ) ^ E.card)).symm
  intro E _
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, root_mem_selectedRootComponent 0 E⟩

/-- Count of the root sets: subsets of Fin (n+1) of cardinality
    j+1 containing the root are counted by choose n j — the
    binomial counts only the OTHER vertices (audit A4). -/
theorem card_rootSets_eq_choose {n j : ℕ} :
    ((Finset.univ.filter (fun S : Finset (Fin (n + 1)) =>
        (0 : Fin (n + 1)) ∈ S)).filter
          (fun S => S.card - 1 = j)).card
      = Nat.choose n j := by
  have hbij : ((Finset.univ.filter
      (fun S : Finset (Fin (n + 1)) =>
        (0 : Fin (n + 1)) ∈ S)).filter
          (fun S => S.card - 1 = j)).card
      = (Finset.powersetCard j
          ((Finset.univ : Finset (Fin (n + 1))).erase 0)).card := by
    refine Finset.card_bij (i := fun S _ => S.erase 0) ?_ ?_ ?_
    · intro S hS
      obtain ⟨hSm, hcard1⟩ := Finset.mem_filter.mp hS
      have h0S := (Finset.mem_filter.mp hSm).2
      refine Finset.mem_powersetCard.mpr
        ⟨Finset.erase_subset_erase 0 (Finset.subset_univ S), ?_⟩
      rw [Finset.card_erase_of_mem h0S]
      exact hcard1
    · intro S₁ h₁ S₂ h₂ heq
      have h01 := (Finset.mem_filter.mp
        (Finset.mem_filter.mp h₁).1).2
      have h02 := (Finset.mem_filter.mp
        (Finset.mem_filter.mp h₂).1).2
      have heq' : S₁.erase 0 = S₂.erase 0 := heq
      rw [← Finset.insert_erase h01, ← Finset.insert_erase h02,
        heq']
    · intro T hT
      obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hT
      have h0T : (0 : Fin (n + 1)) ∉ T :=
        fun h => (Finset.mem_erase.mp (hTsub h)).1 rfl
      refine ⟨insert 0 T, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, Finset.mem_insert_self 0 T⟩, ?_⟩,
        Finset.erase_insert h0T⟩
      rw [Finset.card_insert_of_not_mem h0T, hTcard]
      omega
  rw [hbij, Finset.card_powersetCard,
    Finset.card_erase_of_mem (Finset.mem_univ 0),
    Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]

/-- **CAPSTONE III-3c — THE NUMERATOR RECURRENCE** (audited: j
    runs 0..n; j = n carries the Fin 0 rest; choose n j appears
    ONCE; NO (j+1) factor — that is factorial business, III-4). -/
theorem gasNumerator_succ_recurrence (n : ℕ)
    (z : Polymer N → ℝ) :
    gasNumerator (N := N) (n + 1) z
      = ∑ j ∈ Finset.range (n + 1),
          ((Nat.choose n j : ℕ) : ℝ)
            * ursellNumerator (j + 1) z
            * gasNumerator (n - j) z := by
  have hmain : gasNumerator (N := N) (n + 1) z
      = ∑ S ∈ Finset.univ.filter
          (fun S : Finset (Fin (n + 1)) =>
            (0 : Fin (n + 1)) ∈ S),
          ursellNumerator S.card z * gasNumerator Sᶜ.card z := by
    have h1 : gasNumerator (N := N) (n + 1) z
        = ∑ δ : Fin (n + 1) → Polymer N,
            ∑ S ∈ Finset.univ.filter
              (fun S : Finset (Fin (n + 1)) =>
                (0 : Fin (n + 1)) ∈ S),
              ((∑ E ∈ globalEdgeFiber 0 S
                  (polymerIncompatibilityGraph (N := N)
                    (fun t => (δ t).val)),
                (-1 : ℤ) ^ E.card : ℤ) : ℝ)
                * ∏ i : Fin (n + 1), z (δ i) := by
      unfold gasNumerator
      refine Finset.sum_congr rfl (fun δ _ => ?_)
      rw [graphAllEdgeCoeff_fiber_rootComponent
        (fun t => (δ t).val), Int.cast_sum, Finset.sum_mul]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun S hSmem => ?_)
    exact fixedS_tuple_contribution rfl rfl
      (Finset.mem_filter.mp hSmem).2 z
  rw [hmain]
  have hmapsJ : ∀ S ∈ Finset.univ.filter
      (fun S : Finset (Fin (n + 1)) =>
        (0 : Fin (n + 1)) ∈ S),
      S.card - 1 ∈ Finset.range (n + 1) := by
    intro S hSmem
    have hle : S.card ≤ n + 1 := by
      have h := Finset.card_le_univ S
      rwa [Finset.card_univ, Fintype.card_fin] at h
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmapsJ
    (fun S => ursellNumerator S.card z
      * gasNumerator Sᶜ.card z)]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hconst : ∀ S ∈ (Finset.univ.filter
      (fun S : Finset (Fin (n + 1)) =>
        (0 : Fin (n + 1)) ∈ S)).filter
          (fun S => S.card - 1 = j),
      ursellNumerator (N := N) S.card z
        * gasNumerator Sᶜ.card z
      = ursellNumerator (j + 1) z * gasNumerator (n - j) z := by
    intro S hSf
    obtain ⟨hSm, hcard1⟩ := Finset.mem_filter.mp hSf
    have h0S := (Finset.mem_filter.mp hSm).2
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨0, h0S⟩
    have hcard : S.card = j + 1 := by omega
    have hcompl : (Sᶜ : Finset (Fin (n + 1))).card = n - j := by
      rw [Finset.card_compl, Fintype.card_fin, hcard]
      omega
    rw [hcard, hcompl]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const,
    card_rootSets_eq_choose, nsmul_eq_mul]
  ring

/-- Sanity n = 0: the singleton universe — the whole graph IS the
    root component, the rest is Fin 0. -/
theorem gasNumerator_one_eq (z : Polymer N → ℝ) :
    gasNumerator (N := N) 1 z
      = ursellNumerator 1 z * gasNumerator 0 z := by
  rw [gasNumerator_succ_recurrence 0 z]
  simp [Finset.sum_range_one]

end LatticeGauge
