/-
LatticeGauge/KPRootedTransport.lean — stone 47 (b-iiB), GATE IV-A.

ROOTED RELABELING BETWEEN FINITE LINEAR TYPES (architecture:
Sol/GPT-5.6; execution: Fable). The genuinely new infrastructure of
Gate IV: rooted tree sums over an arbitrary finite LINEARLY ORDERED
type V (the two consumers are ↥B — a subtype of Fin n, inheriting
its order — and Fin (m+1); the linear order is what OrderedEdge
needs, and the stone-38 canonical-edge machinery absorbs arbitrary
NON-monotone equivalences, generalized here verbatim from
Equiv.Perm (Fin M) to σ : V ≃ V'). DESIGN KEY: the tree universe
`connTreesOn` is defined by CONNECTEDNESS + the CARDINAL CONDITION
|E| + 1 = |V| — never by IsTree on a generic type — so no acyclicity
ever needs transporting (connectivity rides the graph Iso as in
stone 38; cardinality rides card_map); the identification with
`spanningTreeEdgeSets ⊤` at the Fin end (Gate IV-B) will use the
stone-40b cardinal converse, where it lives. The rooted weight
excludes the root activity (∏ over univ.erase r); the CAPSTONE
`rootedTreeSumOn_congr` transports the entire rooted sum along any
σ : V ≃ V' with σ r = r', by simultaneous reindexation of
assignments (δ ↦ δ ∘ σ.symm) and edge sets (the canonical relabel
map, an embedding with explicit two-sided inverse). Sanities: refl,
composition, and the unit type (sum = 1, empty products). NOT here:
no fixedRootBlockSum, no identification with rootedTreeSum m, no
F(B), no factorials, no partitions, no recurrence (IV-B/IV-C and
beyond). NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.UrsellCoefficients
import LatticeGauge.PolymerTreeBound
import LatticeGauge.KPCoefficients
import LatticeGauge.RootDecomposition
import LatticeGauge.KPEnumerations
import LatticeGauge.KPOrderedDecomposition
import LatticeGauge.KPWeightFactorization

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {V' : Type*} [Fintype V'] [LinearOrder V']

/-! ## Ordered edges and generated graphs over a linear type -/

def OrderedEdgeOn (V : Type*) [LinearOrder V] := {e : V × V // e.1 < e.2}

noncomputable instance : Fintype (OrderedEdgeOn V) := by
  unfold OrderedEdgeOn
  infer_instance

def graphOfEdgesOn (E : Finset (OrderedEdgeOn V)) : SimpleGraph V where
  Adj i j :=
    (∃ h : i < j, (⟨(i, j), h⟩ : OrderedEdgeOn V) ∈ E) ∨
    (∃ h : j < i, (⟨(j, i), h⟩ : OrderedEdgeOn V) ∈ E)
  symm := by
    intro i j h
    rcases h with ⟨hlt, hm⟩ | ⟨hlt, hm⟩
    · exact Or.inr ⟨hlt, hm⟩
    · exact Or.inl ⟨hlt, hm⟩
  loopless := by
    intro i h
    rcases h with ⟨hlt, _⟩ | ⟨hlt, _⟩ <;> exact absurd hlt (lt_irrefl i)

def canonicalOrderedEdgeOn (i j : V) (h : i ≠ j) : OrderedEdgeOn V :=
  if hlt : i < j then ⟨(i, j), hlt⟩
  else ⟨(j, i), (h.lt_or_lt.resolve_left hlt)⟩

theorem canonicalOrderedEdgeOn_of_lt {i j : V} (h' : i < j)
    (h : i ≠ j) :
    canonicalOrderedEdgeOn i j h = ⟨(i, j), h'⟩ := by
  unfold canonicalOrderedEdgeOn
  rw [dif_pos h']

theorem canonicalOrderedEdgeOn_of_gt {i j : V} (h' : j < i)
    (h : i ≠ j) :
    canonicalOrderedEdgeOn i j h = ⟨(j, i), h'⟩ := by
  unfold canonicalOrderedEdgeOn
  rw [dif_neg (lt_asymm h')]

theorem graphOfEdgesOn_adj_iff_canonical
    {E : Finset (OrderedEdgeOn V)} {i j : V} (h : i ≠ j) :
    (graphOfEdgesOn E).Adj i j ↔ canonicalOrderedEdgeOn i j h ∈ E := by
  rcases h.lt_or_lt with h' | h'
  · rw [canonicalOrderedEdgeOn_of_lt h' h]
    constructor
    · rintro (⟨hlt, hm⟩ | ⟨hlt, hm⟩)
      · exact hm
      · exact absurd h' (lt_asymm hlt)
    · intro hm
      exact Or.inl ⟨h', hm⟩
  · rw [canonicalOrderedEdgeOn_of_gt h' h]
    constructor
    · rintro (⟨hlt, hm⟩ | ⟨hlt, hm⟩)
      · exact absurd h' (lt_asymm hlt)
      · exact hm
    · intro hm
      exact Or.inr ⟨h', hm⟩

/-! ## The canonical relabel along an equivalence -/

def relabelFunOn (σ : V ≃ V') (ed : OrderedEdgeOn V) :
    OrderedEdgeOn V' :=
  canonicalOrderedEdgeOn (σ ed.val.1) (σ ed.val.2)
    (fun h => (ne_of_lt ed.2) (σ.injective h))

theorem relabelFunOn_symm_cancel (σ : V ≃ V')
    (ed : OrderedEdgeOn V) :
    relabelFunOn σ.symm (relabelFunOn σ ed) = ed := by
  obtain ⟨⟨a, b⟩, hab⟩ := ed
  unfold relabelFunOn
  rcases lt_or_gt_of_ne
      (fun h => (ne_of_lt hab) (σ.injective h) :
        σ a ≠ σ b) with h' | h'
  · rw [canonicalOrderedEdgeOn_of_lt h']
    have h2 : σ.symm (σ a) ≠ σ.symm (σ b) := by
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact ne_of_lt hab
    show canonicalOrderedEdgeOn (σ.symm (σ a)) (σ.symm (σ b)) _ = _
    have ha := σ.symm_apply_apply a
    have hb := σ.symm_apply_apply b
    have hlt : σ.symm (σ a) < σ.symm (σ b) := by
      rw [ha, hb]
      exact hab
    rw [canonicalOrderedEdgeOn_of_lt hlt]
    exact Subtype.ext (by rw [Prod.mk.injEq]; exact ⟨ha, hb⟩)
  · rw [canonicalOrderedEdgeOn_of_gt h']
    show canonicalOrderedEdgeOn (σ.symm (σ b)) (σ.symm (σ a)) _ = _
    have ha := σ.symm_apply_apply a
    have hb := σ.symm_apply_apply b
    have hlt : σ.symm (σ a) < σ.symm (σ b) := by
      rw [ha, hb]
      exact hab
    rw [canonicalOrderedEdgeOn_of_gt hlt]
    exact Subtype.ext (by rw [Prod.mk.injEq]; exact ⟨ha, hb⟩)

theorem relabelFunOn_injective (σ : V ≃ V') :
    Function.Injective (relabelFunOn σ) := by
  intro e₁ e₂ h
  have := congrArg (relabelFunOn σ.symm) h
  rwa [relabelFunOn_symm_cancel, relabelFunOn_symm_cancel] at this

noncomputable def relabelSetOn (σ : V ≃ V')
    (E : Finset (OrderedEdgeOn V)) : Finset (OrderedEdgeOn V') :=
  E.map ⟨relabelFunOn σ, relabelFunOn_injective σ⟩

theorem relabelFunOn_symm_cancel' (σ : V ≃ V')
    (ed : OrderedEdgeOn V') :
    relabelFunOn σ (relabelFunOn σ.symm ed) = ed := by
  have h := relabelFunOn_symm_cancel σ.symm ed
  rwa [Equiv.symm_symm] at h

theorem mem_relabelSetOn {σ : V ≃ V'} {E : Finset (OrderedEdgeOn V)}
    {ed : OrderedEdgeOn V'} :
    ed ∈ relabelSetOn σ E ↔ relabelFunOn σ.symm ed ∈ E := by
  unfold relabelSetOn
  rw [Finset.mem_map]
  constructor
  · rintro ⟨e, he, rfl⟩
    show relabelFunOn σ.symm (relabelFunOn σ e) ∈ E
    rwa [relabelFunOn_symm_cancel]
  · intro h
    exact ⟨relabelFunOn σ.symm ed, h, relabelFunOn_symm_cancel' σ ed⟩

theorem card_relabelSetOn (σ : V ≃ V')
    (E : Finset (OrderedEdgeOn V)) :
    (relabelSetOn σ E).card = E.card :=
  Finset.card_map _

theorem relabelFunOn_canonical (σ : V ≃ V') {i j : V} (h : i ≠ j) :
    relabelFunOn σ (canonicalOrderedEdgeOn i j h)
      = canonicalOrderedEdgeOn (σ i) (σ j)
          (fun he => h (σ.injective he)) := by
  unfold relabelFunOn
  rcases h.lt_or_lt with h' | h'
  · rw [canonicalOrderedEdgeOn_of_lt h' h]
  · rw [canonicalOrderedEdgeOn_of_gt h' h]
    show canonicalOrderedEdgeOn (σ j) (σ i) _ = _
    rcases (fun he => h (σ.injective he) :
        σ i ≠ σ j).lt_or_lt with h'' | h''
    · rw [canonicalOrderedEdgeOn_of_lt h'',
        canonicalOrderedEdgeOn_of_gt h'']
    · rw [canonicalOrderedEdgeOn_of_gt h'',
        canonicalOrderedEdgeOn_of_lt h'']

/-! ## Adjacency, Iso and connectivity transport -/

theorem graphOfEdgesOn_relabel_adj (σ : V ≃ V')
    (E : Finset (OrderedEdgeOn V)) (a b : V) :
    (graphOfEdgesOn (relabelSetOn σ E)).Adj (σ a) (σ b)
      ↔ (graphOfEdgesOn E).Adj a b := by
  by_cases hab : a = b
  · subst hab
    simp [SimpleGraph.irrefl]
  · have hab' : σ a ≠ σ b := fun h => hab (σ.injective h)
    rw [graphOfEdgesOn_adj_iff_canonical hab',
      graphOfEdgesOn_adj_iff_canonical hab,
      mem_relabelSetOn]
    have h := relabelFunOn_canonical σ.symm
      (i := σ a) (j := σ b) hab'
    constructor
    · intro hm
      rw [h] at hm
      have ha := σ.symm_apply_apply a
      have hb := σ.symm_apply_apply b
      convert hm using 2 <;> [exact ha.symm; exact hb.symm]
    · intro hm
      rw [h]
      have ha := σ.symm_apply_apply a
      have hb := σ.symm_apply_apply b
      convert hm using 2 <;> [exact ha; exact hb]

noncomputable def graphOfEdgesOnRelabelIso (σ : V ≃ V')
    (E : Finset (OrderedEdgeOn V)) :
    graphOfEdgesOn E ≃g graphOfEdgesOn (relabelSetOn σ E) where
  toEquiv := σ
  map_rel_iff' := by
    intro a b
    exact graphOfEdgesOn_relabel_adj σ E a b

theorem graphOfEdgesOn_relabel_connected_iff (σ : V ≃ V')
    (E : Finset (OrderedEdgeOn V)) :
    (graphOfEdgesOn (relabelSetOn σ E)).Connected
      ↔ (graphOfEdgesOn E).Connected := by
  rw [SimpleGraph.connected_iff, SimpleGraph.connected_iff,
    (graphOfEdgesOnRelabelIso σ E).preconnected_iff]
  exact and_congr Iff.rfl σ.nonempty_congr.symm

/-! ## The tree universe: connectivity + the cardinal condition (no
    IsTree on generic types — the 40b converse enters only at the
    Fin end, in Gate IV-B) -/

noncomputable def connTreesOn (V : Type*) [Fintype V] [LinearOrder V] :
    Finset (Finset (OrderedEdgeOn V)) :=
  Finset.univ.filter (fun E =>
    (graphOfEdgesOn E).Connected ∧ E.card + 1 = Fintype.card V)

theorem mem_connTreesOn {E : Finset (OrderedEdgeOn V)} :
    E ∈ connTreesOn V
      ↔ (graphOfEdgesOn E).Connected
        ∧ E.card + 1 = Fintype.card V := by
  unfold connTreesOn
  simp [Finset.mem_filter]

theorem relabelSetOn_mem_connTreesOn {σ : V ≃ V'}
    {E : Finset (OrderedEdgeOn V)} (h : E ∈ connTreesOn V) :
    relabelSetOn σ E ∈ connTreesOn V' := by
  obtain ⟨hconn, hcard⟩ := mem_connTreesOn.mp h
  refine mem_connTreesOn.mpr ⟨?_, ?_⟩
  · exact (graphOfEdgesOn_relabel_connected_iff σ E).mpr hconn
  · rw [card_relabelSetOn, ← Fintype.card_congr σ]
    exact hcard

/-! ## Rooted weights over V -/

noncomputable def edgeIndicatorOn (δ : V → Polymer N)
    (ed : OrderedEdgeOn V) : ℕ :=
  if PlaquetteCompatible (δ ed.val.1).val (δ ed.val.2).val
  then 0 else 1

theorem edgeIndicatorOn_canonical (δ : V → Polymer N) {i j : V}
    (h : i ≠ j) :
    edgeIndicatorOn δ (canonicalOrderedEdgeOn i j h)
      = if PlaquetteCompatible (δ i).val (δ j).val then 0 else 1 := by
  rcases h.lt_or_lt with h' | h'
  · rw [canonicalOrderedEdgeOn_of_lt h' h]
  · rw [canonicalOrderedEdgeOn_of_gt h' h]
    show (if PlaquetteCompatible (δ j).val (δ i).val
      then 0 else 1) = _
    refine if_congr ?_ rfl rfl
    exact ⟨fun hc => plaquetteCompatible_symm hc,
      fun hc => plaquetteCompatible_symm hc⟩

theorem edgeIndicatorOn_relabel (σ : V ≃ V') (δ : V → Polymer N)
    (ed : OrderedEdgeOn V) :
    edgeIndicatorOn (δ ∘ ⇑σ.symm) (relabelFunOn σ ed)
      = edgeIndicatorOn δ ed := by
  obtain ⟨⟨a, b⟩, hab⟩ := ed
  unfold relabelFunOn
  rw [edgeIndicatorOn_canonical]
  show (if PlaquetteCompatible (δ (σ.symm (σ a))).val
      (δ (σ.symm (σ b))).val then 0 else 1) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

noncomputable def treeIndicatorOn (δ : V → Polymer N)
    (E : Finset (OrderedEdgeOn V)) : ℕ :=
  ∏ ed ∈ E, edgeIndicatorOn δ ed

theorem treeIndicatorOn_relabel (σ : V ≃ V') (δ : V → Polymer N)
    (E : Finset (OrderedEdgeOn V)) :
    treeIndicatorOn (δ ∘ ⇑σ.symm) (relabelSetOn σ E)
      = treeIndicatorOn δ E := by
  unfold treeIndicatorOn relabelSetOn
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl
    (fun ed _ => edgeIndicatorOn_relabel σ δ ed)

noncomputable def rootedActivityOn (ρ : Polymer N → ℝ) (r : V)
    (δ : V → Polymer N) : ℝ :=
  ∏ v ∈ Finset.univ.erase r, ρ (δ v)

theorem rootedActivityOn_relabel (σ : V ≃ V') {r : V} {r' : V'}
    (hr : σ r = r') (ρ : Polymer N → ℝ) (δ : V → Polymer N) :
    rootedActivityOn ρ r' (δ ∘ ⇑σ.symm)
      = rootedActivityOn ρ r δ := by
  unfold rootedActivityOn
  refine (Finset.prod_bij (fun v _ => σ v) ?_ ?_ ?_ ?_).symm
  · intro v hv
    rw [Finset.mem_erase] at hv ⊢
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    rw [← hr] at h
    exact hv.1 (σ.injective h)
  · intro v₁ _ v₂ _ h
    exact σ.injective h
  · intro v' hv'
    rw [Finset.mem_erase] at hv'
    refine ⟨σ.symm v', ?_, ?_⟩
    · rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro h
      refine hv'.1 ?_
      rw [← hr, ← h, Equiv.apply_symm_apply]
    · exact (Equiv.apply_symm_apply σ v').symm
  · intro v _
    show ρ (δ v) = ρ ((δ ∘ ⇑σ.symm) (σ v))
    rw [Function.comp_apply, Equiv.symm_apply_apply]

noncomputable def rootedTreeWeightOn (ρ : Polymer N → ℝ) (r : V)
    (δ : V → Polymer N) (E : Finset (OrderedEdgeOn V)) : ℝ :=
  (treeIndicatorOn δ E : ℝ) * rootedActivityOn ρ r δ

theorem rootedTreeWeightOn_relabel (σ : V ≃ V') {r : V} {r' : V'}
    (hr : σ r = r') (ρ : Polymer N → ℝ) (δ : V → Polymer N)
    (E : Finset (OrderedEdgeOn V)) :
    rootedTreeWeightOn ρ r' (δ ∘ ⇑σ.symm) (relabelSetOn σ E)
      = rootedTreeWeightOn ρ r δ E := by
  unfold rootedTreeWeightOn
  rw [treeIndicatorOn_relabel σ δ E, rootedActivityOn_relabel σ hr ρ δ]

/-! ## The rooted sum and the GATE IV-A CAPSTONE -/

noncomputable def rootedTreeSumOn (ρ : Polymer N → ℝ) (r : V)
    (η : Polymer N) : ℝ :=
  ∑ δ ∈ Finset.univ.filter
      (fun δ : V → Polymer N => δ r = η),
    ∑ E ∈ connTreesOn V, rootedTreeWeightOn ρ r δ E

/-- **GATE IV-A CAPSTONE: the rooted sum transports along any
    root-preserving equivalence** — simultaneous reindexation of
    assignments and edge sets. Symmetric and reusable. -/
theorem rootedTreeSumOn_congr (σ : V ≃ V') {r : V} {r' : V'}
    (hr : σ r = r') (ρ : Polymer N → ℝ) (η : Polymer N) :
    rootedTreeSumOn (V := V) ρ r η
      = rootedTreeSumOn (V := V') ρ r' η := by
  unfold rootedTreeSumOn
  refine Finset.sum_bij (fun δ _ => δ ∘ ⇑σ.symm) ?_ ?_ ?_ ?_
  · intro δ hδ
    rw [Finset.mem_filter] at hδ ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    show δ (σ.symm r') = η
    rw [← hr, Equiv.symm_apply_apply]
    exact hδ.2
  · intro δ₁ _ δ₂ _ h
    funext v
    have := congrArg (fun f => f (σ v)) h
    simpa [Equiv.symm_apply_apply] using this
  · intro δ' hδ'
    rw [Finset.mem_filter] at hδ'
    refine ⟨δ' ∘ ⇑σ, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      show δ' (σ r) = η
      rw [hr]
      exact hδ'.2
    · funext v'
      show δ' (σ (σ.symm v')) = δ' v'
      rw [Equiv.apply_symm_apply]
  · intro δ hδ
    refine Finset.sum_bij (fun E _ => relabelSetOn σ E) ?_ ?_ ?_ ?_
    · intro E hE
      exact relabelSetOn_mem_connTreesOn hE
    · intro E₁ _ E₂ _ h
      have h2 := congrArg (relabelSetOn σ.symm) h
      have hcancel : ∀ F : Finset (OrderedEdgeOn V),
          relabelSetOn σ.symm (relabelSetOn σ F) = F := by
        intro F
        ext ed
        rw [mem_relabelSetOn, mem_relabelSetOn, Equiv.symm_symm,
          relabelFunOn_symm_cancel']
      rwa [hcancel, hcancel] at h2
    · intro E' hE'
      refine ⟨relabelSetOn σ.symm E',
        relabelSetOn_mem_connTreesOn hE', ?_⟩
      ext ed
      rw [mem_relabelSetOn, mem_relabelSetOn, Equiv.symm_symm]
      constructor
      · intro h
        rwa [relabelFunOn_symm_cancel] at h
      · intro h
        rwa [relabelFunOn_symm_cancel]
    · intro E hE
      exact (rootedTreeWeightOn_relabel σ hr ρ δ E).symm

/-! ## Sanities: refl, composition, the unit type -/

theorem rootedTreeSumOn_congr_refl (ρ : Polymer N → ℝ) (r : V)
    (η : Polymer N) :
    rootedTreeSumOn (V := V) ρ r η = rootedTreeSumOn (V := V) ρ r η :=
  rootedTreeSumOn_congr (Equiv.refl V) rfl ρ η

theorem rootedTreeSumOn_congr_trans {V'' : Type*} [Fintype V'']
    [LinearOrder V''] (σ : V ≃ V') (τ : V' ≃ V'')
    {r : V} {r' : V'} {r'' : V''}
    (hr : σ r = r') (hr' : τ r' = r'')
    (ρ : Polymer N → ℝ) (η : Polymer N) :
    rootedTreeSumOn (V := V) ρ r η
      = rootedTreeSumOn (V := V'') ρ r'' η :=
  (rootedTreeSumOn_congr σ hr ρ η).trans
    (rootedTreeSumOn_congr τ hr' ρ η)

/-- The unit type: only the empty tree, only the constant
    assignment, weight 1 (empty products throughout). -/
theorem rootedTreeSumOn_unit (ρ : Polymer N → ℝ) (r : V)
    (η : Polymer N) (hV : Fintype.card V = 1) :
    rootedTreeSumOn (V := V) ρ r η = 1 := by
  have hsub : ∀ v : V, v = r := by
    intro v
    have := Fintype.card_le_one_iff.mp (le_of_eq hV)
    exact this v r
  have htrees : connTreesOn V = {(∅ : Finset (OrderedEdgeOn V))} := by
    ext E
    rw [mem_connTreesOn, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hcard⟩
      rw [hV] at hcard
      exact Finset.card_eq_zero.mp (by omega)
    · rintro rfl
      refine ⟨?_, by rw [Finset.card_empty, hV]⟩
      rw [SimpleGraph.connected_iff]
      refine ⟨?_, ⟨r⟩⟩
      intro a b
      rw [hsub a, hsub b]
  have hfilter : Finset.univ.filter
      (fun δ : V → Polymer N => δ r = η)
      = {fun _ => η} := by
    ext δ
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hδ⟩
      funext v
      rw [hsub v]
      exact hδ
    · rintro rfl
      exact ⟨Finset.mem_univ _, rfl⟩
  unfold rootedTreeSumOn
  rw [htrees, hfilter, Finset.sum_singleton, Finset.sum_singleton]
  unfold rootedTreeWeightOn treeIndicatorOn rootedActivityOn
  rw [Finset.prod_empty]
  have herase : (Finset.univ : Finset V).erase r = ∅ := by
    rw [Finset.eq_empty_iff_forall_not_mem]
    intro v hv
    rw [Finset.mem_erase] at hv
    exact hv.1 (hsub v)
  rw [herase, Finset.prod_empty]
  norm_num

end LatticeGauge
