/-
LatticeGauge/PolymerWalkCount.lean — Phase 3, forty-fifth stone (b-ii).

COUNTING ROOTED CONNECTED POLYMERS BY DOUBLED WALKS
(architecture: Sol/GPT-5.6; execution: Fable). The camera principle:
we never identify individual polymers — we prove every polymer of
size m+1 containing the root p₀ appears as the EXACT visited-vertex
set of SOME closed walk of length 2m from p₀ (a covering by the image
of walks, NOT an injection: no canonical tree, no canonical
traversal, no injectivity), and we count the photographs:
  #walks(p₀, L) ≤ 64^L  (64 = the stone 45b-i degree gate),
hence  #{D : p₀ ∈ D, |D| = m+1} ≤ 64^(2m)   and, through the ≤ 16
incidence gate,  #{D : ℓ ∈ supp D, |D| = m+1} ≤ 16·64^(2m).
The bounds are deliberately non-optimal, volume-free (no N in 16, 64,
or the exponents), exponential in the SIZE not the volume; the
coarseness of 64² = 4096 only affects how small β will have to be.
The covering-walk lemma is proved WITHOUT spanning trees (absent from
the pinned Mathlib): by induction on the size, removing a vertex of
MAXIMAL CONFINED DISTANCE from the root — such a vertex is never a
cut vertex (a minimal confined walk to any other vertex cannot pass
through it: takeUntil surgery + maximality), which meets the
architect's requirement that the removed vertex be a leaf-like,
connectivity-preserving choice, NOT an arbitrary boundary vertex.
The visited set is EXACTLY D (both inclusions; the walk never leaves
D by construction). Confined distances are defined via Nat.sInf over
walk lengths in the AMBIENT plaquetteGraph with support constrained
to D — no induced-subtype metric, no Fin k transport. The bridge from
the stone-33/35 IntrinsicallyConnected predicate is one-directional
(induce walk mapped through Embedding.induce), consuming, never
rebuilding, the existing connectivity notion. Weighted slice bounds
(one size at a time, NO sum over sizes, no geometric series, no α or
β chosen, no Kotecký–Preiss, no convergence, no thermodynamic limit)
prepare stone 46. Walks may repeat vertices and edges — they are
walks, not paths. NO axioms.
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
import LatticeGauge.PolymerActivityBound
import LatticeGauge.LinkCovering
import LatticeGauge.LocalGeometry

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## 3. Rooted polymers of one size -/

/-- Polymers containing the root p₀, of size exactly m + 1 (the
    stone-36 connectivity predicate is consumed, not redefined). -/
noncomputable def rootedPolymersOfSize (p₀ : Site N × Dir × Dir)
    (m : ℕ) : Finset (Finset (Site N × Dir × Dir)) :=
  (allPlaquettePolymers N).filter
    (fun D => p₀ ∈ D ∧ D.card = m + 1)

theorem mem_rootedPolymersOfSize {p₀ : Site N × Dir × Dir} {m : ℕ}
    {D : Finset (Site N × Dir × Dir)} :
    D ∈ rootedPolymersOfSize p₀ m
      ↔ D ∈ allPlaquettePolymers N ∧ p₀ ∈ D ∧ D.card = m + 1 := by
  unfold rootedPolymersOfSize
  simp [Finset.mem_filter]

/-! ## 4. Walk codes of fixed length (walks, not paths: vertices and
    edges may repeat) -/

/-- Codes of walks from p₀ with exactly L steps: L+1 vertices, first
    = p₀, consecutive pairs adjacent in the plaquette graph. -/
noncomputable def walksFrom (p₀ : Site N × Dir × Dir) (L : ℕ) :
    Finset (Fin (L + 1) → Site N × Dir × Dir) :=
  Finset.univ.filter (fun f =>
    f 0 = p₀ ∧ ∀ i : Fin L,
      (plaquetteGraph N).Adj (f i.castSucc) (f i.succ))

theorem mem_walksFrom {p₀ : Site N × Dir × Dir} {L : ℕ}
    {f : Fin (L + 1) → Site N × Dir × Dir} :
    f ∈ walksFrom p₀ L
      ↔ f 0 = p₀ ∧ ∀ i : Fin L,
          (plaquetteGraph N).Adj (f i.castSucc) (f i.succ) := by
  unfold walksFrom
  simp [Finset.mem_filter]

/-- All visited vertices — initial, intermediate and final alike. -/
noncomputable def walkVertexFinset {L : ℕ}
    (f : Fin (L + 1) → Site N × Dir × Dir) :
    Finset (Site N × Dir × Dir) :=
  Finset.image f Finset.univ

theorem mem_walkVertexFinset {L : ℕ}
    {f : Fin (L + 1) → Site N × Dir × Dir}
    {x : Site N × Dir × Dir} :
    x ∈ walkVertexFinset f ↔ ∃ i, f i = x := by
  unfold walkVertexFinset
  simp [Finset.mem_image]

/-! ## 5-6. Counting the walks -/

theorem walksFrom_zero (p₀ : Site N × Dir × Dir) :
    walksFrom (N := N) p₀ 0
      = {fun _ : Fin 1 => p₀} := by
  ext f
  rw [Finset.mem_singleton, mem_walksFrom]
  constructor
  · rintro ⟨h0, -⟩
    funext i
    have hi : i = 0 := by
      have h := i.isLt
      exact Fin.ext (by rw [Fin.val_zero]; omega)
    rw [hi, h0]
  · rintro rfl
    exact ⟨rfl, fun i => i.elim0⟩

theorem neighborFinset_card_le (p : Site N × Dir × Dir) :
    ((plaquetteGraph N).neighborFinset p).card ≤ 64 := by
  have h := plaquetteGraph_degree_le p
  rw [plaquetteAdjDegreeBound_eq] at h
  unfold SimpleGraph.degree at h
  exact h

theorem walksFrom_succ_subset (p₀ : Site N × Dir × Dir) (L : ℕ) :
    walksFrom (N := N) p₀ (L + 1)
      ⊆ (walksFrom p₀ L).biUnion (fun g =>
          ((plaquetteGraph N).neighborFinset (g (Fin.last L))).image
            (fun q => Fin.snoc g q)) := by
  intro f hf
  obtain ⟨h0, hadj⟩ := mem_walksFrom.mp hf
  rw [Finset.mem_biUnion]
  refine ⟨Fin.init f, ?_, ?_⟩
  · rw [mem_walksFrom]
    refine ⟨?_, ?_⟩
    · show f (Fin.castSucc 0) = p₀
      rw [Fin.castSucc_zero']
      exact h0
    · intro j
      show (plaquetteGraph N).Adj
        (f (Fin.castSucc j.castSucc)) (f (Fin.castSucc j.succ))
      have hcs : (Fin.castSucc j).succ = Fin.castSucc j.succ :=
        Fin.ext (by simp [Fin.val_succ])
      have h := hadj j.castSucc
      rwa [hcs] at h
  · rw [Finset.mem_image]
    refine ⟨f (Fin.last (L + 1)), ?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset]
      show (plaquetteGraph N).Adj
        (f (Fin.castSucc (Fin.last L))) (f (Fin.last (L + 1)))
      have hlast : (Fin.castSucc (Fin.last L)).succ
          = Fin.last (L + 1) :=
        Fin.ext (by simp [Fin.val_succ])
      have h := hadj (Fin.castSucc (Fin.last L))
      · rwa [hlast] at h
    · show Fin.snoc (Fin.init f) (f (Fin.last (L + 1))) = f
      funext i
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.snoc_last]
      · intro j
        rw [Fin.snoc_castSucc]
        rfl

theorem walksFrom_card_succ_le (p₀ : Site N × Dir × Dir) (L : ℕ) :
    (walksFrom (N := N) p₀ (L + 1)).card
      ≤ 64 * (walksFrom p₀ L).card := by
  refine (Finset.card_le_card (walksFrom_succ_subset p₀ L)).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ g ∈ walksFrom p₀ L,
        (((plaquetteGraph N).neighborFinset (g (Fin.last L))).image
          (fun q => Fin.snoc g q)).card
      ≤ ∑ _g ∈ walksFrom p₀ L, 64 :=
        Finset.sum_le_sum (fun g _ =>
          Finset.card_image_le.trans
            (neighborFinset_card_le (g (Fin.last L))))
    _ = (walksFrom p₀ L).card * 64 := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = 64 * (walksFrom p₀ L).card := Nat.mul_comm _ _

/-- **The photograph count**: at most 64^L walks of length L. -/
theorem walksFrom_card_le (p₀ : Site N × Dir × Dir) (L : ℕ) :
    (walksFrom (N := N) p₀ L).card ≤ 64 ^ L := by
  induction L with
  | zero =>
    rw [walksFrom_zero, Finset.card_singleton, pow_zero]
  | succ L ih =>
    refine (walksFrom_card_succ_le p₀ L).trans ?_
    calc 64 * (walksFrom p₀ L).card
        ≤ 64 * 64 ^ L := Nat.mul_le_mul_left _ ih
      _ = 64 ^ (L + 1) := by rw [pow_succ, Nat.mul_comm]

/-! ## Confined distances (Nat.sInf over ambient walks with support
    in D — no induced metric, no subtype graphs in the induction) -/

def confinedLengths (Dset : Finset (Site N × Dir × Dir))
    (p q : Site N × Dir × Dir) : Set ℕ :=
  {n | ∃ w : (plaquetteGraph N).Walk p q,
    w.length = n ∧ ∀ x ∈ w.support, x ∈ Dset}

noncomputable def cdist (Dset : Finset (Site N × Dir × Dir))
    (p q : Site N × Dir × Dir) : ℕ :=
  sInf (confinedLengths Dset p q)

theorem exists_min_confined_walk
    {Dset : Finset (Site N × Dir × Dir)}
    {p q : Site N × Dir × Dir}
    (hne : (confinedLengths Dset p q).Nonempty) :
    ∃ w : (plaquetteGraph N).Walk p q,
      w.length = cdist Dset p q ∧ ∀ x ∈ w.support, x ∈ Dset := by
  have h := Nat.sInf_mem hne
  simp only [confinedLengths, Set.mem_setOf_eq] at h
  exact h

theorem cdist_le {Dset : Finset (Site N × Dir × Dir)}
    {p q : Site N × Dir × Dir} {n : ℕ}
    (h : n ∈ confinedLengths Dset p q) :
    cdist Dset p q ≤ n :=
  Nat.sInf_le h

theorem cdist_self_eq_zero {Dset : Finset (Site N × Dir × Dir)}
    {p : Site N × Dir × Dir} (hp : p ∈ Dset) :
    cdist Dset p p = 0 := by
  refine Nat.le_zero.mp (cdist_le ?_)
  refine ⟨SimpleGraph.Walk.nil, rfl, ?_⟩
  intro x hx
  rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
  rw [hx]
  exact hp

/-- The one-directional bridge from stone 33/35 connectivity to
    confined reachability (walk in the induced graph mapped through
    `Embedding.induce`). -/
theorem confinedLengths_nonempty_of_connectedWithin
    {Dset : Finset (Site N × Dir × Dir)}
    {p q : Site N × Dir × Dir}
    (h : connectedWithin Dset p q) :
    (confinedLengths Dset p q).Nonempty := by
  obtain ⟨hp, hq, hreach⟩ := h
  obtain ⟨w⟩ := hreach
  refine ⟨(w.map (SimpleGraph.Embedding.induce
    (↑Dset : Set (Site N × Dir × Dir))).toHom).length,
    w.map _, rfl, ?_⟩
  intro x hx
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hx
  obtain ⟨⟨y, hy⟩, -, hval⟩ := hx
  rw [← hval]
  exact hy

/-! ## 7-9. THE CENTRAL LEMMA: the doubled covering walk -/

/-- **Every connected rooted set is EXACTLY the visited set of some
    closed doubled walk of length 2m** — proved by induction on the
    size, removing a vertex of MAXIMAL confined distance from the
    root (never a cut vertex: a minimal confined walk to any other
    vertex avoids it, by takeUntil surgery and maximality — the
    connectivity-preserving removal the architect required). The walk
    never leaves D and visits all of D. -/
theorem exists_doubled_covering_walk (m : ℕ) :
    ∀ (D : Finset (Site N × Dir × Dir)) (p₀ : Site N × Dir × Dir),
    p₀ ∈ D → D.card = m + 1 →
    (∀ q ∈ D, (confinedLengths D p₀ q).Nonempty) →
    ∃ w : (plaquetteGraph N).Walk p₀ p₀,
      w.length = 2 * m ∧ w.support.toFinset = D := by
  induction m with
  | zero =>
    intro D p₀ hp₀ hcard _
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    have hap : a = p₀ := by
      rw [ha, Finset.mem_singleton] at hp₀
      exact hp₀.symm
    refine ⟨SimpleGraph.Walk.nil, by simp, ?_⟩
    rw [SimpleGraph.Walk.support_nil, ha, hap]
    simp
  | succ m ih =>
    intro D p₀ hp₀ hcard hreach
    -- the maximal-distance vertex
    obtain ⟨v, hvD, hvmax⟩ :=
      Finset.exists_max_image D (cdist D p₀) ⟨p₀, hp₀⟩
    -- v ≠ p₀
    have hvne : v ≠ p₀ := by
      intro hveq
      have hall : ∀ q ∈ D, q = p₀ := by
        intro q hq
        have h1 : cdist D p₀ q ≤ cdist D p₀ v := hvmax q hq
        rw [hveq, cdist_self_eq_zero hp₀] at h1
        have h2 : cdist D p₀ q = 0 := Nat.le_zero.mp h1
        obtain ⟨w, hwlen, -⟩ := exists_min_confined_walk (hreach q hq)
        rw [h2] at hwlen
        exact (SimpleGraph.Walk.eq_of_length_eq_zero hwlen).symm
      have hsub : D ⊆ {p₀} := fun q hq =>
        Finset.mem_singleton.mpr (hall q hq)
      have := Finset.card_le_card hsub
      rw [Finset.card_singleton] at this
      omega
    -- minimal walks to other vertices avoid v
    have havoid : ∀ u ∈ D, u ≠ v →
        ∃ w : (plaquetteGraph N).Walk p₀ u,
          (∀ x ∈ w.support, x ∈ D) ∧ v ∉ w.support := by
      intro u huD hune
      obtain ⟨w, hwlen, hwconf⟩ :=
        exists_min_confined_walk (hreach u huD)
      refine ⟨w, hwconf, ?_⟩
      intro hv
      have h1 : cdist D p₀ v ≤ (w.takeUntil v hv).length :=
        cdist_le ⟨w.takeUntil v hv, rfl,
          fun x hx => hwconf x
            (SimpleGraph.Walk.support_takeUntil_subset w hv hx)⟩
      have h2 : (w.takeUntil v hv).length
          + (w.dropUntil v hv).length = w.length := by
        have hspec := congrArg SimpleGraph.Walk.length
          (SimpleGraph.Walk.take_spec w hv)
        rwa [SimpleGraph.Walk.length_append] at hspec
      have h3 : 1 ≤ (w.dropUntil v hv).length := by
        by_contra hzero
        push_neg at hzero
        have h0 : (w.dropUntil v hv).length = 0 := by omega
        exact hune
          (SimpleGraph.Walk.eq_of_length_eq_zero h0).symm
      have h4 : cdist D p₀ u ≤ cdist D p₀ v := hvmax u huD
      omega
    -- reachability inside D.erase v
    have hp₀' : p₀ ∈ D.erase v :=
      Finset.mem_erase.mpr ⟨fun h => hvne h.symm, hp₀⟩
    have hreach' : ∀ q ∈ D.erase v,
        (confinedLengths (D.erase v) p₀ q).Nonempty := by
      intro q hq
      obtain ⟨hqv, hqD⟩ := Finset.mem_erase.mp hq
      obtain ⟨w, hwconf, hwav⟩ := havoid q hqD hqv
      refine ⟨w.length, w, rfl, ?_⟩
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, hwconf x hx⟩
      intro hxeq
      rw [hxeq] at hx
      exact hwav hx
    have hcard' : (D.erase v).card = m + 1 := by
      rw [Finset.card_erase_of_mem hvD]
      omega
    -- inductive walk over D.erase v
    obtain ⟨W, hWlen, hWsupp⟩ :=
      ih (D.erase v) p₀ hp₀' hcard' hreach'
    -- neighbour u of v inside D.erase v
    obtain ⟨wv, hwvlen, hwvconf⟩ :=
      exists_min_confined_walk (hreach v hvD)
    have hwvpos : 1 ≤ wv.length := by
      by_contra hzero
      push_neg at hzero
      have h0 : wv.length = 0 := by omega
      exact hvne (SimpleGraph.Walk.eq_of_length_eq_zero h0).symm
    set u : Site N × Dir × Dir := wv.getVert (wv.length - 1) with hu
    have hadjuv : (plaquetteGraph N).Adj u v := by
      have h := wv.adj_getVert_succ
        (i := wv.length - 1) (by omega)
      have harith : wv.length - 1 + 1 = wv.length := by omega
      rw [harith, SimpleGraph.Walk.getVert_length] at h
      exact h
    have huD : u ∈ D := by
      refine hwvconf u ?_
      rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
      exact ⟨wv.length - 1, rfl, by omega⟩
    have hune : u ≠ v := (plaquetteGraph N).ne_of_adj hadjuv
    have huE : u ∈ D.erase v := Finset.mem_erase.mpr ⟨hune, huD⟩
    have huW : u ∈ W.support := by
      have h : u ∈ W.support.toFinset := by
        rw [hWsupp]
        exact huE
      rwa [List.mem_toFinset] at h
    -- surgery: insert the detour u → v → u at u
    set W1 := W.takeUntil u huW with hW1
    set W2 := W.dropUntil u huW with hW2
    set W' := W1.append
      (SimpleGraph.Walk.cons hadjuv
        (SimpleGraph.Walk.cons hadjuv.symm W2)) with hW'
    have hlen12 : W1.length + W2.length = W.length := by
      have hspec := congrArg SimpleGraph.Walk.length
        (SimpleGraph.Walk.take_spec W huW)
      rwa [SimpleGraph.Walk.length_append] at hspec
    refine ⟨W', ?_, ?_⟩
    · rw [hW', SimpleGraph.Walk.length_append,
        SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_cons]
      omega
    · -- exact visited set
      have hmemW' : ∀ x, x ∈ W'.support
          ↔ (x ∈ W.support ∨ x = v) := by
        intro x
        rw [hW', SimpleGraph.Walk.mem_support_append_iff,
          SimpleGraph.Walk.support_cons,
          SimpleGraph.Walk.support_cons]
        constructor
        · rintro (hx | hx)
          · refine Or.inl ?_
            have hWx : x ∈ W1.support ∨ x ∈ W2.support :=
              Or.inl hx
            rw [← SimpleGraph.Walk.mem_support_append_iff,
              SimpleGraph.Walk.take_spec W huW] at hWx
            exact hWx
          · rw [List.mem_cons, List.mem_cons] at hx
            rcases hx with hx | hx | hx
            · refine Or.inl ?_
              rw [hx]
              exact huW
            · exact Or.inr hx
            · refine Or.inl ?_
              have hWx : x ∈ W1.support ∨ x ∈ W2.support :=
                Or.inr hx
              rw [← SimpleGraph.Walk.mem_support_append_iff,
                SimpleGraph.Walk.take_spec W huW] at hWx
              exact hWx
        · rintro (hx | hx)
          · have hWx : x ∈ W1.support ∨ x ∈ W2.support := by
              rw [← SimpleGraph.Walk.mem_support_append_iff,
                SimpleGraph.Walk.take_spec W huW]
              exact hx
            rcases hWx with hx1 | hx2
            · exact Or.inl hx1
            · refine Or.inr ?_
              rw [List.mem_cons, List.mem_cons]
              exact Or.inr (Or.inr hx2)
          · refine Or.inr ?_
            rw [List.mem_cons, List.mem_cons]
            exact Or.inr (Or.inl hx)
      ext x
      rw [List.mem_toFinset, hmemW' x]
      constructor
      · rintro (hx | hx)
        · have h : x ∈ D.erase v := by
            rw [← hWsupp]
            rwa [List.mem_toFinset]
          exact (Finset.mem_erase.mp h).2
        · rw [hx]
          exact hvD
      · intro hxD
        by_cases hxv : x = v
        · exact Or.inr hxv
        · refine Or.inl ?_
          have h : x ∈ D.erase v := Finset.mem_erase.mpr ⟨hxv, hxD⟩
          rw [← hWsupp] at h
          rwa [List.mem_toFinset] at h

/-! ## Walk → code conversion and the covering by images -/

/-- A Walk of length exactly L, encoded as a code in `walksFrom`. -/
theorem walk_toCode {p₀ q : Site N × Dir × Dir} {L : ℕ}
    (w : (plaquetteGraph N).Walk p₀ q) (hlen : w.length = L) :
    ∃ f ∈ walksFrom (N := N) p₀ L,
      walkVertexFinset f = w.support.toFinset := by
  refine ⟨fun i : Fin (L + 1) => w.getVert i.val, ?_, ?_⟩
  · rw [mem_walksFrom]
    refine ⟨by simpa using w.getVert_zero, ?_⟩
    intro i
    show (plaquetteGraph N).Adj (w.getVert i.val)
      (w.getVert (i.val + 1))
    refine w.adj_getVert_succ ?_
    rw [hlen]
    exact i.isLt
  · ext x
    rw [mem_walkVertexFinset, List.mem_toFinset,
      SimpleGraph.Walk.mem_support_iff_exists_getVert]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i.val, hi, by rw [hlen]; omega⟩
    · rintro ⟨n, hn, hnle⟩
      refine ⟨⟨n, by rw [hlen] at hnle; omega⟩, hn⟩

/-- **11. The covering by the image of the walks** — pure existence:
    no canonical D ↦ w, no injectivity. -/
theorem rootedPolymersOfSize_subset_image
    (p₀ : Site N × Dir × Dir) (m : ℕ) :
    rootedPolymersOfSize p₀ m
      ⊆ (walksFrom (N := N) p₀ (2 * m)).image walkVertexFinset := by
  intro D hD
  obtain ⟨hall, hp₀, hcard⟩ := mem_rootedPolymersOfSize.mp hD
  have hpoly : IsPlaquettePolymer D := by
    unfold allPlaquettePolymers at hall
    rw [Finset.mem_filter] at hall
    exact hall.2
  have hreach : ∀ q ∈ D, (confinedLengths D p₀ q).Nonempty :=
    fun q hq => confinedLengths_nonempty_of_connectedWithin
      (hpoly.2.2 p₀ hp₀ q hq)
  obtain ⟨w, hwlen, hwsupp⟩ :=
    exists_doubled_covering_walk m D p₀ hp₀ hcard hreach
  obtain ⟨f, hf, hfvert⟩ := walk_toCode w hwlen
  rw [Finset.mem_image]
  exact ⟨f, hf, by rw [hfvert, hwsupp]⟩

/-! ## 12. FIRST COMBINATORIAL CAPSTONE -/

/-- **≤ 64^(2m) rooted polymers of size m+1** — deliberately
    non-optimal, by doubled-walk covering; volume-free; no Cayley,
    Prüfer, Catalan or plane trees; no canonical tree; no injection
    of polymers into walks. -/
theorem rootedPolymersOfSize_card_le
    (p₀ : Site N × Dir × Dir) (m : ℕ) :
    (rootedPolymersOfSize p₀ m).card ≤ 64 ^ (2 * m) := by
  refine (Finset.card_le_card
    (rootedPolymersOfSize_subset_image p₀ m)).trans ?_
  refine Finset.card_image_le.trans ?_
  exact walksFrom_card_le p₀ (2 * m)

/-- Sanity (17A): at most ONE polymer of size 1 per root. -/
theorem rootedPolymersOfSize_zero_card_le
    (p₀ : Site N × Dir × Dir) :
    (rootedPolymersOfSize p₀ 0).card ≤ 1 := by
  have h := rootedPolymersOfSize_card_le p₀ 0
  simpa using h

/-! ## 13-14. Rooted at a link, by size -/

noncomputable def rootedLinkPolymersOfSize (ℓ : Link N) (m : ℕ) :
    Finset (Finset (Site N × Dir × Dir)) :=
  (polymersUsingLink ℓ).filter (fun D => D.card = m + 1)

theorem mem_rootedLinkPolymersOfSize {ℓ : Link N} {m : ℕ}
    {D : Finset (Site N × Dir × Dir)} :
    D ∈ rootedLinkPolymersOfSize ℓ m
      ↔ D ∈ polymersUsingLink ℓ ∧ D.card = m + 1 := by
  unfold rootedLinkPolymersOfSize
  simp [Finset.mem_filter]

/-- The link slice is covered by the ≤ 16 rooted-plaquette slices
    (same D possibly under several roots — deliberate). -/
theorem rootedLinkPolymersOfSize_subset_biUnion
    (ℓ : Link N) (m : ℕ) :
    rootedLinkPolymersOfSize ℓ m
      ⊆ (plaquettesUsingLink ℓ).biUnion
          (fun p => rootedPolymersOfSize p m) := by
  intro D hD
  obtain ⟨hDl, hcard⟩ := mem_rootedLinkPolymersOfSize.mp hD
  obtain ⟨p, hp, hpD⟩ := exists_root_of_mem_polymersUsingLink hDl
  rw [Finset.mem_biUnion]
  exact ⟨p, hp, mem_rootedPolymersOfSize.mpr
    ⟨(mem_polymersUsingLink.mp hDl).1, hpD, hcard⟩⟩

/-- **SECOND COMBINATORIAL CAPSTONE: ≤ 16·64^(2m) polymers of size
    m+1 using a fixed link.** Neither 16 nor 64 is optimized. -/
theorem rootedLinkPolymersOfSize_card_le (ℓ : Link N) (m : ℕ) :
    (rootedLinkPolymersOfSize ℓ m).card ≤ 16 * 64 ^ (2 * m) := by
  refine (Finset.card_le_card
    (rootedLinkPolymersOfSize_subset_biUnion ℓ m)).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ p ∈ plaquettesUsingLink ℓ, (rootedPolymersOfSize p m).card
      ≤ ∑ _p ∈ plaquettesUsingLink ℓ, 64 ^ (2 * m) :=
        Finset.sum_le_sum
          (fun p _ => rootedPolymersOfSize_card_le p m)
    _ = (plaquettesUsingLink ℓ).card * 64 ^ (2 * m) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 16 * 64 ^ (2 * m) := by
        refine Nat.mul_le_mul_right _ ?_
        have h := plaquettesUsingLink_card_le ℓ
        rwa [plaquettesPerLinkBound_eq] at h

/-! ## 15-16. Weighted slice bounds (one size — NO sum over sizes) -/

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **The rooted-plaquette weighted slice** — stone 44 consumed
    pointwise, cardinality from the covering; still a finite sum over
    one size slice. -/
theorem rootedPolymers_kp_slice_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (α : ℝ)
    (p₀ : Site N × Dir × Dir) (m : ℕ) :
    (∑ D ∈ rootedPolymersOfSize p₀ m,
        kpActivityWeight μm β χ α D)
      ≤ ((64 ^ (2 * m) : ℕ) : ℝ)
          * ((2 * β) ^ (m + 1) * Real.exp (α * (m + 1))) := by
  have hpoint : ∀ D ∈ rootedPolymersOfSize p₀ m,
      kpActivityWeight μm β χ α D
        ≤ (2 * β) ^ (m + 1) * Real.exp (α * (m + 1)) := by
    intro D hD
    have hcard := (mem_rootedPolymersOfSize.mp hD).2.2
    have h := kpActivityWeight_le μm hβ mχ hχabs α D
    rwa [hcard, Nat.cast_add, Nat.cast_one] at h
  have h := Finset.sum_le_card_nsmul (rootedPolymersOfSize p₀ m)
    (fun D => kpActivityWeight μm β χ α D)
    ((2 * β) ^ (m + 1) * Real.exp (α * (m + 1))) hpoint
  rw [nsmul_eq_mul] at h
  refine h.trans ?_
  refine mul_le_mul_of_nonneg_right ?_
    (mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le)
  exact_mod_cast rootedPolymersOfSize_card_le p₀ m

/-- **THE ANALYTIC CAPSTONE PREPARED FOR STONE 46**: the rooted-link
    weighted slice of one size. Still finite; no series, no α or β
    chosen, no convergence claimed. -/
theorem rootedLinkPolymers_kp_slice_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (α : ℝ)
    (ℓ : Link N) (m : ℕ) :
    (∑ D ∈ rootedLinkPolymersOfSize ℓ m,
        kpActivityWeight μm β χ α D)
      ≤ ((16 * 64 ^ (2 * m) : ℕ) : ℝ)
          * ((2 * β) ^ (m + 1) * Real.exp (α * (m + 1))) := by
  have hpoint : ∀ D ∈ rootedLinkPolymersOfSize ℓ m,
      kpActivityWeight μm β χ α D
        ≤ (2 * β) ^ (m + 1) * Real.exp (α * (m + 1)) := by
    intro D hD
    have hcard := (mem_rootedLinkPolymersOfSize.mp hD).2
    have h := kpActivityWeight_le μm hβ mχ hχabs α D
    rwa [hcard, Nat.cast_add, Nat.cast_one] at h
  have h := Finset.sum_le_card_nsmul (rootedLinkPolymersOfSize ℓ m)
    (fun D => kpActivityWeight μm β χ α D)
    ((2 * β) ^ (m + 1) * Real.exp (α * (m + 1))) hpoint
  rw [nsmul_eq_mul] at h
  refine h.trans ?_
  refine mul_le_mul_of_nonneg_right ?_
    (mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le)
  exact_mod_cast rootedLinkPolymersOfSize_card_le ℓ m

end LatticeGauge
