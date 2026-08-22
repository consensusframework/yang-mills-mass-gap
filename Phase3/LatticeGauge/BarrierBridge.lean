/-
LatticeGauge/BarrierBridge.lean — PEDRA 50, Gate 50-A6: THE
GEOMETRIC BRIDGE — connector ⟹ bridge ⟹ total size ≥ separation
(architecture: Sol/GPT-5.6; execution: Fable).

The yellow tape comes off GEOMETRY here, but decay stays
grounded: this gate proves that the A5 connector really contains
a geometric bridge between the two barriers, and that its total
plaquette count dominates any separation lower bound — with
separation phrased as a METRIC-FREE predicate (BarrierSeparation:
"n bounds the size of every intrinsically connected set bridging
the two regions"). The NEXT gate may produce such an n from
actual graph geometry; this one does not.

NOT here: SimpleGraph.dist, q^d, exponential tails, 64^d,
16·64^(2m), geometric series, reuse of Stone 45 as if single
polymers were clusters, covariance, thermodynamic limit,
continuum, mass gap.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.PlaquetteConnectivity
import LatticeGauge.PolymerGeometry
import LatticeGauge.PolymerGas
import LatticeGauge.ConnectorClusters

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## A6.1 — the tuple plaquette union -/

noncomputable def tuplePlaquetteUnion {k : ℕ}
    (δ : Fin k → Polymer N) : Finset (Site N × Dir × Dir) :=
  Finset.univ.biUnion (fun i => (δ i).val)

theorem mem_tuplePlaquetteUnion {k : ℕ} {δ : Fin k → Polymer N}
    {p : Site N × Dir × Dir} :
    p ∈ tuplePlaquetteUnion δ ↔ ∃ i, p ∈ (δ i).val := by
  unfold tuplePlaquetteUnion
  simp [Finset.mem_biUnion]

/-! ## A6.2 — incompatibility ⟹ geometric contact -/

/-- Adjacency inside a set yields connectedWithin (one-edge
    reachability in the induced graph). -/
theorem connectedWithin_of_adj
    {A : Finset (Site N × Dir × Dir)}
    {p q : Site N × Dir × Dir} (hp : p ∈ A) (hq : q ∈ A)
    (h : (plaquetteGraph N).Adj p q) :
    connectedWithin (N := N) A p q := by
  refine ⟨hp, hq, SimpleGraph.Adj.reachable ?_⟩
  exact h

/-- **Incompatibility is geometric contact**: incompatible blocks
    contain plaquettes sharing a link. -/
theorem exists_contact_of_incompatible
    {C D : Finset (Site N × Dir × Dir)}
    (h : ¬ PlaquetteCompatible (N := N) C D) :
    ∃ p ∈ C, ∃ q ∈ D,
      ((plaqLinkSet (N := N) p) ∩ plaqLinkSet q).Nonempty := by
  unfold PlaquetteCompatible at h
  rw [Set.not_disjoint_iff] at h
  obtain ⟨ℓ, hℓC, hℓD⟩ := h
  unfold blockLinkSupport familySupport at hℓC hℓD
  obtain ⟨p, hpC, hℓp⟩ := hℓC
  obtain ⟨q, hqD, hℓq⟩ := hℓD
  exact ⟨p, hpC, q, hqD, ⟨ℓ, Finset.mem_inter.mpr ⟨hℓp, hℓq⟩⟩⟩

/-! ## A6.3 — connectivity transported to the union -/

/-- **Two incompatible polymers glue**: any plaquette of C
    connects to any plaquette of D inside any superset. -/
theorem connectedWithin_of_incompatible_blocks
    {A C D : Finset (Site N × Dir × Dir)}
    (hCA : C ⊆ A) (hDA : D ⊆ A)
    (hC : IntrinsicallyConnected (N := N) C)
    (hD : IntrinsicallyConnected (N := N) D)
    (h : ¬ PlaquetteCompatible (N := N) C D)
    {p q : Site N × Dir × Dir} (hp : p ∈ C) (hq : q ∈ D) :
    connectedWithin (N := N) A p q := by
  obtain ⟨p₀, hp₀, q₀, hq₀, hshare⟩ :=
    exists_contact_of_incompatible h
  have h1 : connectedWithin (N := N) A p p₀ :=
    connectedWithin_mono hCA (hC p hp p₀ hp₀)
  have h3 : connectedWithin (N := N) A q₀ q :=
    connectedWithin_mono hDA (hD q₀ hq₀ q hq)
  by_cases hpq : p₀ = q₀
  · subst hpq
    exact connectedWithin_trans h1 h3
  · exact connectedWithin_trans h1
      (connectedWithin_trans
        (connectedWithin_of_adj (hCA hp₀) (hDA hq₀)
          ⟨hpq, hshare⟩) h3)

/-- **A6.3 CAPSTONE — tuple-union connectivity**: a connected
    incompatibility graph makes the plaquette union intrinsically
    connected (walk induction over the index graph; each step is
    the two-block glue; blocks embed by monotonicity). -/
theorem tupleUnion_intrinsicallyConnected {k : ℕ}
    {δ : Fin k → Polymer N}
    (hconn : (polymerIncompatibilityGraph (N := N)
      (fun i => (δ i).val)).Connected) :
    IntrinsicallyConnected (N := N) (tuplePlaquetteUnion δ) := by
  have hpoly : ∀ i, IsPlaquettePolymer (N := N) (δ i).val :=
    fun i => isPolymer_of_mem_all (δ i).property
  have hsub : ∀ i, (δ i).val ⊆ tuplePlaquetteUnion δ :=
    fun i p hp => mem_tuplePlaquetteUnion.mpr ⟨i, hp⟩
  have key : ∀ {i j : Fin k},
      (polymerIncompatibilityGraph (N := N)
        (fun i => (δ i).val)).Reachable i j →
      ∀ p ∈ (δ i).val, ∀ q ∈ (δ j).val,
        connectedWithin (N := N) (tuplePlaquetteUnion δ) p q := by
    intro i j h
    obtain ⟨w⟩ := h
    induction w with
    | nil =>
      intro p hp q hq
      exact connectedWithin_mono (hsub _)
        ((hpoly _).2.2 p hp q hq)
    | @cons a b c hadj w ih =>
      intro p hp q hq
      obtain ⟨-, hinc⟩ := hadj
      obtain ⟨pb, hpb⟩ := (hpoly b).1
      have h1 : connectedWithin (N := N)
          (tuplePlaquetteUnion δ) p pb :=
        connectedWithin_of_incompatible_blocks (hsub a) (hsub b)
          (hpoly a).2.2 (hpoly b).2.2 hinc hp hpb
      exact connectedWithin_trans h1 (ih pb hpb q hq)
  intro p hp q hq
  obtain ⟨i, hpi⟩ := mem_tuplePlaquetteUnion.mp hp
  obtain ⟨j, hqj⟩ := mem_tuplePlaquetteUnion.mp hq
  exact key (hconn.preconnected i j) p hpi q hqj

/-! ## A6.4 — barriers as link regions and the bridge -/

/-- The link region of a barrier: the support s together with the
    link supports of the core members. -/
def barrierRegion (T : Finset (Polymer N)) (s : Set (Link N)) :
    Set (Link N) :=
  s ∪ familySupport
    (fun t : Polymer N => blockLinkSupport (N := N) t.val) T

/-- **Forbidden ⟹ barrier contact**: a remoteAllowed-forbidden
    polymer's link support meets the barrier region. -/
theorem forbidden_meets_barrierRegion {T : Finset (Polymer N)}
    {s : Set (Link N)} {η : Polymer N}
    (h : ¬ remoteAllowed (N := N) T s η) :
    ¬ Disjoint (blockLinkSupport (N := N) η.val)
      (barrierRegion (N := N) T s) := by
  rw [not_remoteAllowed_iff] at h
  intro hd
  rw [barrierRegion, Set.disjoint_union_right] at hd
  rcases h with ht | ⟨t, htT, hnc⟩
  · exact ht hd.1
  · unfold PlaquetteCompatible at hnc
    rw [Set.not_disjoint_iff] at hnc
    obtain ⟨ℓ, hℓη, hℓt⟩ := hnc
    exact Set.disjoint_left.mp hd.2 hℓη ⟨t, htT, hℓt⟩

/-- A block meeting a region contains a plaquette meeting it. -/
theorem exists_plaquette_touching
    {C : Finset (Site N × Dir × Dir)} {R : Set (Link N)}
    (h : ¬ Disjoint (blockLinkSupport (N := N) C) R) :
    ∃ p ∈ C, ¬ Disjoint
      (↑(plaqLinkSet (N := N) p) : Set (Link N)) R := by
  rw [Set.not_disjoint_iff] at h
  obtain ⟨ℓ, hℓC, hℓR⟩ := h
  unfold blockLinkSupport familySupport at hℓC
  obtain ⟨p, hpC, hℓp⟩ := hℓC
  exact ⟨p, hpC, Set.not_disjoint_iff.mpr ⟨ℓ, hℓp, hℓR⟩⟩

/-- **THE BRIDGE**: a connected two-barrier connector tuple
    contains, inside its own plaquette union, a plaquette meeting
    barrier 1 and a plaquette meeting barrier 2, CONNECTED to each
    other within the union. -/
theorem connector_tuple_bridge {k : ℕ} {δ : Fin k → Polymer N}
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)}
    (hconn : (polymerIncompatibilityGraph (N := N)
      (fun i => (δ i).val)).Connected)
    (hhit : TupleHitsBothForbidden
      (remoteAllowed (N := N) T s)
      (remoteAllowed (N := N) T' s') δ) :
    ∃ p₁ ∈ tuplePlaquetteUnion δ, ∃ p₂ ∈ tuplePlaquetteUnion δ,
      ¬ Disjoint (↑(plaqLinkSet (N := N) p₁) : Set (Link N))
          (barrierRegion (N := N) T s)
        ∧ ¬ Disjoint (↑(plaqLinkSet (N := N) p₂) : Set (Link N))
            (barrierRegion (N := N) T' s')
        ∧ connectedWithin (N := N) (tuplePlaquetteUnion δ)
            p₁ p₂ := by
  obtain ⟨h1, h2⟩ := hhit
  obtain ⟨i, hi⟩ := not_forall.mp h1
  obtain ⟨j, hj⟩ := not_forall.mp h2
  obtain ⟨p₁, hp₁, hm₁⟩ := exists_plaquette_touching
    (forbidden_meets_barrierRegion hi)
  obtain ⟨p₂, hp₂, hm₂⟩ := exists_plaquette_touching
    (forbidden_meets_barrierRegion hj)
  refine ⟨p₁, mem_tuplePlaquetteUnion.mpr ⟨i, hp₁⟩,
    p₂, mem_tuplePlaquetteUnion.mpr ⟨j, hp₂⟩, hm₁, hm₂, ?_⟩
  exact tupleUnion_intrinsicallyConnected hconn
    p₁ (mem_tuplePlaquetteUnion.mpr ⟨i, hp₁⟩)
    p₂ (mem_tuplePlaquetteUnion.mpr ⟨j, hp₂⟩)

/-! ## A6.5 — separation without a metric, and the size bound -/

/-- **BarrierSeparation** (the metric-free separation): n bounds
    the size of EVERY intrinsically connected plaquette set that
    bridges the two regions. The next gate may produce such an n
    from actual graph geometry; this gate only consumes it. -/
def BarrierSeparation (R₁ R₂ : Set (Link N)) (n : ℕ) : Prop :=
  ∀ A : Finset (Site N × Dir × Dir),
    IntrinsicallyConnected (N := N) A →
    (∃ p ∈ A, ¬ Disjoint
      (↑(plaqLinkSet (N := N) p) : Set (Link N)) R₁) →
    (∃ q ∈ A, ¬ Disjoint
      (↑(plaqLinkSet (N := N) q) : Set (Link N)) R₂) →
    n ≤ A.card

/-- **CAPSTONE 50-A6 — total size ≥ separation**: every connected
    two-barrier connector tuple carries at least n plaquettes of
    combinatorial matter. -/
theorem connector_tuple_card_ge {k : ℕ} {δ : Fin k → Polymer N}
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hconn : (polymerIncompatibilityGraph (N := N)
      (fun i => (δ i).val)).Connected)
    (hhit : TupleHitsBothForbidden
      (remoteAllowed (N := N) T s)
      (remoteAllowed (N := N) T' s') δ)
    (hsep : BarrierSeparation (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    n ≤ (tuplePlaquetteUnion δ).card := by
  obtain ⟨p₁, hp₁, p₂, hp₂, hm₁, hm₂, -⟩ :=
    connector_tuple_bridge hconn hhit
  exact hsep _ (tupleUnion_intrinsicallyConnected hconn)
    ⟨p₁, hp₁, hm₁⟩ ⟨p₂, hp₂, hm₂⟩

end LatticeGauge
