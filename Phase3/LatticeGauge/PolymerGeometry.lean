/-
LatticeGauge/PolymerGeometry.lean — Phase 3, thirty-fifth stone.

PLAQUETTE POLYMERS AND THE CANONICAL DECOMPOSITION (architecture and
baptism: Sol/GPT-5.6; execution: Fable). This stone introduces
PLAQUETTE POLYMERS in finite volume: a polymer is a nonempty,
admissible, INTRINSICALLY link-connected finite set of plaquettes.
componentFamily provides the canonical decomposition of a subset:
every component of an admissible A is a polymer, and distinct
components are compatible (disjoint link supports) — so
componentFamily A is a compatible polymer family, canonically
determined by A. The mathematical core is the NEW PATH LEMMA that
stone 33 deliberately postponed: a walk witnessing connectivity
within A between elements of a component can be taken ENTIRELY within
the component (induction on SimpleGraph.Walk nil/cons — signatures
verified in the pinned v4.15 source, Walk.lean:53-55). Compatibility
of polymers implies non-adjacency AND disjointness of the plaquette
sets themselves (each plaquette owns a link in its support), so the
definition is NOT artificially strengthened. NOT YET PROVED: the
inverse correspondence (compatible family → subset), the bijection,
any realZ reindexing as a polymer gas — those are stone 36. No Ursell
activities, no log realZ, no convergence, no trees, no polymer
counting, no volume uniformity, no clustering, no mass gap.
polymerWeight carries NO geometric certificate in its type: validity
is a hypothesis of theorems, not part of the weight's type.
NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.Beta0
import LatticeGauge.WilsonDisjointBeta0
import LatticeGauge.FiniteSupportFactorizationBeta0
import LatticeGauge.PlaquetteActivity
import LatticeGauge.PlaquetteConnectivity
import LatticeGauge.ComponentFactorization

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ}

/-- **Intrinsic connectivity**: C is connected within ITSELF (not
    merely within some ambient set). -/
def IntrinsicallyConnected [NeZero N]
    (C : Finset (Site N × Dir × Dir)) : Prop :=
  ∀ p ∈ C, ∀ q ∈ C, connectedWithin C p q

/-- **A PLAQUETTE POLYMER**: nonempty, admissible, intrinsically
    link-connected. Purely geometric — no weight, no β, no χ. -/
def IsPlaquettePolymer [NeZero N] [Fintype (Site N)]
    (C : Finset (Site N × Dir × Dir)) : Prop :=
  C.Nonempty ∧ C ⊆ admissiblePlaquettes N ∧ IntrinsicallyConnected C

/-- **Compatibility**: disjoint link supports (incompatibility = link
    sharing). -/
def PlaquetteCompatible [NeZero N]
    (C D : Finset (Site N × Dir × Dir)) : Prop :=
  Disjoint (blockLinkSupport C) (blockLinkSupport D)

theorem plaquetteCompatible_symm [NeZero N]
    {C D : Finset (Site N × Dir × Dir)}
    (h : PlaquetteCompatible C D) : PlaquetteCompatible D C :=
  h.symm

/-- **A compatible polymer family**: every member is a polymer and
    distinct members are compatible. No dependent family type. -/
def IsCompatiblePolymerFamily [NeZero N] [Fintype (Site N)]
    (Γ : Finset (Finset (Site N × Dir × Dir))) : Prop :=
  (∀ C ∈ Γ, IsPlaquettePolymer C) ∧
    (∀ C ∈ Γ, ∀ D ∈ Γ, C ≠ D → PlaquetteCompatible C D)

/-- The empty family is a compatible polymer family (needed so that
    A = ∅ stays valid throughout). -/
theorem isCompatiblePolymerFamily_empty [NeZero N] [Fintype (Site N)] :
    IsCompatiblePolymerFamily
      (∅ : Finset (Finset (Site N × Dir × Dir))) :=
  ⟨fun C hC => absurd hC (Finset.not_mem_empty C),
    fun C hC => absurd hC (Finset.not_mem_empty C)⟩

/-- **THE NEW PATH LEMMA (core of the stone): a walk within A starting
    at a point connected to p stays — as a connectivity statement —
    inside the component of p.** Induction on Walk.nil / Walk.cons. -/
theorem connectedWithin_component_of_walk [NeZero N]
    {A : Finset (Site N × Dir × Dir)} {p : Site N × Dir × Dir}
    {u v : (↑A : Set (Site N × Dir × Dir))}
    (W : ((plaquetteGraph N).induce
      (↑A : Set (Site N × Dir × Dir))).Walk u v) :
    connectedWithin A p ↑u →
      connectedWithin (plaquetteComponent A p) (↑u) (↑v) := by
  induction W with
  | nil =>
    rename_i w
    intro hu
    exact connectedWithin_refl
      (mem_plaquetteComponent_iff.mpr ⟨Finset.mem_coe.mp w.2, hu⟩)
  | @cons a b c hadj W' ih =>
    intro ha
    have hab : connectedWithin A (↑a) (↑b) :=
      ⟨Finset.mem_coe.mp a.2, Finset.mem_coe.mp b.2,
        ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil⟩⟩
    have hb : connectedWithin A p ↑b := connectedWithin_trans ha hab
    have haC : (↑a : Site N × Dir × Dir) ∈ plaquetteComponent A p :=
      mem_plaquetteComponent_iff.mpr ⟨Finset.mem_coe.mp a.2, ha⟩
    have hbC : (↑b : Site N × Dir × Dir) ∈ plaquetteComponent A p :=
      mem_plaquetteComponent_iff.mpr ⟨Finset.mem_coe.mp b.2, hb⟩
    have hadjC : ((plaquetteGraph N).induce
        ((↑(plaquetteComponent A p)) :
          Set (Site N × Dir × Dir))).Adj ⟨↑a, haC⟩ ⟨↑b, hbC⟩ := by
      show (plaquetteGraph N).Adj ↑a ↑b
      exact hadj
    have hstep : connectedWithin (plaquetteComponent A p) (↑a) (↑b) :=
      ⟨haC, hbC, ⟨SimpleGraph.Walk.cons hadjC SimpleGraph.Walk.nil⟩⟩
    exact connectedWithin_trans hstep (ih hb)

section Capstones

variable [Fintype (Site N)] [NeZero N]
variable {A : Finset (Site N × Dir × Dir)}

/-- **Consequence (obligatory): every nonempty component is
    intrinsically connected.** -/
theorem plaquetteComponent_intrinsicallyConnected
    (_hA : A ⊆ admissiblePlaquettes N) (p : Site N × Dir × Dir) :
    IntrinsicallyConnected (plaquetteComponent A p) := by
  intro a ha b hb
  obtain ⟨haA, hpa⟩ := mem_plaquetteComponent_iff.mp ha
  obtain ⟨hbA, hpb⟩ := mem_plaquetteComponent_iff.mp hb
  obtain ⟨ha', hb', hreach⟩ :=
    connectedWithin_trans (connectedWithin_symm hpa) hpb
  obtain ⟨W⟩ := hreach
  exact connectedWithin_component_of_walk W hpa

/-- **3. Every member of componentFamily A is a plaquette polymer.** -/
theorem componentFamily_mem_isPolymer
    (hA : A ⊆ admissiblePlaquettes N)
    {C : Finset (Site N × Dir × Dir)}
    (hC : C ∈ componentFamily A) : IsPlaquettePolymer C := by
  refine ⟨componentFamily_mem_nonempty hA hC,
    fun q hq => hA (componentFamily_mem_subset hA hC hq), ?_⟩
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hC
  exact plaquetteComponent_intrinsicallyConnected hA p

/-- **CAPSTONE (pedra 35): the canonical decomposition of an
    admissible subset is a COMPATIBLE POLYMER FAMILY.** Together with
    `biUnion_componentFamily` (stone 34), componentFamily A is a
    compatible family of polymers whose union is exactly A. The
    inverse direction is deliberately NOT proved here (stone 36). -/
theorem isCompatiblePolymerFamily_componentFamily
    (hA : A ⊆ admissiblePlaquettes N) :
    IsCompatiblePolymerFamily (componentFamily A) :=
  ⟨fun _ hC => componentFamily_mem_isPolymer hA hC,
    fun _ hC _ hD hne =>
      componentFamily_blockLinkSupport_disjoint hA hC hD hne⟩

/-- **Explicit union capstone (restated interface of stone 34):** the
    union of the canonical polymer family is A. -/
theorem componentFamily_union_eq
    (hA : A ⊆ admissiblePlaquettes N) :
    (componentFamily A).biUnion id = A :=
  biUnion_componentFamily hA

end Capstones

/-- **4'. Compatibility implies non-adjacency**: no plaquette of C is
    adjacent to a plaquette of D. -/
theorem not_adj_of_plaquetteCompatible [NeZero N]
    {C D : Finset (Site N × Dir × Dir)}
    (h : PlaquetteCompatible C D)
    {a b : Site N × Dir × Dir} (ha : a ∈ C) (hb : b ∈ D) :
    ¬ (plaquetteGraph N).Adj a b := by
  rintro ⟨_, ℓ, hℓ⟩
  have hℓa : ℓ ∈ blockLinkSupport C :=
    ⟨a, ha, Finset.mem_coe.mpr (Finset.mem_inter.mp hℓ).1⟩
  have hℓb : ℓ ∈ blockLinkSupport D :=
    ⟨b, hb, Finset.mem_coe.mpr (Finset.mem_inter.mp hℓ).2⟩
  exact Set.disjoint_left.mp h hℓa hℓb

/-- **4''. Compatibility implies disjointness of the plaquette sets
    themselves** (each plaquette owns a link inside its support) —
    so the compatibility definition needs no artificial second
    condition. Holds for ALL Finsets, no polymer hypothesis needed. -/
theorem disjoint_of_plaquetteCompatible [NeZero N]
    {C D : Finset (Site N × Dir × Dir)}
    (h : PlaquetteCompatible C D) : Disjoint C D := by
  rw [Finset.disjoint_left]
  intro r hrC hrD
  have hℓ : ((r.1, r.2.1) : Link N) ∈ plaqLinkSet r := by
    simp [plaqLinkSet]
  have h1 : ((r.1, r.2.1) : Link N) ∈ blockLinkSupport C :=
    ⟨r, hrC, Finset.mem_coe.mpr hℓ⟩
  have h2 : ((r.1, r.2.1) : Link N) ∈ blockLinkSupport D :=
    ⟨r, hrD, Finset.mem_coe.mpr hℓ⟩
  exact Set.disjoint_left.mp h h1 h2

section Weight

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **7. The polymer weight**: w(C) = E₀[blockActivity C]. Defined for
    ANY Finset — the geometric validity (IsPlaquettePolymer) is a
    hypothesis of theorems, never part of the weight's type. -/
noncomputable def polymerWeight [NeZero N] [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) (C : Finset (Site N × Dir × Dir)) : ℝ :=
  gibbsExpectation (N := N) μm 0 χ (fun U => blockActivity β χ C U)

/-- Free normalization: the weight of the empty set is 1 (the empty
    set is NOT a polymer; this is bookkeeping, not physics). -/
theorem polymerWeight_empty [NeZero N] [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) :
    polymerWeight (N := N) μm β χ ∅ = 1 := by
  unfold polymerWeight blockActivity
  rw [gibbsExpectation_zero (N := N) μm χ]
  simp

/-- **Stone 34 rephrased in polymer language (free, no reindexing):**
    realZ is the sum over ALL subsets of the products of the polymer
    weights of their canonical components. Still a sum over subsets —
    the polymer-gas reindexing is stone 36. -/
theorem realZ_eq_sum_prod_polymerWeight [NeZero N] [Fintype (Site N)]
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) :
    realZ (N := N) μm β χ
      = ∑ A ∈ (admissiblePlaquettes N).powerset,
          ∏ C ∈ componentFamily A, polymerWeight (N := N) μm β χ C :=
  realZ_eq_sum_component_weights μm hβ mχ hχabs

end Weight

end LatticeGauge
