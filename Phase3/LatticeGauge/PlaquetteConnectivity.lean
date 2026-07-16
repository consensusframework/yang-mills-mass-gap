/-
LatticeGauge/PlaquetteConnectivity.lean — Phase 3, thirty-third stone.

FINITE PLAQUETTE CONNECTIVITY AND LINK-SHARING COMPONENTS
(architecture: Sol/GPT-5.6; execution: Fable). PURE FINITE
GEOMETRY/COMBINATORICS: link sharing is the basic geometric relation;
a finite set of plaquettes decomposes into connected blocks
(components), and DIFFERENT COMPONENTS HAVE DISJOINT LINK SUPPORTS —
the formal bridge to stone 26, NOT yet applied here.
ARCHITECTURE: the canonical SimpleGraph.induce is used INTERNALLY;
the induced subtype never appears in a public statement — the public
API (connectedWithin, plaquetteComponent, blockLinkSupport) speaks
only of ambient plaquette indices and plain Finsets. ADMISSIBILITY
DISCIPLINE (architect's instruction): the adjacency is purely
geometric; every public component-level theorem carries the explicit
certification `A ⊆ admissiblePlaquettes N` so that invalid indices
never enter the API silently (the combinatorics itself holds for any
A; the hypothesis certifies the intended physical instantiation, as
with IsClosed for loops). No `ConnectedComponent` quotient, no
canonical representatives, no `componentFamily`, no products over
components, no activity integration, no stone-26 application, no
polymer objects, no trees or animal counting, no log realZ. THIS IS
NOT: a convergence estimate; a polymer expansion; an expectation
factorization; a thermodynamic limit; clustering; a mass gap.
NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.FiniteSupportFactorizationBeta0
import LatticeGauge.PlaquetteActivity

namespace LatticeGauge

variable {N : ℕ}

/-- **The four link variables read by a plaquette** (direct reading of
    the plaquette definition: (x,μ), (x+μ,ν), (x+ν,μ), (x,ν)). -/
def plaqLinkSet [NeZero N] (p : Site N × Dir × Dir) :
    Finset (Link N) :=
  {(p.1, p.2.1), (shift p.1 p.2.1, p.2.2),
    (shift p.1 p.2.2, p.2.1), (p.1, p.2.2)}

/-- **The basic geometric relation**: two plaquettes share a link. -/
def plaquetteShareLink [NeZero N] (p q : Site N × Dir × Dir) : Prop :=
  (plaqLinkSet p ∩ plaqLinkSet q).Nonempty

theorem plaquetteShareLink_symm [NeZero N]
    {p q : Site N × Dir × Dir}
    (h : plaquetteShareLink p q) : plaquetteShareLink q p := by
  unfold plaquetteShareLink at h ⊢
  rwa [Finset.inter_comm]

/-- **The plaquette adjacency graph**: distinct plaquettes sharing a
    link. Irreflexive by the `≠`, symmetric by `inter_comm`. -/
def plaquetteGraph (N : ℕ) [NeZero N] :
    SimpleGraph (Site N × Dir × Dir) where
  Adj p q := p ≠ q ∧ plaquetteShareLink p q
  symm := by
    rintro p q ⟨hne, hsh⟩
    exact ⟨hne.symm, plaquetteShareLink_symm hsh⟩
  loopless := by
    rintro p ⟨hne, _⟩
    exact hne rfl

/-- **Connectivity WITHIN a finite set of plaquettes.** Internally
    this is `Reachable` on `SimpleGraph.induce`; the induced subtype
    is encapsulated here and never escapes to the public API. -/
def connectedWithin [NeZero N] (A : Finset (Site N × Dir × Dir))
    (p q : Site N × Dir × Dir) : Prop :=
  ∃ (hp : p ∈ A) (hq : q ∈ A),
    ((plaquetteGraph N).induce
      (↑A : Set (Site N × Dir × Dir))).Reachable ⟨p, hp⟩ ⟨q, hq⟩

theorem connectedWithin_refl [NeZero N]
    {A : Finset (Site N × Dir × Dir)} {p : Site N × Dir × Dir}
    (hp : p ∈ A) : connectedWithin A p p :=
  ⟨hp, hp, ⟨SimpleGraph.Walk.nil⟩⟩

theorem connectedWithin_symm [NeZero N]
    {A : Finset (Site N × Dir × Dir)} {p q : Site N × Dir × Dir}
    (h : connectedWithin A p q) : connectedWithin A q p := by
  obtain ⟨hp, hq, hr⟩ := h
  exact ⟨hq, hp, hr.symm⟩

theorem connectedWithin_trans [NeZero N]
    {A : Finset (Site N × Dir × Dir)} {p q r : Site N × Dir × Dir}
    (h1 : connectedWithin A p q) (h2 : connectedWithin A q r) :
    connectedWithin A p r := by
  obtain ⟨hp, hq, hr1⟩ := h1
  obtain ⟨hq', hr, hr2⟩ := h2
  exact ⟨hp, hr, hr1.trans hr2⟩

/-- **The connected block (component) of a plaquette inside A** — a
    plain Finset in the ambient index type. Decidability of
    connectivity is supplied classically and stays internal. -/
noncomputable def plaquetteComponent [NeZero N]
    (A : Finset (Site N × Dir × Dir)) (p : Site N × Dir × Dir) :
    Finset (Site N × Dir × Dir) :=
  @Finset.filter _ (fun q => connectedWithin A p q)
    (Classical.decPred _) A

theorem mem_plaquetteComponent_iff [NeZero N]
    {A : Finset (Site N × Dir × Dir)} {p q : Site N × Dir × Dir} :
    q ∈ plaquetteComponent A p
      ↔ q ∈ A ∧ connectedWithin A p q := by
  unfold plaquetteComponent
  exact Finset.mem_filter

section Capstones

variable [NeZero N] [Fintype (Site N)]
variable {A : Finset (Site N × Dir × Dir)}

/-- **A. The component is contained in A.** -/
theorem plaquetteComponent_subset
    (_hA : A ⊆ admissiblePlaquettes N) (p : Site N × Dir × Dir) :
    plaquetteComponent A p ⊆ A :=
  Finset.filter_subset _ _

/-- **B. Every element of A belongs to its own component.** -/
theorem mem_plaquetteComponent_self
    (_hA : A ⊆ admissiblePlaquettes N) {p : Site N × Dir × Dir}
    (hp : p ∈ A) : p ∈ plaquetteComponent A p :=
  mem_plaquetteComponent_iff.mpr ⟨hp, connectedWithin_refl hp⟩

/-- **C. Membership in a component is exactly connectivity within A**
    (for elements of A). -/
theorem mem_plaquetteComponent_iff_connectedWithin
    (_hA : A ⊆ admissiblePlaquettes N) {p q : Site N × Dir × Dir}
    (hq : q ∈ A) :
    q ∈ plaquetteComponent A p ↔ connectedWithin A p q := by
  rw [mem_plaquetteComponent_iff]
  exact ⟨fun h => h.2, fun h => ⟨hq, h⟩⟩

/-- **D. Connected plaquettes have the same component.** -/
theorem plaquetteComponent_eq_of_connectedWithin
    (_hA : A ⊆ admissiblePlaquettes N) {p q : Site N × Dir × Dir}
    (h : connectedWithin A p q) :
    plaquetteComponent A p = plaquetteComponent A q := by
  ext r
  simp only [mem_plaquetteComponent_iff]
  constructor
  · rintro ⟨hrA, hpr⟩
    exact ⟨hrA, connectedWithin_trans (connectedWithin_symm h) hpr⟩
  · rintro ⟨hrA, hqr⟩
    exact ⟨hrA, connectedWithin_trans h hqr⟩

/-- **E. Components that intersect are equal.** -/
theorem plaquetteComponent_eq_of_mem_inter
    (hA : A ⊆ admissiblePlaquettes N) {p q r : Site N × Dir × Dir}
    (hrp : r ∈ plaquetteComponent A p)
    (hrq : r ∈ plaquetteComponent A q) :
    plaquetteComponent A p = plaquetteComponent A q := by
  obtain ⟨_, hpr⟩ := mem_plaquetteComponent_iff.mp hrp
  obtain ⟨_, hqr⟩ := mem_plaquetteComponent_iff.mp hrq
  exact plaquetteComponent_eq_of_connectedWithin hA
    (connectedWithin_trans hpr (connectedWithin_symm hqr))

/-- **F. Different components are disjoint Finsets.** -/
theorem plaquetteComponent_disjoint_of_ne
    (hA : A ⊆ admissiblePlaquettes N) {p q : Site N × Dir × Dir}
    (hne : plaquetteComponent A p ≠ plaquetteComponent A q) :
    Disjoint (plaquetteComponent A p) (plaquetteComponent A q) := by
  rw [Finset.disjoint_left]
  intro r hrp hrq
  exact hne (plaquetteComponent_eq_of_mem_inter hA hrp hrq)

/-- **G. Every element of A belongs to some component — concretely,
    its own.** -/
theorem exists_plaquetteComponent_mem
    (hA : A ⊆ admissiblePlaquettes N) {p : Site N × Dir × Dir}
    (hp : p ∈ A) :
    ∃ q ∈ A, p ∈ plaquetteComponent A q :=
  ⟨p, hp, mem_plaquetteComponent_self hA hp⟩

end Capstones

/-- **The link support of a block of plaquettes**: the union of the
    plaqLinkSets, in the support language of stones 25-26
    (familySupport). -/
def blockLinkSupport [NeZero N] (A : Finset (Site N × Dir × Dir)) :
    Set (Link N) :=
  familySupport (fun p => (↑(plaqLinkSet p) : Set (Link N))) A

/-- **GEOMETRIC CAPSTONE (pedra 33): different components have
    DISJOINT LINK SUPPORTS.** If two plaquettes of different
    components shared a link they would be adjacent, hence connected
    within A, hence in the same component. This is the formal bridge
    to stone 26 — the probabilistic factorization is deliberately NOT
    applied here (stone 34). -/
theorem blockLinkSupport_disjoint_of_ne_component [NeZero N]
    [Fintype (Site N)] {A : Finset (Site N × Dir × Dir)}
    (hA : A ⊆ admissiblePlaquettes N) {p q : Site N × Dir × Dir}
    (hne : plaquetteComponent A p ≠ plaquetteComponent A q) :
    Disjoint (blockLinkSupport (plaquetteComponent A p))
      (blockLinkSupport (plaquetteComponent A q)) := by
  rw [Set.disjoint_left]
  rintro ℓ ⟨a, ha, hℓa⟩ ⟨b, hb, hℓb⟩
  have haA : a ∈ A := plaquetteComponent_subset hA p ha
  have hbA : b ∈ A := plaquetteComponent_subset hA q hb
  obtain ⟨_, hpa⟩ := mem_plaquetteComponent_iff.mp ha
  obtain ⟨_, hqb⟩ := mem_plaquetteComponent_iff.mp hb
  by_cases hab : a = b
  · subst hab
    exact hne (plaquetteComponent_eq_of_mem_inter hA ha hb)
  · have hsh : plaquetteShareLink a b :=
      ⟨ℓ, Finset.mem_inter.mpr
        ⟨Finset.mem_coe.mp hℓa, Finset.mem_coe.mp hℓb⟩⟩
    have hadj : ((plaquetteGraph N).induce
        (↑A : Set (Site N × Dir × Dir))).Adj ⟨a, haA⟩ ⟨b, hbA⟩ := by
      show (plaquetteGraph N).Adj a b
      exact ⟨hab, hsh⟩
    have hconn : connectedWithin A a b :=
      ⟨haA, hbA, ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil⟩⟩
    exact hne (plaquetteComponent_eq_of_connectedWithin hA
      (connectedWithin_trans hpa
        (connectedWithin_trans hconn (connectedWithin_symm hqb))))

end LatticeGauge
