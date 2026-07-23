/-
LatticeGauge/LocalGeometry.lean — Phase 3, forty-fifth stone (b-i).

UNIFORM LOCAL GEOMETRY OF THE PLAQUETTE LATTICE
(architecture: Sol/GPT-5.6; execution: Fable). The local gate counts,
independent of the volume N — with independence VISIBLE IN THE TYPES:
the bounds are ℕ-constants defined with no N parameter at all.

Census of the real representation (item 1): Site N = (Fin N)^4,
Dir = Fin 4 (the dimension is FIXED at 4 in this library — no d
parameter exists), Link N = Site N × Dir; shift adds 1 (mod N) to one
coordinate, so it is injective in the site for each fixed direction
(add_right_cancel in the Fin N group); a plaquette (x, μ, ν) has the
four sides {(x,μ), (x+μ,ν), (x+ν,μ), (x,ν)}; admissible means
μ.val < ν.val; periodic identifications in small volumes can only
DECREASE incidence counts, never break the ≤ bounds. The candidate
formulas M = 2(d−1) and M = 4·#Dir were NOT assumed: what is proved
is an upper bound by slot decomposition — every plaquette whose side
set contains a fixed link ℓ falls into one of FOUR side classes
(which of its sides equals ℓ), and inside each class the plaquette is
determined by ONE free direction; so the classes inject into Dir and
  #(plaquettes using ℓ) ≤ 4·#Dir = Fintype.card (Fin 4 × Dir) = 16.
The slot type (side index, free direction) = Fin 4 × Dir realizes
item 3 classwise; no optimal constant is claimed (in small volumes
the true count may be smaller). From the ≤ 4 sides of stone 45a:
  neighbour degree ≤ 4·16 = 64 (plaquetteAdjDegreeBound),
including the official SimpleGraph degree of the stone-33
plaquetteGraph. Finally the rooted-link sums of 45a are reduced to
rooted-PLAQUETTE sums: every polymer using ℓ contains an admissible
root plaquette using ℓ, so (overcounting deliberately accepted, same
45a machinery)
  Σ_{D ∋ ℓ} a(D) ≤ Σ_{p using ℓ} Σ_{D ∋ p} a(D) ≤ 16·B,
and combined with 45a:
  Σ_{D incompatible with C} kpWeight(D) ≤ 4·|C| · (16·B).
The ONLY remaining problem is counting connected polymers containing
a fixed root plaquette — stone 45b-ii, NOT here: no counting by size,
no Dyck codes, no plane trees, no DFS/Euler traversals, no Fin k
transport, no walk counting, no Catalan, no Penrose-tree reuse, no
geometric series, no α/β choices, no Kotecký–Preiss, no infinite
series, no thermodynamic limit. Sanity: a link used by no plaquette
roots no polymer; a plaquette sharing two links may appear in several
covers (harmless); small volumes only shrink real cardinalities.
NO axioms.
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

open MeasureTheory
open scoped Classical

namespace LatticeGauge

/-! ## 3-4. The volume-free local constants (no N in the types) -/

/-- The local slot of an incident plaquette: which of the four sides
    meets the link, and the one free transverse direction. Defined
    with NO volume parameter. -/
abbrev LinkPlaquetteSlot := Fin 4 × Dir

/-- **The incidence gate constant** — dimension-fixed, volume-free. -/
def plaquettesPerLinkBound : ℕ := Fintype.card LinkPlaquetteSlot

theorem plaquettesPerLinkBound_eq_mul :
    plaquettesPerLinkBound = 4 * Fintype.card Dir := by
  simp [plaquettesPerLinkBound, LinkPlaquetteSlot]

theorem plaquettesPerLinkBound_eq :
    plaquettesPerLinkBound = 16 := by
  simp [plaquettesPerLinkBound, LinkPlaquetteSlot]

/-- **The local degree constant** — volume-free. -/
def plaquetteAdjDegreeBound : ℕ := 4 * plaquettesPerLinkBound

theorem plaquetteAdjDegreeBound_eq :
    plaquetteAdjDegreeBound = 64 := by
  simp [plaquetteAdjDegreeBound, plaquettesPerLinkBound_eq]

variable {N : ℕ} [NeZero N]

/-! ## Census support: shift is injective in the site -/

theorem shift_injective {μ : Dir} {x y : Site N}
    (h : shift x μ = shift y μ) : x = y := by
  obtain ⟨x1, x2, x3, x4⟩ := x
  obtain ⟨y1, y2, y3, y4⟩ := y
  fin_cases μ
  · have h1 : x1 + 1 = y1 + 1 := congrArg Prod.fst h
    have h2 : x2 = y2 := congrArg (fun z => z.2.1) h
    have h3 : x3 = y3 := congrArg (fun z => z.2.2.1) h
    have h4 : x4 = y4 := congrArg (fun z => z.2.2.2) h
    have e1 : x1 = y1 := add_right_cancel h1
    subst e1; subst h2; subst h3; subst h4; rfl
  · have h1 : x1 = y1 := congrArg Prod.fst h
    have h2 : x2 + 1 = y2 + 1 := congrArg (fun z => z.2.1) h
    have h3 : x3 = y3 := congrArg (fun z => z.2.2.1) h
    have h4 : x4 = y4 := congrArg (fun z => z.2.2.2) h
    have e2 : x2 = y2 := add_right_cancel h2
    subst h1; subst e2; subst h3; subst h4; rfl
  · have h1 : x1 = y1 := congrArg Prod.fst h
    have h2 : x2 = y2 := congrArg (fun z => z.2.1) h
    have h3 : x3 + 1 = y3 + 1 := congrArg (fun z => z.2.2.1) h
    have h4 : x4 = y4 := congrArg (fun z => z.2.2.2) h
    have e3 : x3 = y3 := add_right_cancel h3
    subst h1; subst h2; subst e3; subst h4; rfl
  · have h1 : x1 = y1 := congrArg Prod.fst h
    have h2 : x2 = y2 := congrArg (fun z => z.2.1) h
    have h3 : x3 = y3 := congrArg (fun z => z.2.2.1) h
    have h4 : x4 + 1 = y4 + 1 := congrArg (fun z => z.2.2.2) h
    have e4 : x4 = y4 := add_right_cancel h4
    subst h1; subst h2; subst h3; subst e4; rfl

/-! ## The four side classes of an incident plaquette -/

/-- Membership of a link in the four-element side set, as an explicit
    four-way case split on which side it is. -/
theorem mem_plaqLinkSet_cases {p : Site N × Dir × Dir} {ℓ : Link N}
    (h : ℓ ∈ plaqLinkSet p) :
    (p.1 = ℓ.1 ∧ p.2.1 = ℓ.2)
    ∨ (shift p.1 p.2.1 = ℓ.1 ∧ p.2.2 = ℓ.2)
    ∨ (shift p.1 p.2.2 = ℓ.1 ∧ p.2.1 = ℓ.2)
    ∨ (p.1 = ℓ.1 ∧ p.2.2 = ℓ.2) := by
  unfold plaqLinkSet at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h
  · exact Or.inl ⟨by rw [h], by rw [h]⟩
  · exact Or.inr (Or.inl ⟨by rw [h], by rw [h]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by rw [h], by rw [h]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by rw [h], by rw [h]⟩))

variable [Fintype (Site N)]

private noncomputable def slotFilter0 (ℓ : Link N) :
    Finset (Site N × Dir × Dir) :=
  Finset.univ.filter (fun p => p.1 = ℓ.1 ∧ p.2.1 = ℓ.2)

private noncomputable def slotFilter1 (ℓ : Link N) :
    Finset (Site N × Dir × Dir) :=
  Finset.univ.filter (fun p => shift p.1 p.2.1 = ℓ.1 ∧ p.2.2 = ℓ.2)

private noncomputable def slotFilter2 (ℓ : Link N) :
    Finset (Site N × Dir × Dir) :=
  Finset.univ.filter (fun p => shift p.1 p.2.2 = ℓ.1 ∧ p.2.1 = ℓ.2)

private noncomputable def slotFilter3 (ℓ : Link N) :
    Finset (Site N × Dir × Dir) :=
  Finset.univ.filter (fun p => p.1 = ℓ.1 ∧ p.2.2 = ℓ.2)

private theorem slotFilter0_card_le (ℓ : Link N) :
    (slotFilter0 ℓ).card ≤ Fintype.card Dir := by
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun p => p.2.2)
    (fun p _ => Finset.mem_univ _) ?_
  intro a ha b hb hab
  unfold slotFilter0 at ha hb
  rw [Finset.mem_coe, Finset.mem_filter] at ha hb
  dsimp only at hab
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  simp only [Prod.mk.injEq]
  exact ⟨ha.2.1.trans hb.2.1.symm, ha.2.2.trans hb.2.2.symm, hab⟩

private theorem slotFilter1_card_le (ℓ : Link N) :
    (slotFilter1 ℓ).card ≤ Fintype.card Dir := by
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun p => p.2.1)
    (fun p _ => Finset.mem_univ _) ?_
  intro a ha b hb hab
  unfold slotFilter1 at ha hb
  rw [Finset.mem_coe, Finset.mem_filter] at ha hb
  dsimp only at hab
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  dsimp only at ha hb hab
  have h3 : a3 = b3 := ha.2.2.trans hb.2.2.symm
  have h1 : a1 = b1 := by
    refine shift_injective (μ := b2) ?_
    have hs : shift a1 a2 = shift b1 b2 := ha.2.1.trans hb.2.1.symm
    rwa [hab] at hs
  simp only [Prod.mk.injEq]
  exact ⟨h1, hab, h3⟩

private theorem slotFilter2_card_le (ℓ : Link N) :
    (slotFilter2 ℓ).card ≤ Fintype.card Dir := by
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun p => p.2.2)
    (fun p _ => Finset.mem_univ _) ?_
  intro a ha b hb hab
  unfold slotFilter2 at ha hb
  rw [Finset.mem_coe, Finset.mem_filter] at ha hb
  dsimp only at hab
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  dsimp only at ha hb hab
  have h2 : a2 = b2 := ha.2.2.trans hb.2.2.symm
  have h1 : a1 = b1 := by
    refine shift_injective (μ := b3) ?_
    have hs : shift a1 a3 = shift b1 b3 := ha.2.1.trans hb.2.1.symm
    rwa [hab] at hs
  simp only [Prod.mk.injEq]
  exact ⟨h1, h2, hab⟩

private theorem slotFilter3_card_le (ℓ : Link N) :
    (slotFilter3 ℓ).card ≤ Fintype.card Dir := by
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun p => p.2.1)
    (fun p _ => Finset.mem_univ _) ?_
  intro a ha b hb hab
  unfold slotFilter3 at ha hb
  rw [Finset.mem_coe, Finset.mem_filter] at ha hb
  dsimp only at hab
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  simp only [Prod.mk.injEq]
  exact ⟨ha.2.1.trans hb.2.1.symm, hab, ha.2.2.trans hb.2.2.symm⟩

/-! ## 2. Plaquettes incident on a link -/

/-- **Admissible plaquettes whose side set contains ℓ** (a Finset of
    PLAQUETTES — not to be confused with the 45a `polymersUsingLink`,
    a Finset of polymers). -/
noncomputable def plaquettesUsingLink (ℓ : Link N) :
    Finset (Site N × Dir × Dir) :=
  (admissiblePlaquettes N).filter (fun p => ℓ ∈ plaqLinkSet p)

theorem mem_plaquettesUsingLink {ℓ : Link N}
    {p : Site N × Dir × Dir} :
    p ∈ plaquettesUsingLink ℓ
      ↔ p ∈ admissiblePlaquettes N ∧ ℓ ∈ plaqLinkSet p := by
  unfold plaquettesUsingLink
  simp [Finset.mem_filter]

/-- Every plaquette (admissible or not) using ℓ lies in one of the
    four side classes. -/
private theorem usingLink_subset_slots (ℓ : Link N) :
    Finset.univ.filter (fun p : Site N × Dir × Dir =>
        ℓ ∈ plaqLinkSet p)
      ⊆ (slotFilter0 ℓ ∪ slotFilter1 ℓ)
          ∪ (slotFilter2 ℓ ∪ slotFilter3 ℓ) := by
  intro p hp
  rw [Finset.mem_filter] at hp
  rcases mem_plaqLinkSet_cases hp.2 with h | h | h | h
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  · exact Finset.mem_union_right _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  · exact Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))

/-- **4. THE INCIDENCE GATE**: at most 16 plaquettes use a fixed
    link, uniformly in the volume (in small volumes the true count
    may be smaller; no optimality claimed). -/
theorem plaquettesUsingLink_card_le (ℓ : Link N) :
    (plaquettesUsingLink ℓ).card ≤ plaquettesPerLinkBound := by
  have hsub : plaquettesUsingLink ℓ
      ⊆ Finset.univ.filter (fun p : Site N × Dir × Dir =>
          ℓ ∈ plaqLinkSet p) :=
    Finset.filter_subset_filter _ (Finset.subset_univ _)
  have h1 := Finset.card_le_card
    (hsub.trans (usingLink_subset_slots ℓ))
  have h2 := Finset.card_union_le (slotFilter0 ℓ ∪ slotFilter1 ℓ)
    (slotFilter2 ℓ ∪ slotFilter3 ℓ)
  have h3 := Finset.card_union_le (slotFilter0 ℓ) (slotFilter1 ℓ)
  have h4 := Finset.card_union_le (slotFilter2 ℓ) (slotFilter3 ℓ)
  have b0 := slotFilter0_card_le ℓ
  have b1 := slotFilter1_card_le ℓ
  have b2 := slotFilter2_card_le ℓ
  have b3 := slotFilter3_card_le ℓ
  rw [plaquettesPerLinkBound_eq_mul]
  omega

/-! ## 5-7. The link neighbourhood of a plaquette -/

/-- The neighbours of p in the stone-33 adjacency: distinct
    plaquettes sharing a link. The same neighbour may share more than
    one link — no disjointness demanded. -/
noncomputable def plaquetteLinkNeighbors (p : Site N × Dir × Dir) :
    Finset (Site N × Dir × Dir) :=
  Finset.univ.filter (fun q => (plaquetteGraph N).Adj p q)

theorem mem_plaquetteLinkNeighbors {p q : Site N × Dir × Dir} :
    q ∈ plaquetteLinkNeighbors p
      ↔ p ≠ q ∧ ∃ ℓ : Link N,
          ℓ ∈ plaqLinkSet p ∧ ℓ ∈ plaqLinkSet q := by
  unfold plaquetteLinkNeighbors plaquetteGraph
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, hsh⟩
    obtain ⟨ℓ, hℓ⟩ := hsh
    rw [Finset.mem_inter] at hℓ
    exact ⟨hne, ℓ, hℓ⟩
  · rintro ⟨hne, ℓ, hℓp, hℓq⟩
    exact ⟨hne, ⟨ℓ, Finset.mem_inter.mpr ⟨hℓp, hℓq⟩⟩⟩

/-- **6. The neighbourhood is covered by the four gates** (a
    neighbour sharing several links may appear under several of
    them; p itself possibly appearing on the right is harmless). -/
theorem plaquetteLinkNeighbors_subset_biUnion
    (p : Site N × Dir × Dir) :
    plaquetteLinkNeighbors p
      ⊆ (plaqLinkSet p).biUnion (fun ℓ =>
          Finset.univ.filter (fun q : Site N × Dir × Dir =>
            ℓ ∈ plaqLinkSet q)) := by
  intro q hq
  obtain ⟨-, ℓ, hℓp, hℓq⟩ := mem_plaquetteLinkNeighbors.mp hq
  rw [Finset.mem_biUnion]
  exact ⟨ℓ, hℓp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hℓq⟩⟩

private theorem univFilter_usingLink_card_le (ℓ : Link N) :
    (Finset.univ.filter (fun p : Site N × Dir × Dir =>
        ℓ ∈ plaqLinkSet p)).card ≤ plaquettesPerLinkBound := by
  have h1 := Finset.card_le_card (usingLink_subset_slots ℓ)
  have h2 := Finset.card_union_le (slotFilter0 ℓ ∪ slotFilter1 ℓ)
    (slotFilter2 ℓ ∪ slotFilter3 ℓ)
  have h3 := Finset.card_union_le (slotFilter0 ℓ) (slotFilter1 ℓ)
  have h4 := Finset.card_union_le (slotFilter2 ℓ) (slotFilter3 ℓ)
  have b0 := slotFilter0_card_le ℓ
  have b1 := slotFilter1_card_le ℓ
  have b2 := slotFilter2_card_le ℓ
  have b3 := slotFilter3_card_le ℓ
  rw [plaquettesPerLinkBound_eq_mul]
  omega

/-- **7. THE DEGREE GATE**: at most 4·16 = 64 link-neighbours,
    uniformly in the volume (the loose bound is kept — no subtraction
    of p itself). -/
theorem plaquetteLinkNeighbors_card_le (p : Site N × Dir × Dir) :
    (plaquetteLinkNeighbors p).card ≤ plaquetteAdjDegreeBound := by
  refine (Finset.card_le_card
    (plaquetteLinkNeighbors_subset_biUnion p)).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  unfold plaquetteAdjDegreeBound
  calc ∑ ℓ ∈ plaqLinkSet p,
        (Finset.univ.filter (fun q : Site N × Dir × Dir =>
          ℓ ∈ plaqLinkSet q)).card
      ≤ ∑ _ℓ ∈ plaqLinkSet p, plaquettesPerLinkBound :=
        Finset.sum_le_sum
          (fun ℓ _ => univFilter_usingLink_card_le ℓ)
    _ = (plaqLinkSet p).card * plaquettesPerLinkBound := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 4 * plaquettesPerLinkBound :=
        Nat.mul_le_mul_right _ (card_plaqLinkSet_le p)

/-! ## 8. The official graph degree -/

theorem plaquetteGraph_neighborFinset_eq (p : Site N × Dir × Dir) :
    (plaquetteGraph N).neighborFinset p = plaquetteLinkNeighbors p := by
  ext q
  rw [SimpleGraph.mem_neighborFinset]
  unfold plaquetteLinkNeighbors
  simp [Finset.mem_filter]

/-- **CAPSTONE (item 8)**: the stone-33 adjacency graph — the one
    that defines connected polymers — has degree ≤ 64 at every
    plaquette, uniformly in the volume. -/
theorem plaquetteGraph_degree_le (p : Site N × Dir × Dir) :
    (plaquetteGraph N).degree p ≤ plaquetteAdjDegreeBound := by
  unfold SimpleGraph.degree
  rw [plaquetteGraph_neighborFinset_eq]
  exact plaquetteLinkNeighbors_card_le p

/-! ## 10. Root choice: from links to plaquettes -/

/-- The polymers whose plaquette set contains a fixed root. -/
noncomputable def polymersContainingPlaquette
    (p : Site N × Dir × Dir) :
    Finset (Finset (Site N × Dir × Dir)) :=
  (allPlaquettePolymers N).filter (fun D => p ∈ D)

theorem mem_polymersContainingPlaquette {p : Site N × Dir × Dir}
    {D : Finset (Site N × Dir × Dir)} :
    D ∈ polymersContainingPlaquette p
      ↔ D ∈ allPlaquettePolymers N ∧ p ∈ D := by
  unfold polymersContainingPlaquette
  simp [Finset.mem_filter]

theorem subset_admissible_of_mem_allPlaquettePolymers
    {D : Finset (Site N × Dir × Dir)}
    (hD : D ∈ allPlaquettePolymers N) :
    D ⊆ admissiblePlaquettes N := by
  unfold allPlaquettePolymers at hD
  rw [Finset.mem_filter, Finset.mem_powerset] at hD
  exact hD.1

/-- **Every polymer using ℓ contains an ADMISSIBLE root plaquette
    using ℓ.** -/
theorem exists_root_of_mem_polymersUsingLink {ℓ : Link N}
    {D : Finset (Site N × Dir × Dir)}
    (hD : D ∈ polymersUsingLink ℓ) :
    ∃ p ∈ plaquettesUsingLink ℓ, p ∈ D := by
  obtain ⟨hall, hsupp⟩ := mem_polymersUsingLink.mp hD
  have hfin : ℓ ∈ blockLinkFinset D := mem_blockLinkFinset.mpr hsupp
  unfold blockLinkFinset at hfin
  rw [Finset.mem_biUnion] at hfin
  obtain ⟨p, hpD, hpℓ⟩ := hfin
  exact ⟨p, mem_plaquettesUsingLink.mpr
    ⟨subset_admissible_of_mem_allPlaquettePolymers hall hpD, hpℓ⟩,
    hpD⟩

/-- The rooted-link polymers are covered by the rooted-plaquette
    families over the ≤ 16 incident plaquettes (the same D may appear
    for several roots — deliberate overcounting). -/
theorem polymersUsingLink_subset_biUnion (ℓ : Link N) :
    polymersUsingLink ℓ
      ⊆ (plaquettesUsingLink ℓ).biUnion polymersContainingPlaquette := by
  intro D hD
  obtain ⟨p, hp, hpD⟩ := exists_root_of_mem_polymersUsingLink hD
  rw [Finset.mem_biUnion]
  exact ⟨p, hp, mem_polymersContainingPlaquette.mpr
    ⟨(mem_polymersUsingLink.mp hD).1, hpD⟩⟩

/-! ## 11. Reduction of rooted-link sums to rooted-plaquette sums -/

theorem rootedLink_sum_le_rootedPlaquette_sum
    {a : Finset (Site N × Dir × Dir) → ℝ}
    (ha : ∀ D ∈ allPlaquettePolymers N, 0 ≤ a D) (ℓ : Link N) :
    (∑ D ∈ polymersUsingLink ℓ, a D)
      ≤ ∑ p ∈ plaquettesUsingLink ℓ,
          ∑ D ∈ polymersContainingPlaquette p, a D := by
  refine sum_le_sum_over_cover (polymersUsingLink_subset_biUnion ℓ) ?_
  intro D hD
  rw [Finset.mem_biUnion] at hD
  obtain ⟨p, -, hDp⟩ := hD
  exact ha D (mem_polymersContainingPlaquette.mp hDp).1

/-- **CAPSTONE OPERACIONAL (45b-i)**: a uniform rooted-plaquette
    bound gives a rooted-link bound with the volume-free factor 16. -/
theorem rootedLink_sum_le_bound_mul
    {a : Finset (Site N × Dir × Dir) → ℝ}
    (ha : ∀ D ∈ allPlaquettePolymers N, 0 ≤ a D) (ℓ : Link N)
    {B : ℝ} (hB : 0 ≤ B)
    (hroot : ∀ p ∈ plaquettesUsingLink ℓ,
      (∑ D ∈ polymersContainingPlaquette p, a D) ≤ B) :
    (∑ D ∈ polymersUsingLink ℓ, a D)
      ≤ (plaquettesPerLinkBound : ℝ) * B := by
  refine (rootedLink_sum_le_rootedPlaquette_sum ha ℓ).trans ?_
  have h := Finset.sum_le_card_nsmul (plaquettesUsingLink ℓ)
    (fun p => ∑ D ∈ polymersContainingPlaquette p, a D) B hroot
  rw [nsmul_eq_mul] at h
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast plaquettesUsingLink_card_le ℓ) hB

/-! ## 12-13. Specialization to the KP weight and full combination -/

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

theorem rootedLink_kp_sum_le
    (β : ℝ) (χ : G → ℝ) (α : ℝ) (ℓ : Link N)
    {B : ℝ} (hB : 0 ≤ B)
    (hroot : ∀ p ∈ plaquettesUsingLink ℓ,
      (∑ D ∈ polymersContainingPlaquette p,
        kpActivityWeight μm β χ α D) ≤ B) :
    (∑ D ∈ polymersUsingLink ℓ, kpActivityWeight μm β χ α D)
      ≤ (plaquettesPerLinkBound : ℝ) * B :=
  rootedLink_sum_le_bound_mul
    (fun D _ => kpActivityWeight_nonneg μm β χ α D) ℓ hB hroot

/-- **FULL SCHEME (item 13)**: controlling the polymers incompatible
    with C is reduced to controlling connected polymers containing a
    fixed plaquette; all external geometric factors (4 per plaquette
    of C, 16 per link) are volume-free. The ONLY remaining problem is
    the size-counting of rooted connected polymers (45b-ii). -/
theorem incompatible_kp_sum_le_full
    (β : ℝ) (χ : G → ℝ) (α : ℝ)
    (C : Finset (Site N × Dir × Dir)) {B : ℝ} (hB : 0 ≤ B)
    (hroot : ∀ p ∈ admissiblePlaquettes N,
      (∑ D ∈ polymersContainingPlaquette p,
        kpActivityWeight μm β χ α D) ≤ B) :
    (∑ D ∈ incompatiblePolymers C, kpActivityWeight μm β χ α D)
      ≤ ((4 * C.card : ℕ) : ℝ)
          * ((plaquettesPerLinkBound : ℝ) * B) := by
  refine incompatible_kpActivity_sum_le_four_mul μm β χ α C
    (mul_nonneg (Nat.cast_nonneg _) hB) ?_
  intro ℓ _
  refine rootedLink_kp_sum_le μm β χ α ℓ hB ?_
  intro p hp
  exact hroot p (mem_plaquettesUsingLink.mp hp).1

/-! ## 14. Sanity -/

/-- **A. A link used by no plaquette roots no polymer** (the other
    sanities are immediate: a single incident plaquette gives a
    single root sum; multi-link sharers may repeat across covers
    without harming the inequalities; small volumes only shrink the
    real cardinalities, never break the uniform bounds). -/
theorem polymersUsingLink_eq_empty {ℓ : Link N}
    (h : plaquettesUsingLink ℓ = (∅ : Finset (Site N × Dir × Dir))) :
    polymersUsingLink ℓ
      = (∅ : Finset (Finset (Site N × Dir × Dir))) := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro D hD
  obtain ⟨p, hp, -⟩ := exists_root_of_mem_polymersUsingLink hD
  rw [h] at hp
  exact Finset.not_mem_empty p hp

end LatticeGauge
