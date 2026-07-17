/-
LatticeGauge/PolymerGas.lean — Phase 3, thirty-sixth stone.

EXACT FINITE POLYMER-GAS REPRESENTATION OF realZ (architecture:
Sol/GPT-5.6; execution: Fable). This stone completes the exact part of
the expansion: Mayer → components → polymers → FINITE GAS. The inverse
of stone 35 is proved — a walk inside the union of a compatible family
CANNOT cross between distinct polymers (path confinement), so each
polymer is exactly a component of the union and
componentFamily (polymerUnion Γ) = Γ. Together with stone 34/35's
polymerUnion (componentFamily A) = A this is a bijection between
admissible plaquette subsets and compatible polymer families, and the
partition function reindexes EXACTLY:
  realZ β χ = Σ_{Γ compatible} ∏_{C ∈ Γ} polymerWeight C —
a finite HARD-CORE polymer gas (compatibility = disjoint link
supports). The empty family represents the A = ∅ term (empty product
= 1); no artificial Nonempty hypotheses. STILL AN EXACT FINITE-VOLUME
IDENTITY: no Ursell coefficients, no connected functions, no log Z
expansion, no tree-graph inequality, no weight estimates, no polymer
counting, no Kotecký–Preiss, no volume uniformity, no thermodynamic
limit, no clustering, no mass gap. NO axioms.
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
import LatticeGauge.PolymerGeometry

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ}

/-- **1. The union of a family of polymer candidates** — plain
    biUnion, no dependent subtype. -/
def polymerUnion [NeZero N]
    (Γ : Finset (Finset (Site N × Dir × Dir))) :
    Finset (Site N × Dir × Dir) :=
  Γ.biUnion id

theorem mem_polymerUnion [NeZero N]
    {Γ : Finset (Finset (Site N × Dir × Dir))}
    {p : Site N × Dir × Dir} :
    p ∈ polymerUnion Γ ↔ ∃ C ∈ Γ, p ∈ C := by
  unfold polymerUnion
  simp [Finset.mem_biUnion]

@[simp] theorem polymerUnion_empty [NeZero N] :
    polymerUnion (∅ : Finset (Finset (Site N × Dir × Dir))) = ∅ :=
  Finset.biUnion_empty

/-- **1A. Each member is contained in the union.** -/
theorem subset_polymerUnion [NeZero N]
    {Γ : Finset (Finset (Site N × Dir × Dir))}
    {C : Finset (Site N × Dir × Dir)} (hC : C ∈ Γ) :
    C ⊆ polymerUnion Γ :=
  fun _ hx => mem_polymerUnion.mpr ⟨C, hC, hx⟩

section Fintype

variable [Fintype (Site N)] [NeZero N]

/-- **1B. The union of a compatible polymer family is admissible.** -/
theorem polymerUnion_subset_admissible
    {Γ : Finset (Finset (Site N × Dir × Dir))}
    (hΓ : IsCompatiblePolymerFamily Γ) :
    polymerUnion Γ ⊆ admissiblePlaquettes N := by
  intro x hx
  obtain ⟨C, hC, hxC⟩ := mem_polymerUnion.mp hx
  exact (hΓ.1 C hC).2.1 hxC

/-- **Monotonicity of connectivity under inclusion**: a walk in the
    induced graph on A transports along A ⊆ B (local Walk induction;
    the induced adjacency is defeq to the ambient one on both sides). -/
private theorem reachable_mono_aux
    {A B : Finset (Site N × Dir × Dir)} (hAB : A ⊆ B) :
    ∀ {u v : (↑A : Set (Site N × Dir × Dir))},
    ((plaquetteGraph N).induce
      (↑A : Set (Site N × Dir × Dir))).Walk u v →
    ((plaquetteGraph N).induce
      (↑B : Set (Site N × Dir × Dir))).Reachable
      ⟨↑u, Finset.mem_coe.mpr (hAB (Finset.mem_coe.mp u.2))⟩
      ⟨↑v, Finset.mem_coe.mpr (hAB (Finset.mem_coe.mp v.2))⟩ := by
  intro u v W
  induction W with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | @cons a b c hadj W' ih =>
    have hadjB : ((plaquetteGraph N).induce
        (↑B : Set (Site N × Dir × Dir))).Adj
        ⟨↑a, Finset.mem_coe.mpr (hAB (Finset.mem_coe.mp a.2))⟩
        ⟨↑b, Finset.mem_coe.mpr (hAB (Finset.mem_coe.mp b.2))⟩ := by
      show (plaquetteGraph N).Adj ↑a ↑b
      exact hadj
    exact SimpleGraph.Reachable.trans
      ⟨SimpleGraph.Walk.cons hadjB SimpleGraph.Walk.nil⟩ ih

theorem connectedWithin_mono
    {A B : Finset (Site N × Dir × Dir)} (hAB : A ⊆ B)
    {p q : Site N × Dir × Dir}
    (h : connectedWithin A p q) : connectedWithin B p q := by
  obtain ⟨hp, hq, ⟨W⟩⟩ := h
  exact ⟨hAB hp, hAB hq, reachable_mono_aux hAB W⟩

/-- **2. PATH CONFINEMENT (core of the stone)**: inside the union of a
    compatible family, a walk that starts in a polymer C cannot cross
    into a distinct polymer — one adjacency step would share a link,
    contradicting compatibility. -/
private theorem walk_confined_aux
    {Γ : Finset (Finset (Site N × Dir × Dir))}
    (hΓ : IsCompatiblePolymerFamily Γ)
    {C : Finset (Site N × Dir × Dir)} (hC : C ∈ Γ) :
    ∀ {u v : (↑(polymerUnion Γ) : Set (Site N × Dir × Dir))},
    ((plaquetteGraph N).induce
      (↑(polymerUnion Γ) : Set (Site N × Dir × Dir))).Walk u v →
    (↑u : Site N × Dir × Dir) ∈ C →
    (↑v : Site N × Dir × Dir) ∈ C := by
  intro u v W
  induction W with
  | nil =>
    intro h
    exact h
  | @cons a b c hadj W' ih =>
    intro ha
    have hGadj : (plaquetteGraph N).Adj ↑a ↑b := hadj
    have hbU : (↑b : Site N × Dir × Dir) ∈ polymerUnion Γ :=
      Finset.mem_coe.mp b.2
    obtain ⟨D, hD, hbD⟩ := mem_polymerUnion.mp hbU
    by_cases hCD : C = D
    · exact ih (by rw [hCD]; exact hbD)
    · exact absurd hGadj
        (not_adj_of_plaquetteCompatible (hΓ.2 C hC D hD hCD) ha hbD)

theorem mem_of_connectedWithin_polymerUnion
    {Γ : Finset (Finset (Site N × Dir × Dir))}
    (hΓ : IsCompatiblePolymerFamily Γ)
    {C : Finset (Site N × Dir × Dir)} (hC : C ∈ Γ)
    {p q : Site N × Dir × Dir} (hp : p ∈ C)
    (hconn : connectedWithin (polymerUnion Γ) p q) : q ∈ C := by
  obtain ⟨hpU, hqU, ⟨W⟩⟩ := hconn
  exact walk_confined_aux hΓ hC W hp

/-- **3. Each polymer of a compatible family is EXACTLY a component of
    the union.** ⊆: path confinement; ⊇: intrinsic connectivity of C
    plus monotonicity of connectivity under C ⊆ polymerUnion Γ. -/
theorem plaquetteComponent_polymerUnion_eq
    {Γ : Finset (Finset (Site N × Dir × Dir))}
    (hΓ : IsCompatiblePolymerFamily Γ)
    {C : Finset (Site N × Dir × Dir)} (hC : C ∈ Γ)
    {p : Site N × Dir × Dir} (hp : p ∈ C) :
    plaquetteComponent (polymerUnion Γ) p = C := by
  ext q
  rw [mem_plaquetteComponent_iff]
  constructor
  · rintro ⟨_, hconn⟩
    exact mem_of_connectedWithin_polymerUnion hΓ hC hp hconn
  · intro hqC
    refine ⟨subset_polymerUnion hC hqC, ?_⟩
    have hintr := (hΓ.1 C hC).2.2
    exact connectedWithin_mono (subset_polymerUnion hC)
      (hintr p hp q hqC)

/-- **4. RECOVERY OF THE FAMILY (combinatorial capstone)**:
    componentFamily inverts polymerUnion on compatible families.
    Valid for Γ = ∅ (both sides empty), with no representative
    choices. -/
theorem componentFamily_polymerUnion_eq
    {Γ : Finset (Finset (Site N × Dir × Dir))}
    (hΓ : IsCompatiblePolymerFamily Γ) :
    componentFamily (polymerUnion Γ) = Γ := by
  ext C
  constructor
  · intro hC
    obtain ⟨p, hpU, rfl⟩ := Finset.mem_image.mp hC
    obtain ⟨D, hD, hpD⟩ := mem_polymerUnion.mp hpU
    rw [plaquetteComponent_polymerUnion_eq hΓ hD hpD]
    exact hD
  · intro hC
    obtain ⟨p, hp⟩ := (hΓ.1 C hC).1
    refine Finset.mem_image.mpr
      ⟨p, subset_polymerUnion hC hp, ?_⟩
    exact plaquetteComponent_polymerUnion_eq hΓ hC hp

/-- **The direction already obtained by stones 34/35, restated in gas
    language**: polymerUnion inverts componentFamily on admissible
    subsets. -/
theorem polymerUnion_componentFamily_eq
    {A : Finset (Site N × Dir × Dir)}
    (hA : A ⊆ admissiblePlaquettes N) :
    polymerUnion (componentFamily A) = A :=
  biUnion_componentFamily hA

/-- **6a. Injectivity of componentFamily on admissible subsets.** -/
theorem componentFamily_inj
    {A₁ A₂ : Finset (Site N × Dir × Dir)}
    (h₁ : A₁ ⊆ admissiblePlaquettes N)
    (h₂ : A₂ ⊆ admissiblePlaquettes N)
    (h : componentFamily A₁ = componentFamily A₂) : A₁ = A₂ := by
  have := congrArg polymerUnion h
  rwa [polymerUnion_componentFamily_eq h₁,
    polymerUnion_componentFamily_eq h₂] at this

/-- **6b. Injectivity of polymerUnion on compatible families.** -/
theorem polymerUnion_inj
    {Γ₁ Γ₂ : Finset (Finset (Site N × Dir × Dir))}
    (h₁ : IsCompatiblePolymerFamily Γ₁)
    (h₂ : IsCompatiblePolymerFamily Γ₂)
    (h : polymerUnion Γ₁ = polymerUnion Γ₂) : Γ₁ = Γ₂ := by
  have := congrArg componentFamily h
  rwa [componentFamily_polymerUnion_eq h₁,
    componentFamily_polymerUnion_eq h₂] at this

/-- **5a. The finite universe of admissible polymers.** -/
noncomputable def allPlaquettePolymers (N : ℕ) [NeZero N]
    [Fintype (Site N)] : Finset (Finset (Site N × Dir × Dir)) :=
  (admissiblePlaquettes N).powerset.filter
    (fun C => IsPlaquettePolymer C)

/-- **5b. The finite universe of compatible polymer families.** -/
noncomputable def compatiblePolymerFamilies (N : ℕ) [NeZero N]
    [Fintype (Site N)] :
    Finset (Finset (Finset (Site N × Dir × Dir))) :=
  (allPlaquettePolymers N).powerset.filter
    (fun Γ => IsCompatiblePolymerFamily Γ)

/-- **5c. Membership characterization**: the filter condition is
    exactly IsCompatiblePolymerFamily (the powerset containment is a
    consequence). -/
theorem mem_compatiblePolymerFamilies
    {Γ : Finset (Finset (Site N × Dir × Dir))} :
    Γ ∈ compatiblePolymerFamilies N ↔ IsCompatiblePolymerFamily Γ := by
  unfold compatiblePolymerFamilies allPlaquettePolymers
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, h⟩
    intro C hC
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (h.1 C hC).2.1, h.1 C hC⟩

/-- The empty family belongs to the universe — it represents the
    A = ∅ term of the gas (empty product = 1). -/
theorem empty_mem_compatiblePolymerFamilies :
    (∅ : Finset (Finset (Site N × Dir × Dir)))
      ∈ compatiblePolymerFamilies N :=
  mem_compatiblePolymerFamilies.mpr isCompatiblePolymerFamily_empty

/-- **5d. The canonical decomposition lands in the universe.** -/
theorem componentFamily_mem_compatiblePolymerFamilies
    {A : Finset (Site N × Dir × Dir)}
    (hA : A ⊆ admissiblePlaquettes N) :
    componentFamily A ∈ compatiblePolymerFamilies N :=
  mem_compatiblePolymerFamilies.mpr
    (isCompatiblePolymerFamily_componentFamily hA)

end Fintype

section Measure

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **7. FINAL CAPSTONE (pedra 36): the EXACT FINITE POLYMER-GAS
    representation.** The partition function is the sum, over ALL
    compatible families of plaquette polymers, of the products of the
    polymer weights:
    realZ β χ = Σ_{Γ compatible} ∏_{C ∈ Γ} w_β(C).
    A finite HARD-CORE gas (compatibility = disjoint link supports).
    The empty family carries the A = ∅ term with empty product 1.
    Exact finite-volume identity — no convergence, no log Z, no
    Ursell coefficients, no volume uniformity, no clustering, no mass
    gap. -/
theorem realZ_eq_finite_polymer_gas [NeZero N] [Fintype (Site N)]
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) :
    realZ (N := N) μm β χ
      = ∑ Γ ∈ compatiblePolymerFamilies N,
          ∏ C ∈ Γ, polymerWeight (N := N) μm β χ C := by
  rw [realZ_eq_sum_prod_polymerWeight μm hβ mχ hχabs]
  exact Finset.sum_bij
    (fun A _ => componentFamily A)
    (fun A ha => componentFamily_mem_compatiblePolymerFamilies
      (Finset.mem_powerset.mp ha))
    (fun A₁ h₁ A₂ h₂ heq => componentFamily_inj
      (Finset.mem_powerset.mp h₁) (Finset.mem_powerset.mp h₂) heq)
    (fun Γ hΓ => ⟨polymerUnion Γ,
      Finset.mem_powerset.mpr (polymerUnion_subset_admissible
        (mem_compatiblePolymerFamilies.mp hΓ)),
      componentFamily_polymerUnion_eq
        (mem_compatiblePolymerFamilies.mp hΓ)⟩)
    (fun A ha => rfl)

end Measure

end LatticeGauge
