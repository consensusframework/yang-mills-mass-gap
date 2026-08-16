/-
LatticeGauge/KPTypedGas.lean — stone 49C-I: THE TYPED HARD-CORE
GAS BRIDGE (architecture: Sol/GPT-5.6; execution: Fable).

The raw/subtype level gap is eliminated: Stone 36 delivers realZ as
the hard-core gas over RAW families of plaquette sets; the 49A/B
cluster series lives on the subtype Polymer N. This stone builds
the typed family universe, the exact raw↔typed correspondence
(injective shadow rawFamily = image of Subtype.val; the lift by
attach; compatibility equivalent across the bridge), the typed gas
typedPolymerGas, the EXACT reindexation (product preserved exactly
— families are Finsets: no factorial, no multiplicity), and the
CAPSTONE realZ_eq_typed_polymer_gas with the full Stone-36
generality (0 ≤ β, measurable χ, |χ| ≤ 1 — NO β ≤ 1/40000: this is
a FINITE identity, valid before any KP/convergence).
NOT here (49C-II+, not started): gas coefficients Aₙ, the
inclusion–exclusion switch, the root-component recurrence,
exp/log, cluster-expansion identification. NOT claimed:
exp(clusterSum) = gas, log realZ = clusterSum, any realZ
positivity from clusters. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.PolymerGeometry
import LatticeGauge.PolymerGas
import LatticeGauge.KPCoefficients

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## 49C-I.1 — membership helpers (the two directions of the
    polymer-universe filter, named) -/

theorem isPolymer_of_mem_all
    {C : Finset (Site N × Dir × Dir)}
    (h : C ∈ allPlaquettePolymers N) : IsPlaquettePolymer C := by
  unfold allPlaquettePolymers at h
  exact (Finset.mem_filter.mp h).2

theorem mem_all_of_isPolymer
    {C : Finset (Site N × Dir × Dir)}
    (h : IsPlaquettePolymer C) : C ∈ allPlaquettePolymers N := by
  unfold allPlaquettePolymers
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr h.2.1, h⟩

/-! ## 49C-I.2 — the raw shadow and the typed universe -/

/-- The raw shadow of a typed family (injective: Subtype.val). -/
noncomputable def rawFamily (Γ : Finset (Polymer N)) :
    Finset (Finset (Site N × Dir × Dir)) :=
  Γ.image Subtype.val

theorem rawFamily_injective :
    Function.Injective (rawFamily (N := N)) :=
  Finset.image_injective Subtype.val_injective

/-- Typed compatibility: pairwise only — membership in the polymer
    universe is carried by the subtype itself. -/
def TypedCompatible (Γ : Finset (Polymer N)) : Prop :=
  ∀ η ∈ Γ, ∀ θ ∈ Γ, η ≠ θ → PlaquetteCompatible η.val θ.val

noncomputable def typedCompatiblePolymerFamilies
    (N : ℕ) [NeZero N] [Fintype (Site N)] :
    Finset (Finset (Polymer N)) :=
  Finset.univ.filter (fun Γ => TypedCompatible Γ)

theorem mem_typedCompatiblePolymerFamilies
    {Γ : Finset (Polymer N)} :
    Γ ∈ typedCompatiblePolymerFamilies N ↔ TypedCompatible Γ := by
  unfold typedCompatiblePolymerFamilies
  simp [Finset.mem_filter]

/-! ## 49C-I.3 — compatibility equivalence across the bridge -/

theorem isCompatible_rawFamily_iff {Γ : Finset (Polymer N)} :
    IsCompatiblePolymerFamily (rawFamily Γ)
      ↔ TypedCompatible Γ := by
  constructor
  · intro h η hη θ hθ hne
    exact h.2 η.val (Finset.mem_image_of_mem _ hη)
      θ.val (Finset.mem_image_of_mem _ hθ)
      (fun hval => hne (Subtype.ext hval))
  · intro h
    constructor
    · intro C hC
      obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hC
      exact isPolymer_of_mem_all η.property
    · intro C hC D hD hne
      obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hD
      exact h η hη θ hθ
        (fun hs => hne (congrArg Subtype.val hs))

/-! ## 49C-I.4 — the typed gas and the EXACT reindexation -/

/-- The typed hard-core polymer gas. -/
noncomputable def typedPolymerGas (z : Polymer N → ℝ) : ℝ :=
  ∑ Γ ∈ typedCompatiblePolymerFamilies N, ∏ η ∈ Γ, z η

/-- **The exact reindexation** — product preserved EXACTLY; no
    factorial, no multiplicity: families are Finsets on both
    sides. The lift of a raw family is the attach-image with the
    membership proofs supplied by the compatibility hypothesis. -/
theorem typedPolymerGas_eq_raw
    (w : Finset (Site N × Dir × Dir) → ℝ) :
    typedPolymerGas (N := N) (fun η => w η.val)
      = ∑ Γ ∈ compatiblePolymerFamilies N, ∏ C ∈ Γ, w C := by
  unfold typedPolymerGas
  refine Finset.sum_bij (i := fun Γ _ => rawFamily Γ)
    ?_ ?_ ?_ ?_
  · intro Γ hΓ
    exact mem_compatiblePolymerFamilies.mpr
      (isCompatible_rawFamily_iff.mpr
        (mem_typedCompatiblePolymerFamilies.mp hΓ))
  · intro Γ₁ _ Γ₂ _ h
    exact rawFamily_injective h
  · intro Γraw hraw
    have hcomp := mem_compatiblePolymerFamilies.mp hraw
    refine ⟨Γraw.attach.image (fun C =>
      (⟨C.val, mem_all_of_isPolymer
        (hcomp.1 C.val C.property)⟩ : Polymer N)), ?_, ?_⟩
    · refine mem_typedCompatiblePolymerFamilies.mpr ?_
      intro η hη θ hθ hne
      obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hη
      obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hθ
      exact hcomp.2 C.val C.property D.val D.property
        (fun h => hne (Subtype.ext h))
    · unfold rawFamily
      rw [Finset.image_image]
      exact Finset.attach_image_val
  · intro Γ hΓ
    unfold rawFamily
    exact (Finset.prod_image
      (fun η _ θ _ h => Subtype.val_injective h)).symm

/-! ## 49C-I.5 — THE CAPSTONE -/

/-- **realZ has an exact finite hard-core gas representation over
    the TYPED polymer universe** — Stone 36 consumed, the bridge
    reindexed; full Stone-36 generality, NO smallness hypothesis:
    a finite identity, valid before any KP/convergence. -/
theorem realZ_eq_typed_polymer_gas {β : ℝ} (hβ : 0 ≤ β)
    {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) :
    realZ (N := N) μm β χ
      = typedPolymerGas (N := N)
          (fun η => polymerWeight (N := N) μm β χ η.val) := by
  rw [realZ_eq_finite_polymer_gas μm hβ mχ hχabs,
    typedPolymerGas_eq_raw
      (fun C => polymerWeight (N := N) μm β χ C)]

end LatticeGauge
