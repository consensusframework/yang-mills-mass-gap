/-
LatticeGauge/KPSpecialization.lean — stone 47c, GATE C: THE KEY
FITS THE LOCK (architecture: Sol/GPT-5.6; execution: Fable).

The 40000 key of stone 46 opens the abstract lock of stone 47:
C0, the ONLY real plumbing — the exact glue equality between the
indicator sum over the Polymer subtype and the raw sum over
incompatiblePolymers (two VISIBLE conversion steps: subtype ↔ raw
valid polymers via Finset.sum_subtype, censused at
BigOperators/Group/Finset.lean:989 — Polymer N is BY DEFINITION
{D // D ∈ allPlaquettePolymers N}, censused, no "presumably" —
then indicator ↔ filter via sum_filter, censused at :866; no giant
simp); C1, stone 46's β ≤ 1/40000 specialization delivers the
AbstractKPHypothesis for ρ = |polymerWeight| and a = card (the
threshold is NOT reproved); C2, the abstract induction of 47c-B is
consumed and every finite partial sum is bounded by exp(card),
plus the root-activity corollary (capital for stone 48, not
simplified further). NO new analysis: composition of existing
theorems only. NOT here: Summable, tsum, tendsto, limits, infinite
series, log Z, thermodynamic limit, clustering, mass gap — stone
47 ends EXACTLY at the uniform bound on ALL FINITE partial sums.
NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.PolymerGeometry
import LatticeGauge.PolymerGas
import LatticeGauge.LinkCovering
import LatticeGauge.KPSmallness
import LatticeGauge.KPCoefficients
import LatticeGauge.KPWeightFactorization
import LatticeGauge.KPStratification
import LatticeGauge.KPInduction

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## 47c-C0 — the glue (the hard gate: an EXACT equality before
    stone 46 is ever called) -/

/-- The indicator as a 0/1 ite on the incompatibility — the named
    lemma that turns all the following glue into ordinary filter
    manipulation. -/
theorem incompatibilityIndicator_eq_ite (γ₀ η : Polymer N) :
    ((incompatibilityIndicator γ₀ η : ℕ) : ℝ)
      = if ¬ PlaquetteCompatible γ₀.val η.val then 1 else 0 := by
  unfold incompatibilityIndicator
  by_cases h : PlaquetteCompatible γ₀.val η.val
  · rw [if_pos h, if_neg (not_not_intro h), Nat.cast_zero]
  · rw [if_neg h, if_pos h, Nat.cast_one]

/-- **C0 CAPSTONE (the glue)**: the indicator sum over the Polymer
    subtype IS the raw sum over the incompatible polymers — for any
    raw weight F, in two visible steps. -/
theorem sum_indicator_eq_sum_incompatible (γ₀ : Polymer N)
    (F : Finset (Site N × Dir × Dir) → ℝ) :
    (∑ η : Polymer N,
        ((incompatibilityIndicator γ₀ η : ℕ) : ℝ) * F η.val)
      = ∑ D ∈ incompatiblePolymers γ₀.val, F D := by
  calc (∑ η : Polymer N,
        ((incompatibilityIndicator γ₀ η : ℕ) : ℝ) * F η.val)
      = ∑ η : Polymer N,
          (if ¬ PlaquetteCompatible γ₀.val η.val then (1 : ℝ)
            else 0) * F η.val :=
        Finset.sum_congr rfl (fun η _ => by
          rw [incompatibilityIndicator_eq_ite])
    _ = ∑ D ∈ allPlaquettePolymers N,
          (if ¬ PlaquetteCompatible γ₀.val D then (1 : ℝ)
            else 0) * F D :=
        (Finset.sum_subtype (allPlaquettePolymers N)
          (fun _ => Iff.rfl)
          (fun D => (if ¬ PlaquetteCompatible γ₀.val D then (1 : ℝ)
            else 0) * F D)).symm
    _ = ∑ D ∈ allPlaquettePolymers N,
          (if ¬ PlaquetteCompatible γ₀.val D then F D else 0) :=
        Finset.sum_congr rfl (fun D _ => by
          by_cases h : ¬ PlaquetteCompatible γ₀.val D
          · rw [if_pos h, if_pos h, one_mul]
          · rw [if_neg h, if_neg h, zero_mul])
    _ = ∑ D ∈ (allPlaquettePolymers N).filter
          (fun D => ¬ PlaquetteCompatible γ₀.val D), F D :=
        (Finset.sum_filter _ _).symm
    _ = ∑ D ∈ incompatiblePolymers γ₀.val, F D := by
        unfold incompatiblePolymers

/-! ## 47c-C1 — the stone-46 key delivers the abstract hypothesis
    (the threshold is NOT reproved) -/

/-- **C1**: for β ≤ 1/40000, the concrete activity |polymerWeight|
    with a = card satisfies the ABSTRACT KP hypothesis — the glue,
    one reassociation, and the stone-46 specialization. -/
theorem abstractKP_of_beta_le_one_div_40000
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) :
    AbstractKPHypothesis (N := N)
      (fun η => |polymerWeight (N := N) μm β χ η.val|)
      (fun η => ((η.val.card : ℕ) : ℝ)) := by
  intro γ₀
  show (∑ η : Polymer N,
      ((incompatibilityIndicator γ₀ η : ℕ) : ℝ)
        * |polymerWeight (N := N) μm β χ η.val|
        * Real.exp (((η.val.card : ℕ) : ℝ)))
    ≤ ((γ₀.val.card : ℕ) : ℝ)
  calc (∑ η : Polymer N,
      ((incompatibilityIndicator γ₀ η : ℕ) : ℝ)
        * |polymerWeight (N := N) μm β χ η.val|
        * Real.exp (((η.val.card : ℕ) : ℝ)))
      = ∑ η : Polymer N,
          ((incompatibilityIndicator γ₀ η : ℕ) : ℝ)
            * (|polymerWeight (N := N) μm β χ η.val|
              * Real.exp (((η.val.card : ℕ) : ℝ))) :=
        Finset.sum_congr rfl (fun η _ => mul_assoc _ _ _)
    _ = ∑ D ∈ incompatiblePolymers γ₀.val,
          |polymerWeight (N := N) μm β χ D|
            * Real.exp ((D.card : ℝ)) :=
        sum_indicator_eq_sum_incompatible γ₀
          (fun D => |polymerWeight (N := N) μm β χ D|
            * Real.exp ((D.card : ℝ)))
    _ ≤ ((γ₀.val.card : ℕ) : ℝ) :=
        kp_hypothesis_beta_le_one_div_40000 μm hβ mχ hχabs
          hsmall γ₀.val

/-! ## 47c-C2 — THE STONE-47 CAPSTONE -/

/-- **THE STONE-47 CAPSTONE**: for 0 ≤ β ≤ 1/40000, EVERY finite
    partial sum of the rooted cluster coefficients with the real
    polymer activity is uniformly bounded by exp(card γ₀) — the
    abstract finite KP induction of 47c-B consumed with the
    stone-46 key. No passage M → ∞ occurs anywhere. -/
theorem polymer_kpPartialSum_le_exp_card
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (M : ℕ) (γ₀ : Polymer N) :
    kpPartialSum M
        (fun η => |polymerWeight (N := N) μm β χ η.val|) γ₀
      ≤ Real.exp (((γ₀.val.card : ℕ) : ℝ)) :=
  kpPartialSum_le_exp
    (fun _ => abs_nonneg _)
    (fun _ => Nat.cast_nonneg _)
    (abstractKP_of_beta_le_one_div_40000 μm hβ mχ hχabs hsmall)
    M γ₀

/-- **The root-activity corollary** (capital for stone 48 — not
    simplified into any other object). -/
theorem polymer_rooted_partialSum_bound
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (M : ℕ) (γ₀ : Polymer N) :
    |polymerWeight (N := N) μm β χ γ₀.val|
        * kpPartialSum M
            (fun η => |polymerWeight (N := N) μm β χ η.val|) γ₀
      ≤ |polymerWeight (N := N) μm β χ γ₀.val|
          * Real.exp (((γ₀.val.card : ℕ) : ℝ)) :=
  mul_le_mul_of_nonneg_left
    (polymer_kpPartialSum_le_exp_card μm hβ mχ hχabs hsmall M γ₀)
    (abs_nonneg _)

end LatticeGauge
